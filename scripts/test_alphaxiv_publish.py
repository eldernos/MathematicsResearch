#!/usr/bin/env python3
"""Unit tests for the security and release guards in scripts/alphaxiv_publish.py."""
from __future__ import annotations

import copy
import sys
import tempfile
import unittest
import urllib.request
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import alphaxiv_publish as ap


class TrustedHostTests(unittest.TestCase):
    def test_valid_alphaxiv_hosts(self) -> None:
        self.assertTrue(ap.trusted_host("https://alphaxiv.org/mcp/v1"))
        self.assertTrue(ap.trusted_host("https://api.alphaxiv.org/mcp/v1"))
        self.assertTrue(ap.trusted_host("https://UPLOAD.API.ALPHAXIV.ORG/v1/files"))

    def test_rejects_non_https_schemes(self) -> None:
        self.assertFalse(ap.trusted_host("http://api.alphaxiv.org/mcp/v1"))
        self.assertFalse(ap.trusted_host("ftp://api.alphaxiv.org/file.pdf"))
        self.assertFalse(ap.trusted_host("file:///etc/passwd"))
        self.assertFalse(ap.trusted_host("javascript://api.alphaxiv.org/%0aalert(1)"))
        self.assertFalse(ap.trusted_host("//api.alphaxiv.org/mcp/v1"))

    def test_rejects_suffix_and_prefix_bypasses(self) -> None:
        self.assertFalse(ap.trusted_host("https://alphaxiv.org.evil.com/mcp/v1"))
        self.assertFalse(ap.trusted_host("https://api.alphaxiv.org.evil.com/mcp/v1"))
        self.assertFalse(ap.trusted_host("https://evilalphaxiv.org/mcp/v1"))
        self.assertFalse(ap.trusted_host("https://evil-alphaxiv.org/mcp/v1"))
        self.assertFalse(ap.trusted_host("https://alphaxiv.com/mcp/v1"))

    def test_rejects_userinfo_host_confusion_and_idn_homoglyphs(self) -> None:
        self.assertFalse(ap.trusted_host("https://api.alphaxiv.org@evil.com/mcp/v1"))
        self.assertFalse(ap.trusted_host("https://user:api.alphaxiv.org@evil.com/mcp/v1"))
        # Cyrillic 'а' (U+0430) homoglyph in domain suffix
        self.assertFalse(ap.trusted_host("https://api.\u0430lphaxiv.org/mcp/v1"))
        self.assertFalse(ap.trusted_host("https://storage.googleapis.com/upload/bucket"))

    def test_redirect_handler_forwards_authorization_by_default(self) -> None:
        """Demonstrate Finding 1: urllib's default HTTPRedirectHandler copies Authorization across hosts."""
        handler = urllib.request.HTTPRedirectHandler()
        req = urllib.request.Request(
            "https://api.alphaxiv.org/upload",
            data=b"pdf-bytes",
            method="POST",
            headers={"Authorization": "Bearer secret-api-key", "Content-Type": "application/pdf"},
        )
        redirected = handler.redirect_request(
            req, fp=None, code=302, msg="Found", headers={}, newurl="https://evil.example.com/collect"
        )
        self.assertIsNotNone(redirected)
        self.assertEqual(redirected.full_url, "https://evil.example.com/collect")
        self.assertEqual(redirected.get_header("Authorization"), "Bearer secret-api-key")


class BuildRequestAndDisclosureTests(unittest.TestCase):
    def test_dry_run_request_for_paper_06(self) -> None:
        paper_dir = ap.ROOT / "papers" / "06-multiplicative-lambert"
        request, confirmed = ap.build_request(paper_dir)
        self.assertFalse(confirmed)
        self.assertEqual(request["title"], "Disjunctive but Nonnormal Multiplicative Lambert Series")
        self.assertEqual(request["authors"], ["Christopher Anderson"])
        self.assertEqual(request["url_slug"], "disjunctive-nonnormal-multiplicative-lambert-series")
        self.assertNotIn("new_version_of", request)
        self.assertEqual(set(request["ai_disclosure"]["stages"]), set(ap.STAGES))
        self.assertEqual(len(request["ai_disclosure"]["tools"]), 4)

    def test_build_request_switches_to_new_version_of_when_recorded(self) -> None:
        paper_dir = ap.ROOT / "papers" / "06-multiplicative-lambert"
        meta, _ = ap.manuscript(paper_dir)
        fake_record = {
            "id": meta["id"],
            "alphaxiv": "https://www.alphaxiv.org/abs/06-test-id",
            "versions": [{"version": "0.9", "release": "manuscripts-v1.1.0"}],
        }
        with mock.patch.object(ap, "find_record", return_value=fake_record):
            request, _ = ap.build_request(paper_dir)
        self.assertEqual(request.get("new_version_of"), "https://www.alphaxiv.org/abs/06-test-id")
        self.assertNotIn("url_slug", request)

    def test_build_request_rejects_invalid_stages_and_tools(self) -> None:
        paper_dir = ap.ROOT / "papers" / "06-multiplicative-lambert"
        meta, sub = ap.manuscript(paper_dir)

        bad_stages = copy.deepcopy(sub)
        bad_stages["ai_disclosure"]["stages"]["writing"] = "invalid_rating"
        with mock.patch.object(ap, "manuscript", return_value=(meta, bad_stages)):
            with self.assertRaises(ap.Refusal):
                ap.build_request(paper_dir)

        empty_tools = copy.deepcopy(sub)
        empty_tools["ai_disclosure"]["tools"] = []
        with mock.patch.object(ap, "manuscript", return_value=(meta, empty_tools)):
            with self.assertRaises(ap.Refusal):
                ap.build_request(paper_dir)


class ReleaseAndPdfGuardTests(unittest.TestCase):
    def test_check_pdf_accepts_recorded_working_tree_pdf(self) -> None:
        paper_dir = ap.ROOT / "papers" / "06-multiplicative-lambert"
        pdf = ap.check_pdf(paper_dir, None)
        self.assertEqual(pdf, paper_dir / "paper.pdf")

    def test_check_pdf_rejects_checksum_mismatch(self) -> None:
        paper_dir = ap.ROOT / "papers" / "06-multiplicative-lambert"
        with mock.patch.object(ap, "git", return_value="00" * 32 + "  papers/06-multiplicative-lambert/paper.pdf\n"):
            with self.assertRaises(ap.Refusal):
                ap.check_pdf(paper_dir, "manuscripts-v2.0.0")

    def test_check_release_rejects_unapproved_tag(self) -> None:
        meta = {"id": "A", "version": "1.0"}
        with self.assertRaises(ap.Refusal):
            ap.check_release(meta, "manuscripts-v1.1.0")
        with self.assertRaises(ap.Refusal):
            ap.check_release(meta, "not-a-tag")

    def test_check_release_rejects_commit_mismatch_dirty_tree_and_duplicate_version(self) -> None:
        meta = {"id": "A", "version": "1.0"}

        # 1. Commit mismatch between tag and HEAD
        def git_mismatch(*args: str) -> str:
            if args[:3] == ("rev-parse", "--verify", "--quiet"):
                return "1111111111111111111111111111111111111111\n"
            if args == ("rev-parse", "HEAD"):
                return "2222222222222222222222222222222222222222\n"
            return ""

        with mock.patch.object(ap, "git", side_effect=git_mismatch):
            with self.assertRaises(ap.Refusal) as ctx:
                ap.check_release(meta, "manuscripts-v2.0.0")
            self.assertIn("not the commit tagged", str(ctx.exception))

        # 2. Dirty working tree
        def git_dirty(*args: str) -> str:
            if "rev-parse" in args:
                return "1111111111111111111111111111111111111111\n"
            if args[:2] == ("status", "--porcelain"):
                return " M papers/06-multiplicative-lambert/paper.pdf\n"
            return ""

        with mock.patch.object(ap, "git", side_effect=git_dirty):
            with self.assertRaises(ap.Refusal) as ctx:
                ap.check_release(meta, "manuscripts-v2.0.0")
            self.assertIn("uncommitted changes", str(ctx.exception))

        # 3. Duplicate version already recorded
        def git_clean(*args: str) -> str:
            if "rev-parse" in args:
                return "1111111111111111111111111111111111111111\n"
            return ""

        recorded = {"id": "A", "alphaxiv": "https://www.alphaxiv.org/abs/test", "versions": [{"version": "1.0"}]}
        with mock.patch.object(ap, "git", side_effect=git_clean), mock.patch.object(
            ap, "find_record", return_value=recorded
        ):
            with self.assertRaises(ap.Refusal) as ctx:
                ap.check_release(meta, "manuscripts-v2.0.0")
            self.assertIn("already recorded", str(ctx.exception))

        # 4. Clean tree, exact tag commit, unrecorded version -> passes
        unrecorded = {"id": "A", "alphaxiv": "https://www.alphaxiv.org/abs/test", "versions": [{"version": "0.9"}]}
        with mock.patch.object(ap, "git", side_effect=git_clean), mock.patch.object(
            ap, "find_record", return_value=unrecorded
        ):
            ap.check_release(meta, "manuscripts-v2.0.0")


class UploadInstructionParsingTests(unittest.TestCase):
    def test_upload_refuses_non_https_url_and_Withholds_credentials_from_external_host(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / "paper.pdf"
            pdf.write_bytes(b"%PDF-1.5\nhello\n%%EOF\n")

            # Non-HTTPS upload URL in instructions must be refused before any network request
            with mock.patch.object(
                ap,
                "tool",
                return_value='curl -X POST http://storage.example.com/upload -F "file=@paper.pdf"',
            ):
                with self.assertRaises(ap.Refusal) as ctx:
                    ap.upload(pdf, "secret-key")
                self.assertIn("non-https", str(ctx.exception))

            # External HTTPS storage host must NOT receive Authorization header
            captured_requests: list[urllib.request.Request] = []

            class FakeResponse:
                def __enter__(self):
                    return self

                def __exit__(self, *exc):
                    return False

                def read(self) -> bytes:
                    return b'{"pdfId": "3f2b8c1e-9a4d-4e7b-8c2f-1d5e6a7b9c0d"}'

            def fake_urlopen(req: urllib.request.Request, timeout: int = 300):
                captured_requests.append(req)
                return FakeResponse()

            with mock.patch.object(
                ap,
                "tool",
                return_value='curl -X POST https://storage.googleapis.com/alphaxiv-uploads/slot '
                '-H "x-upload-token: tok-123" -F "pdf=@paper.pdf"',
            ), mock.patch.object(urllib.request, "urlopen", side_effect=fake_urlopen):
                pdf_id = ap.upload(pdf, "secret-key")

            self.assertEqual(pdf_id, "3f2b8c1e-9a4d-4e7b-8c2f-1d5e6a7b9c0d")
            self.assertEqual(len(captured_requests), 1)
            sent = captured_requests[0]
            self.assertIsNone(sent.get_header("Authorization"))
            self.assertEqual(sent.get_header("X-upload-token"), "tok-123")
            self.assertIn(b'name="pdf"; filename="paper.pdf"', sent.data)


if __name__ == "__main__":
    unittest.main()
