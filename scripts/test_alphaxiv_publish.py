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
    PAPER = ap.ROOT / "papers" / "06-multiplicative-lambert"

    def setUp(self) -> None:
        # Isolate from the live papers/alphaxiv-records.toml (VI is published there).
        patcher = mock.patch.object(ap, "find_record", return_value=None)
        patcher.start()
        self.addCleanup(patcher.stop)

    def inputs(self):
        return ap.load_inputs(self.PAPER, None)

    def test_dry_run_request_for_paper_06(self) -> None:
        meta, sub = self.inputs()
        self.assertEqual(meta["id"], "VI")
        request, confirmed = ap.build_request(meta, sub, None)
        self.assertFalse(confirmed)
        self.assertEqual(request["title"], "Disjunctive but Nonnormal Multiplicative Lambert Series")
        self.assertEqual(request["authors"], ["Christopher Anderson"])
        self.assertEqual(request["url_slug"], "disjunctive-nonnormal-multiplicative-lambert-series")
        self.assertNotIn("new_version_of", request)
        self.assertEqual(set(request["ai_disclosure"]["stages"]), set(ap.STAGES))
        self.assertEqual(len(request["ai_disclosure"]["tools"]), 4)

    def test_build_request_switches_to_new_version_of_when_recorded(self) -> None:
        meta, sub = self.inputs()
        record = {"id": "VI", "alphaxiv": "https://www.alphaxiv.org/abs/06-test-id",
                  "versions": [{"version": "0.9", "release": "manuscripts-v1.1.0"}]}
        with mock.patch.object(ap, "find_record", return_value=record):
            request, _ = ap.build_request(meta, sub, None)
        self.assertEqual(request.get("new_version_of"), "https://www.alphaxiv.org/abs/06-test-id")
        self.assertNotIn("url_slug", request)

    def test_record_url_must_be_alphaxiv(self) -> None:
        meta, sub = self.inputs()
        with mock.patch.object(ap, "find_record", return_value={"id": "VI", "alphaxiv": "https://evil.example/abs/1"}):
            with self.assertRaises(ap.Refusal):
                ap.build_request(meta, sub, None)

    def test_build_request_rejects_invalid_stages_tools_and_slugs(self) -> None:
        meta, sub = self.inputs()
        for mutate in (lambda d: d["ai_disclosure"]["stages"].__setitem__("writing", "invalid_rating"),
                       lambda d: d["ai_disclosure"].__setitem__("tools", []),
                       lambda d: d.__setitem__("url_slug", "x" * 121),
                       lambda d: d.__setitem__("url_slug", "Bad Slug")):
            bad = copy.deepcopy(sub)
            mutate(bad)
            with self.assertRaises(ap.Refusal):
                ap.build_request(meta, bad, None)

    def test_confirmation_requires_literal_true(self) -> None:
        meta, sub = self.inputs()
        for value in ("true", 1, "yes"):
            loose = copy.deepcopy(sub)
            loose["owner_confirmed"] = value
            self.assertFalse(ap.build_request(meta, loose, None)[1])

    def test_submission_state_is_read_from_control_ref(self) -> None:
        def fake_git(*args, check=True):
            if args[0] == "show" and args[1].endswith("submission/alphaxiv.toml"):
                return 'owner_confirmed = true\n[ai_disclosure.stages]\nidea = "mixed"\n'
            return ""
        with mock.patch.object(ap, "git", side_effect=fake_git):
            meta, sub = ap.load_inputs(self.PAPER, "refs/remotes/origin/main")
        self.assertIs(sub["owner_confirmed"], True)
        self.assertEqual(meta["id"], "VI")  # metadata still comes from the checked-out release tree


class LiveRecordTests(unittest.TestCase):
    def test_published_manuscripts_post_new_versions(self) -> None:
        for d, num in (("06-multiplicative-lambert", "VI"), ("01-stoneham-polynomials-v2", "I"),
                       ("07-synthetic-expansions", "VII"), ("10-discrepancy-arithmetic", "X")):
            meta, sub = ap.load_inputs(ap.ROOT / "papers" / d, None)
            request, _ = ap.build_request(meta, sub, None)
            self.assertTrue(request["new_version_of"].startswith("https://www.alphaxiv.org/abs/2611."), d)
            self.assertNotIn("url_slug", request)


class ReleaseAndPdfGuardTests(unittest.TestCase):
    META = {"id": "VI", "version": "1.0"}
    CONTROL = "refs/remotes/origin/main"

    def test_check_pdf_accepts_recorded_working_tree_pdf(self) -> None:
        paper_dir = ap.ROOT / "papers" / "06-multiplicative-lambert"
        self.assertEqual(ap.check_pdf(paper_dir, None), paper_dir / "paper.pdf")

    def test_check_pdf_rejects_checksum_mismatch(self) -> None:
        paper_dir = ap.ROOT / "papers" / "06-multiplicative-lambert"
        with mock.patch.object(ap, "git", return_value="00" * 32 + "  papers/06-multiplicative-lambert/paper.pdf\n"):
            with self.assertRaises(ap.Refusal):
                ap.check_pdf(paper_dir, "refs/tags/manuscripts-v2.0.0")

    def test_check_release_rejects_unapproved_tag(self) -> None:
        for tag in ("manuscripts-v1.1.0", "not-a-tag"):
            with self.assertRaises(ap.Refusal):
                ap.check_release(self.META, tag, self.CONTROL)

    def _git(self, tag="1" * 40, head="1" * 40, status="", control="3" * 40):
        def fake(*args, check=True):
            if args[:3] == ("rev-parse", "--verify", "--quiet"):
                return (tag if args[3].startswith("refs/tags/") else control) + "\n"
            if args == ("rev-parse", "HEAD"):
                return head + "\n"
            if args[:2] == ("status", "--porcelain"):
                return status
            return ""
        return fake

    def test_check_release_guards(self) -> None:
        cases = [(dict(tag=""), "does not exist"), (dict(head="2" * 40), "not the commit tagged"),
                 (dict(status=" M papers/x\n"), "uncommitted changes"), (dict(control=""), "control ref")]
        for kwargs, message in cases:
            with mock.patch.object(ap, "git", side_effect=self._git(**kwargs)):
                with self.assertRaises(ap.Refusal) as ctx:
                    ap.check_release(self.META, "manuscripts-v2.0.0", self.CONTROL)
                self.assertIn(message, str(ctx.exception))

    def test_duplicate_version_refused_and_new_version_allowed(self) -> None:
        recorded = {"id": "VI", "alphaxiv": "https://www.alphaxiv.org/abs/t", "versions": [{"version": "1.0"}]}
        with mock.patch.object(ap, "git", side_effect=self._git()), mock.patch.object(ap, "find_record", return_value=recorded):
            with self.assertRaises(ap.Refusal) as ctx:
                ap.check_release(self.META, "manuscripts-v2.0.0", self.CONTROL)
            self.assertIn("already recorded", str(ctx.exception))
        older = {"id": "VI", "alphaxiv": "https://www.alphaxiv.org/abs/t", "versions": [{"version": "0.9"}]}
        with mock.patch.object(ap, "git", side_effect=self._git()), mock.patch.object(ap, "find_record", return_value=older):
            ap.check_release(self.META, "manuscripts-v2.0.0", self.CONTROL)


class TransportTests(unittest.TestCase):
    def test_redirects_are_refused(self) -> None:
        handler = ap._NoRedirect()
        req = urllib.request.Request("https://api.alphaxiv.org/mcp/v1", headers={"Authorization": "Bearer k"})
        with self.assertRaises(ap.Refusal):
            handler.redirect_request(req, None, 302, "Found", {}, "https://evil.example/")

    def test_credentials_never_leave_alphaxiv(self) -> None:
        with self.assertRaises(ap.Refusal):
            ap.post_json("https://evil.example/mcp", {"id": "1"}, "secret")

    def test_sse_response_selects_matching_id(self) -> None:
        body = ('event: message\ndata: {"jsonrpc":"2.0","id":"other","result":{}}\n\n'
                'event: message\ndata: {"jsonrpc":"2.0","id":"abc",\ndata: "result":{"ok":true}}\n\n')

        class Response:
            def __enter__(self):
                return self

            def __exit__(self, *exc):
                return False

            def read(self):
                return body.encode()

        with mock.patch.object(ap.OPENER, "open", return_value=Response()):
            message = ap.post_json(ap.ENDPOINT, {"id": "abc"}, "k")
        self.assertEqual(message["result"], {"ok": True})

    def test_outcome_parsing_handles_fenced_json(self) -> None:
        self.assertEqual(ap.parse_outcome('Done.\n```json\n{"status": "published", "url": "u"}\n```')["status"], "published")
        self.assertEqual(ap.parse_outcome("plain text")["raw"], "plain text")


class UploadInstructionParsingTests(unittest.TestCase):
    def test_parser_handles_fences_continuations_and_fields(self) -> None:
        text = ("Upload the PDF:\n```bash\ncurl -X POST https://api.alphaxiv.org/v1/pdf \\\n"
                "  -H 'Authorization: Bearer $KEY' -H 'X-Upload-Token: t1' \\\n"
                "  -F 'key=uploads/1' -F 'file=@paper.pdf'\n```\nDon't forget to ask the operator.")
        url, headers, fields, file_field = ap.parse_upload_command(text)
        self.assertEqual(url, "https://api.alphaxiv.org/v1/pdf")
        self.assertNotIn("authorization", headers)  # Authorization is never taken from the instructions
        self.assertEqual(headers["x-upload-token"], "t1")
        self.assertEqual(fields, {"key": "uploads/1"})
        self.assertEqual(file_field, "file")

    def test_parser_rejects_unsafe_field_names_and_http(self) -> None:
        with self.assertRaises(ap.Refusal):
            ap.parse_upload_command('curl https://api.alphaxiv.org/u -F \'a"b=@paper.pdf\'')
        with self.assertRaises(ap.Refusal):
            ap.parse_upload_command("curl -X POST http://storage.example.com/upload -F file=@paper.pdf")

    def test_external_upload_host_receives_no_credentials(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / "paper.pdf"
            pdf.write_bytes(b"%PDF-1.5\nhello\n%%EOF\n")
            captured: list[urllib.request.Request] = []

            class Response:
                def __enter__(self):
                    return self

                def __exit__(self, *exc):
                    return False

                def read(self):
                    return b'{"pdfId": "3f2b8c1e-9a4d-4e7b-8c2f-1d5e6a7b9c0d"}'

            def fake_open(req, timeout=300):
                captured.append(req)
                return Response()

            with mock.patch.object(ap, "tool", return_value='curl -X POST https://storage.googleapis.com/slot '
                                   '-H "x-upload-token: tok-123" -F "pdf=@paper.pdf"'), \
                    mock.patch.object(ap.OPENER, "open", side_effect=fake_open):
                self.assertEqual(ap.upload(pdf, "secret-key"), "3f2b8c1e-9a4d-4e7b-8c2f-1d5e6a7b9c0d")
            sent = captured[0]
            self.assertIsNone(sent.get_header("Authorization"))
            self.assertEqual(sent.get_header("X-upload-token"), "tok-123")
            self.assertIn(b'name="pdf"; filename="paper.pdf"', sent.data)


if __name__ == "__main__":
    unittest.main()
