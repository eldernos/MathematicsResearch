"""Tests for the CITATION.cff structural check (scripts/check_citation.py)."""

import pathlib
import unittest

import check_citation as cc

ROOT = pathlib.Path(__file__).resolve().parent.parent


class CitationTests(unittest.TestCase):
    def test_repository_file_is_valid(self):
        data = cc.parse((ROOT / "CITATION.cff").read_text(encoding="utf-8"))
        self.assertEqual(cc.check(data), [])
        self.assertEqual(data["version"], "manuscripts-v2.0.0")
        self.assertEqual(data["type"], "software")
        self.assertEqual(data["license"], "MIT")

    def test_candidate_comment_present(self):
        self.assertRegex((ROOT / "CITATION.cff").read_text(encoding="utf-8"), r"(?i)#\s*CANDIDATE")

    def load(self):
        return cc.parse((ROOT / "CITATION.cff").read_text(encoding="utf-8"))

    def test_rejects_unapproved_fields(self):
        data = self.load()
        data["authors"][0]["orcid"] = "https://orcid.org/0000-0000-0000-0000"
        self.assertTrue(any("not approved" in e for e in cc.check(data)))
        data = self.load()
        data["authors"].append({"family-names": "Doe", "given-names": "Jane"})
        self.assertTrue(cc.check(data))

    def test_rejects_missing_and_unknown_keys(self):
        data = self.load()
        del data["title"]
        data["colour"] = "red"
        errs = cc.check(data)
        self.assertIn("missing required key title", errs)
        self.assertIn("unknown key colour", errs)

    def test_parser_handles_maps_and_lists(self):
        got = cc.parse('a: "x y"\nl:\n  - "p"\n  - q\nm:\n  - k: v\n    j: w\n')
        self.assertEqual(got, {"a": "x y", "l": ["p", "q"], "m": [{"k": "v", "j": "w"}]})
        with self.assertRaises(ValueError):
            cc.parse("a: 1\na: 2\n")


if __name__ == "__main__":
    unittest.main()
