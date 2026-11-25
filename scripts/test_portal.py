"""Unit tests for the documentation portal helpers (scripts/portal.py)."""

import copy
import pathlib
import tempfile
import unittest

import portal


class SlugTests(unittest.TestCase):
    """GitHub heading anchors, checked against headings that occur in this repository."""

    def test_plain(self):
        self.assertEqual(portal.slug("Reproduce and review"), "reproduce-and-review")

    def test_punctuation_and_case(self):
        self.assertEqual(portal.slug("I. Polynomial images of Stoneham numbers"),
                         "i-polynomial-images-of-stoneham-numbers")
        self.assertEqual(portal.slug("Higher orders and the lower-order residues (paper proof)"),
                         "higher-orders-and-the-lower-order-residues-paper-proof")

    def test_unicode_letters_kept(self):
        self.assertEqual(portal.slug("Hexadecimal observations for π"), "hexadecimal-observations-for-π")

    def test_markup_removed(self):
        self.assertEqual(portal.slug("A product on *different* prime axes"), "a-product-on-different-prime-axes")
        self.assertEqual(portal.slug("ST-01 · Polynomial images"), "st-01--polynomial-images")


class BlockTests(unittest.TestCase):
    def test_replace_empty_and_filled_blocks(self):
        text = "a\n<!-- BEGIN X -->\n<!-- END X -->\nb\n"
        once = portal.replace_block(text, "X", "body")
        self.assertEqual(once, "a\n<!-- BEGIN X -->\nbody\n<!-- END X -->\nb\n")
        self.assertEqual(portal.replace_block(once, "X", "body"), once)
        self.assertEqual(portal.replace_block(once, "Y", "other"), once)


class RegistryTests(unittest.TestCase):
    def test_identifiers_well_formed_and_unique(self):
        results, papers = portal.load_registry()
        ids = [r["id"] for r in results]
        self.assertEqual(len(ids), len(set(ids)))
        for rid in ids:
            self.assertRegex(rid, portal.ID_RE)
        for p in papers:
            self.assertIn(p["status"], portal.PAPER_STATUS)

    def test_first_sentence(self):
        self.assertEqual(portal.first_sentence("One. Two."), "One.")
        self.assertEqual(portal.first_sentence("a | b"), "a \\| b")


def paper(**kw):
    base = {"number": "I", "dir": "papers/01-x", "title": "T", "families": ["ST"], "principal": ["ST-01"],
            "status": "internally reviewed", "abstract": "A"}
    base.update(kw)
    return base


class ManuscriptTests(unittest.TestCase):
    def test_current_and_superseded(self):
        old = paper(release=portal.RELEASED_TAG)
        new = paper(dir="papers/01-x-v2", version="2.0", release=portal.CANDIDATE_TAG, supersedes="papers/01-x",
                    status="draft", summary="s", abstract="")
        out = portal.enrich_papers([old, new], root=pathlib.Path(tempfile.gettempdir()) / "no-such-root")
        self.assertFalse(out[0]["current"])
        self.assertEqual(out[0]["superseded_by"], "papers/01-x-v2")
        self.assertTrue(out[1]["current"])
        self.assertEqual(out[0]["layout"], "released")
        self.assertEqual(out[1]["layout"], "wave2")
        self.assertEqual(out[1]["abstract"], "s")
        self.assertTrue(out[1]["provisional"])
        self.assertEqual(out[0]["version"], "1.1")

    def test_metadata_overrides_registry(self):
        with tempfile.TemporaryDirectory() as d:
            root = pathlib.Path(d)
            (root / "papers/01-x-v2").mkdir(parents=True)
            (root / "papers/01-x-v2/metadata.toml").write_text(
                'title = "Meta Title"\nabstract = "Meta abstract."\nregistry_ids = ["ST-11"]\n',
                encoding="utf-8")
            new = paper(dir="papers/01-x-v2", version="2.0", release=portal.CANDIDATE_TAG, results=["ST-01"])
            (out,) = portal.enrich_papers([new], root=root)
        self.assertEqual(out["title"], "Meta Title")
        self.assertEqual(out["abstract"], "Meta abstract.")
        self.assertEqual(out["results"], ["ST-11"])
        self.assertFalse(out["provisional"])

    def test_paper_of_prefers_current_and_explicit_results(self):
        old = paper(release=portal.RELEASED_TAG)
        new = paper(dir="papers/01-x-v2", number="I", version="2.0", release=portal.CANDIDATE_TAG,
                    supersedes="papers/01-x")
        other = paper(dir="papers/06-y", number="VI", families=[], results=["ST-07"], release=portal.CANDIDATE_TAG)
        papers = portal.enrich_papers([old, new, other], root=pathlib.Path(tempfile.gettempdir()) / "none")
        self.assertEqual(portal.paper_of("ST-01", papers)["dir"], "papers/01-x-v2")
        self.assertEqual(portal.paper_of("ST-07", papers)["dir"], "papers/06-y")
        self.assertIsNone(portal.paper_of("CC-01", papers))

    def test_roman_order(self):
        order = ["IV", "II", "IX", "VIII", "I", "VI"]
        self.assertEqual(sorted(order, key=portal.roman_value), ["I", "II", "IV", "VI", "VIII", "IX"])

    def test_papers_block_has_current_and_superseded_tables(self):
        old = paper(release=portal.RELEASED_TAG, version="1.1")
        new = paper(dir="papers/01-x-v2", version="2.0", release=portal.CANDIDATE_TAG, supersedes="papers/01-x",
                    status="draft")
        papers = portal.enrich_papers([old, new], root=pathlib.Path(tempfile.gettempdir()) / "none")
        block = portal.build_papers_block(papers)
        self.assertIn("| I | **T** | 2.0 |", block)
        self.assertIn("Superseded manuscript", block)
        self.assertIn("papers/01-x-v2/VERIFICATION.md", block)
        self.assertIn("papers/01-x/REVIEW.md", block)

    def test_registry_papers_are_consistent(self):
        _, papers = portal.load_registry()
        dirs = {p["dir"] for p in papers}
        for p in papers:
            if p["supersedes"]:
                self.assertIn(p["supersedes"], dirs)
        current = [p for p in papers if p["current"]]
        self.assertEqual(len({p["number"] for p in current}), len(current))


class MetadataTests(unittest.TestCase):
    META = {"id": "06-x", "title": "T", "authors": ["Christopher Anderson"], "affiliation": "Independent Researcher",
            "short_title": "T", "version": "1.0", "status": "preprint draft",
            "abstract": "An abstract.", "keywords": ["normal numbers"], "msc_primary": "11K16",
            "msc_secondary": ["11A63", "37A45"], "supersedes": "", "lean_commit": portal.WAVE2_LEAN_COMMIT,
            "registry_ids": ["CC-48"]}

    def check(self, **kw):
        meta = copy.deepcopy(self.META)
        meta.update(kw)
        p = {"version": "1.0", "supersedes": ""}
        return portal.validate_metadata(meta, p, {"CC-48", "ST-01"})

    def test_valid(self):
        self.assertEqual(self.check(), [])

    def test_missing_key(self):
        meta = dict(self.META)
        del meta["keywords"]
        self.assertEqual(portal.validate_metadata(meta, {"version": "1.0", "supersedes": ""}, set()),
                         ["missing key keywords"])

    def test_detects_problems(self):
        self.assertTrue(any("MSC" in e for e in self.check(msc_primary="11K")))
        self.assertTrue(any("status" in e for e in self.check(status="draft")))
        self.assertEqual(self.check(status="research note"), [])
        self.assertTrue(any("lean_commit" in e for e in self.check(lean_commit="abc")))
        self.assertTrue(any("unknown registry" in e for e in self.check(registry_ids=["ST-99"])))
        self.assertTrue(any("peer-reviewed" in e for e in self.check(abstract="This is peer-reviewed.")))
        self.assertTrue(any("version" in e for e in self.check(version="2.0")))
        self.assertTrue(any("authors" in e for e in self.check(authors=["Someone Else"])))
        self.assertTrue(any("affiliation" in e for e in self.check(affiliation="University")))
        self.assertTrue(any("orcid" in e for e in self.check(orcid="0000-0000-0000-0000")))

    def test_supersedes_accepts_directory_spellings(self):
        meta = copy.deepcopy(self.META)
        meta.update(version="2.0", supersedes="papers/01-x/")
        p = {"version": "2.0", "supersedes": "papers/01-x"}
        self.assertEqual(portal.validate_metadata(meta, p, {"CC-48"}), [])
        meta["supersedes"] = "01-x"
        self.assertEqual(portal.validate_metadata(meta, p, {"CC-48"}), [])


if __name__ == "__main__":
    unittest.main()
