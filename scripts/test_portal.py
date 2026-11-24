"""Unit tests for the documentation portal helpers (scripts/portal.py)."""

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


if __name__ == "__main__":
    unittest.main()
