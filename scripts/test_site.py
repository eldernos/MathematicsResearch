"""Unit tests for the research landing site generator (scripts/site.py)."""

import importlib.util
import json
import pathlib
import re
import sys
import tempfile
import unittest
from html.parser import HTMLParser

import portal

# scripts/site.py shares its name with the standard-library module `site`, so load it by path.
_spec = importlib.util.spec_from_file_location("research_site", pathlib.Path(__file__).with_name("site.py"))
research_site = importlib.util.module_from_spec(_spec)
sys.modules["research_site"] = research_site
_spec.loader.exec_module(research_site)

BASE = "https://example.org/Repo/"
NOWHERE = pathlib.Path(tempfile.gettempdir()) / "no-such-manuscript-root"


class Collector(HTMLParser):
    def __init__(self):
        super().__init__()
        self.stack, self.tags, self.links, self.scripts, self.errors = [], [], [], [], []
        self.void = {"meta", "link", "br", "img", "hr", "input"}

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        self.tags.append((tag, a))
        if tag not in self.void:
            self.stack.append(tag)
        for key in ("href", "src"):
            if key in a:
                self.links.append(a[key])
        if tag == "script":
            self.scripts.append(a)

    def handle_endtag(self, tag):
        if tag in self.void:
            return
        if not self.stack or self.stack[-1] != tag:
            self.errors.append(f"unbalanced </{tag}> with stack {self.stack[-3:]}")
            if tag in self.stack:
                while self.stack and self.stack.pop() != tag:
                    pass
        else:
            self.stack.pop()


def parse(text):
    c = Collector()
    c.feed(text)
    c.close()
    return c


def wave2(**kw):
    p = {"number": "VI", "dir": "papers/06-x", "title": "A <Title> & More", "families": [], "principal": ["CC-48"],
         "status": "draft", "version": "1.0", "release": portal.CANDIDATE_TAG, "tags": [portal.CANDIDATE_TAG],
         "supersedes": "", "summary": "Summary with *emphasis* and $x^2$."}
    p.update(kw)
    return p


def released(**kw):
    p = wave2(dir="papers/01-x", number="I", version="1.1", release=portal.RELEASED_TAG, abstract="Old.",
              tags=["manuscripts-v1.0.0", portal.RELEASED_TAG])
    p.update(kw)
    return p


class HelperTests(unittest.TestCase):
    def test_inline(self):
        self.assertEqual(research_site.inline("a < b *c* $x$"), 'a &lt; b <em>c</em> <span class="math">x</span>')
        self.assertEqual(research_site.inline("2*3*4"), "2*3*4")

    def test_paragraphs(self):
        self.assertEqual(research_site.paragraphs("a\nb\n\n\nc"), ["a b", "c"])

    def test_bibtex_uses_named_author_only(self):
        (p,) = portal.enrich_papers([wave2(dir="papers/06-lambert")], root=NOWHERE)
        bib = research_site.bibtex(p, year="2026", url="https://x")
        self.assertTrue(bib.startswith("@unpublished{anderson-lambert,"))
        self.assertIn("author = {Anderson, Christopher}", bib)
        self.assertNotRegex(bib.lower(), r"orcid|e-?mail|@[a-z0-9-]+\.")

    def test_version_history(self):
        new = wave2(dir="papers/01-x-v2", number="I", version="2.0", supersedes="papers/01-x")
        papers = portal.enrich_papers([released(), new], root=NOWHERE)
        by_dir = {p["dir"]: p for p in papers}
        rows = research_site.history(papers[1], by_dir)
        self.assertEqual([(v, t) for v, t, _ in rows],
                         [("2.0", portal.CANDIDATE_TAG), ("1.1", portal.RELEASED_TAG), ("1.0", "manuscripts-v1.0.0")])
        self.assertEqual(rows[-1][2], "papers/01-x")

    def test_retained_paper_history(self):
        old = released(dir="papers/03-x", number="III",
                       tags=["manuscripts-v1.0.0", portal.RELEASED_TAG, portal.CANDIDATE_TAG])
        (p,) = portal.enrich_papers([old], root=NOWHERE)
        rows = research_site.history(p, {p["dir"]: p})
        self.assertEqual(rows[0][0], "1.1 (retained)")
        self.assertFalse(research_site.named_author(p))
        self.assertIn(portal.RELEASED_TAG, research_site.pdf_urls(p)[0])


class PageTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
        d = self.root / "papers/06-x"
        d.mkdir(parents=True)
        (d / "metadata.toml").write_text(
            'id = "06-x"\ntitle = "Disjunctive but Nonnormal"\nshort_title = "Lambert"\nversion = "1.0"\n'
            'status = "preprint draft"\n'
            "abstract = '''We show $D_N \\to 1$ for *every* series.\n\nSecond paragraph.'''\n"
            'keywords = ["normal numbers", "Lambert series"]\nmsc_primary = "11K16"\nmsc_secondary = ["11A63"]\n'
            f'supersedes = ""\nlean_commit = "{portal.WAVE2_LEAN_COMMIT}"\nregistry_ids = ["CC-48"]\n',
            encoding="utf-8")
        self.papers = portal.enrich_papers([released(), wave2()], root=self.root)
        self.by_dir = {p["dir"]: p for p in self.papers}

    def tearDown(self):
        self.tmp.cleanup()

    def html(self):
        return research_site.manuscript_page(self.papers[1], self.by_dir, BASE, strict=False)

    def test_wellformed_and_accessible(self):
        text = self.html()
        c = parse(text)
        self.assertEqual(c.errors, [])
        self.assertEqual(c.stack, [])
        self.assertIn('<html lang="en">', text)
        self.assertIn('name="viewport"', text)
        self.assertEqual(len(re.findall(r"<h1>", text)), 1)
        self.assertIn('class="skip"', text)
        self.assertEqual(len([t for t, _ in c.tags if t == "main"]), 1)

    def test_no_scripts_fonts_or_trackers(self):
        for text in (self.html(), research_site.index_page(self.papers, BASE)):
            c = parse(text)
            self.assertEqual([s for s in c.scripts if s.get("type") != "application/ld+json"], [])
            for url in c.links:
                if url.startswith("http"):
                    self.assertRegex(url, r"^https://(github\.com/eldernos|raw\.githubusercontent\.com/eldernos|"
                                          r"zbmath\.org/classification|example\.org)")
            self.assertNotIn("fonts.googleapis", text)
        self.assertNotIn("@import", research_site.STYLE)
        self.assertNotIn("url(", research_site.STYLE)

    def test_highwire_and_jsonld(self):
        text = self.html()
        c = parse(text)
        meta = {a["name"]: a["content"] for t, a in c.tags if t == "meta" and "name" in a}
        self.assertEqual(meta["citation_title"], "Disjunctive but Nonnormal")
        self.assertEqual(meta["citation_author"], "Anderson, Christopher")
        self.assertEqual(meta["citation_author_institution"], "Independent Researcher")
        self.assertRegex(meta["citation_publication_date"], r"^\d{4}/\d{2}/\d{2}$")
        self.assertEqual(meta["citation_pdf_url"],
                         f"{research_site.RAW}/{portal.CANDIDATE_TAG}/papers/06-x/paper.pdf")
        self.assertEqual(meta["citation_keywords"], "normal numbers; Lambert series")
        raw = re.search(r'<script type="application/ld\+json">\n(.*?)\n</script>', text, re.S).group(1)
        data = json.loads(raw)
        self.assertEqual(data["@type"], "ScholarlyArticle")
        self.assertEqual(data["author"]["@type"], "Person")
        self.assertEqual(data["author"]["name"], "Christopher Anderson")
        self.assertNotIn("email", raw.lower())
        self.assertNotIn("orcid", raw.lower())

    def test_content_sections(self):
        text = self.html()
        for needle in ("Abstract", "MSC2020", "Version history", "How to cite", "Formal verification",
                       "11K16", "(primary)", "VERIFICATION.md", "cross-model review is not", "@unpublished",
                       "fallback", "Christopher Anderson"):
            self.assertIn(needle, text)
        self.assertIn("<em>every</em>", text)
        self.assertIn("<p>We show", text)
        self.assertIn("Second paragraph.", text)

    def test_escaping_of_titles(self):
        (p,) = portal.enrich_papers([wave2()], root=self.root / "none")
        text = research_site.manuscript_page(p, {p["dir"]: p}, BASE, strict=False)
        self.assertNotIn("A <Title>", text)
        self.assertIn("A &lt;Title&gt; &amp; More", text)

    def test_pending_page_without_metadata(self):
        p = portal.enrich_papers([wave2(dir="papers/07-y")], root=self.root)[0]
        text = research_site.manuscript_page(p, {p["dir"]: p}, BASE, strict=False)
        self.assertIn("provisional registry summary", text)
        with self.assertRaises(SystemExit):
            research_site.manuscript_page(p, {p["dir"]: p}, BASE, strict=True)

    def test_archived_version_has_no_author_meta(self):
        text = research_site.manuscript_page(self.papers[0], self.by_dir, BASE, strict=False)
        self.assertNotIn("citation_author", text)
        self.assertNotIn('"author"', text)
        self.assertIn("carries no author line", text)

    def test_build_site_writes_expected_files(self):
        out = self.root / "out"
        written = research_site.build_site(self.papers, out, BASE)
        for name in ("index.html", "style.css", ".nojekyll", "404.html", "papers/06-x/index.html"):
            self.assertIn(name, written)
        index = (out / "index.html").read_text(encoding="utf-8")
        self.assertIn("Independent Researcher", index)
        self.assertIn("not\nindependent human peer review".replace("\n", " "), " ".join(index.split()))
        self.assertNotRegex(index, r"(?i)google scholar")


class BibliographyTests(unittest.TestCase):
    def test_bibliography_complete(self):
        _, papers = portal.load_registry()
        text = research_site.build_bibliography(papers)
        keys = re.findall(r"^@\w+\{([^,]+),", text, re.M)
        self.assertEqual(len(keys), len(set(keys)))
        self.assertEqual(sum(1 for p in papers if p["current"]) + 2, len(keys))
        for a in re.findall(r"^\s*author\s*=\s*\{([^}]*)\}", text, re.M):
            self.assertEqual(a, "Anderson, Christopher")


if __name__ == "__main__":
    unittest.main()
