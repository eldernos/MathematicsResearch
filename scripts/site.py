#!/usr/bin/env python3
"""Build the static research landing site and the manuscript bibliography.

    python3 scripts/site.py build [--out site] [--strict] [--base-url URL]
    python3 scripts/site.py bib [--check]      # write (or verify) papers/BIBLIOGRAPHY.bib

``build`` writes plain HTML and one stylesheet into ``site/`` (git-ignored build output): an index page and one
page per current manuscript. The pages need no JavaScript, load no external fonts, scripts or trackers, and
carry Highwire Press ``citation_*`` meta tags and schema.org ``ScholarlyArticle`` JSON-LD. The data come from
``docs/registry/papers.toml`` and from each manuscript's ``metadata.toml`` (see scripts/portal.py). With
``--strict`` a missing ``metadata.toml`` or ``paper.pdf`` is an error; without it the page is built from the
registry summary and marked as pending.

Nothing here submits anything to an index. The meta tags and structured data describe the pages; whether any
search service lists them is outside this repository's control.
"""

from __future__ import annotations

import argparse
import datetime
import html
import json
import tomllib
import pathlib
import re
import subprocess
import sys

import portal

ROOT = portal.ROOT
REPO = portal.REPO
RAW = "https://raw.githubusercontent.com/eldernos/MathematicsResearch"
BASE_URL = "https://eldernos.github.io/MathematicsResearch/"
DEFAULT_BRANCH = "main"
SITE_TITLE = "Normality and Discrepancy of Arithmetic Expansions"
DESCRIPTION = ("AI-assisted mathematical research on normal numbers, digit discrepancy, Stoneham constants, and "
               "arithmetic expansions, with Lean 4 proofs and reproducible preprints.")
AUTHOR_GIVEN, AUTHOR_FAMILY, AFFILIATION = "Christopher", "Anderson", "Independent Researcher"
AUTHOR_NAME = f"{AUTHOR_GIVEN} {AUTHOR_FAMILY}"
AUTHOR_BIB = f"{AUTHOR_FAMILY}, {AUTHOR_GIVEN}"
AUTHOR_PROFILE = "https://www.alphaxiv.org/@christopher-anderson"  # owner-supplied alphaXiv profile
BIB_FILE = "papers/BIBLIOGRAPHY.bib"
CANDIDATE_YEAR = "2026"
REVIEW_STATEMENT = ("Not peer reviewed. The written proofs, literature comparisons and priority statements have "
                    "been checked only by AI models from different providers; cross-model review is not "
                    "independent human peer review. The Lean kernel checks only the declarations listed in each "
                    "manuscript's verification map.")
AI_STATEMENT = ("The research was carried out with extensive AI assistance: mathematical exploration, proof "
                "development, Lean 4 formalization, computational verification, literature investigation and "
                "manuscript preparation were done largely by large language models from several providers, "
                "directed by the repository owner, who is responsible for its release.")

STYLE = """\
:root{--bg:#fbfbf8;--fg:#1c1f23;--muted:#4a525c;--line:#d5d8dc;--link:#0b5cad;--visited:#5b3d9a;--card:#f1f3f5;--warn:#7a3b00;--warnbg:#fff4e5}
@media (prefers-color-scheme:dark){:root{--bg:#14171a;--fg:#e8eaed;--muted:#aab2bb;--line:#363c43;--link:#7fb8f5;--visited:#b9a0f0;--card:#1d2226;--warn:#ffcf99;--warnbg:#2b2113}}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--fg);font:1.0625rem/1.6 system-ui,-apple-system,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif}
.wrap{max-width:48rem;margin:0 auto;padding:0 1rem 3rem}
a{color:var(--link)}a:visited{color:var(--visited)}
a:focus-visible,summary:focus-visible{outline:3px solid var(--link);outline-offset:2px}
.skip{position:absolute;left:-999px;top:0;background:var(--card);padding:.5rem 1rem}.skip:focus{left:0;z-index:10}
header.site{border-bottom:1px solid var(--line);margin-bottom:1.5rem}
header.site .wrap{padding-top:.75rem;padding-bottom:.75rem;display:flex;flex-wrap:wrap;gap:.25rem 1.25rem;align-items:baseline}
header.site strong{font-size:1rem}
nav ul{list-style:none;margin:0;padding:0;display:flex;flex-wrap:wrap;gap:.25rem 1rem}
h1{font-size:1.75rem;line-height:1.25;margin:.5rem 0}h2{font-size:1.3rem;margin:2rem 0 .5rem}h3{font-size:1.1rem}
.byline{color:var(--muted);margin:.25rem 0 1rem}
.notice{background:var(--warnbg);color:var(--warn);border:1px solid var(--line);border-left:4px solid var(--warn);padding:.6rem .9rem;border-radius:4px;margin:1rem 0}
.pill{display:inline-block;border:1px solid var(--line);border-radius:999px;padding:0 .6rem;font-size:.9rem;background:var(--card);margin-right:.35rem}
.scroll{overflow-x:auto}
table{border-collapse:collapse;width:100%;font-size:.97rem}
th,td{border-bottom:1px solid var(--line);padding:.4rem .5rem;text-align:left;vertical-align:top}
th{background:var(--card)}
pre{background:var(--card);border:1px solid var(--line);padding:.75rem;overflow-x:auto;font-size:.9rem;border-radius:4px}
code{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:.92em}
.math{font-family:"Cambria Math","STIX Two Math","Latin Modern Math",serif;font-style:italic}
ul.plain{padding-left:1.2rem}
footer{border-top:1px solid var(--line);margin-top:2.5rem;padding-top:1rem;color:var(--muted);font-size:.95rem}
@media (max-width:40em){h1{font-size:1.5rem}body{font-size:1rem}}
@media print{header.site nav,.skip{display:none}}
"""


# ---------------------------------------------------------------------------
# small helpers

def esc(s) -> str:
    return html.escape(str(s), quote=True)


def inline(text: str) -> str:
    """Escape text and render the *emphasis* and $tex$ spans that appear in abstracts."""
    out = esc(text)
    out = re.sub(r"\$([^$]+)\$", lambda m: f'<span class="math">{m.group(1)}</span>', out)
    return re.sub(r"(?<![\w*])\*([^*\n]+)\*(?![\w*])", r"<em>\1</em>", out)


def paragraphs(text: str):
    return [" ".join(chunk.split()) for chunk in re.split(r"\n\s*\n", text.strip()) if chunk.strip()]


def git(*args) -> str:
    try:
        out = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    except OSError:
        return ""
    return out.stdout.strip() if out.returncode == 0 else ""


def tag_exists(tag: str) -> bool:
    return bool(git("rev-parse", "-q", "--verify", f"refs/tags/{tag}^{{commit}}"))


def tag_date(tag: str) -> str:
    return git("log", "-1", "--format=%cs", tag) if tag_exists(tag) else ""


def paper_date(p) -> str:
    """ISO date of the manuscript: metadata ``date``, else the last commit touching its directory."""
    meta = p.get("metadata") or {}
    if meta.get("date"):
        return str(meta["date"])
    return git("log", "-1", "--format=%cs", "--", p["dir"]) or datetime.date.today().isoformat()


def slug(p) -> str:
    return portal.dir_name(p["dir"])


def named_author(p) -> bool:
    """The wave-2 manuscripts carry the author line; the archived v1.1 PDFs do not."""
    return p["layout"] == "wave2"


def pdf_urls(p, tag=None, directory=None):
    tag = tag or p["release"]
    d = directory or p["dir"]
    return f"{RAW}/{tag}/{d}/paper.pdf", f"{REPO}/blob/{DEFAULT_BRANCH}/{d}/paper.pdf"


def tag_version(e, tag) -> str:
    if tag == "manuscripts-v1.0.0":
        return "1.0"
    if tag == portal.RELEASED_TAG and e["layout"] == "released":
        return "1.1"
    return e["version"] + (" (retained)" if e["layout"] == "released" else "")


def history(p, by_dir):
    """Rows (version, tag, directory) for the manuscript and the versions it supersedes, newest first."""
    rows, e = [], p
    while e:
        for tag in reversed(e["tags"]):
            rows.append((tag_version(e, tag), tag, e["dir"]))
        e = by_dir.get(e.get("supersedes"))
    return rows


# ---------------------------------------------------------------------------
# citation data

def bib_key(p) -> str:
    return "anderson-" + re.sub(r"^\d+-", "", slug(p))


def bib_note(p) -> str:
    if p["layout"] == "released":
        return (f"Version {p['version']}, release {portal.RELEASED_TAG}. Preprint draft; not peer reviewed. "
                "The archived PDF carries no author line.")
    note = (f"Version {p['version']}, preprint draft in release {portal.CANDIDATE_TAG}. "
            "Not peer reviewed. AI-assisted research; see the AI-use statement in the manuscript.")
    ax = alphaxiv_record(p.get("metadata"))
    if ax:
        note += f" Also posted on alphaXiv's AI Track (screening is not peer review): {ax}."
    return note


def bibtex(p, year=None, url=None) -> str:
    year = year or CANDIDATE_YEAR
    url = url or f"{REPO}/tree/{DEFAULT_BRANCH}/{p['dir']}"
    return (f"@unpublished{{{bib_key(p)},\n"
            f"  author = {{{AUTHOR_BIB}}},\n"
            f"  title  = {{{p['title']}}},\n"
            f"  year   = {{{year}}},\n"
            f"  note   = {{{bib_note(p)}}},\n"
            f"  url    = {{{url}}}\n}}")


def release_bibtex(tag, year, papers_list) -> str:
    key = "anderson-release-" + tag.removeprefix("manuscripts-")
    return (f"@misc{{{key},\n"
            f"  author       = {{{AUTHOR_BIB}}},\n"
            f"  title        = {{{SITE_TITLE}: manuscript release {tag.removeprefix('manuscripts-')}}},\n"
            f"  year         = {{{year}}},\n"
            f"  howpublished = {{GitHub release {tag}}},\n"
            f"  note         = {{{papers_list}}},\n"
            f"  url          = {{{REPO}/releases/tag/{tag}}}\n}}")


def build_bibliography(papers) -> str:
    out = ["% Generated by scripts/site.py bib from docs/registry/papers.toml. Do not edit by hand.",
           "% Author: Christopher Anderson, Independent Researcher (no ORCID, email or other affiliation).",
           "% These are preprint drafts. None has been peer reviewed. The v1.0.0 and v1.1.0 archives carry no",
           "% author line; the author field records the repository owner who is responsible for the release.",
           ""]
    out.append("% Release manuscripts-v2.0.0: current manuscripts")
    for p in sorted((q for q in papers if q["current"]), key=portal.paper_key):
        out += [bibtex(p), ""]
    out.append("% Historical releases (kept unchanged at their tags)")
    for tag, what in (("manuscripts-v1.0.0", "First release of Papers I to V."),
                      ("manuscripts-v1.1.0", "Papers I to V, version 1.1. Superseded in part by manuscripts-v2.0.0.")):
        year = (tag_date(tag) or "2026")[:4]
        out += [release_bibtex(tag, year, what + " Preprint drafts; not peer reviewed."), ""]
    return "\n".join(out).rstrip() + "\n"


# ---------------------------------------------------------------------------
# structured data

def meta_tag(name, content) -> str:
    return f'<meta name="{esc(name)}" content="{esc(content)}">'


def highwire(p, url, date, keywords) -> list[str]:
    pdf = pdf_urls(p)[0]
    tags = [meta_tag("citation_title", p["title"])]
    if named_author(p):
        tags.append(meta_tag("citation_author", AUTHOR_BIB))
        tags.append(meta_tag("citation_author_institution", AFFILIATION))
    tags += [meta_tag("citation_publication_date", date.replace("-", "/")),
             meta_tag("citation_pdf_url", pdf),
             meta_tag("citation_abstract_html_url", url),
             meta_tag("citation_language", "en")]
    if keywords:
        tags.append(meta_tag("citation_keywords", "; ".join(keywords)))
    if (p.get("metadata") or {}).get("license") == "CC-BY-4.0":
        tags.append(meta_tag("DC.rights", "https://creativecommons.org/licenses/by/4.0/"))
    return tags


def jsonld(p, url, date, keywords, abstract) -> str:
    data = {
        "@context": "https://schema.org",
        "@type": "ScholarlyArticle",
        "@id": url,
        "url": url,
        "headline": p["title"],
        "name": p["title"],
        "abstract": abstract,
        "inLanguage": "en",
        "datePublished": date,
        "version": p["version"],
        "keywords": keywords,
        "isAccessibleForFree": True,
        "creativeWorkStatus": "Preprint draft, not peer reviewed",
        "encoding": {"@type": "MediaObject", "contentUrl": pdf_urls(p)[0], "encodingFormat": "application/pdf"},
        "isBasedOn": {"@type": "SoftwareSourceCode", "codeRepository": REPO, "name": SITE_TITLE},
    }
    if named_author(p):
        data["author"] = {"@type": "Person", "name": AUTHOR_NAME, "givenName": AUTHOR_GIVEN,
                          "familyName": AUTHOR_FAMILY,
                          "affiliation": {"@type": "Organization", "name": AFFILIATION},
                          "url": AUTHOR_PROFILE}
    return json.dumps(data, ensure_ascii=False, indent=2).replace("<", "\\u003c")


# ---------------------------------------------------------------------------
# HTML

def page(title, body, *, depth, description, head_extra=(), canonical=None) -> str:
    up = "../" * depth
    canon = f'<link rel="canonical" href="{esc(canonical)}">' if canonical else ""
    extra = "\n".join(head_extra)
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>
<meta name="description" content="{esc(description)}">
{canon}
<link rel="stylesheet" href="{up}style.css">
{extra}
</head>
<body>
<a class="skip" href="#main">Skip to main content</a>
<header class="site"><div class="wrap">
<strong><a href="{up}index.html">{esc(SITE_TITLE)}</a></strong>
<nav aria-label="Site"><ul>
<li><a href="{up}index.html#manuscripts">Manuscripts</a></li>
<li><a href="{up}index.html#classical">Classical constants</a></li>
<li><a href="{up}index.html#process">How the work was done</a></li>
<li><a href="{REPO}">Repository</a></li>
</ul></nav>
</div></header>
<main id="main" class="wrap">
{body}
</main>
<footer><div class="wrap">
<p>{esc(REVIEW_STATEMENT)}</p>
<p>Corrections, missing references and questions: <a href="{REPO}/issues">GitHub issues</a>. This page uses no scripts, fonts or trackers.</p>
</div></footer>
</body>
</html>
"""


def byline(p) -> str:
    if named_author(p):
        return (f'<p class="byline"><a href="{esc(AUTHOR_PROFILE)}">{esc(AUTHOR_NAME)}</a>'
                f' · {esc(AFFILIATION)}</p>')
    return (f'<p class="byline">{esc(AUTHOR_NAME)} · {esc(AFFILIATION)} (repository owner). '
            "The archived PDF of this version carries no author line.</p>")


def link(url, text) -> str:
    return f'<a href="{esc(url)}">{esc(text)}</a>'


def alphaxiv_record(meta):
    """The alphaXiv URL recorded for this manuscript's permanent id, if any (papers/alphaxiv-records.toml)."""
    path = ROOT / "papers" / "alphaxiv-records.toml"
    if not meta or not path.is_file():
        return None
    manuscript = str(meta.get("id", "")).strip()
    for record in tomllib.loads(path.read_text(encoding="utf-8")).get("record", []):
        url = str(record.get("alphaxiv", ""))
        if record.get("id") == manuscript and url.startswith("https://www.alphaxiv.org/"):
            return url
    return None


def manuscript_page(p, by_dir, base, strict):
    meta = p["metadata"]
    if meta is None and strict and p["layout"] == "wave2":
        raise SystemExit(f"error: {p['dir']}/metadata.toml is missing")
    if strict and not (ROOT / p["dir"] / "paper.pdf").exists():
        raise SystemExit(f"error: {p['dir']}/paper.pdf is missing")
    pending = meta is None and p["layout"] == "wave2"
    keywords, primary, secondary = p["keywords"], p["msc_primary"], p["msc_secondary"]
    date = paper_date(p)
    url = f"{base}papers/{slug(p)}/"
    abstract = p["abstract"]
    pdf, fallback = pdf_urls(p)
    d = p["dir"]
    blob = f"{REPO}/blob/{DEFAULT_BRANCH}/{d}"
    cand = p["layout"] == "wave2"
    tag = p["release"]

    parts = [f"<h1>{esc(p['title'])}</h1>", byline(p),
             f'<p><span class="pill">Version {esc(p["version"])}</span>'
             f'<span class="pill">{esc(portal.paper_label(p))}</span>'
             f'<span class="pill">{esc(tag)}{" (candidate)" if tag == portal.CANDIDATE_TAG and not tag_exists(tag) else ""}</span></p>']
    if pending:
        parts.append('<p class="notice">This manuscript’s metadata file is not yet available; the text below is a '
                     "provisional registry summary, not the manuscript’s abstract.</p>")
    record = alphaxiv_record(meta)
    if record:
        parts.append(f'<p>Published on alphaXiv: <a href="{esc(record)}">{esc(record)}</a> '
                     "(alphaXiv screens submissions; screening is not peer review).</p>")
    parts.append(f'<p class="notice">{esc(REVIEW_STATEMENT)}</p>')
    parts.append("<h2>Abstract</h2>")
    parts += [f"<p>{inline(x)}</p>" for x in paragraphs(abstract)]
    if keywords:
        parts.append("<h2>Keywords</h2>")
        parts.append("<p>" + ", ".join(esc(k) for k in keywords) + "</p>")
    if meta and meta.get("license") == "CC-BY-4.0":
        parts.append("<h2>Licence</h2>")
        parts.append('<p>&copy; 2026 Christopher Anderson. The manuscript is licensed under '
                     '<a href="https://creativecommons.org/licenses/by/4.0/">CC BY 4.0</a> '
                     f'(<a href="{REPO}/blob/{DEFAULT_BRANCH}/LICENSE-MANUSCRIPTS.md">scope</a>); code in the repository is MIT.</p>')
    if primary:
        codes = [primary] + secondary
        items = "".join(
            f'<li><a href="https://zbmath.org/classification/?q=cc%3A{esc(c)}"><code>{esc(c)}</code></a>'
            f'{" (primary)" if c == primary else ""}</li>' for c in codes)
        parts.append(f"<h2>MSC2020 classification</h2><ul class=\"plain\">{items}</ul>")
    parts.append("<h2>Download</h2>")
    parts.append(f'<ul class="plain"><li>{link(pdf, "PDF at release tag " + tag)}</li>'
                 f'<li>{link(fallback, "PDF on the main branch (fallback if the release tag is not yet published)")}</li>'
                 f'<li>{link(blob + "/paper.tex", "LaTeX source")}</li>'
                 f'<li>{link(blob + "/references.bib", "References (BibTeX)")}</li></ul>')
    parts.append("<h2>Formal verification and reproducibility</h2>")
    ver = [f'<li>{link(blob + "/VERIFICATION.md", "Verification map")}: one row per theorem with its evidence label, '
           "Lean declarations, external inputs and reproduction command.</li>"] if cand else []
    if cand:
        ver.append(f'<li>{link(blob + "/LEDGER.md", "Claim-to-source ledger")} for priority and literature '
                   "comparisons.</li>")
        if p.get("supersedes"):
            ver.append(f'<li>{link(blob + "/CHANGES.md", "What changed")} relative to version '
                       f'{esc(by_dir[p["supersedes"]]["version"])}.</li>')
    else:
        ver.append(f'<li>{link(blob + "/REVIEW.md", "Reviewer guide")} and '
                   f'{link(blob + "/CORRESPONDENCE.md", "correspondence check")} for the archived version.</li>')
    ids = p.get("results") or p["principal"]
    ver.append("<li>Registry results: " + ", ".join(
        link(f"{REPO}/blob/{DEFAULT_BRANCH}/docs/results.md#{x.lower()}", x) for x in ids) + ".</li>")
    ver.append(f'<li>Lean sources and axiom audit at the pinned commit: '
               f'{link(f"{REPO}/tree/{portal.WAVE2_LEAN_COMMIT}", portal.WAVE2_LEAN_COMMIT[:7])} · '
               f'{link(f"{REPO}/blob/{DEFAULT_BRANCH}/docs/verification.md", "how to reproduce the build")}.</li>')
    ver.append("<li>Evidence labels used in the manuscripts: Kernel-verified, Lean-supported paper proof, Paper proof, "
               "Finite certificate, Conditional, External input.</li>")
    parts.append('<ul class="plain">' + "".join(ver) + "</ul>")
    parts.append("<h2>How to cite</h2>")
    parts.append("<p>The archived record is a preprint draft. Cite the version and the release tag.</p>")
    parts.append(f"<pre><code>{esc(bibtex(p, year=date[:4], url=url))}</code></pre>")
    parts.append("<h2>Version history</h2>")
    rows = []
    for version, t, directory in history(p, by_dir):
        raw, _ = pdf_urls(p, t, directory)
        when = tag_date(t) or ("not yet tagged" if t == portal.CANDIDATE_TAG else "")
        note = "release candidate" if t == portal.CANDIDATE_TAG and not tag_exists(t) else ""
        rows.append(f"<tr><td>{esc(version)}</td><td><a href=\"{esc(REPO)}/releases/tag/{esc(t)}\">{esc(t)}</a></td>"
                    f"<td>{esc(when)}</td><td>{link(raw, 'PDF')}</td><td>{esc(note)}</td></tr>")
    parts.append('<div class="scroll"><table><caption class="byline">Earlier PDFs remain unchanged at their tags.'
                 "</caption><thead><tr><th scope=\"col\">Version</th><th scope=\"col\">Release tag</th>"
                 "<th scope=\"col\">Date</th><th scope=\"col\">File</th><th scope=\"col\">Note</th></tr></thead>"
                 "<tbody>" + "".join(rows) + "</tbody></table></div>")
    parts.append(f'<p><a href="../../index.html#manuscripts">All manuscripts</a></p>')

    head = highwire(p, url, date, keywords) + [
        f'<script type="application/ld+json">\n{jsonld(p, url, date, keywords, " ".join(abstract.split()))}\n</script>']
    short = " ".join(abstract.split())
    return page(f"{p['title']} · {SITE_TITLE}", "\n".join(parts), depth=2,
                description=short[:300], head_extra=head, canonical=url)


CLASSICAL = [
    ("ln 2", "Transcendental. Binary normality is open, and no asymptotic discrepancy bound below 1 is known.",
     "Reduced denominators of shifted prefixes grow at a proved exponential rate; rational-orbit certificates need slower growth."),
    ("π", "Transcendental. Normality is open in every base, and no discrepancy bound below 1 is known.",
     "BBP and Machin-type rational models have exponentially growing denominators; a distribution estimate for their orbits is missing."),
    ("e", "Transcendental. Normality is open in every base, and no discrepancy bound below 1 is known.",
     "Taylor-prefix denominators and continued-fraction transition counts leave only logarithmic control."),
    ("√2 and φ", "Algebraic of degree 2. Normality is open; known transition counts give density zero only.",
     "Reduces to bounding digit runs on a set of positive density."),
    ("Erdős–Borwein constant", "Irrational (Erdős, 1948). Neither normality nor non-normality is established here.",
     "Finite column, moment and Fourier tests provably cannot certify the question below stated thresholds."),
]

HEADLINES = [
    ("Polynomial images of Stoneham numbers", "Kernel-verified",
     "For coprime b ≥ 2 and c > 2, every nonconstant rational polynomial of the Stoneham number α(b, c) is normal in base b."),
    ("Localized polylogarithms", "Kernel-verified",
     "On a finite prime support, the unsigned series has discrepancy limit 0 or 1 according to whether some support prime does not divide the radix."),
    ("Synthetic expansions", "Kernel-verified switch; paper-proof rate",
     "With coefficients 1/p^(s·v) at positions growing at least quadratically, the discrepancy tends to 1 at s = 0 and to 0 at every positive integer s."),
    ("Multiplicative Lambert series", "Lean-supported paper proof",
     "Binary multiplicative Lambert series of prime-support density δ in (0, 1) are disjunctive but not normal, with 1 − D_N of order (log log N)/(log N)^(1−δ)."),
    ("Sharp translation identity", "Kernel-verified",
     "The largest change of finite discrepancy under translation by z equals one minus the discrepancy of z."),
]


def index_page(papers, base):
    current = sorted((p for p in papers if p["current"]), key=portal.paper_key)
    rows = []
    for p in current:
        rows.append(f'<tr><th scope="row">{esc(p["number"])}</th>'
                    f'<td><a href="papers/{esc(slug(p))}/index.html">{esc(p["title"])}</a></td>'
                    f'<td>{esc(p["version"])}</td><td>{esc(portal.paper_label(p))}</td></tr>')
    parts = [f"<h1>{esc(SITE_TITLE)}</h1>",
             f'<p class="byline">{esc(AUTHOR_NAME)} · {esc(AFFILIATION)}</p>',
             f"<p>{esc(DESCRIPTION)}</p>",
             "<p>The work has four standing aims: establish normality, establish nonnormality, quantify digit "
             "distribution, and establish rigorous mathematical limitations. Each result is registered with a "
             "permanent identifier and one evidence label.</p>",
             f'<p class="notice">{esc(REVIEW_STATEMENT)}</p>',
             "<h2>Headline results</h2>",
             '<ul class="plain">' + "".join(
                 f"<li><strong>{esc(t)}</strong> ({esc(label)}). {esc(s)}</li>" for t, label, s in HEADLINES) + "</ul>",
             f'<p>Exact statements, scope and proofs: <a href="{REPO}#principal-theorems">repository README</a> · '
             f'<a href="{REPO}/blob/{DEFAULT_BRANCH}/docs/results.md">result index</a>.</p>',
             '<h2 id="manuscripts">Manuscripts</h2>',
             f"<p>Release <code>{esc(portal.CANDIDATE_TAG)}</code>. Version 1.0 and 1.1 PDFs remain "
             "unchanged at their release tags.</p>",
             '<div class="scroll"><table><thead><tr><th scope="col"></th><th scope="col">Manuscript</th>'
             '<th scope="col">Version</th><th scope="col">Status</th></tr></thead><tbody>' + "".join(rows) +
             "</tbody></table></div>",
             '<h2 id="classical">Classical constants: what is and is not known</h2>',
             "<p>Nothing here proves normality, or an asymptotic discrepancy bound below 1, for any of these "
             "constants.</p>",
             '<div class="scroll"><table><thead><tr><th scope="col">Constant</th><th scope="col">Status</th>'
             '<th scope="col">Where the methods stop</th></tr></thead><tbody>' + "".join(
                 f'<tr><th scope="row">{esc(a)}</th><td>{esc(b)}</td><td>{esc(c)}</td></tr>' for a, b, c in CLASSICAL) +
             "</tbody></table></div>",
             f'<p>Details: <a href="{REPO}#classical-targets-status">classical targets status</a>.</p>',
             '<h2 id="process">How the work was done</h2>',
             f"<p>{esc(AI_STATEMENT)}</p>",
             "<p>Lean 4 checks the formal declarations; every manuscript lists which statements are kernel-verified "
             "and which rest on written arguments or published theorems. Review by models from different "
             "providers found errors that were corrected, but it is not independent human peer review. "
             "Human specialist review is outstanding.</p>",
             f'<p>Attribution and verification scope: <a href="{REPO}/blob/{DEFAULT_BRANCH}/docs/attribution.md">'
             "docs/attribution.md</a>.</p>",
             "<h2>Corrections and collaboration</h2>",
             f'<p>Corrections, prior-art references and questions about a specific result are welcome as '
             f'<a href="{REPO}/issues">GitHub issues</a>; quoting the result identifier helps. The issue tracker is '
             "the only contact route.</p>"]
    desc = DESCRIPTION
    return page(SITE_TITLE, "\n".join(parts), depth=0, description=desc, canonical=base)


NOT_FOUND = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Page not found · {SITE_TITLE}</title><link rel="stylesheet" href="style.css"></head>
<body><main class="wrap"><h1>Page not found</h1><p><a href="index.html">Back to the manuscripts</a></p></main></body></html>
"""


def build_site(papers, out: pathlib.Path, base: str = BASE_URL, strict: bool = False):
    base = base if base.endswith("/") else base + "/"
    by_dir = {p["dir"]: p for p in papers}
    out.mkdir(parents=True, exist_ok=True)
    written = []

    def write(rel, text):
        path = out / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8", newline="\n")
        written.append(rel)

    write("style.css", STYLE)
    write(".nojekyll", "")
    write("404.html", NOT_FOUND)
    write("index.html", index_page(papers, base))
    for p in (q for q in papers if q["current"]):
        write(f"papers/{slug(p)}/index.html", manuscript_page(p, by_dir, base, strict))
    return written


# ---------------------------------------------------------------------------

def cmd_build(args):
    _, papers = portal.load_registry()
    out = pathlib.Path(args.out)
    written = build_site(papers, out, args.base_url, args.strict)
    pending = [portal.dir_name(p["dir"]) for p in papers if p["current"] and p["metadata"] is None
               and p["layout"] == "wave2"]
    print(f"Wrote {len(written)} files to {out}")
    if pending:
        print(f"warning: no metadata.toml yet for: {', '.join(pending)}")
    return 0


def cmd_bib(args):
    _, papers = portal.load_registry()
    text = build_bibliography(papers)
    path = ROOT / BIB_FILE
    if args.check:
        if not path.exists() or path.read_text(encoding="utf-8") != text:
            print(f"{BIB_FILE} is stale. Run python3 scripts/site.py bib")
            return 1
        print(f"{BIB_FILE} is current")
        return 0
    path.write_text(text, encoding="utf-8", newline="\n")
    print(f"wrote {BIB_FILE}")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    b.add_argument("--out", default=str(ROOT / "site"))
    b.add_argument("--strict", action="store_true", help="fail when a manuscript has no metadata.toml or PDF")
    b.add_argument("--base-url", default=BASE_URL)
    c = sub.add_parser("bib")
    c.add_argument("--check", action="store_true")
    args = ap.parse_args(argv)
    return {"build": cmd_build, "bib": cmd_bib}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
