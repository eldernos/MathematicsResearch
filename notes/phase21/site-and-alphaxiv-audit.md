# Phase 21 Track F3: live research site and alphaXiv audit, with an exact improvement specification

Audit date: 25 November 2026 (local time, UTC−06:00; the repository and alphaXiv record the publications as 26 November in UTC). Worktree branch `research/phase-21-radix-boundaries` at Phase 20 commit `be4a160`. **Read-only audit.** The only files written are this note and [phase20-audit-and-paper-plans.md](phase20-audit-and-paper-plans.md). The implementation below was built and tested in a throw-away `git clone` of the worktree in the session scratch directory; no file of the worktree was changed, nothing was posted anywhere, no archived release or tag was touched.

Nothing here claims that any search engine or index lists the manuscripts. Nothing here claims peer review: alphaXiv screens submissions, and screening is not peer review.

This note continues [publication-audit.md](../phase20/publication-audit.md) (Phase 20, Tracks F1–F2). Its findings F-1 (links not deployed), F-2 (README table), F-3 (BibTeX note), F-5, F-6 and F-7 are now resolved in the repository (§1.4).

## 1. What is live (25 November 2026)

### 1.1 GitHub Pages

| Check | Result |
| --- | --- |
| `origin/main` | `062e66c`, "Merge pull request #3 from eldernos/release-followup", committed 2026-11-25T20:43:15-06:00 (= 2026-11-26T02:43:15Z) |
| Pages workflow | `gh run list --workflow pages.yml`: run 45744288443 for that merge, `completed success`, 30 s, 2026-11-26T02:43:18Z; the previous run (PR #2) 2026-11-26T01:08:11Z |
| `https://eldernos.github.io/MathematicsResearch/` | HTTP 200, 9,141 bytes; **no mention of alphaXiv** (0 matches) |
| Ten current manuscript pages `…/papers/<slug>/` | all HTTP 200 (01-stoneham-polynomials-v2, 02-localized-normality-v2, 03-signed-resonance-v1.2, 04-arithmetic-certificates-v2, 05-classical-denominators-v2, 06-multiplicative-lambert, 07-synthetic-expansions, 08-stoneham-product-orbits, 09-erdos-borwein-note, 10-discrepancy-arithmetic). `…/papers/01-stoneham-polynomials/` is 404, as expected for a superseded manuscript |
| **All four alphaXiv links are now live** | `06-multiplicative-lambert`, `01-stoneham-polynomials-v2`, `07-synthetic-expansions` and `10-discrepancy-arithmetic` each contain exactly one `https://www.alphaxiv.org/abs/2611.<slug>` link, with the slug recorded in `papers/alphaxiv-records.toml`. The other six pages contain none (they are in the second batch) |
| `<link rel="canonical">` | present, equal to the page URL (checked on 06) |
| `citation_pdf_url` on the live pages | `https://raw.githubusercontent.com/eldernos/MathematicsResearch/manuscripts-v2.0.0/<dir>/paper.pdf`, i.e. **not** in the abstract page's directory (finding G1) |
| `citation_publication_date` on the live pages | `2026/11/25`; alphaXiv's own tag says `2026/11/26` (finding G2) |
| Same-origin PDF `…/papers/06-multiplicative-lambert/paper.pdf` | HTTP 404 (no PDF is deployed) |
| `…/MathematicsResearch/sitemap.xml`, `…/robots.txt` | HTTP 404 both |
| `https://eldernos.github.io/robots.txt`, `…/sitemap.xml`, `https://eldernos.github.io/` | HTTP 404 all three (there is no user-site repository, so no host-root robots file) |

### 1.2 The four alphaXiv records (re-verified)

Fetched with `curl -A "Mozilla/5.0"` (a Python `urllib` request with a custom User-Agent string was refused with HTTP 403, while the plain `Mozilla/5.0` string got 200).

| Id | Page | `<title>` equals registry title | `citation_author` | `citation_publication_date` | Licence in the page payload | PDF `…<slug>.pdf` |
| --- | --- | --- | --- | --- | --- | --- |
| VI | HTTP 200 | yes | Christopher Anderson | 2026/11/26 | `http://creativecommons.org/licenses/by/4.0/` | 540,558 bytes, SHA-256 `69f91163…`; **identical** to the repository PDF and to `papers/SHA256SUMS` |
| I | HTTP 200 | yes | Christopher Anderson | 2026/11/26 | CC BY 4.0 | 509,205 bytes, `51a6769c…`; identical |
| **VII** | HTTP 200 | yes | Christopher Anderson | 2026/11/26 | **`https://www.alphaxiv.org/docs/submission-policy#license`** | 577,089 bytes, `703fb39a…`; identical |
| X | HTTP 200 | yes | Christopher Anderson | 2026/11/26 | CC BY 4.0 | 476,584 bytes, `79c045a4…`; identical |

A made-up slug returns 404, so the 200s are not a catch-all. The four PDFs served by alphaXiv are byte-identical to the repository files (same size and SHA-256), which is the evidence that what alphaXiv hosts is what `papers/SHA256SUMS` records.

**Paper VII's public licence setting is unchanged.** It still shows the default alphaXiv submission-policy licence, while the repository manuscript is CC BY 4.0 (`metadata.toml` `license = "CC-BY-4.0"`). This cannot be fixed from the repository: the licence is chosen in the alphaXiv web form and is not an API parameter (`submission/alphaxiv.toml`, `scripts/alphaxiv_publish.py`). It is an **owner action on alphaXiv** (§5, item O1).

*Not verified.* The client-rendered AI-disclosure widgets on the four pages, and how alphaXiv displays the licence to a reader, were not looked at (the check read the server-rendered payload only). The owner should confirm them by eye.

### 1.3 Sizes and limits (verified against primary pages)

| Quantity | Value |
| --- | --- |
| PDFs in `papers/*/paper.pdf` | 15 files, 335,559 to 603,645 bytes each (11 MiB for the whole `papers/` directory including sources) |
| The 10 **current** PDFs | 5,255,264 bytes (5.01 MiB). A strict site build with the PDFs copied in is **5,413,788 bytes (5.16 MiB)** in 26 files |
| GitHub Pages limits (`docs.github.com` "GitHub Pages limits", fetched today) | published site at most **1 GB**; deployment times out after **10 minutes**; soft bandwidth **100 GB per month**; the 10-builds-per-hour soft limit does not apply to a custom Actions workflow |
| Google Scholar inclusion guidelines (`scholar.google.com/intl/en/scholar/inclusion.html`, fetched today) | "The content of the tag [`citation_pdf_url`] is the absolute URL of the PDF file; for security reasons, it **must refer to a file in the same subdirectory as the HTML abstract**." At least three fields are required: the title, the full name of at least the first author, and the year of publication. "Documents larger than 5MB, such as books and long dissertations, should be uploaded to Google Book Search" (every manuscript PDF is under 0.6 MB). The abstract must be visible without sign-in or interstitials |

The artifact is about 0.5% of the Pages limit.

### 1.4 Status of the earlier audit's items

`publication-audit.md` F-2 (README Files column): done, `portal.py` now appends an alphaXiv link from the records file. F-3 (BibTeX): done, `bib_note` appends the alphaXiv record and `site.py bib --check` is current. F-5 and F-6 (stale prose in `docs/repository-metadata.md` and `docs/attribution.md`): updated. F-7 (`FIRST-BATCH.md`): no "Owner confirmed | not yet" rows remain. F-1: resolved by the merge of PR #3. Remaining from that audit: F-9 (discoverability) and the new items below.

## 2. Findings on the generator and the workflow

Files read in full: `scripts/site.py`, `scripts/test_site.py`, `.github/workflows/pages.yml`, `docs/site.md`.

| # | Finding | Evidence | Severity |
| --- | --- | --- | --- |
| **G1** | `citation_pdf_url` is an off-site URL (`raw.githubusercontent.com`) and no PDF is served beside the abstract page. Google Scholar's guideline requires the PDF in the same subdirectory as the abstract. | `site.py` `highwire()` uses `pdf_urls(p)[0]`; live page; §1.3 | **High** for discoverability (no effect on correctness) |
| **G2** | `citation_publication_date` and `datePublished` are one day early. `paper_date()` uses `git log --format=%cs`, the commit date **in the committer's own time zone**, so the release commit (2026-11-26 01:08 UTC = 2026-11-25 19:08 −06:00) reads 2026-11-25. alphaXiv and the registry say 2026-11-26. | live tags; `TZ=UTC git log --date=format-local:%Y-%m-%d --format=%cd` gives 2026-11-26 | Medium |
| **G3** | JSON-LD has one `encoding` (the raw tag URL), no `sameAs` for the alphaXiv record, no `license`. | `jsonld()` | Medium |
| **G4** | No `sitemap.xml`, no `robots.txt`. A `robots.txt` at `/MathematicsResearch/robots.txt` is not read by crawlers (they read the host root); a sitemap in a subdirectory may list URLs below that directory and must be submitted or referenced by other means. | §1.1 | Low, and a caveat for the owner |
| **G5** | The landing page does not mention the alphaXiv records. | live index, 0 matches | Low |
| **G6** | `404.html` has no `noindex`. | `NOT_FOUND` | Low |
| **G7** | `--strict` checks that `paper.pdf` exists but not that it equals the digest in `papers/SHA256SUMS`; a PDF copied into the site would not be checked. | `manuscript_page()` | Medium once PDFs are deployed |
| **G8** | `pages.yml` has no size guard and no post-deployment check; nothing detects a missing deployed PDF or a mismatched `citation_pdf_url`. | workflow | Low |
| **G9** | The tests cover none of: the PDF location, UTC dates, `sameAs`, the licence, sitemap, robots. `test_no_scripts_fonts_or_trackers` whitelists external hosts and would reject an `www.alphaxiv.org/abs/…` link on any page whose metadata has a record. | `test_site.py` | Medium (blocks the spec unless the whitelist is extended) |
| G10 | Already fine, keep: canonical links on every page; the three Google-required fields (title, `Anderson, Christopher`, year); abstract visible without scripts; `isAccessibleForFree`; `creativeWorkStatus` "Preprint draft, not peer reviewed"; the immutable release-tag PDF link; no scripts, fonts or trackers. | live pages | — |

## 3. Exact specification

Everything in §3 was applied to a clean clone of this worktree (`be4a160`) in the session scratch directory and tested there. **Results:** `python -B scripts/test_site.py` runs 20 tests, OK (the 14 existing tests unchanged apart from two whitelist/expectation lines, and 6 new); `python -B scripts/site.py bib --check` reports "papers/BIBLIOGRAPHY.bib is current"; `python -B scripts/site.py build --strict --out <dir>` writes 26 files (5.16 MiB) including the ten PDFs, `sitemap.xml` and `robots.txt`; the four sampled deployed-copy PDFs are byte-identical to the repository PDFs; the sitemap parses as XML; the built page for Paper VI has `citation_pdf_url` `https://eldernos.github.io/MathematicsResearch/papers/06-multiplicative-lambert/paper.pdf`, `citation_publication_date` `2026/11/26`, JSON-LD `sameAs` the alphaXiv URL, `license` CC BY 4.0 and two `encoding` entries; `python -B scripts/portal.py check --strict` (with `PYTHONUTF8=1`) and `scripts/check_citation.py` still pass. Apply the diffs in this order and run the commands in §3.6.

The diffs are `git diff` output relative to `be4a160`. They are independent of the Phase 21 Lean and registry edits. They touch only `scripts/site.py`, `scripts/test_site.py`, the new `scripts/check_live.py`, `.github/workflows/pages.yml` and `docs/site.md`.

### 3.1 `scripts/site.py`

Design decisions, each tied to a finding:

- **G1, G7.** `build_site` copies `<dir>/paper.pdf` to `site/papers/<slug>/paper.pdf` for every current manuscript. In `--strict` mode the build exits with an error if the SHA-256 of the PDF differs from, or is missing in, `papers/SHA256SUMS`. The page links the deployed copy, prints its SHA-256, keeps the immutable release-tag link, adds the alphaXiv-hosted PDF where a record exists, and keeps the `main`-branch fallback. `citation_pdf_url` and the first JSON-LD `encoding` use the deployed copy **only when the PDF exists**; otherwise the release-tag URL, as before.
- **G2.** `commit_date_utc()` converts the committer date (`%cI`) to UTC in Python, with no dependence on the environment's `TZ`. `tag_date` and `paper_date` use it.
- **G3.** `sameAs` (the alphaXiv URL) and `license` (CC BY 4.0, from `metadata.toml`) are added to the JSON-LD; `creativeWorkStatus` is kept.
- **G4.** `sitemap.xml` (Sitemap 0.9: the landing page, ten manuscript pages, ten PDFs; no `lastmod`, which would be invented) and `robots.txt` (`Allow: /` and a `Sitemap:` line; advisory only at a project path).
- **G5.** A "Preprint server" column on the landing page with the alphaXiv link, and a sentence that says screening is not peer review.
- **G6.** `noindex` on `404.html`.

```diff
diff --git a/scripts/site.py b/scripts/site.py
index 0d3653c..3b1a20b 100644
--- a/scripts/site.py
+++ b/scripts/site.py
@@ -11,6 +11,10 @@ carry Highwire Press ``citation_*`` meta tags and schema.org ``ScholarlyArticle`
 ``--strict`` a missing ``metadata.toml`` or ``paper.pdf`` is an error; without it the page is built from the
 registry summary and marked as pending.
 
+Each manuscript page is deployed next to a byte-identical copy of its ``paper.pdf`` (checked against
+``papers/SHA256SUMS`` in ``--strict`` mode), and ``citation_pdf_url`` points to that same-directory copy, which is
+what Google Scholar's inclusion guidelines require. ``sitemap.xml`` and ``robots.txt`` are written beside the pages.
+
 Nothing here submits anything to an index. The meta tags and structured data describe the pages; whether any
 search service lists them is outside this repository's control.
 """
@@ -19,11 +23,13 @@ from __future__ import annotations
 
 import argparse
 import datetime
+import hashlib
 import html
 import json
 import tomllib
 import pathlib
 import re
+import shutil
 import subprocess
 import sys
 
@@ -114,8 +120,17 @@ def tag_exists(tag: str) -> bool:
     return bool(git("rev-parse", "-q", "--verify", f"refs/tags/{tag}^{{commit}}"))
 
 
+def commit_date_utc(*args) -> str:
+    """UTC calendar date of the newest commit selected by ``git log -1 ARGS`` (the %cs date is in the committer's
+    local zone, which put the 2026-11-26 01:08 UTC release on 2026-11-25)."""
+    stamp = git("log", "-1", "--format=%cI", *args)
+    if not stamp:
+        return ""
+    return datetime.datetime.fromisoformat(stamp).astimezone(datetime.timezone.utc).date().isoformat()
+
+
 def tag_date(tag: str) -> str:
-    return git("log", "-1", "--format=%cs", tag) if tag_exists(tag) else ""
+    return commit_date_utc(tag) if tag_exists(tag) else ""
 
 
 def paper_date(p) -> str:
@@ -123,7 +138,7 @@ def paper_date(p) -> str:
     meta = p.get("metadata") or {}
     if meta.get("date"):
         return str(meta["date"])
-    return git("log", "-1", "--format=%cs", "--", p["dir"]) or datetime.date.today().isoformat()
+    return commit_date_utc("--", p["dir"]) or datetime.datetime.now(datetime.timezone.utc).date().isoformat()
 
 
 def slug(p) -> str:
@@ -141,6 +156,26 @@ def pdf_urls(p, tag=None, directory=None):
     return f"{RAW}/{tag}/{d}/paper.pdf", f"{REPO}/blob/{DEFAULT_BRANCH}/{d}/paper.pdf"
 
 
+def pdf_path(p) -> pathlib.Path:
+    return ROOT / p["dir"] / "paper.pdf"
+
+
+def sha256_file(path) -> str:
+    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
+
+
+def recorded_sha256() -> dict:
+    """``papers/SHA256SUMS`` as {repository-relative path: hex digest}."""
+    path = ROOT / "papers" / "SHA256SUMS"
+    out = {}
+    if path.is_file():
+        for line in path.read_text(encoding="utf-8").splitlines():
+            m = re.fullmatch(r"([0-9a-f]{64}) [ *](\S+)", line.strip())
+            if m:
+                out[m.group(2)] = m.group(1)
+    return out
+
+
 def tag_version(e, tag) -> str:
     if tag == "manuscripts-v1.0.0":
         return "1.0"
@@ -224,8 +259,9 @@ def meta_tag(name, content) -> str:
     return f'<meta name="{esc(name)}" content="{esc(content)}">'
 
 
-def highwire(p, url, date, keywords) -> list[str]:
-    pdf = pdf_urls(p)[0]
+def highwire(p, url, date, keywords, local_pdf=None) -> list[str]:
+    """``local_pdf`` is the deployed same-directory copy; without it the immutable release-tag URL is used."""
+    pdf = local_pdf or pdf_urls(p)[0]
     tags = [meta_tag("citation_title", p["title"])]
     if named_author(p):
         tags.append(meta_tag("citation_author", AUTHOR_BIB))
@@ -241,7 +277,7 @@ def highwire(p, url, date, keywords) -> list[str]:
     return tags
 
 
-def jsonld(p, url, date, keywords, abstract) -> str:
+def jsonld(p, url, date, keywords, abstract, local_pdf=None, record=None) -> str:
     data = {
         "@context": "https://schema.org",
         "@type": "ScholarlyArticle",
@@ -256,9 +292,14 @@ def jsonld(p, url, date, keywords, abstract) -> str:
         "keywords": keywords,
         "isAccessibleForFree": True,
         "creativeWorkStatus": "Preprint draft, not peer reviewed",
-        "encoding": {"@type": "MediaObject", "contentUrl": pdf_urls(p)[0], "encodingFormat": "application/pdf"},
+        "encoding": [{"@type": "MediaObject", "contentUrl": u, "encodingFormat": "application/pdf"}
+                     for u in ([local_pdf] if local_pdf else []) + [pdf_urls(p)[0]]],
         "isBasedOn": {"@type": "SoftwareSourceCode", "codeRepository": REPO, "name": SITE_TITLE},
     }
+    if record:
+        data["sameAs"] = [record]  # the alphaXiv preprint record; creativeWorkStatus keeps the review caveat
+    if (p.get("metadata") or {}).get("license") == "CC-BY-4.0":
+        data["license"] = "https://creativecommons.org/licenses/by/4.0/"
     if named_author(p):
         data["author"] = {"@type": "Person", "name": AUTHOR_NAME, "givenName": AUTHOR_GIVEN,
                           "familyName": AUTHOR_FAMILY,
@@ -378,8 +419,18 @@ def manuscript_page(p, by_dir, base, strict):
             f'<li><a href="https://zbmath.org/classification/?q=cc%3A{esc(c)}"><code>{esc(c)}</code></a>'
             f'{" (primary)" if c == primary else ""}</li>' for c in codes)
         parts.append(f"<h2>MSC2020 classification</h2><ul class=\"plain\">{items}</ul>")
+    has_pdf = pdf_path(p).is_file()
+    local_pdf = f"{url}paper.pdf" if has_pdf else None
     parts.append("<h2>Download</h2>")
-    parts.append(f'<ul class="plain"><li>{link(pdf, "PDF at release tag " + tag)}</li>'
+    dl = []
+    if has_pdf:
+        dl.append(f'<li>{link("paper.pdf", "PDF (copy served from this site)")}; SHA-256 '
+                  f'<code>{esc(sha256_file(pdf_path(p)))}</code>, the digest recorded in '
+                  f'{link(f"{REPO}/blob/{DEFAULT_BRANCH}/papers/SHA256SUMS", "papers/SHA256SUMS")}</li>')
+    dl.append(f'<li>{link(pdf, "PDF at release tag " + tag + " (immutable)")}</li>')
+    if record:
+        dl.append(f'<li>{link(record + ".pdf", "PDF on alphaXiv")} (the alphaXiv record is not peer review)</li>')
+    parts.append('<ul class="plain">' + "".join(dl) +
                  f'<li>{link(fallback, "PDF on the main branch (fallback if the release tag is not yet published)")}</li>'
                  f'<li>{link(blob + "/paper.tex", "LaTeX source")}</li>'
                  f'<li>{link(blob + "/references.bib", "References (BibTeX)")}</li></ul>')
@@ -421,8 +472,9 @@ def manuscript_page(p, by_dir, base, strict):
                  "<tbody>" + "".join(rows) + "</tbody></table></div>")
     parts.append(f'<p><a href="../../index.html#manuscripts">All manuscripts</a></p>')
 
-    head = highwire(p, url, date, keywords) + [
-        f'<script type="application/ld+json">\n{jsonld(p, url, date, keywords, " ".join(abstract.split()))}\n</script>']
+    head = highwire(p, url, date, keywords, local_pdf) + [
+        '<script type="application/ld+json">\n'
+        f'{jsonld(p, url, date, keywords, " ".join(abstract.split()), local_pdf, record)}\n</script>']
     short = " ".join(abstract.split())
     return page(f"{p['title']} · {SITE_TITLE}", "\n".join(parts), depth=2,
                 description=short[:300], head_extra=head, canonical=url)
@@ -459,9 +511,11 @@ def index_page(papers, base):
     current = sorted((p for p in papers if p["current"]), key=portal.paper_key)
     rows = []
     for p in current:
+        ax = alphaxiv_record(p.get("metadata"))
         rows.append(f'<tr><th scope="row">{esc(p["number"])}</th>'
                     f'<td><a href="papers/{esc(slug(p))}/index.html">{esc(p["title"])}</a></td>'
-                    f'<td>{esc(p["version"])}</td><td>{esc(portal.paper_label(p))}</td></tr>')
+                    f'<td>{esc(p["version"])}</td><td>{esc(portal.paper_label(p))}</td>'
+                    f'<td>{link(ax, "alphaXiv") if ax else ""}</td></tr>')
     parts = [f"<h1>{esc(SITE_TITLE)}</h1>",
              f'<p class="byline">{esc(AUTHOR_NAME)} · {esc(AFFILIATION)}</p>',
              f"<p>{esc(DESCRIPTION)}</p>",
@@ -478,8 +532,12 @@ def index_page(papers, base):
              f"<p>Release <code>{esc(portal.CANDIDATE_TAG)}</code>. Version 1.0 and 1.1 PDFs remain "
              "unchanged at their release tags.</p>",
              '<div class="scroll"><table><thead><tr><th scope="col"></th><th scope="col">Manuscript</th>'
-             '<th scope="col">Version</th><th scope="col">Status</th></tr></thead><tbody>' + "".join(rows) +
+             '<th scope="col">Version</th><th scope="col">Status</th>'
+             '<th scope="col">Preprint server</th></tr></thead><tbody>' + "".join(rows) +
              "</tbody></table></div>",
+             "<p>An alphaXiv link marks a manuscript that the owner posted there; alphaXiv screens submissions, "
+             "and screening is not peer review. Each manuscript page also serves a copy of the PDF whose SHA-256 "
+             "digest is recorded in the repository.</p>",
              '<h2 id="classical">Classical constants: what is and is not known</h2>',
              "<p>Nothing here proves normality, or an asymptotic discrepancy bound below 1, for any of these "
              "constants.</p>",
@@ -506,11 +564,28 @@ def index_page(papers, base):
 
 NOT_FOUND = f"""<!doctype html>
 <html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
-<title>Page not found · {SITE_TITLE}</title><link rel="stylesheet" href="style.css"></head>
+<title>Page not found · {SITE_TITLE}</title><meta name="robots" content="noindex"><link rel="stylesheet" href="style.css"></head>
 <body><main class="wrap"><h1>Page not found</h1><p><a href="index.html">Back to the manuscripts</a></p></main></body></html>
 """
 
 
+def sitemap_xml(papers, base) -> str:
+    """Sitemap 0.9: the landing page, each current manuscript page and each deployed PDF (no lastmod)."""
+    urls = [base]
+    for p in sorted((q for q in papers if q["current"]), key=portal.paper_key):
+        urls.append(f"{base}papers/{slug(p)}/")
+        if pdf_path(p).is_file():
+            urls.append(f"{base}papers/{slug(p)}/paper.pdf")
+    body = "".join(f"  <url><loc>{esc(u)}</loc></url>\n" for u in urls)
+    return ('<?xml version="1.0" encoding="UTF-8"?>\n'
+            '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n' + body + "</urlset>\n")
+
+
+def robots_txt(base) -> str:
+    """Only authoritative at a host root; on a project site such as this one it is advisory (see docs/site.md)."""
+    return f"User-agent: *\nAllow: /\n\nSitemap: {base}sitemap.xml\n"
+
+
 def build_site(papers, out: pathlib.Path, base: str = BASE_URL, strict: bool = False):
     base = base if base.endswith("/") else base + "/"
     by_dir = {p["dir"]: p for p in papers}
@@ -523,12 +598,26 @@ def build_site(papers, out: pathlib.Path, base: str = BASE_URL, strict: bool = F
         path.write_text(text, encoding="utf-8", newline="\n")
         written.append(rel)
 
+    def copy(rel, src):
+        path = out / rel
+        path.parent.mkdir(parents=True, exist_ok=True)
+        shutil.copyfile(src, path)
+        written.append(rel)
+
+    sums = recorded_sha256()
     write("style.css", STYLE)
     write(".nojekyll", "")
     write("404.html", NOT_FOUND)
     write("index.html", index_page(papers, base))
     for p in (q for q in papers if q["current"]):
         write(f"papers/{slug(p)}/index.html", manuscript_page(p, by_dir, base, strict))
+        if pdf_path(p).is_file():
+            key = f"{p['dir']}/paper.pdf"
+            if strict and sums.get(key) != sha256_file(pdf_path(p)):
+                raise SystemExit(f"error: {key} does not match its digest in papers/SHA256SUMS")
+            copy(f"papers/{slug(p)}/paper.pdf", pdf_path(p))
+    write("sitemap.xml", sitemap_xml(papers, base))
+    write("robots.txt", robots_txt(base))
     return written
 
 
```

### 3.2 `scripts/test_site.py`

The whitelist regex gains `www.alphaxiv.org/abs/2611.`; the file-list test expects the new outputs; `DeployTests` redirects the module-level `ROOT` to a fixture directory (and restores it) so the tests do not depend on the repository's papers.

```diff
diff --git a/scripts/test_site.py b/scripts/test_site.py
index 31427e2..379d6c5 100644
--- a/scripts/test_site.py
+++ b/scripts/test_site.py
@@ -3,10 +3,12 @@
 import importlib.util
 import json
 import pathlib
+import hashlib
 import re
 import sys
 import tempfile
 import unittest
+import xml.dom.minidom
 from html.parser import HTMLParser
 
 import portal
@@ -147,7 +149,8 @@ class PageTests(unittest.TestCase):
             for url in c.links:
                 if url.startswith("http"):
                     self.assertRegex(url, r"^https://(github\.com/eldernos|raw\.githubusercontent\.com/eldernos|"
-                                          r"zbmath\.org/classification|www\.alphaxiv\.org/@christopher-anderson|example\.org)")
+                                          r"zbmath\.org/classification|www\.alphaxiv\.org/(@christopher-anderson|abs/2611\.)|"
+                                          r"example\.org)")
             self.assertNotIn("fonts.googleapis", text)
         self.assertNotIn("@import", research_site.STYLE)
         self.assertNotIn("url(", research_site.STYLE)
@@ -203,7 +206,8 @@ class PageTests(unittest.TestCase):
     def test_build_site_writes_expected_files(self):
         out = self.root / "out"
         written = research_site.build_site(self.papers, out, BASE)
-        for name in ("index.html", "style.css", ".nojekyll", "404.html", "papers/06-x/index.html"):
+        for name in ("index.html", "style.css", ".nojekyll", "404.html", "papers/06-x/index.html",
+                     "sitemap.xml", "robots.txt"):
             self.assertIn(name, written)
         index = (out / "index.html").read_text(encoding="utf-8")
         self.assertIn("Independent Researcher", index)
@@ -211,6 +215,101 @@ class PageTests(unittest.TestCase):
         self.assertNotRegex(index, r"(?i)google scholar")
 
 
+PDF_BYTES = b"%PDF-1.7\n% fixture\n"
+RECORD = "https://www.alphaxiv.org/abs/2611.disjunctive-nonnormal"
+
+
+class DeployTests(unittest.TestCase):
+    """Same-origin PDF, UTC dates, alphaXiv sameAs, sitemap.xml and robots.txt (module ROOT redirected to a fixture)."""
+
+    def setUp(self):
+        self.tmp = tempfile.TemporaryDirectory()
+        self.root = pathlib.Path(self.tmp.name)
+        d = self.root / "papers/06-x"
+        d.mkdir(parents=True)
+        (d / "paper.pdf").write_bytes(PDF_BYTES)
+        self.digest = hashlib.sha256(PDF_BYTES).hexdigest()
+        (self.root / "papers/SHA256SUMS").write_text(f"{self.digest}  papers/06-x/paper.pdf\n", encoding="utf-8")
+        (self.root / "papers/alphaxiv-records.toml").write_text(
+            f'[[record]]\nid = "06-x"\nalphaxiv = "{RECORD}"\nversions = []\n', encoding="utf-8")
+        (d / "metadata.toml").write_text(
+            'id = "06-x"\ntitle = "Disjunctive but Nonnormal"\nauthors = ["Christopher Anderson"]\n'
+            'affiliation = "Independent Researcher"\nshort_title = "Lambert"\nversion = "1.0"\n'
+            'status = "preprint draft"\nlicense = "CC-BY-4.0"\nabstract = "We show it."\n'
+            'keywords = ["normal numbers"]\nmsc_primary = "11K16"\nmsc_secondary = []\nsupersedes = ""\n'
+            f'lean_commit = "{portal.WAVE2_LEAN_COMMIT}"\nregistry_ids = ["CC-48"]\n', encoding="utf-8")
+        self.papers = portal.enrich_papers([wave2()], root=self.root)
+        self.saved_root = research_site.ROOT
+        research_site.ROOT = self.root
+
+    def tearDown(self):
+        research_site.ROOT = self.saved_root
+        self.tmp.cleanup()
+
+    def page(self):
+        p = self.papers[0]
+        return research_site.manuscript_page(p, {p["dir"]: p}, BASE, strict=False)
+
+    def test_citation_pdf_url_is_same_directory_copy(self):
+        text = self.page()
+        meta = {a["name"]: a["content"] for t, a in parse(text).tags if t == "meta" and "name" in a}
+        self.assertEqual(meta["citation_pdf_url"], BASE + "papers/06-x/paper.pdf")
+        self.assertEqual(meta["citation_abstract_html_url"], BASE + "papers/06-x/")
+        self.assertEqual(meta["citation_pdf_url"].rsplit("/", 1)[0], meta["citation_abstract_html_url"].rstrip("/"))
+        self.assertIn(self.digest, text)
+        self.assertIn(f"{research_site.RAW}/{portal.CANDIDATE_TAG}/papers/06-x/paper.pdf", text)  # immutable link kept
+
+    def test_jsonld_same_as_licence_and_review_caveat(self):
+        raw = re.search(r'<script type="application/ld\+json">\n(.*?)\n</script>', self.page(), re.S).group(1)
+        data = json.loads(raw)
+        self.assertEqual(data["sameAs"], [RECORD])
+        self.assertEqual(data["license"], "https://creativecommons.org/licenses/by/4.0/")
+        self.assertEqual(data["creativeWorkStatus"], "Preprint draft, not peer reviewed")
+        self.assertEqual([e["contentUrl"] for e in data["encoding"]][0], BASE + "papers/06-x/paper.pdf")
+        self.assertEqual(len(data["encoding"]), 2)
+
+    def test_pdf_missing_falls_back_to_release_tag(self):
+        (self.root / "papers/06-x/paper.pdf").unlink()
+        meta = {a["name"]: a["content"] for t, a in parse(self.page()).tags if t == "meta" and "name" in a}
+        self.assertEqual(meta["citation_pdf_url"], f"{research_site.RAW}/{portal.CANDIDATE_TAG}/papers/06-x/paper.pdf")
+
+    def test_commit_dates_are_utc(self):
+        original = research_site.git
+        try:
+            research_site.git = lambda *a: "2026-11-25T19:08:04-06:00"
+            self.assertEqual(research_site.commit_date_utc("--", "x"), "2026-11-26")
+            research_site.git = lambda *a: "2026-11-26T01:08:04Z"
+            self.assertEqual(research_site.commit_date_utc("--", "x"), "2026-11-26")
+            research_site.git = lambda *a: ""
+            self.assertEqual(research_site.commit_date_utc("--", "x"), "")
+        finally:
+            research_site.git = original
+
+    def test_build_copies_pdf_and_writes_sitemap_and_robots(self):
+        out = self.root / "out"
+        written = research_site.build_site(self.papers, out, BASE, strict=True)
+        self.assertIn("papers/06-x/paper.pdf", written)
+        self.assertEqual((out / "papers/06-x/paper.pdf").read_bytes(), PDF_BYTES)
+        dom = xml.dom.minidom.parse(str(out / "sitemap.xml"))
+        locs = [n.firstChild.data for n in dom.getElementsByTagName("loc")]
+        self.assertEqual(locs, [BASE, BASE + "papers/06-x/", BASE + "papers/06-x/paper.pdf"])
+        self.assertEqual(dom.documentElement.namespaceURI, "http://www.sitemaps.org/schemas/sitemap/0.9")
+        robots = (out / "robots.txt").read_text(encoding="utf-8")
+        self.assertIn("User-agent: *", robots)
+        self.assertIn(f"Sitemap: {BASE}sitemap.xml", robots)
+        self.assertIn('name="robots" content="noindex"', (out / "404.html").read_text(encoding="utf-8"))
+        index = (out / "index.html").read_text(encoding="utf-8")
+        self.assertIn(RECORD, index)
+        self.assertNotRegex(index + self.page(), r"(?i)google scholar|\bindexed\b")
+
+    def test_strict_build_rejects_pdf_that_differs_from_sha256sums(self):
+        (self.root / "papers/06-x/paper.pdf").write_bytes(PDF_BYTES + b"x")
+        with self.assertRaises(SystemExit) as ctx:
+            research_site.build_site(self.papers, self.root / "out", BASE, strict=True)
+        self.assertIn("SHA256SUMS", str(ctx.exception))
+        research_site.build_site(self.papers, self.root / "out2", BASE, strict=False)  # non-strict still builds
+
+
 class BibliographyTests(unittest.TestCase):
     def test_bibliography_complete(self):
         _, papers = portal.load_registry()
```

### 3.3 New file `scripts/check_live.py`

A read-only network check, not run by the unit tests. It exits 1 on any error, and prints a warning (exit 0) when alphaXiv shows a licence other than CC BY 4.0. Complete source:

```python
#!/usr/bin/env python3
"""Read-only check of the public pages: GitHub Pages and the alphaXiv records.

    python3 -B scripts/check_live.py [--base-url URL] [--no-alphaxiv] [--retries N]

For every current manuscript it fetches the deployed page and its same-directory PDF and compares the PDF's SHA-256
with ``papers/SHA256SUMS``. For every record in ``papers/alphaxiv-records.toml`` it fetches the alphaXiv page and PDF,
compares the title and the PDF digest, and prints the licence setting alphaXiv shows. A differing alphaXiv licence is a
WARNING for the owner to settle on alphaXiv (nothing here can change it); every other mismatch is an error (exit 1).
Nothing is posted anywhere, and nothing here says that any search engine lists these pages.
"""
import argparse
import hashlib
import html
import re
import sys
import time
import tomllib
import urllib.error
import urllib.request

import portal

ROOT = portal.ROOT
BASE_URL = "https://eldernos.github.io/MathematicsResearch/"
CC_BY = "creativecommons.org/licenses/by/4.0"


def fetch(url, retries=0):
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.status, r.read()
        except urllib.error.HTTPError as e:
            status, body = e.code, b""
        except OSError:
            status, body = 0, b""
        if attempt < retries:
            time.sleep(5 * (attempt + 1))
    return status, body


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base-url", default=BASE_URL)
    ap.add_argument("--no-alphaxiv", action="store_true")
    ap.add_argument("--retries", type=int, default=0)
    a = ap.parse_args(argv)
    base = a.base_url if a.base_url.endswith("/") else a.base_url + "/"
    sums = {}
    for line in (ROOT / "papers" / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        m = re.fullmatch(r"([0-9a-f]{64}) [ *](\S+)", line.strip())
        if m:
            sums[m.group(2)] = m.group(1)
    _, papers = portal.load_registry()
    records = {r["id"]: r for r in tomllib.loads(
        (ROOT / "papers" / "alphaxiv-records.toml").read_text(encoding="utf-8")).get("record", [])}
    errors, warnings = [], []

    for p in sorted((q for q in papers if q["current"]), key=portal.paper_key):
        slug = portal.dir_name(p["dir"])
        page = f"{base}papers/{slug}/"
        status, body = fetch(page, a.retries)
        text = body.decode("utf-8", "replace")
        if status != 200:
            errors.append(f"{page}: HTTP {status}")
            continue
        mid = str((p.get("metadata") or {}).get("id") or "")
        rec = records.get(mid)
        if rec and rec["alphaxiv"] not in text:
            errors.append(f"{page}: no link to {rec['alphaxiv']}")
        if not rec and "alphaxiv.org/abs/" in text:
            errors.append(f"{page}: alphaXiv link without a record")
        want = sums.get(f"{p['dir']}/paper.pdf")
        status, pdf = fetch(page + "paper.pdf", a.retries)
        if status != 200 or hashlib.sha256(pdf).hexdigest() != want:
            errors.append(f"{page}paper.pdf: HTTP {status}, digest "
                          f"{'matches' if status == 200 and hashlib.sha256(pdf).hexdigest() == want else 'differs'}")
        m = re.search(r'name="citation_pdf_url" content="([^"]*)"', text)
        if not m or m.group(1) != page + "paper.pdf":
            errors.append(f"{page}: citation_pdf_url is {m.group(1) if m else None}")
        print(f"checked {slug}")

    if not a.no_alphaxiv:
        for mid, rec in records.items():
            url = rec["alphaxiv"]
            title = next(p["title"] for p in papers if (p.get("metadata") or {}).get("id") == mid and p["current"])
            status, body = fetch(url, a.retries)
            text = body.decode("utf-8", "replace")
            m = re.search(r"<title>([^<]*)</title>", text)
            if status != 200 or not m or html.unescape(m.group(1)) != f"{title} | alphaXiv":
                errors.append(f"{url}: HTTP {status}, title {m.group(1) if m else None!r}")
            lic = re.search(r'license:"([^"]*)"', text)
            if not lic or CC_BY not in lic.group(1):
                warnings.append(f"{url}: licence shown is {lic.group(1) if lic else None} (repository: CC-BY-4.0)")
            d = next(v["dir"] for v in rec["versions"])
            status, pdf = fetch(url + ".pdf", a.retries)
            if status != 200 or hashlib.sha256(pdf).hexdigest() != sums.get(f"papers/{d}/paper.pdf"):
                errors.append(f"{url}.pdf: HTTP {status}, digest differs from papers/SHA256SUMS")
            print(f"checked alphaXiv {mid}")

    for w in warnings:
        print("WARNING:", w)
    for e in errors:
        print("ERROR:", e)
    print(f"{len(errors)} error(s), {len(warnings)} warning(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
```

Run on 25 November 2026 against the **current** deployment it reports exactly what is expected before the patch is deployed: 20 errors (ten missing same-origin PDFs and ten `citation_pdf_url` values that are not the same-directory copy), no alphaXiv error, one warning for Paper VII's licence.

### 3.4 `.github/workflows/pages.yml` and `docs/site.md`

The workflow adds a size guard (100 MiB, well under the 1 GB Pages limit) and a `verify-live` job that runs after the deployment, with retries because the CDN may lag. It does not check alphaXiv (bot protection and flakiness belong outside CI). `docs/site.md` gets the new data-source rows, the `check_live.py` command, and a rewritten "Indexing" section that states the Scholar rule, the robots caveat and that nothing is claimed about indexing. `yaml.safe_load` parses the workflow (jobs `build`, `deploy`, `verify-live`).

```diff
diff --git a/.github/workflows/pages.yml b/.github/workflows/pages.yml
index c48222b..1946979 100644
--- a/.github/workflows/pages.yml
+++ b/.github/workflows/pages.yml
@@ -24,6 +24,12 @@ jobs:
         run: python3 -B scripts/site.py bib --check
       - name: Build the site
         run: python3 -B scripts/site.py build --strict --out site
+      - name: Guard the artifact size
+        # The PDFs are about 5 MiB in total; GitHub Pages allows 1 GB. Fail on an accident (a stray large file).
+        run: |
+          size_kib=$(du -sk site | cut -f1)
+          echo "site artifact: ${size_kib} KiB"
+          test "${size_kib}" -lt 102400
       - uses: actions/configure-pages@45bfe0192ca1faeb007ade9deae92b16b8254a0d # v6.0.0
       - uses: actions/upload-pages-artifact@fc324d3547104276b827a68afc52ff2a11cc49c9 # v5.0.0
         with:
@@ -37,6 +43,18 @@ jobs:
     environment:
       name: github-pages
       url: ${{ steps.deployment.outputs.page_url }}
+    outputs:
+      page_url: ${{ steps.deployment.outputs.page_url }}
     steps:
       - id: deployment
         uses: actions/deploy-pages@368f82528645a54fb793d4d04e342629a3f51346 # v5.0.1
+  verify-live:
+    # Fetches the deployed pages and PDFs and compares each PDF with papers/SHA256SUMS. Runs after the deployment, so a
+    # failure does not undo it; read the log. The alphaXiv records are checked by hand (scripts/check_live.py without
+    # --no-alphaxiv), because alphaXiv serves bots a 403 unless the request looks like a browser.
+    needs: deploy
+    runs-on: ubuntu-latest
+    steps:
+      - uses: actions/checkout@34e114876b0b11c390a56381ad16ebd13914f8d5 # v4.3.1
+      - name: Check the deployed site
+        run: python3 -B scripts/check_live.py --no-alphaxiv --retries 4 --base-url "${{ needs.deploy.outputs.page_url }}"
diff --git a/docs/site.md b/docs/site.md
index d4f8e40..82667a0 100644
--- a/docs/site.md
+++ b/docs/site.md
@@ -21,6 +21,7 @@ python3 scripts/site.py build            # writes site/ (git-ignored)
 python3 scripts/site.py build --strict   # also fails if a manuscript lacks metadata.toml or paper.pdf
 python3 scripts/site.py bib              # regenerates papers/BIBLIOGRAPHY.bib
 python3 -B scripts/test_site.py          # unit tests
+python3 -B scripts/check_live.py         # read-only check of the deployed pages, PDFs and alphaXiv records
 ```
 
 Open `site/index.html` in a browser. The pages use no JavaScript, external fonts, analytics or trackers, adapt to narrow screens and to a dark colour scheme, and have a skip link and landmark regions.
@@ -32,9 +33,10 @@ Open `site/index.html` in a browser. The pages use no JavaScript, external fonts
 | Manuscript list, versions, status, supersession | [docs/registry/papers.toml](registry/papers.toml) |
 | Title, abstract, keywords, MSC2020 codes, registry identifiers | `metadata.toml` in each manuscript directory, validated by `python3 scripts/portal.py check` |
 | Paper III (version 1.1, retained) | `papers.toml`, because its archived directory is never edited |
-| PDF links | `https://raw.githubusercontent.com/eldernos/MathematicsResearch/<tag>/<dir>/paper.pdf`, with the file on the `main` branch as a fallback until the release tag exists |
+| PDF | a byte-identical copy of `<dir>/paper.pdf` served beside each page (`papers/<slug>/paper.pdf`; in `--strict` mode its SHA-256 must equal the entry in `papers/SHA256SUMS`), the immutable file at the release tag `https://raw.githubusercontent.com/eldernos/MathematicsResearch/<tag>/<dir>/paper.pdf`, the alphaXiv-hosted PDF where a record exists, and the file on the `main` branch as a fallback |
 | Version history | the release tags `manuscripts-v1.0.0`, `manuscripts-v1.1.0` and `manuscripts-v2.0.0`; earlier PDFs stay unchanged at their tags |
-| Dates | `date` in `metadata.toml` if present, else the last commit that touched the manuscript directory |
+| Dates | `date` in `metadata.toml` if present, else the **UTC** date of the last commit that touched the manuscript directory (the release `manuscripts-v2.0.0` is 26 November 2026 in UTC and on alphaXiv) |
+| alphaXiv link, `sameAs` | `papers/alphaxiv-records.toml`, keyed by the manuscript's permanent id |
 
 ## Author information
 
@@ -42,6 +44,6 @@ The v2 manuscripts and their pages show "Christopher Anderson · Independent Res
 
 ## Indexing
 
-Each manuscript page carries Highwire Press `citation_*` meta tags (`citation_title`, `citation_author`, `citation_publication_date`, `citation_pdf_url`, `citation_keywords`) and schema.org `ScholarlyArticle` JSON-LD. These describe the page in the formats that scholarly indexers read. **Nothing here submits the site anywhere, and nothing guarantees that Google Scholar, any other index or any search engine will list it.** Services apply their own inclusion rules, and a page that is only a landing page for a PDF hosted on GitHub may not qualify. Do not describe the manuscripts as indexed unless a search service actually lists them.
+Each manuscript page carries Highwire Press `citation_*` meta tags (`citation_title`, `citation_author`, `citation_publication_date`, `citation_pdf_url`, `citation_abstract_html_url`, `citation_keywords`), a canonical link and schema.org `ScholarlyArticle` JSON-LD (with `sameAs` for the alphaXiv record and the licence where recorded, and `creativeWorkStatus` "Preprint draft, not peer reviewed"). `citation_pdf_url` points to the copy of the PDF served in the same directory as the abstract page, because Google Scholar's inclusion guidelines require that file to be "in the same subdirectory as the HTML abstract". `sitemap.xml` lists the landing page, the manuscript pages and the PDFs. `robots.txt` is written beside it but is only authoritative at a host root; on this project site (`/MathematicsResearch/`) crawlers do not read it, so the sitemap is not advertised through it to them. **Nothing here submits the site anywhere, and nothing guarantees that Google Scholar, any other index or any search engine will list it.** Services apply their own inclusion rules, and a page that is only a landing page for a PDF may not qualify. Do not describe the manuscripts as indexed unless a search service actually lists them.
 
 All pages state that the manuscripts are preprint drafts, that cross-model review is not independent human peer review, and that the Lean kernel checks only the declarations listed in each verification map.
```

### 3.5 What the spec deliberately does not do

- It does not touch `papers/`, any archived release, `papers/SHA256SUMS` or `papers/alphaxiv-records.toml`.
- It does not set `status = "published"` anywhere (`portal.PAPER_STATUS`; the label would be read as journal publication).
- It does not add `citation_doi`, `citation_arxiv_id` or any identifier the manuscripts do not have, and it does not assert that any index lists the pages.
- It does not add a `Disallow` rule, `lastmod`, or any mention of Google Scholar to a page (the test `test_build_site_writes_expected_files` and the new `DeployTests` reject "google scholar" and "indexed" on the index and manuscript pages).
- It does not try to change Paper VII's alphaXiv licence (impossible from the repository).

### 3.6 Commands to run after applying

```sh
python3 -B scripts/test_site.py                       # expect: Ran 20 tests ... OK
python3 -B scripts/site.py bib --check                # expect: papers/BIBLIOGRAPHY.bib is current
python3 -B scripts/site.py build --strict --out site  # expect: Wrote 26 files to site
PYTHONUTF8=1 python3 scripts/portal.py check --strict # expect: Portal verified
python3 scripts/check_citation.py                     # expect: structure valid
```

Spot checks of the built output: `site/papers/06-multiplicative-lambert/paper.pdf` has SHA-256 `69f911638d29c2f2ad90e74c84a603945a7ba767fe49c8a1515202d03d4ff7b5`; the page's `citation_pdf_url` ends with `/papers/06-multiplicative-lambert/paper.pdf`; `sitemap.xml` has 21 `<loc>` entries; `du -sk site` is about 5,300 KiB (the guard is 102,400).

After the merge to `main` and the Pages run, from any machine:

```sh
python3 -B scripts/check_live.py --no-alphaxiv --retries 4   # expect: 0 error(s), 0 warning(s)
curl -sI https://eldernos.github.io/MathematicsResearch/papers/06-multiplicative-lambert/paper.pdf | head -1   # HTTP/2 200
curl -s  https://eldernos.github.io/MathematicsResearch/sitemap.xml | grep -c '<loc>'                           # 21
python3 -B scripts/check_live.py                              # also the alphaXiv records; expect only the Paper VII licence warning until O1 is done
```

Wait for the workflow to finish before the first check (the `verify-live` job does exactly this on the deployment's own URL).

## 4. Risks and unknowns

1. **Scholar eligibility is not guaranteed and not claimed.** Google's page says a site that is only a landing page for a PDF may not be included, and that inclusion takes weeks if it happens at all. The patch removes one objective obstacle (G1). It does not make the claim "indexed" true.
2. **`robots.txt` and the sitemap are weak at a project path.** Crawlers read `https://eldernos.github.io/robots.txt` (404 today), not the project-level file. The sitemap can still be submitted by the owner in a search-console tool, or the owner can add a `robots.txt` with a `Sitemap:` line to a user-site repository `eldernos.github.io`. That is an owner decision outside this repository.
3. **alphaXiv.** The records endpoint refuses non-browser User-Agents (HTTP 403). `check_live.py` sends `Mozilla/5.0`; if alphaXiv tightens this the alphaXiv half of the check fails with a clear error. The `.pdf` suffix URL is the one alphaXiv itself publishes in `citation_pdf_url`; it returned byte-identical PDFs today and is a third-party behaviour that can change.
4. **Dates.** After the UTC change the manuscript pages show 2026-11-26 for the release commit. If a manuscript directory is later edited the date moves to that commit's UTC date, as before. Adding `date` to a `metadata.toml` would be more stable but changes a file under `papers/`, which for the published manuscripts must not happen.
5. **Cache.** GitHub Pages' CDN can serve the old page for some minutes; the live check retries 4 times with 5, 10, 15 and 20 seconds of waiting.

## 5. Owner-only actions

- **O1. Paper VII's alphaXiv licence.** Set or confirm CC BY 4.0 for `2611.synthetic-arithmetic-expansions-prescribed-discrepancy` on alphaXiv (the repository file is CC BY 4.0; VI, I and X already show it). Re-run `python3 -B scripts/check_live.py`; the only warning should disappear. A future VII v2.0 submission should select the licence in the web form.
- **O2.** Confirm by eye the AI-disclosure widgets and the attached PDF on the four alphaXiv pages (not checked here).
- **O3.** Decide whether to add a user-site repository for a host-root `robots.txt` and to submit the sitemap to a search console. Optional; do not describe the pages as indexed until a service lists them.
- **O4.** Optional: `CITATION.cff` `references` entries for the four alphaXiv preprints (`check_citation.py` allows `references`); this changes the "Cite this repository" metadata and is not part of this spec.
