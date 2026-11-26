# Phase 20 Tracks F1–F2: audit of the alphaXiv publication records and public discoverability

Audit date: 25 November 2026 (local clock; the repository and alphaXiv record the publications as 26 November 2026, presumably UTC). Branch `research/phase-20-generating-functions`, which starts from `22e40fe` (PR #3, "Record the four alphaXiv publications"). **Read-only audit:** no file other than this note and `notes/phase20/literature.md` was changed, no archived release or tag was touched, and nothing was posted anywhere. Where a change to a shared file is wanted, the exact diff is given in §5 for the coordinator to apply.

Nothing here claims peer review. alphaXiv screens submissions; screening is not peer review, and every manuscript remains an AI-assisted preprint draft.

## 1. Baseline checks (exact status)

All run from the worktree root with `python -B`; all read-only except that the site build wrote to a scratchpad directory outside the repository.

| Command | Result |
| --- | --- |
| `python -B scripts/portal.py check --strict` | exit 0: "Portal verified: 180 registered results, 244 Markdown files, links, anchors, identifiers, topics and figures." (`portal.py check` accepts `--strict`; it is the form the archiving guide lists.) |
| `python -B scripts/check_citation.py` | exit 0: "CITATION.cff: structure valid (CFF 1.2.0)" |
| `python -B scripts/site.py bib --check` | exit 0: "papers/BIBLIOGRAPHY.bib is current" |
| `python -B papers/check_release.py --require-all --verify-history` | exit 0: "Verified source companions and SHA-256 for 15 manuscripts." |
| `python -B scripts/site.py build --strict --out <scratch>` | exit 0: "Wrote 14 files" (the strict flag is what `.github/workflows/pages.yml` runs) |
| `python -B scripts/test_alphaxiv_publish.py` | 24 tests OK |
| `python -B scripts/test_site.py` | 14 tests OK |

Baseline is green. The two stale-text findings below (F-5, F-6) pass every check, which means no existing check protects against them.

## 2. The four alphaXiv records: verified facts

`papers/alphaxiv-records.toml` records four entries, all `route = "web form"`, `published = "2026-11-26"`, release `manuscripts-v2.0.0`:

| Id | Version | Directory | alphaXiv URL (slug after `2611.`) |
| --- | --- | --- | --- |
| VI | 1.0 | `06-multiplicative-lambert` | `disjunctive-nonnormal-multiplicative-lambert-series` |
| I | 2.0 | `01-stoneham-polynomials-v2` | `polynomial-images-of-stoneham-numbers` |
| VII | 1.0 | `07-synthetic-expansions` | `synthetic-arithmetic-expansions-prescribed-discrepancy` |
| X | 1.0 | `10-discrepancy-arithmetic` | `arithmetic-of-extreme-discrepancy` |

Each slug equals the `url_slug` in that manuscript's `submission/alphaxiv.toml`, and each id equals the `id` in the manuscript's `metadata.toml`, so `scripts/site.py` (`alphaxiv_record`) and `scripts/alphaxiv_publish.py` (`find_record`) resolve them correctly.

**Network access was available**, via `curl` and web search. Live fetches, 25 November 2026:

| URL | Result |
| --- | --- |
| the four `https://www.alphaxiv.org/abs/2611.…` URLs above | HTTP 200 each. The HTML `<title>` of each is exactly the manuscript title followed by "\| alphaXiv" (VI, I, VII, X all match `metadata.toml`). A deliberately invalid slug returns HTTP 404, so the 200s are not a catch-all. |
| the owner's profile `https://www.alphaxiv.org/@christopher-anderson` | HTTP 200 |
| `https://eldernos.github.io/MathematicsResearch/` and the ten manuscript pages under `papers/…/` | HTTP 200 |
| `https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v2.0.0` | HTTP 200; `gh release view`: published 2026-11-26T01:41:31Z, not a draft, not a prerelease; the release body mentions alphaXiv |
| `https://eldernos.github.io/MathematicsResearch/sitemap.xml` and `/robots.txt` | HTTP 404 (see F-9) |

**SSR payload verification and remaining live checks:** Direct HTML inspection of the four alphaXiv pages (25 November 2026) confirms for all four manuscripts:
- `citation_title` matches `metadata.toml` verbatim;
- `citation_author` = `Christopher Anderson`, `article:author` = `https://www.alphaxiv.org/@christopher-anderson`;
- `citation_publication_date` = `2026/11/26`;
- `citation_pdf_url` = `https://www.alphaxiv.org/abs/2611.<slug>.pdf`;
- `AI Track` and `math.NT` appear in all four payloads.
- **License discrepancy flagged for the owner:** the embedded payload of VI, I and X records `license:"http://creativecommons.org/licenses/by/4.0/"` (`CC BY 4.0`), whereas Paper VII (`2611.synthetic-arithmetic-expansions-prescribed-discrepancy`) records `license:"https://www.alphaxiv.org/docs/submission-policy#license"` (the default alphaXiv submission-policy licence rather than CC BY 4.0). The owner should inspect Paper VII's licence setting on alphaXiv and also confirm by eye the displayed AI disclosure and attached PDF checksums on all four pages (since client-rendered disclosure widgets and binary PDF contents were not checked).

## 3. Where the four links appear (and where they do not)

| Location | Carries alphaXiv links? | Note |
| --- | --- | --- |
| `papers/alphaxiv-records.toml` | yes (source of truth) | |
| `README.md` line 17 ("New in manuscripts-v2.0.0") | yes, four links plus the author profile | only place in `README.md` |
| `README.md` lines 133–156 (`<!-- BEGIN PAPERS -->` table) | **no** | Files column lists PDF, LaTeX, Verification map and Ledger only |
| `papers/README.md` table | yes ("published" links in the alphaXiv column), others "second batch" | |
| `papers/submission/FIRST-BATCH.md` line 3 | yes | per-manuscript sheets do not repeat the URL |
| research site, local strict build | the four manuscript pages show "Published on alphaXiv: URL (… screening is not peer review)"; the six other manuscript pages and the landing page do not | verified by building and grepping |
| research site, **deployed** | **no** (see F-1) | |
| `papers/BIBLIOGRAPHY.bib` / `scripts/site.py bib` | no | generated file |
| BibTeX on each site manuscript page | no | same `bib_note` function |
| `CITATION.cff` | profile `website` only; no manuscript links | |
| `docs/registry/papers.toml` | no | |
| `scripts/portal.py` | no reference to alphaXiv at all | |

## 4. Findings

**F-1 (functional, must fix): the deployed research site does not yet show the alphaXiv links.** `origin/main` is `83b1974` (merge of PR #2). Commit `22e40fe` is only on `origin/release-followup` (PR #3), and `.github/workflows/pages.yml` deploys on push to `main`. The live manuscript pages (fetched today) contain only the author-profile link and no `alphaxiv.org/abs/…` link, whereas a build of this branch contains four. The last Pages run on `main` was 2026-11-26T01:08:11Z. Merging PR #3 (or this branch) triggers the deployment. After the deployment, re-run: `curl -s https://eldernos.github.io/MathematicsResearch/papers/06-multiplicative-lambert/ | grep -c 'alphaxiv.org/abs/2611'` (expect 1 or more; likewise `01-stoneham-polynomials-v2`, `07-synthetic-expansions`, `10-discrepancy-arithmetic`).

**F-2 (consistency, optional): `README.md` front-page table has no alphaXiv links.** The table is generated from `scripts/portal.py` (lines 508–509 build the Files column) between `<!-- BEGIN PAPERS -->` and `<!-- END PAPERS -->`, so a hand edit would be overwritten and `portal.py check` would fail. Links appear only in the prose on line 17. A reader who goes straight to the table does not see them. Adding them requires a small `portal.py` change (diff in §5).

**F-3 (metadata): BibTeX entries for I, VI, VII and X carry no alphaXiv pointer.** `build_bibliography` and `bib_note` in `scripts/site.py` produce the same `note` for every current manuscript. A reader who cites from `BIBLIOGRAPHY.bib` is never told that a public alphaXiv record exists. The canonical `url` should stay the GitHub source directory (it is the immutable evidence); the alphaXiv record belongs in `note` with the screening caveat. `site.py bib --check` regenerates the file, so the change must be made in `site.py` (diff in §5), and `scripts/test_site.py` may need a new test.

**F-4 (registry): do not change `status` in `docs/registry/papers.toml`.** Allowed values are `planned, draft, internally reviewed, external review, published` (`portal.PAPER_STATUS`), and `portal.PAPER_LABEL` renders `published` as "Published" in the README table, `docs/results.md` and the research site. For a non-peer-reviewed preprint that label would be read as journal publication and contradicts the file's own header ("None of these manuscripts has been peer reviewed or accepted"). Keep `status = "draft"` for I (v2.0), VI, VII and X. The registry has no field for preprint links; the single source of truth stays `papers/alphaxiv-records.toml`, which `portal.py` does not read. Neither `portal.py check --strict` nor `site.py build --strict` requires any alphaXiv-related field, so the checks are indifferent to this decision.

**F-5 (stale prose): `docs/repository-metadata.md` says the metadata commands "have not been run".** It reads "Status: proposal for owner approval. The commands below have not been run." and "No homepage and no topics are set." The live repository now has `homepageUrl = https://eldernos.github.io/MathematicsResearch/` and exactly the 17 proposed topics (I compared the sets; they are equal), GitHub Pages is enabled with `build_type = workflow`, and the release is published. The "Related owner actions" list (enable Pages; publish the release) is also done. Fix with a status line (diff in §5). Neither check detects this.

**F-6 (stale prose): `docs/attribution.md` line 26 calls the release "a **candidate** until the owner publishes the tag".** The release was published on 2026-11-26. The same line says "Paper III is retained at version 1.1 in this release", while `docs/registry/papers.toml` and the README table list the named-author edition III 1.2 as the release entry (README line 131 also says "Paper III unchanged (version 1.1)" beside a table row of version 1.2). The statement "no DOI has been issued" cannot be checked from here (see F-8). `docs/licensing-proposal.md` ("release candidate"), `docs/survey.md` line 3 and `docs/registry/SCHEMA.md` line 16 ("candidate") are historical or schema wording and can stay; `papers/RELEASES.md` is an archival record and must not be edited.

**F-7 (FIRST-BATCH, clarify only): "Owner confirmed | **not yet**" at lines 29, 53, 77 and 101 is accurate for the API pipeline and misleading as a status.** I verified that `owner_confirmed = false` in all four `submission/alphaxiv.toml` files, and `alphaxiv_publish.py` would still refuse an API submission. The header (line 3) says all four were published through the web form, so the rows read as a contradiction. The papers were not submitted through the pipeline, so leaving the flag `false` is correct and also prevents an accidental API double submission (the script refuses to resubmit a recorded version in any case). Recommended change: relabel the row to "Pipeline flag `owner_confirmed` | false (published through the web form; the pipeline was not used)" in all four sheets. Line 3's present-tense "Each submission needs three things from the owner" and the five "Common steps" are historical; line 3 already says the sheets "are kept as the submission record". The submission order in the sheets (VI, X, VII, I) differs from the recorded order (VI, I, VII, X); `published` is the same date, so nothing breaks.

**F-8 (cannot be verified here): DOIs, Google Scholar and search-engine indexing.** `docs/site.md` rightly says nothing guarantees indexing and that the manuscripts must not be described as indexed unless a service lists them. I did not search any index. `CITATION.cff` and `BIBLIOGRAPHY.bib` correctly record no DOI.

**F-9 (discoverability gaps in the static site, optional):**
1. No `sitemap.xml` or `robots.txt` (both 404). `site.py` writes 14 files and neither is among them.
2. The landing page (`index.html`) and its manuscript table do not mention alphaXiv; only the four manuscript pages do.
3. The schema.org JSON-LD and Highwire tags on the four pages do not point to the alphaXiv record (`sameAs` is the schema.org property for an equivalent page). Adding it needs care: the review statement ("Preprint draft, not peer reviewed") must stay.
4. `CITATION.cff` allows `references` and `identifiers` (they are in `ALLOWED_KEYS` of `scripts/check_citation.py`), so four `references` entries with `status: preprint` and the alphaXiv URL are possible; `check_citation.py` should be re-run after any such edit. This changes the "Cite this repository" metadata, so it is an owner decision.

**F-10 (no action): the date.** The records say 2026-11-26 while this audit's local date is 25 November. Git timestamps for the merge and the release are 2026-11-26T01:08Z and 01:41Z, so the records are in UTC and consistent with each other. The `2611.` prefix of the alphaXiv ids is consistent with November 2026.

## 5. Checklist and exact diffs for the coordinator

Priority 1 (stale or broken):

1. **Merge PR #3 / this branch to `main`** (F-1), then verify the four deployed pages as described above.
2. **`docs/repository-metadata.md`** (F-5). Replace line 3 with:

   ```diff
   -**Status: proposal for owner approval. The commands below have not been run.** They change the public GitHub repository settings (description, homepage, topics), which are outward-facing, so the owner runs them after approval.
   +**Status (25 November 2026): applied.** The live repository settings already match the proposal: the homepage is `https://eldernos.github.io/MathematicsResearch/`, the 17 topics below are set, and GitHub Pages is enabled with the Actions source. The commands are kept as the record of what was proposed.
   ```

   Also replace "No homepage and no topics are set." (line 21) with "At the time of that query no homepage and no topics were set; they have since been set as proposed.", and either delete the three "Related owner actions" bullets or mark them done (Pages: done; licence: decided, CC BY 4.0 for manuscripts; release: published 26 November 2026).
3. **`docs/attribution.md` line 26.** Replace "The release is a **candidate** until the owner publishes the tag, and no DOI has been issued." with "The release `manuscripts-v2.0.0` was published on 26 November 2026, and no DOI has been issued." (Keep the DOI clause only if the owner confirms it.) Correct the Paper III sentence to name the 1.2 named-author edition.

Priority 2 (clarity):

4. **`papers/submission/FIRST-BATCH.md` lines 29, 53, 77, 101** (F-7): replace each `| Owner confirmed | **not yet** |` with `| Pipeline flag `owner_confirmed` | false (published through the web form; the pipeline was not used) |`.
5. **`scripts/portal.py` lines 508–509** (F-2), sketch: after building `parts`, append `("alphaXiv", url)` for a manuscript whose `id` has an entry in `papers/alphaxiv-records.toml`, with an absolute URL rather than a relative file path. The Files column builder currently joins relative links, so the implementer must emit the absolute link explicitly. Then run `python3 scripts/portal.py build` and `check --strict`. Label the link "alphaXiv preprint (not peer reviewed)" or keep it "alphaXiv" because the column already says "Preprint draft".
6. **`scripts/site.py` `bib_note`** (F-3), sketch: when the manuscript has a record, append " Also posted on alphaXiv's AI Track (screening is not peer review): URL." to the `note`. Regenerate with `python3 scripts/site.py bib`, extend `scripts/test_site.py`, run `site.py bib --check`. The `url` field stays the GitHub directory.

Priority 3 (optional discoverability, owner decision): `sitemap.xml` and `robots.txt` in `site.py`, a one-line alphaXiv mention on the landing page, `sameAs` in the JSON-LD, `references` in `CITATION.cff` (F-9).

**Do not:** change any `status` to `published` (F-4); edit `papers/RELEASES.md`, any file under a released tag, the four PDFs, or `papers/SHA256SUMS`; flip `owner_confirmed` to `true` (that would re-enable an API resubmission path for papers already published); or describe the manuscripts as indexed, accepted or peer reviewed.
