# Publication Wave 2: working contract

This file is the shared contract for everyone working on the `publication/wave-2` branch. The branch starts at research-checkpoint-18 (`e4809cf561573aef588e6ffc491a35cdb79fd9ec`). **Update (2026-11-25): Phase 19 is complete and the owner has approved incorporating it where applicable.** It is merged into this branch (`research/phase-19-operations` at `c2c9da683666b3b9368e5d4b5cb858caccf528f5`, which descends from checkpoint 18). Its notes are in `notes/phase19/` (start with README.md, publication-handoff.md, verification.md and literature.md), its registry entries are in `docs/registry/OP.toml` and `SY.toml`, and its new Lean modules are AdditionSpectrum, DiscrepancyGeometry, SurvivingGrid and PrimePowerGrid. Pin links to Phase 19 Lean declarations at `c2c9da683666b3b9368e5d4b5cb858caccf528f5` (the preamble provides `\leanat{commit}{File}{line}{label}`). Checkpoint-18 declarations stay pinned at e4809cf. Phase 19 applies the same evidence-label discipline. In particular, the joint normality of the flagship cubic number and its square is a **paper proof** (notes/phase19/nonlinear.md, with an independent audit in notes/phase19/reviews/nonlinear.md), not a Lean theorem. The handoff also records a correction to the Phase 18 translation/summation review: the prime-5 valuation argument there is invalid, while the protected-prime-3 proof stands.

## Principles

1. Correctness and clear communication matter more than the number of claimed discoveries. If a theorem fails review, repair it, narrow the claim or withhold it.
2. Every theorem gets exactly one evidence label (see below). Never call a paper theorem "Lean-verified" or "formally verified" when Lean checks only a supporting inequality, a finite certificate or one step.
3. Priority is provisional. Use language such as "we have not located this exact statement in the sources examined." A failed search does not prove novelty. Credit antecedents and overlapping public work precisely, including Mira Cult's gists and Captain Sude's repositories where they are relevant.
4. Historical artifacts are immutable. Never edit, move or delete anything under `papers/0[1-5]-*/`, `papers/reviews/0[1-5]-*/`, `papers/SHA256SUMS` entries for those five PDFs, or any existing tag. Revisions go in new directories with new version identifiers.
5. **Authorship (owner decision, 2026-11-25):** the named author is **Christopher Anderson**, designated **Independent Researcher**. Use exactly this in title pages (through `\makebyline`, which also sets the PDF author metadata), `metadata.toml` (`authors = ["Christopher Anderson"]`, `affiliation = "Independent Researcher"`) and submission packages. The research is not anonymous. Do not invent an academic affiliation, ORCID, email or other contact details. The only public contact route is the repository issue tracker. Keep the full AI-use disclosure. Do not edit `papers/common/`; report any needed change instead.
6. Human specialist review is outstanding. Cross-model review is not independent human peer review. Say so wherever review is mentioned.

## Evidence labels

Use these exact labels in manuscripts (theorem notes or a verification table), ledgers and the portal:

| Label | Meaning |
| --- | --- |
| **Kernel-verified** | The complete stated theorem, under the stated definitions, is a Lean declaration that has passed the kernel replay and axiom audit. Give the declaration name and a pinned link. |
| **Lean-supported paper proof** | A written proof in which named steps are Lean declarations. Say which steps. |
| **Paper proof** | A written argument only, possibly citing published theorems. List the external inputs. |
| **Finite certificate** | An exact computation proving a finite statement. Give the script, its parameters and its output. |
| **Conditional** | Depends on an unproved hypothesis. State it. |
| **External input** | A published theorem used as a black box. Give the citation with theorem number and page. |

## Directory layout for new and revised manuscripts

| ID | Directory | Version | Source paper |
| --- | --- | --- | --- |
| A | `papers/06-multiplicative-lambert/` | 1.0 | new |
| B | `papers/01-stoneham-polynomials-v2/` | 2.0 (revises Paper I v1.1) | `papers/01-stoneham-polynomials/` |
| C | `papers/07-synthetic-expansions/` | 1.0 | new |
| H | `papers/10-discrepancy-arithmetic/` | 1.0 | new (split from C on 2026-11-25; first batch, since A and C cite it) |
| D | `papers/08-stoneham-product-orbits/` | 1.0 | new |
| E | `papers/02-localized-normality-v2/` | 2.0 (revises Paper II v1.1) | `papers/02-localized-normality/` |
| F | `papers/05-classical-denominators-v2/` | 2.0 (revises Paper V v1.1) | `papers/05-classical-denominators/` |
| G | `papers/04-arithmetic-certificates-v2/` | 2.0 (revises Paper IV v1.1) | `papers/04-arithmetic-certificates/` |
| EB | `papers/09-erdos-borwein-note/` | 1.0 (research note) | new |

Each directory must contain:

- `paper.tex`. Start with `\documentclass[11pt]{article}`, matching the released papers, followed by `\input{../common/preamble.tex}` and `\input{../common/byline.tex}`. Do not redefine the shared theorem environments. Under the title, put `\makebyline{<version>}{<date>}`. Link Lean with `\lean{File}{line}{label}`, which pins to e4809cf. Mark evidence with `\evidence{Kernel-verified}` and the other labels. End the paper with the sections "Formal verification and data availability" and "Use of AI tools", the latter containing the disclosure below.
- `references.bib`. Every entry must be checked against the primary source. Include the DOI, or the arXiv identifier or stable URL. Book entries need publisher and year. Do not include entries you could not verify. If an entry cannot be checked, mark it with `note = {unverified}` and list it in the ledger.
- `paper.pdf`. Build it with the toolchain below and confirm that it compiles without undefined references or citations.
- `metadata.toml`. Required keys: `id`, `title`, `authors`, `affiliation`, `short_title`, `version`, `status = "preprint draft"`, `abstract`, `keywords` (list), `msc_primary`, `msc_secondary` (list, MSC2020), `supersedes` (a directory or ""), `lean_commit = "e4809cf561573aef588e6ffc491a35cdb79fd9ec"`, `registry_ids` (list).
- `VERIFICATION.md`. A theorem verification map: one table row per numbered theorem, proposition and corollary in the paper. Columns: statement (short), evidence label, Lean declarations (pinned links), external inputs (with theorem and page), reproduction command. Follow it with sections "What is completely kernel-verified", "External analytic dependencies" and "Reproduce".
- `LEDGER.md`. The claim-to-source novelty ledger (format below).
- `CHANGES.md` (revisions only). What changed relative to v1.1, with section mapping, and what moved to another manuscript.
- `submission/`. Contents:
  - `abstract.txt` (plain text, at most 250 words, no TeX macros apart from simple `$...$`).
  - `alphaxiv.md`: title, abstract, authors placeholder, categories, keywords, MSC codes, AI-use disclosure (exact wording below), source and verification links pinned to the commit, verification scope paragraph.
  - `announcement.md`: one short nonpromotional post of at most 280 characters for X, plus one paragraph for a mathematics forum.
  - `summary.md`: a one-paragraph mathematical summary.
  - `reviewer-inquiry.md`: one or two short individualized inquiry templates. Each names one concrete theorem and the closest prior work, explains why that researcher's published work is directly relevant (cite their paper), and asks one specific question. Use `[Name]` placeholders, never real email addresses. These are drafts for the owner, not to be sent.
  - `reviewer-packet.md`: exact statement, shortest complete proof or proof sketch with every external input cited, evidence label, reproduction link, and the specific steps on which review is wanted.

Pin Lean links as `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/<path>#L<n>` and check the line numbers against that commit (`git show e4809cf:<path>`). `papers/check_release.py --verify-pins` validates them.

## Ledger format (`LEDGER.md`)

For each headline theorem:

```
### <Theorem number>: <short name>
- **Statement and hypotheses:** exact statement.
- **Evidence:** label, plus declarations or proof location.
- **Earliest relevant literature:** author, year, title, venue, DOI/arXiv/URL, page or theorem number.
- **Closest published results:** what they actually state, quoted or closely paraphrased with theorem numbers.
- **Closest unpublished or public-repository results:** including Mira Cult and Captain Sude where relevant, with pinned URLs.
- **Relation:** inherited / specializes / strengthens / different method / apparently new in the sources examined, with one sentence on why.
- **Search record:** formulations searched (several equivalent mathematical phrasings), databases (arXiv, zbMATH Open, MathSciNet if accessible, Google Scholar, journal archives) and reference trails followed.
- **Dependencies and outstanding review:** what a specialist must check.
```

## AI-use disclosure (standard wording; adapt only the specifics)

> This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.

## Toolchain

- **LaTeX:** TinyTeX (TeX Live 2026) is installed in WSL Ubuntu with the latexrecommended, latexextra, fontsrecommended, pictures and mathscience collections. From the worktree root, in any Windows shell, run `wsl -d Ubuntu -- bash papers/wsl-build.sh <dir>`. This runs `papers/build.sh`, which fails on undefined references or citations and copies `paper.pdf` into the directory. Install a missing package with `wsl -d Ubuntu -- bash -lc 'export PATH=$HOME/bin:$PATH; tlmgr install <pkg>'`.
- **Lean:** `lake` lives in WSL at `~/.elan/bin`. Building the full library takes a long time, so do not run a full `lake build` in a manuscript worktree. The checkpoint's verified build record is `notes/phase18/verification.md`. To check a single declaration statement, use `git show e4809cf:<file>`.
- **Python:** `python` on Windows (miniconda) or `python3` in WSL. Write exact-arithmetic checks with `fractions`/`int`.

## Sources of truth

- Released manuscripts: `papers/0[1-5]-*/paper.tex`, reviewer guides, `papers/reviews/`.
- Research notes: `notes/phase13` through `notes/phase18`, plus the top-level notes in `notes/`.
- Registry: `docs/registry/*.toml`, `docs/results.md`; Lean: `NormalityChecker/`.
- Earlier reviews: `notes/phase1*/review*`, `notes/phase18/reviews/`, `notes/phase18/sources.md`.
- Roadmaps: `docs/publication-roadmap.md`, `notes/phase18/publication.md`.

## Writing standard

Write in a professional mathematical style: open with the main theorem in short, readable form, define all notation, then give complete proofs. Avoid conversational transitions, hype, redundant summaries, repository-internal jargon ("Phase 17", "Track B") and project-coined terminology without definition. Mention phase notes only in VERIFICATION.md and LEDGER.md, not in the paper body (except a short "Formal verification and data availability" section linking the repository at the pinned commit).
