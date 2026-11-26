# Archive and cite this release

The manuscript release groups all five PDFs with their LaTeX sources, bibliographies, figures, research notes and Lean proofs. For this published GitHub release, the manual deposit below lets the project owner confirm author credits and metadata before issuing the DOI. The release tag is **manuscripts-v1.1.0**. Checkpoint 11, the mathematical baseline, is a separate tag. [Manuscripts](README.md) · [GitHub manuscript release](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v1.1.0) · [Checkpoint 11](https://github.com/eldernos/MathematicsResearch/commit/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035)

## Release manuscripts-v2.0.0

The tag **manuscripts-v2.0.0** was published on 26 November 2026 ([release](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v2.0.0)). No DOI has been issued. It is intended to carry eight manuscripts: revised Papers I, II, IV and V (version 2.0 in `papers/01-stoneham-polynomials-v2`, `papers/02-localized-normality-v2`, `papers/04-arithmetic-certificates-v2` and `papers/05-classical-denominators-v2`), the new papers in `papers/06-multiplicative-lambert`, `papers/07-synthetic-expansions` and `papers/08-stoneham-product-orbits`, and the research note `papers/09-erdos-borwein-note`. Paper III is retained unchanged at version 1.1. The superseded v1.1 directories and the tags `manuscripts-v1.0.0` and `manuscripts-v1.1.0` stay as they are, so the sections below remain valid for those releases. [Manuscript table](../README.md#research-papers) · [Research site](../docs/site.md)

**Creator.** The v2 manuscripts name **Christopher Anderson, Independent Researcher** as author. For a Zenodo record or any other deposit, enter exactly this name and affiliation. Do not add an ORCID, email address or institutional affiliation unless the owner supplies and approves it. The issue tracker is the only contact route. The v1.0.0 and v1.1.0 archives carry no author line; a named-author edition of those papers would need a new version identifier such as v1.2.

**Citation files.** [CITATION.cff](../CITATION.cff) describes the repository, with `version: "manuscripts-v2.0.0"` and its release date. [BIBLIOGRAPHY.bib](BIBLIOGRAPHY.bib) has one entry for each current manuscript and one for each historical release. Both name the same author. Regenerate and check them with `python3 scripts/site.py bib` and `python3 scripts/check_citation.py`. When both CITATION.cff and a `.zenodo.json` exist, Zenodo uses `.zenodo.json`.

**Before tagging**, the owner or the release assistant should confirm each of the following.

1. Every manuscript directory has `paper.tex`, `references.bib`, `paper.pdf`, `metadata.toml`, `VERIFICATION.md`, `LEDGER.md` and `submission/`, and each PDF compiles with no undefined references or citations (`papers/build.sh`).
2. `python3 scripts/portal.py build`, then `python3 scripts/portal.py check --strict`, `python3 scripts/site.py bib --check`, `python3 scripts/check_citation.py` and `python3 scripts/site.py build --strict` all pass.
3. The Lean workflow succeeds on the commit that will be tagged. The manuscripts pin their Lean links to research-checkpoint-18 (`e4809cf561573aef588e6ffc491a35cdb79fd9ec`).
4. The digests of the new PDFs are appended to `SHA256SUMS`. The existing entries for the five v1.1 PDFs are never edited.
5. The owner has approved the licence of the manuscripts ([licensing proposal](../docs/licensing-proposal.md)) and the author line.
6. The tag, release notes and any Zenodo record state that the manuscripts are preprint drafts, that cross-model review is not independent human peer review, and that the Lean kernel checks only the declarations listed in each verification map.

**Archiving.** Use one route per release, as described below. Choose a software record for the repository snapshot and, if wanted, separate preprint records for individual manuscripts, each with its own licence. Verify the archive with the same checksum procedure as for v1.1, replacing the tag name, and record the issued DOI in `CITATION.cff` and `BIBLIOGRAPHY.bib` in the next revision. Never move a published tag.

## 1. Verify the files you are about to archive

The simplest route is to download the eight named assets from the GitHub release into one folder. Keep the five PDFs, the named ZIP archive, `release-manifest.json` and `SHA256SUMS.txt` together. In that folder run:

```sh
sha256sum -c SHA256SUMS.txt
```

All seven listed files should report `OK`. The manifest gives the full Git commit, the URLs of its two verification runs and the digest of each paper. The named ZIP contains the LaTeX, figures, review reports, PDFs and Lean sources in one file. This is the ZIP to upload for a collection DOI.

To verify the source independently from a clone of the repository, use a fresh checkout of the release tag. Record the full SHA printed by the second command. Compare it with the release manifest and the successful Lean workflow for that commit.

```sh
git fetch origin tag manuscripts-v1.1.0
git rev-parse 'manuscripts-v1.1.0^{commit}'
git worktree add --detach ../normality-manuscript-archive manuscripts-v1.1.0
cd ../normality-manuscript-archive
sha256sum -c papers/SHA256SUMS
```

The checksum file is relative to the repository root. It compares each PDF byte for byte with the recorded digest for this tag. The tag identifies the full source tree, including the paper-specific correspondence checks. The release archive can be created directly from Git, even if your working directory contains local changes.

```sh
git archive --format=zip --prefix=MathematicsResearch-manuscripts-v1.1.0/ \
  -o ../MathematicsResearch-manuscripts-v1.1.0.zip manuscripts-v1.1.0
sha256sum ../MathematicsResearch-manuscripts-v1.1.0.zip
```

## 2. Choose what the DOI will identify

For **one DOI covering the complete research release**, deposit the source archive above and identify the five papers in the description. For **an individually citable manuscript**, create a separate Zenodo preprint record for that paper. Upload its final PDF, and link the version DOI of the proof archive under related identifiers. A paper DOI and a software release DOI identify distinct scholarly objects. Decide the creator names and ordering, ORCIDs, licenses and manuscript status before publishing either record. The repository license and the upstream Weyl source notice travel with the proof archive. [Repository license](../LICENSE) · [Weyl source license](../NormalityChecker/Analysis/LICENSE-Weyl)

## 3. Deposit the existing release manually

1. Sign in to **zenodo.org** and create a new upload. Use a software record for the complete repository snapshot or a publication/preprint record for an individual paper. Use a production account for a citable DOI.
2. Upload the verified archive or the paper PDF. Enter the title, owner-approved creators, version and description. For the archive, include the GitHub tag URL, full commit SHA, successful verification URL and the coverage of the five manuscripts. For a paper, include the statement identifiers and a related link to the archived proof source. Review the uploaded files and the access and licensing selections.
3. Use the DOI field to have Zenodo assign a DOI. Reserving one in the draft is useful if a DOI must appear in a title page before publication. If you change a PDF to insert a reserved DOI, produce a new tagged release with matching checksums and use its files and SHA in the deposit.
4. Use **Preview** to inspect the record, then **Publish** when the credits, files and status are correct. Open the DOI landing page, check its version and files, and compare a downloaded PDF or archive with the release checksums. Record the issued DOI in the repository citation guidance on the next revision.

[Create a Zenodo upload](https://help.zenodo.org/docs/deposit/create-new-upload/) · [How to reserve a DOI](https://help.zenodo.org/docs/deposit/describe-records/reserve-doi/) · [Zenodo record versions](https://help.zenodo.org/docs/deposit/manage-versions/)

## Alternative for a GitHub software release

For automatic archival of published GitHub releases, link the owner’s GitHub account to Zenodo and open **profile menu → GitHub → Sync now**. Enable **eldernos/MathematicsResearch** before publishing the corresponding GitHub Release. A Git tag alone leaves this publication step available. On GitHub, choose the existing release tag and verify its target commit. Publish the release, then return to Zenodo’s GitHub panel and open the processed release DOI. Zenodo archives the repository snapshot. All five PDFs are committed under `papers/`, so they travel with the proofs. Verify their presence and checksums on the resulting record. Use the manual route above if the release event already occurred before the integration was enabled. Use one archival route per release to avoid duplicate records.

Zenodo supports repository metadata in CITATION.cff and .zenodo.json. When both are present, Zenodo gives .zenodo.json precedence. Ensure automated records will use the credits you intend before enabling release ingestion. [Enable the repository](https://help.zenodo.org/docs/github/enable-repository/) · [Archive a GitHub release](https://help.zenodo.org/docs/github/archive-software/github-upload/) · [Citation metadata precedence](https://help.zenodo.org/docs/github/describe-software/citation-file/)

## Later revisions

Cite the **version DOI** when a claim depends on a particular manuscript or proof snapshot. Use the all-versions DOI for the evolving collection. For a revision, publish a new Git tag and create the corresponding new Zenodo version. Preserve the SHA, checksums and version DOI of each prior release. [Zenodo versioning](https://help.zenodo.org/docs/deposit/manage-versions/)
