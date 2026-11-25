# Licensing proposal for manuscripts and code

**Status: proposal for explicit owner approval. Nothing in this file has been applied.** The [LICENSE](../LICENSE) file is unchanged. This is not legal advice. The repository owner decides, and may wish to confirm the points below with the policies of the venues involved.

## Current situation

| Material | Current licence | Notes |
| --- | --- | --- |
| Lean library, scripts and other code | MIT ([LICENSE](../LICENSE), copyright line "MathematicsResearch contributors") | Clear and permissive. |
| Port of Trevor Morris's Weyl criterion ([NormalityChecker/Analysis/Weyl.lean](../NormalityChecker/Analysis/Weyl.lean)) | Apache-2.0, kept with its attribution ([LICENSE-Weyl](../NormalityChecker/Analysis/LICENSE-Weyl)) | Must stay Apache-2.0. |
| Manuscripts, research notes, figures, documentation prose | Implicitly the MIT licence, which was written for software and "associated documentation files" | Ambiguous for papers: MIT does not require attribution in the form scholars expect, and says nothing about derivative works of an article, translations or reuse of figures. |
| PDFs of released manuscripts | Distributed with the repository, so also under the same implicit terms | The v1.0.0 and v1.1.0 archives carry no licence statement of their own. |

## Code

Keep **MIT** for code and keep **Apache-2.0** for the Weyl port. No change is proposed. Lean and Mathlib, on which the library depends, are themselves Apache-2.0, which is compatible with MIT distribution of the project's own files. If the owner prefers that the copyright line name a person instead of "MathematicsResearch contributors", that is a one-line edit of `LICENSE` that this proposal does not make.

## Manuscripts: options

| Option | What it permits | Fit with arXiv, alphaXiv, Zenodo and journals |
| --- | --- | --- |
| **CC BY 4.0** | Anyone may copy, adapt and redistribute, including commercially, with attribution. Irrevocable once granted for the version released. | Accepted by arXiv and Zenodo (Zenodo's usual default for publications). The alphaXiv site is, to our understanding, a discussion layer over arXiv papers, so the arXiv licence is the one that governs. Most mathematics journals accept a preprint under CC BY, and a transfer of copyright or an exclusive licence for the journal version then covers only the journal's own typeset article; check the target journal's preprint policy before submitting. |
| **CC BY-SA 4.0** | As CC BY, but adaptations must carry the same licence. | Accepted by arXiv and Zenodo. The share-alike condition can conflict with a journal's exclusive licence for a revised version, so it is the more restrictive choice for later publication. |
| **arXiv non-exclusive licence** (arXiv's default, a perpetual non-exclusive licence to distribute) | arXiv may distribute the paper. Reuse by others is limited by copyright law. | Fits arXiv and alphaXiv. Compatible with journal transfer, because the owner keeps all other rights. It does not make the repository copy reusable. |
| **All rights reserved** | Nothing beyond what law and the platform terms allow. | Compatible with everything, but it contradicts the repository's openness, and some platforms require a licence for open-access deposits. Zenodo records for open access need a stated licence. |
| **CC BY-NC variants** | No commercial reuse. | Accepted by arXiv and Zenodo, but "non-commercial" is hard to apply and is disliked by repositories and indexing services. Not recommended. |

Points that apply to all options:

- Under a Creative Commons licence the owner keeps the copyright and may still sign a publisher agreement for a later version, subject to the publisher's terms. A licence already granted for an earlier version stays in force for that version.
- The copyrightability of text and proofs produced largely by AI is unsettled in several jurisdictions, and a licence can only convey rights that exist. The manuscripts disclose their AI assistance and state who is responsible for the release; the licence does not change that.
- Research notes and documentation prose share the issue. Lean files and scripts are code and stay under MIT.

## Recommendation

1. **Manuscripts, figures and prose documentation: CC BY 4.0**, with the owner as the attributed author, for the release candidate manuscripts-v2.0.0 and later versions. It states the reuse terms clearly, is accepted by arXiv, alphaXiv-via-arXiv and Zenodo, asks for the attribution scholars expect, and does not block a journal's licence for a later article version.
2. **Code: MIT**, and **the Weyl port: Apache-2.0**, unchanged.
3. **arXiv submission:** choose CC BY 4.0 when submitting, so that the arXiv licence matches the repository. If the owner expects to sign a journal copyright transfer for a specific paper, choose arXiv's non-exclusive licence for that paper instead and note the difference in its `submission/alphaxiv.md`.
4. **Zenodo:** archive the software snapshot under MIT and any separate manuscript record under CC BY 4.0, as two records, so that one licence field does not misdescribe both.
5. **Released v1.0.0 and v1.1.0 archives** are not relicensed retroactively. The new licence statement applies from the version that carries it.

## Files that would change if the owner approves

| File | Change |
| --- | --- |
| `LICENSE-MANUSCRIPTS.md` (new) | CC BY 4.0 notice and link to the legal code, listing the covered paths: `papers/0[1-9]-*-v2/` and `papers/0[6-9]-*/` manuscript sources and PDFs, `assets/figures/`, `notes/`, `docs/`. |
| `README.md` | The sentence in "Attribution, citation and contributing" that now says original contributions use the MIT licence: add that manuscripts and prose use CC BY 4.0. |
| `docs/attribution.md` | The "License" section, in the same way. |
| `CITATION.cff` | Keep `license: MIT` for the software. Optionally add `references` entries with `license: CC-BY-4.0` for the manuscripts. |
| `papers/common/byline.tex` or `papers/common/preamble.tex` | One licence line under the byline (owner decision; these files are shared by all manuscripts and are not edited in this wave). |
| each manuscript's `submission/alphaxiv.md` | A licence line matching the arXiv choice. |
| `papers/ARCHIVING.md` | The Zenodo steps: the licence to select for the software record and for a paper record. |
| `.zenodo.json` (new, optional) | Only if separate records need metadata different from `CITATION.cff`; Zenodo gives this file precedence over `CITATION.cff`. |
| `CONTRIBUTING.md` | One sentence stating that contributions are accepted under the same terms. |
| `LICENSE` (optional) | Replace the copyright holder "MathematicsResearch contributors" by a personal name, only if the owner wishes. |

## Related decision: named-author editions of the v1.1 papers

The five v1.1 PDFs were released without an author line and are archived as they are at the tags `manuscripts-v1.0.0` and `manuscripts-v1.1.0`. The v2 manuscripts carry the author line. If the owner wants named-author editions of the five v1.1 papers **before** the main release, they would need a new version identifier, for example v1.2, because the existing tags and PDF checksums must not change. They have not been created. The bibliography ([papers/BIBLIOGRAPHY.bib](../papers/BIBLIOGRAPHY.bib)) names the owner as author of every entry and notes that the archived v1.x PDFs carry no author line.
