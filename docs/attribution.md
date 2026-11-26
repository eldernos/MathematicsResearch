# Attribution, verification scope and citation

## How the work was done

The research is AI-assisted. The repository owner directed the project, chose its questions and decided what to publish. Large language models, used both as conversational assistants and as autonomous coding agents, proposed conjectures and proof strategies, wrote the human-readable proofs, the Lean formalizations, the exact-arithmetic scripts and this documentation, and compared the results with the literature. Every Lean proof was checked by the Lean kernel; the written proofs and literature comparisons were produced in the same process and have not been reviewed by mathematicians outside the project. The research conversation that guided the early phases is [shared publicly](https://chatgpt.com/share/6b04aebe-d930-83e9-9175-772054b7d221), and the [commit history](https://github.com/eldernos/MathematicsResearch/commits/main) records every step.

Models from several providers also reviewed drafts and proofs against one another. That cross-model review found errors that were corrected, but it is not independent human peer review, and human specialist review is outstanding. [Research process](../README.md#how-the-research-was-done)

The author of the release candidate manuscripts is Christopher Anderson, Independent Researcher. The project has no institutional affiliation and no external endorsement. The only contact route is the [issue tracker](https://github.com/eldernos/MathematicsResearch/issues); no email address, ORCID or other affiliation is published. The manuscripts in [papers/](../papers/README.md) are drafts; none has been peer reviewed or accepted.

## What Lean verification establishes

A Lean theorem in this repository is a statement about the definitions in the library, checked by the Lean 4 kernel against Mathlib. The [axiom audit](../Audit.lean) confirms that the audited theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`, with no unproved assumptions, and the kernel replay re-checks every module. [Verification details](verification.md)

Verification does **not** establish:

- **Statement correspondence.** That a Lean definition, for example of normality, discrepancy or a Stoneham number, matches the mathematical notion described in prose. The [guide for Lean reviewers](guide-formal-review.md) lists the definitions to inspect and the conventions to check.
- **Written deductions.** Results marked *Lean + written deduction* or *Written proof* in the [result index](results.md) rely on arguments outside Lean, sometimes on published theorems such as Roth's theorem, Ridout's theorem, Bang's primitive-divisor theorem or the prime number theorem.
- **Finite computations as asymptotic evidence.** An exact computation proves only its finite statement. Figures labelled *numerical illustration* are not evidence for any limit.
- **Novelty.** Whether a result is new. Priority is under investigation; see the [literature comparisons](../notes/reviewers.md#relation-to-prior-work).

## How to cite

### Release candidate `manuscripts-v2.0.0`

Cite a manuscript by author, title, version and release tag. The author of the v2 manuscripts is Christopher Anderson, Independent Researcher. The release is a **candidate** until the owner publishes the tag, and no DOI has been issued. A BibTeX entry for every current manuscript is in [papers/BIBLIOGRAPHY.bib](../papers/BIBLIOGRAPHY.bib), and the repository itself is described by [CITATION.cff](../CITATION.cff), which GitHub shows under "Cite this repository". Paper III is retained at version 1.1 in this release. The manuscripts are preprint drafts and have not been peer reviewed.

```bibtex
@unpublished{anderson-stoneham-polynomials-v2,
  author = {Anderson, Christopher},
  title  = {Polynomial Images of Stoneham Numbers},
  year   = {2026},
  note   = {Version 2.0, preprint draft in release candidate manuscripts-v2.0.0. Not peer reviewed.},
  url    = {https://github.com/eldernos/MathematicsResearch/tree/main/papers/01-stoneham-polynomials-v2}
}
```

For a formal result, give its identifier, the Lean declaration and the proof commit; `python3 scripts/portal.py link <ID> --commit <sha>` prints the permanent links. The v2 manuscripts pin their Lean links to research-checkpoint-18 (`e4809cf561573aef588e6ffc491a35cdb79fd9ec`). The [research site](site.md) shows the same BibTeX on each manuscript page. Once a DOI is issued, cite the version DOI ([papers/ARCHIVING.md](../papers/ARCHIVING.md)).

### Earlier releases (history)

For a manuscript, cite its title, the release tag `manuscripts-v1.1.0` and the version DOI when available. The release manifest identifies the associated commit and PDF checksum. For a formal result, give its proof commit, result identifier and Lean declaration. The following example cites the Checkpoint 11 polynomial theorem. [Manuscript release](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v1.1.0)

```bibtex
@misc{normality-arithmetic-expansions,
  title        = {Normality and Discrepancy of Arithmetic Expansions},
  howpublished = {GitHub repository, commit a09e011720bc74396a27f4cb3ce2d8a5b3ce5035 (Checkpoint 11)},
  url          = {https://github.com/eldernos/MathematicsResearch/tree/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035},
  note         = {Result ST-01, Lean declaration NormalityChecker.StonehamPolynomial.prime_power_polynomial_normal}
}
```

Replace the commit, identifier and declaration as needed; `python3 scripts/portal.py link <ID> --commit <sha>` prints the permanent links. The v1.0.0 and v1.1.0 archives carry no author line. Manuscript releases, DOIs and the recommended form of citation for each paper are described in [papers/ARCHIVING.md](../papers/ARCHIVING.md); once a DOI is issued, cite the version DOI.

## License

The manuscripts of manuscripts-v2.0.0 and their designated accompanying prose and figures are licensed under [CC BY 4.0](../LICENSE-MANUSCRIPTS.md), © 2026 Christopher Anderson; earlier releases are not relicensed. Other original contributions, including all code, are released under the [MIT license](../LICENSE). The port of Trevor Morris's Weyl criterion in [NormalityChecker/Analysis/Weyl.lean](../NormalityChecker/Analysis/Weyl.lean) retains its Apache-2.0 license and attribution. Cited papers belong to their authors and are linked, not redistributed.

## Corrections and contact

Corrections, missing literature, questions about a statement, and reports of a gap between a formal statement and its prose are welcome as [GitHub issues](https://github.com/eldernos/MathematicsResearch/issues). Please quote the result identifier, for example ST-01. [Contributing](../CONTRIBUTING.md)
