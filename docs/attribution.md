# Attribution, verification scope and citation

## How the work was done

The research is AI-assisted. The repository owner directed the project, chose its questions and decided what to publish. Large language models, used both as conversational assistants and as autonomous coding agents, proposed conjectures and proof strategies, wrote the human-readable proofs, the Lean formalizations, the exact-arithmetic scripts and this documentation, and compared the results with the literature. Every Lean proof was checked by the Lean kernel; the written proofs and literature comparisons were produced in the same process and have not been reviewed by mathematicians outside the project. The research conversation that guided the early phases is [shared publicly](https://chatgpt.com/share/6b04aebe-d930-83e9-9175-772054b7d221), and the [commit history](https://github.com/eldernos/MathematicsResearch/commits/main) records every step.

The project has no institutional affiliation and no external endorsement. The manuscripts in [papers/](../papers/README.md) are drafts; none has been peer reviewed or accepted.

## What Lean verification establishes

A Lean theorem in this repository is a statement about the definitions in the library, checked by the Lean 4 kernel against Mathlib. The [axiom audit](../Audit.lean) confirms that the audited theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`, with no unproved assumptions, and the kernel replay re-checks every module. [Verification details](verification.md)

Verification does **not** establish:

- **Statement correspondence.** That a Lean definition, for example of normality, discrepancy or a Stoneham number, matches the mathematical notion described in prose. The [guide for Lean reviewers](guide-formal-review.md) lists the definitions to inspect and the conventions to check.
- **Written deductions.** Results marked *Lean + written deduction* or *Written proof* in the [result index](results.md) rely on arguments outside Lean, sometimes on published theorems such as Roth's theorem, Ridout's theorem, Bang's primitive-divisor theorem or the prime number theorem.
- **Finite computations as asymptotic evidence.** An exact computation proves only its finite statement. Figures labelled *numerical illustration* are not evidence for any limit.
- **Novelty.** Whether a result is new. Priority is under investigation; see the [literature comparisons](../notes/reviewers.md#relation-to-prior-work).

## How to cite

Cite a fixed version, not the moving default branch. Give the commit, the result identifier and, where relevant, the Lean declaration.

```bibtex
@misc{normality-arithmetic-expansions,
  title        = {Normality and Discrepancy of Arithmetic Expansions},
  howpublished = {GitHub repository, commit a09e011720bc74396a27f4cb3ce2d8a5b3ce5035 (Checkpoint 11)},
  url          = {https://github.com/eldernos/MathematicsResearch/tree/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035},
  note         = {Result ST-01, Lean declaration NormalityChecker.StonehamPolynomial.prime_power_polynomial_normal}
}
```

Replace the commit, identifier and declaration as needed; `python3 scripts/portal.py link <ID> --commit <sha>` prints the permanent links. Use the creator names from the owner-approved archival record when it becomes available. Manuscript releases, DOIs and the recommended form of citation for each paper are described in [papers/ARCHIVING.md](../papers/ARCHIVING.md); once a DOI is issued, cite the version DOI.

## License

Original contributions are released under the [MIT license](../LICENSE). The port of Trevor Morris's Weyl criterion in [NormalityChecker/Analysis/Weyl.lean](../NormalityChecker/Analysis/Weyl.lean) retains its Apache-2.0 license and attribution. Cited papers belong to their authors and are linked, not redistributed.

## Corrections and contact

Corrections, missing literature, questions about a statement, and reports of a gap between a formal statement and its prose are welcome as [GitHub issues](https://github.com/eldernos/MathematicsResearch/issues). Please quote the result identifier, for example ST-01. [Contributing](../CONTRIBUTING.md)
