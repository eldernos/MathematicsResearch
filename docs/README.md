# Documentation

This directory holds reader guides, the result indexes and the verification documentation. The mathematics itself is in the [research notes](../notes/results.md), the [manuscripts](../papers/README.md) and the [Lean library](../NormalityChecker).

## Start here

| If you want to | Read |
| --- | --- |
| understand what was proved, without prerequisites | [Guide for newcomers](guide-newcomers.md) |
| check a particular theorem and its literature | [Guide for mathematicians](guide-mathematicians.md) |
| audit a formal statement and reproduce the build | [Guide for Lean reviewers](guide-formal-review.md) |

## Indexes

- [Curated result index](results.md): every major result with a permanent identifier, statement, scope, Lean declaration, proof, paper and kind of evidence. Generated from the [registry](registry/SCHEMA.md).
- [Complete declaration directory](theorems.md): every public theorem and lemma, by topic and module, with docstring summaries. Generated from the [manifest](data/declarations.json).
- [Figures](figures.md): the nine scientific figures with captions, provenance, data and generators.

## Context

- [How the results fit together](framework.md): the common method, a proof-dependency map, and the difference between normality, exact discrepancy, bounds and coverage.
- [Open problems and limitations](open-problems.md): what has not been proved.
- [Verification and reproducibility](verification.md): toolchain, build, tests, axiom audit, kernel replay, generated indexes and exact-commit links.
- [Research history](history.md): the checkpoint record, kept separate from the exposition.
- [Attribution and citation](attribution.md): how the work was done, what Lean verification covers, how to cite, license.
- [Contributing](../CONTRIBUTING.md): how to report a correction or a literature reference.

## Repository layout

| Path | Contents |
| --- | --- |
| [README.md](../README.md) | Principal results and overview |
| [papers/](../papers/README.md) | Manuscripts, publication status, notation and archiving |
| [notes/](../notes/results.md) | Complete written proofs and research notes |
| [docs/](README.md) | Guides, indexes, verification documentation |
| [assets/](../assets/figures) | Figures and their data |
| [scripts/](../scripts) | Verification, exact-arithmetic checks and generators |
| [NormalityChecker/](../NormalityChecker) | The Lean library |

## Maintaining the derived pages

`docs/results.md`, `docs/theorems.md`, `docs/figures.md`, the declaration manifest and two blocks of the README are generated. After changing Lean statements, run `lake build`, then `NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean`, which also runs `python3 scripts/portal.py build`. After editing the registry, run `python3 scripts/portal.py build`. After editing a figure generator, run `python3 scripts/figures/build.py --pdf`. `python3 scripts/portal.py check` verifies all of it and runs as part of `scripts/verify.sh`.
