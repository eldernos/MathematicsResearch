# Verification and reproducibility

Everything in the repository that claims to be verified can be re-checked from a clean clone with one script. This page lists what the script does, how to run each step alone, and how to cite an exact version.

## Toolchain

| Component | Version | Where it is fixed |
| --- | --- | --- |
| Lean | v4.36.0 | [lean-toolchain](../lean-toolchain) |
| Mathlib | v4.36.0 (exact commit in the manifest) | [lakefile.toml](../lakefile.toml), [lake-manifest.json](../lake-manifest.json) |
| Python | 3.11 or later, standard library only | exact-arithmetic tests, figures, documentation checks |
| LaTeX | latexmk with pdfLaTeX | manuscripts only, [papers/build.sh](../papers/build.sh) |

## Full verification

From the repository root, with [Elan](https://github.com/leanprover/elan) installed:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get $(sed -nE 's/^(public )?import (Mathlib\.[A-Za-z0-9_.]+)$/\2/p' NormalityChecker/*.lean NormalityChecker/Analysis/*.lean | sort -u)
scripts/verify.sh
```

The same script runs in [Lean continuous integration](../.github/workflows/lean.yml) on every push. The separate [manuscript workflow](../.github/workflows/manuscripts.yml) checks the archived PDFs and the exact source lines embedded in them, then rebuilds all five papers from LaTeX. [Workflow runs](https://github.com/eldernos/MathematicsResearch/actions/workflows/lean.yml)

## What each step establishes

| Step | Command | What it checks |
| --- | --- | --- |
| Exact-arithmetic tests | `python3 -B -m unittest discover -s scripts -p 'test_*.py'` | The finite computations quoted in the notes, with rational arithmetic, and the portal's own checks |
| Build | `lake build` | Every module elaborates; every proof is accepted by Lean's elaborator |
| Independent paper statements | The `check.sh` or `check.lean` entry in each numbered manuscript folder | The library theorems inhabit the public statement types in the two principal papers at the specified radix and indexing conventions |
| Axiom audit | `lake env lean Audit.lean` | The listed theorems depend only on `propext`, `Classical.choice` and `Quot.sound`; no `sorry` and no added axioms |
| Declaration directory | `NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean` | The README directory and [declarations.json](data/declarations.json) list exactly the public theorems and lemmas of the compiled library, at their actual source lines |
| Documentation | `python3 -B scripts/portal.py check --strict` | Registry entries name existing declarations and files; every relative link and anchor resolves; every result identifier mentioned is registered; every module has a topic; generated pages, figures and data are current |
| Kernel replay | `lake env leanchecker <module>` for every module, then `replayFromImports` on the root | The compiled declarations are re-checked by the Lean kernel, independently of the elaborator |

The axiom audit covers the theorems listed in [Audit.lean](../Audit.lean), which include every principal result. The kernel replay covers every module.

## Regenerating derived files

```sh
NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean   # directory, manifest, derived pages
python3 scripts/portal.py build          # after editing docs/registry/*.toml or docs/data/topics.toml
python3 scripts/figures/build.py --pdf   # after editing a figure generator (PDFs need Chrome or Chromium)
python3 scripts/portal.py check --strict # also fail on links to manuscript files that are not yet committed
```

The PDF figures are printed from the light SVGs by a headless browser and are not byte-reproducible; the SVGs and data files are, and the check compares them byte for byte.

## Exact versions and permanent links

Links in the README and the indexes point to the current files, so they follow the code as it changes. A manuscript should instead cite a fixed commit.

- **Checkpoint 11**, the mathematical baseline of the manuscripts, is commit [`a09e011720bc74396a27f4cb3ce2d8a5b3ce5035`](https://github.com/eldernos/MathematicsResearch/commit/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035), tagged `research-checkpoint-11`. The [result index](results.md) gives a Checkpoint 11 permalink for each registered declaration that existed then.
- For any commit, `python3 scripts/portal.py link ST-01 --commit <sha>` prints permanent links to the declarations of a result. Run it in a checkout of that commit so the line numbers match.
- Released manuscripts are tagged and archived as described in [papers/ARCHIVING.md](../papers/ARCHIVING.md).
- Earlier checkpoints are listed in the [research history](history.md).

## What verification does not establish

Lean checks that each formal statement follows from the definitions in the library. It does not check that a definition means what the prose says, that a written proof outside Lean is complete, or that a result is new. The [guide for Lean reviewers](guide-formal-review.md) lists the definitions to inspect, and results that depend on written deductions or published theorems are marked as such in the [result index](results.md).
