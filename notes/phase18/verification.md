# Verification and independent mathematical review

The Phase 18 branch descends from the [completed Phase 17 checkpoint](baseline.md). Verification used Lean 4.36.0, the pinned Mathlib manifest and an isolated WSL Ubuntu build checkout. Its generated declaration directory was copied back and checked against the source worktree. The [proof dependency map](dependencies.md) identifies the written steps between formal declarations.

## Formal and computational checks

- The integrated `lake build` succeeded (8,746 jobs in Lake’s dependency graph). The axiom audit checked 1,593 public theorem declarations and accepted only `propext`, `Classical.choice` and `Quot.sound`. The declaration index contains 1,230 named public theorems and lemmas. These counts use the repository’s different audit and indexing conventions.
- Independent kernel replay completed for all 248 module files and the root. The 245-module pass included the generalized logarithm partition, positive rational summation, and Phase 17. The final pass replayed the exact denominator and normality switch, sharp translation, and consolidated geometric/programming module against the integrated build. The localized joint test and all five paper statement checks passed.
- The repository’s 51 Python unit tests passed. The principal-family check exercised 12,987 prefix shifts. The programming check exercised 12,288 transitions, 1,516 all-prefix enclosures and 7,500 weighted cutoffs. The author and independent algebra programs reproduced exactly the fraction 14035285166320179631/47872170047321719707829651794 at precision 21 for the flagship square. This fraction bounds the limiting upper discrepancy by the written coverage proof. Decimal digit statistics in the scripts are illustrations.
- The classical test uses original signed BBP terms and exact rational sums. The logarithm truncation has a rational geometric-tail bound. Machin alternating-series brackets certify the errors of the selected Chebyshev approximants independently of the coefficient computation. Logarithms printed as decimals are display values. The summation unit tests cover CRT grids, the lower bound on completion delays, Liouville target words and translations with atoms.
- The archive checker verified the five current PDFs, source companions, independent review files and pinned Lean line links. The five SHA-256 entries also matched separately at each release tag, `manuscripts-v1.0.0` and `manuscripts-v1.1.0`. The archived manuscript tree is unchanged from the Phase 17 checkpoint.
- The new front-page mathematics uses ordinary text and Unicode. The added passages were rendered using GitHub’s Markdown endpoint and inspected at actual 390 px and 1,280 px viewport widths in light and dark themes. The local portal rebuild checks the registry, generated pages, dependency data and links inside the Phase 18 notes.

## Review dispositions

The [principal and algebra review](reviews/principal-algebra.md) independently derived the pole, period and convolution estimates and supplied a second implementation. The notes now state the late-shell thresholds, the opposite-axis unit condition and the range of joint polynomial normality. The quantitative comparison cites Vandehey’s original corollary. The [translation and summation review](reviews/translation-summation.md) identified two scope corrections. Ray primes are chosen coprime to the working radix. The general masked-support theorem gives a discrepancy bound, with normality in its specified cases. The cited primary text confirms Rauzy’s prediction direction and Bergelson–Downarowicz’s theorem numbers.

The [dynamics review](reviews/dynamics.md) rederived the sharp finite translation identity, atom handling, fixed-point classification and cubic estimates. The Lambert application now distinguishes the exact supremum from the asymptotic order with character-dependent constants. The [second programming review](reviews/programming-certificate.md) also covered the bounded-denominator necessity, arbitrary invariant-measure limit sets, and the endpoint Liouville argument. The completed principal proof now supplies the period lemma referenced in both audits.

## Reproduction

From the repository root, with the dependencies in [the verification guide](../../docs/verification.md) installed, run

```sh
bash scripts/verify.sh
python3 -B scripts/phase18_principal.py --square-layers 21
python3 -B scripts/phase18_review_algebra.py --layers 21
python3 -B scripts/phase18_programming.py
python3 -B scripts/phase18_classical.py
python3 -B papers/check_release.py --require-reviews --verify-pins
```

The standard script checks the generated registry and declaration index, and replays the modules serially. Finite computations certify the instances or finite combinatorial inputs named in their respective notes. The general estimates, transcendence deductions and literature comparisons have the scope recorded in the [checkpoint report](README.md).
