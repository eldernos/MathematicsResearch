# Verification and independent mathematical review

The Phase 18 branch descends from the [completed Phase 17 checkpoint](baseline.md). Verification used Lean 4.36.0, the pinned Mathlib manifest and an isolated WSL Ubuntu build checkout. Its generated declaration directory was copied back and checked against the source worktree. The [proof dependency map](dependencies.md) identifies the written steps between formal declarations.

## Formal and computational checks

- The integrated `lake build` succeeded (8,746 jobs in Lake’s dependency graph). The axiom audit checked 1,593 public theorem declarations and accepted only `propext`, `Classical.choice` and `Quot.sound`. The declaration index contains 1,230 named public theorems and lemmas. These counts use the repository’s different audit and indexing conventions.
- Independent kernel replay completed for all 248 module files and the root. The 245-module pass included the generalized logarithm partition, positive rational summation, and Phase 17. The final pass replayed the exact denominator and normality switch, sharp translation, and consolidated geometric/programming module against the integrated build. The serial verification run also completed. When its host interrupted it after 174 confirmed modules, the continuation verified the ordered log against the source list, replayed the first unconfirmed file and all 73 remaining files, then replayed the root. The localized joint test and all five paper statement checks passed.
- The repository’s 51 Python unit tests passed. The principal-family check exercised 12,987 prefix shifts. The programming check exercised 12,288 transitions, 1,516 all-prefix enclosures and 7,500 weighted cutoffs. The author and independent algebra programs reproduced exactly the fraction 14035285166320179631/47872170047321719707829651794 at precision 21 for the flagship square. This fraction bounds the limiting upper discrepancy by the written coverage proof. Floating-point Gauss-sum diagnostics and decimal digit statistics in the scripts are illustrations. The two 21-layer bounds are computed with exact integers and fractions.
- The [independent Legendre review](reviews/phase17-transfer.md) checked the first-crossing argument, integral growth and quantitative limitations. Its [separate computation](reviews/phase17-transfer-check.py) reproduced both examples. The main script certifies nearest-grid agreement throughout its finite test and the Machin period of 9,391,865,143,397,864,727,600 at shift 600. The Phase 17 extension to π passed 518 exact rational comparisons across two arctangent identities, including all shifts from 1 to 256. At shift 600 the certified absolute-error bounds are 2⁻²⁶¹ and 2⁻²¹³ for Machin and Størmer respectively. The classical test uses original signed BBP terms and exact rational sums. The logarithm truncation has a rational geometric-tail bound. Machin alternating-series brackets certify the errors of the selected Chebyshev approximants independently of the coefficient computation. Logarithms printed as decimals are display values. The summation unit tests cover CRT grids, the lower bound on completion delays, Liouville target words and translations with atoms.
- The archive checker verified the five current PDFs, source companions, independent review files and pinned Lean line links. The five SHA-256 entries also matched separately at each release tag, `manuscripts-v1.0.0` and `manuscripts-v1.1.0`. The archived manuscript tree is unchanged from the Phase 17 checkpoint.
- The new front-page mathematics uses ordinary text and Unicode. The added passages were rendered using GitHub’s Markdown endpoint and inspected at actual 390 px and 1,280 px viewport widths in light and dark themes. The strict portal check passed for the registry, including 24 Phase 18 entries, and all indexed Markdown files. It also checked generated pages, figure data and links inside the Phase 18 notes.

## Review dispositions

The [principal and algebra review](reviews/principal-algebra.md) independently derived the pole, period and convolution estimates and supplied a second implementation. The notes now state the late-shell thresholds, the opposite-axis unit condition and the range of joint polynomial normality. The quantitative comparison cites Vandehey’s original corollary. The [translation and summation review](reviews/translation-summation.md) identified two scope corrections. Ray primes are chosen coprime to the working radix. The general masked-support theorem gives a discrepancy bound, with normality in its specified cases. The cited primary text confirms Rauzy’s prediction direction and Bergelson–Downarowicz’s theorem numbers.

The [dynamics review](reviews/dynamics.md) rederived the sharp finite translation identity, atom handling, fixed-point classification and cubic estimates. The Lambert application now distinguishes the exact supremum from the asymptotic order with character-dependent constants. The [second programming review](reviews/programming-certificate.md) also covered the bounded-denominator necessity, arbitrary invariant-measure limit sets, and the endpoint Liouville argument. The completed principal proof now supplies the period lemma referenced in both audits.

The [independent classical and source audit](reviews/classical-sources.md) supplies the fixed-band signed proofs for BBP and Bellard. It recovered every odd prime in the original two BBP slots, corrected the logarithmic error claimed for the cross-ray separation bound, and checked all nine Chebyshev errors by rational enclosure. The final text distinguishes point entropy from topological entropy, states the correct Pell valuation, and records the primitive-root and denominator-chain hypotheses in the primary literature. The external projects are cited at pinned statements; their own kernels were outside the local replay.

All six Phase 17 computational scripts also passed again on the integrated checkout at their default settings. The finite-exception audit distinguished interrupted processes from completed research: all five previously failed Phase 18 workstreams were recovered, with the review findings, proofs and scripts committed.

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
