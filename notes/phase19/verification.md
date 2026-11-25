# Phase 19 evidence and reproducibility

The branch starts at `research-checkpoint-18` (`e4809cf561573aef588e6ffc491a35cdb79fd9ec`). The four objectives remain normality, nonnormality, quantitative classification and rigorous limitations. The [registry](../../docs/registry/OP.toml) gives the evidence status for each result. The [publication handoff](publication-handoff.md) records corrections to earlier material.

## Independent mathematical reviews

- The [addition review](reviews/addition.md) rederived the five weights, finite necessity, positive state corrections, unfinished-block bounds and effective independence construction. It checked the higher-dimensional polygon and the obstruction for six forms. The proof now credits classical qualitative realization separately. The [joint box review](reviews/joint-and-rapid.md) verifies the Hensel direction and the height-dependent Fourier bounds needed for a box rate.
- The [grid review](reviews/grids.md) checked the order, lift exhaustion, real grids, all-prefix costs, CRT prime-power gaps, the accelerated schedules and the cited shifted-prime lcm estimate. The largest ternary grid has no uniform upper bound by a constant times the cutoff parameter. A subgrid satisfies the advertised two-sided scale.
- The [nonlinear review](reviews/nonlinear.md) independently checked the derivative estimate, removed degeneracies, localized grid intersections, second moments and the frozen-prefix transfer. A second [schedule review](reviews/joint-and-rapid.md) covers rapid variation and weighted generators. The [distinct-prime review](reviews/independent-axes.md) checks the cross-prime congruences and all three competing pole losses. These asymptotic results are written proofs.
- The [geometry and period review](reviews/geometry-periods.md) covers finite pseudometrics, quotient kernels, scalar actions, boundary spectra and the lower bound on actual Taylor periods. The later [classical review](reviews/classical.md) corrects an overlap count in the earlier review's rate suggestion and checks the sharper rate, the inverse dilation estimate, and the horizontal logarithm spectra. Primary-source comparisons and the limits of priority claims appear in the [literature note](literature.md).

## Verification evidence

The integrated Lean build ran 8,754 Lake jobs using the pinned toolchain. The axiom audit accepted 1,719 public theorem declarations using only `propext`, `Classical.choice` and `Quot.sound`. The generated directory indexes 1,332 named public theorems and lemmas. The exact qualitative addition spectrum is unconditional in every radix. The cubic rate, computable algebraic independence and analytic proof for the flagship square are written theorems.

The independent classical audit resumed after a provider error. Its first committed report contains the same-cutoff lifting and sharpened mean denominator-loss estimate. The [final audit](reviews/classical-final.md) independently reproduced the million-prime local histogram and checked the 2,260 constructed dyadic groups, theorem conventions and primary-source precedents. Rogers studied the weighted harmonic-prefix zero problem and Sanna gives the comparison for counting pairs of zeros. These precedents inform the scope of the new arithmetic bounds.

## Reproduce

Use the pinned Lean toolchain and Mathlib manifest as in the [repository verification guide](../../docs/verification.md). From the repository root run:

```sh
bash scripts/verify.sh
python3 -B scripts/phase19_addition.py
python3 -B scripts/phase19_grids.py
python3 -B scripts/phase19_nonlinear.py
python3 -B scripts/phase19_classical.py
python3 -B scripts/phase19_horizontal.py
python3 -B scripts/phase19_independent_axes.py
python3 -B papers/check_release.py --require-reviews --verify-pins
```

The general theorems rely on the mathematical proofs and the formal lemmas identified with them. Integer or rational finite checks certify the stated runs. Numerical diagnostics in independent scripts do not establish asymptotic normality or historical priority.
