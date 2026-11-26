# Phase 14 research checkpoint

**The dyadic quadratic obstruction is equivalent to a specific 2-adic approximation problem.** For each odd radix *b* ≥ 3 and rational quadratic evaluated at α(*b*,2), Lean determines exactly when ordinary normality holds. Every such value is logarithmically equidistributed, its ordinary lower discrepancy is zero, and its upper discrepancy is at most 1/4. These conclusions allow arbitrary rational coefficients. [Criterion](quadratic-orbits.md) · [Exact upper discrepancy](plateau-spectrum.md)

The starting commit was `6d653bed452f345bf9bc5202627912f0f341237c`. The series begins at index one. All discrepancy bounds concern half-open intervals and every integer prefix unless a different averaging convention is specified. [Phase 13](https://github.com/eldernos/MathematicsResearch/tree/research-checkpoint-13) · [Published manuscripts](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v1.1.0) · [Result registry](../../docs/results.md)

## Arithmetic expansions

| Track | Result | Verification and remaining boundary |
| --- | --- | --- |
| A. Parameter-two quadratics | The proposed affine approximation for *T*ₖ holds with error valuation exactly *k* − 1 + 2*s*. The cleared upper-shell denominator is 2 raised to the positive part of *k* − *v*₂(2*A*λ) − *v*₂(*k* − κ), with value 1 at *k* = κ. Algebraic κ suffices for normality. The exact upper discrepancy is one quarter of the upper limit of the discrepancies of the eventual rational plateau cycles. | Lean covers the actual shifted polynomial, separation of small denominators, the equivalence with growth, log weighting, the all-prefix comparison and exact upper limit. For *X*² − 2*X*, a bijective 2-adic isometry gives two opposite eligible residue classes as the radix varies. The cited logarithm estimates do not determine ordinary normality for a fixed integer radix. [Denominators](quadratic-denominators.md) · [Cycle theorem](plateau-spectrum.md) · [Radix classification](resonant-radices.md) · [Independent audit](reviews/quadratic-orbits.md) |
| B. Remaining degrees | All rational polynomials of degrees 3 through 15 give normal values at α(*b*,2) in every odd radix *b* ≥ 3. Every degree here includes arbitrary rational lower coefficients. | The quartic proof is kernel-verified, as were the odd prime-power degrees in Phase 13. Degrees 6, 8, 10, 12, 14 and 15 use exhaustive finite arithmetic and the leading-denominator argument. The secondary order for an even box missing its diagonal is a separate theorem; it need not be the order of an actual prefix. [Proof and tables](higher-degrees.md) · [Independent audit](reviews/higher-degrees.md) |
| C. Independent prime axes | For α(2,3)α(2,5), the ordinary upper density of simultaneous first-precision failures is between 0.575523806608492 and 0.575523806608494. Full rectangles still have growing reduced denominators, so the upper discrepancy of the product is at most **0.37047223953703**. The ordinary lower discrepancy is zero. | Lean proves 0.575524 for the original count and **0.37048** after excluding rectangles. The narrower enclosures use exact rational phase bracketing. At depths *h*, *j* ≥ 1 the joint logarithmic failure density is 1/(8·3ʰ⁻¹·5ʲ⁻¹), while the ordinary upper failure density is at least 4/11 at every fixed pair of depths. The density and log-equidistribution deductions have paper proofs. Ordinary normality and pointwise sublinear loss on every nonrectangle remain open. [Full count](mixed-flow.md) · [Refined bound](nonrectangular-coverage.md) · [Interpolation](mixed-interpolation.md) · [Independent checks](reviews/mixed-depth.md) |
| D. Quantitative normality | For fixed coprime parameters *b* ≥ 2, *c* > 2 and a rational polynomial of degree *d* ≥ 1, the defining-radix discrepancy is bounded by a computable constant times *N* raised to −1/[2(2ᵈ⁺¹ − 2)]. The method also covers the parameter-two square and the previously verified odd prime-power degrees. The square and cube admit sharper rates with logarithmic powers 3/2 and 5/4, respectively. | Lean verifies the denominator, insertion-gap and finite transfer estimates. The final exponents use Vandehey and Erdős–Turán on paper. The proof gives an algorithm for the fixed-input constants; it makes no optimality claim for those exponents. [Quantitative proof](quantitative-composites.md) · [Independent source check](reviews/quantitative-composites.md) |

## Classical constants

| Track | Result | Verification and remaining boundary |
| --- | --- | --- |
| E. Gaussian logarithms | The best reduced-denominator rate for ln 2 is **5/12**, and the runner-up is **13/30**, among fixed finite rational combinations of the specified real dyadic logarithms and real parts of Gaussian dyadic logarithms, with unbounded strides and a common binary cutoff. Both constants were attained in Phase 13. The new result is global optimality and uniqueness of the corresponding prefix sequences in this alphabet. | The norm descent invokes Grechkoseeva; the four-parameter classification and exact prime-band optimization have paper proofs. Lean checks cutoff and Frobenius identities, valuation constraints and finite prime witnesses. [Class definition and proof](gaussian-relations.md) · [Independent optimization](reviews/gaussian-optimality.md) |
| F. Actual digit statistics | A positive proportion η of starts with at least ρ*T* internal changes in length-*T* words on every late dyadic shell would give lower transition density at least ηρ/6. This holds for *T* = ⌊*N*ᵟ⌋, 0 < δ ≤ 1. Exact arithmetic certifies seven finite shells for the actual digits. On growing windows the genuine primary components at any fixed number of good primes have joint character cancellation. | The implication and primary-factor arithmetic are kernel-verified. The analytic joint estimate uses Bourgain–Chang. The complementary factors leave an uncontrolled equal-frequency character, precisely the real logarithm character of interest. No uniform positive ρ and η for the actual logarithm on all late shells have been proved. [Transition transfer and finite experiment](transition-windows.md) · [Joint characters and obstruction](primary-components.md) · [Independent review](reviews/primary-characters.md) |
| G. Erdős–Borwein constant | The one-source divisor analysis narrows the Fourier localization band. A Poisson comparison with the one-source odd-part distribution predicts a binary one-frequency in [0.492230, 0.492685]. If the actual one-frequency tends to 1/2, the actual 32-level distribution must stay separated from this model in total variation by more than 0.006 in the lower limit. | The Poisson number is a certified model value. The actual one-frequency and correct limiting word frequencies are open. The finite carry and reindexing steps have Lean proofs. The external positive word-density and disjunctivity results are attributed to Mira Cult and Captain Sude, respectively. [Proofs, pinned antecedents and computation](erdos-borwein-frequencies.md) · [Independent interval calculation](reviews/classical-frequencies.md) |

## What warrants manuscript revision

- **Paper I:** the quadratic normality criterion, exact cycle discrepancy and degree 3–15 coverage; the improved ordinary bound for independent axes and their logarithmic equidistribution. Give the finite certificates their own scope.
- **Paper IV:** the all-cutoff power-saving estimates for composite parameters and the corrected logarithmic factors for squares and cubes.
- **Paper V:** the Gaussian optimality classification and the conditional transition-window theorem, with the finite true-digit tests and the obstruction to passing from prime projections to the real orbit.
- **External research:** the Erdős–Borwein dependence test belongs with the external positive-density work and its one-source hypotheses. It supplies no proof of normality or nonnormality.

The five published manuscripts remain at their released revisions. The comparisons in the individual notes identify established analytic inputs and extensions of the previous checkpoint. Historical priority of the extensions remains to be assessed by specialists.

## Reproduction

Run `bash scripts/verify.sh` for the build, axiom checks, theorem directory, tests and kernel replay. The main independent computations can also be run directly.

```sh
python3 -B scripts/check_phase14_cancellation.py
python3 -B scripts/phase14_dyadic_power_cells.py --audit
python3 -B scripts/phase14_mixed_flow.py
python3 -B scripts/phase14_nonrectangular.py
python3 -B notes/phase14/gaussian_relations.py
python3 -B scripts/phase14_transition_windows.py
python3 -B scripts/erdos_borwein_poisson.py
```
