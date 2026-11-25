# How the results fit together

The theorems in this repository concern different numbers, but their proofs share one structure. This page describes that structure, shows which techniques support which theorems, and explains the different strengths of conclusion that appear in the [result index](results.md).

## One method in five steps

1. **Arithmetic expansion.** The object is a series in which the base-*b* digit positions of the terms are known: a Stoneham number, a logarithm restricted to finitely many primes, a series with polynomial or periodic weights, or a signed series with bounded phases.
2. **Rational radix-orbit model.** Multiply by *b*ⁿ and keep only the terms whose digit position is at most *n*. The result is a rational number *R*ₙ, and *b*ⁿ*x* − *R*ₙ is a small tail. The fractional parts of *b*ⁿ*x* and of *R*ₙ are close, so statistics of the orbit can be read off the rational models.
3. **Denominator survival or cancellation.** Along a block of positions, *R*ₙ₊ᵢ = *b*ⁱ*R*ₙ as long as no new term enters. If the reduced denominator of *R*ₙ keeps a growing power of a prime *p* that does not divide *b*, the block is a piece of the orbit of a rational number with large denominator, and its points are nearly uniformly distributed. If the denominator cancels persistently, the block stays near a fixed rational point.
4. **Local statistical behaviour.** A fixed-support short-orbit estimate turns surviving denominators into interval counts that are uniform up to a small error, simultaneously for all intervals. Cancellation regions are tracked exactly: their positions in each geometric scale are determined by *p*-adic and cyclotomic conditions.
5. **Global discrepancy or normality.** Summing over positions, the uniform blocks contribute nothing to the asymptotic discrepancy and the cancellation regions contribute exactly their density. Normality follows when the cancellation regions have density zero; otherwise the same count gives the exact value of *D*∞ or an upper bound.

| Family | Step 3: why a prime power survives, or where it cancels | Step 5: conclusion |
| --- | --- | --- |
| Stoneham polynomials ([ST-01](results.md#st-01)) | The insertions of a power form an upward-closed set; its generating-function numerator satisfies *K*(*p*) ≡ 1 (mod *p* − 1), so it is never 0 | normality, joint uniformity |
| Finite prime supports ([LS-01](results.md#ls-01)) | Persistent cancellation would give positive measure on a logarithmic circle; finite differences and *p*-adic separation of rays make every fiber finite | normality or *D*∞ = 1 |
| Signed shells ([DS-01](results.md#ds-01)) | On shell *j* the prefix is *b*ⁿ⁻ᵖʲ*c*ⱼ/*p*ʲ modulo 1, whose reduced denominator is at least *p*ʲ/*C* when \|*c*ⱼ\| ≤ *C* and *c*ⱼ ≠ 0, and 1 when *c*ⱼ = 0 | *D*∞ equals the upper density of positions in zero-phase shells |
| Cyclotomic sums ([CR-01](results.md#cr-01)) | Cancellation modulo *p*ᵏ is detected by a cyclotomic polynomial at a lift of 1/*b* | normality, or explicit resonant distributions |

## Proof-dependency map

<!-- BEGIN FIGURE proof-dependency-map -->
<p align="center">
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="../assets/figures/proof-dependency-map-dark.svg">
  <img src="../assets/figures/proof-dependency-map-light.svg" alt="Node-link diagram in three columns. Left column, techniques: upper-orthant sums with K(p) congruent to 1 mod p minus 1; short-orbit cancellation on a fixed prime support; shell counting of signed phases; discrepancy of rational orbits; complete-orbit character sums; p-adic lift of cell coefficients; recurrence on the logarithmic circle; finite differences and finite-ray separation. Middle column, frameworks: rational-prefix normality certificate; discrepancy on selected positions; Ridout's theorem as a paper input; insertion-cell model; the order-one joint-failure formula of Phase 10 as a historical node; persistent failed regions with exact discrepancy at all orders; polynomial masks. Right column, results ST-01, ST-05, DS-01, DS-03, DS-04, CR-01, LS-01, MW-01. Solid arrows: orthant sums and the certificate to ST-01, ST-01 to ST-05; short-orbit cancellation to the certificate, certificate to selected positions, which with shell counting feeds DS-01; DS-01 to DS-03 and DS-04; rational orbits to DS-03; orbit sums and p-adic lifts to the cell model, which feeds CR-01; recurrence, finite differences and persistent regions to LS-01; LS-01 and polynomial masks to MW-01. Dashed arrows: CR-01 to DS-01 and the order-one formula to persistent regions, both historical. A dotted arrow from Ridout's theorem to DS-01. A band at the bottom states that all eight result modules import the definition of normality, Weyl's criterion and the Fourier test." width="640">
</picture>
</p>

<sub>Figure 7. Which techniques the principal theorems use. Solid edges are checked against the Lean import graph; dashed edges are historical, not logical. [Caption, data and generator](../docs/figures.md#proof-dependency-map)</sub>
<!-- END FIGURE proof-dependency-map -->

A solid line is a **mathematical dependency**: the theorem's proof uses the technique, and the generator checks that the Lean module of the theorem imports the module of the technique. A dashed line is a **historical relationship**: one result suggested or preceded another, but the later proof does not rely on it. The figure caption lists the historical links shown. A dotted line marks a published theorem used on paper and not formalized.

## Synthetic expansions

The [Phase 18 dependency map](../notes/phase18/dependencies.md) follows the arithmetic from exact prefix denominators and positive rational state corrections through finite period estimates to full-prefix conclusions. It records which implications use a written proof or an external theorem. The infinite-prime example uses a surviving grid modulo the whole denominator.

## Strength of a conclusion

The [result index](results.md) states which of the following each result establishes. Confusing them is the most common way to overstate a result in this area.

- **Normality.** *D*∞ = 0, equivalently every block of digits has its expected limiting frequency. Examples: [ST-01](results.md#st-01), [LS-01](results.md#ls-01) with an off-base prime, [MW-01](results.md#mw-01).
- **Exact asymptotic discrepancy.** The value of *D*∞ is determined exactly. Examples: [DS-01](results.md#ds-01) to [DS-04](results.md#ds-04), the value 1 in [LS-01](results.md#ls-01), the value 2/3 for two rational polynomial weights. An exact positive value proves nonnormality.
- **Upper discrepancy bound.** *D*∞ ≤ *c* for an explicit *c* < 1. Normality may still hold or fail. Examples: 0.37048 for the product of the binary Stoneham numbers with parameters 3 and 5 ([ST-29](results.md#st-29)); 1 − 1/(*p* − 1) for masked supports; 0.234 for the {2, 5, 13} support at the first precision.
- **Positive uniform coverage.** A positive lower density of positions lies in blocks certified to be nearly uniform. A share *g* with local discrepancy at most *d* gives *D*∞ ≤ 1 − *g*(1 − *d*) ([AC-02](results.md#ac-02)). Certifying finitely many initial blocks, however many, gives no asymptotic information.
- **Unresolved certificate region.** Positions where no available test applies. A failed sufficient certificate is not evidence of nonnormality. For ln 2, π, *e* and the golden ratio the unresolved region currently has full density: no positive coverage, and hence no bound *D*∞ < 1, is known.

## What these methods cannot reach

The certificates need denominators whose prime factors lie in a fixed finite set and whose size is polynomial in the block length. The shifted prefixes of the classical series for ln 2 and π have denominators that grow exponentially with the digit position, so they fall outside these hypotheses. Halving the growth rate, as in [CC-01](results.md#cc-01), does not change this. A counting argument shows that smooth rational models of polynomial size cannot explain the statistics of a typical normal number. [Classical-constant figure](figures.md#classical-denominator-growth) · [Limits of smooth models](../notes/finite-support-discrepancy.md#how-far-polynomial-denominator-models-can-reach) · [Open problems](open-problems.md)
