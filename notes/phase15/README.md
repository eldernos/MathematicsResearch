# Phase 15 — the limiting binary orbit of ln 2

**A prescribed approach to the endpoint of the binary product cannot certify strict discrepancy.** Let *z* be the point on the unit circle with angle 2π*x*. At cutoff *N*, multiply the factors 1 + *a w* at the first *N* points *w* = *z*, *z*², *z*⁴, … . For any prescribed sequence of parameters in (0, 1) tending to one, some irrational *x* has binary discrepancy tending to one even though the log modulus of this product divided by *N* tends to zero when evaluated at the *N*th parameter. Holding any interior parameter *a* fixed instead gives the maximal exponential growth rate 1 + *a*. The construction specifies how slowly to increase the gaps between the ones in the binary expansion. [Paper proof](fredholm-and-products.md#a-moving-parameter-still-cannot-recover-a-fixed-interior-deficit)

The starting point is the annotated tag [research-checkpoint-14](https://github.com/eldernos/MathematicsResearch/tree/research-checkpoint-14) at commit `2d97706896a297f1e8054c1a61c13dcb6087cd5b`. Its independent reviews cover the analytic inputs and finite computations. Its Lean and manuscript workflows passed, and Hail reproduced the base build with Lean 4.36.0. The manuscript releases are [v1.0.0](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v1.0.0) and [v1.1.0](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v1.1.0). [Phase 14 evidence](../phase14/README.md)

## Where the arguments reach

| Track | What is established | What the real orbit still needs |
| --- | --- | --- |
| A. Complex orbit functions | Lean proves the Fredholm equation and the sharp-cutoff comparison with absolute error at most two. Strict limiting discrepancy is equivalent to positive lower normalized radial deficit. A fixed interior product parameter gives the same criterion on paper. [Proof and product counterexample](fredholm-and-products.md) | A positive radial lower mean at the specific angle of ln 2. A lower mean of 0.0004 would already yield the requested bound 0.9999. |
| B. Higher rank | The mixed functional differences recover the binary axis exactly. A sparse irrational can defeat even position-dependent selection among all multipliers up to any prescribed subexponential height. [Projection and geometry](projection-and-returns.md) · [Height theorem](multiplier-height.md) | A positive mixed estimate with a bounded cost of transfer to that axis. Higher-rank orbit density alone supplies none. |
| C. Lattice lifting | Lean verifies affine gcd feasibility and the coefficient-weighted error. Even arbitrarily many Taylor cutoffs in a sublinear-width interval retain the full odd-denominator rate under integer affine combinations. [Kernel statements](../../NormalityChecker/AffineDenominator.lean) · [Uniform denominator proof](nearby-taylor.md) · [Three-source lattice experiment](affine-experiment.md) | A sequence of feasible, low-cost lifts whose real rational orbits have the requisite escape on a positive share of positions. |
| D. Algebraic logarithms | At every cutoff, logarithmic trace sources of arbitrary degree with a common half-integral binary exponent reduce to real and Gaussian sources. The two least rates for fixed formulas in this class are still 5/12 and 13/30. [Arithmetic constructions](arithmetic-lifts.md) | A genuinely new sequence of approximants with enough usable future shifts and an estimate on their real numerators. |
| E. Moving primes | With equal position weights, pooled conditional variance has a computable positive contribution from mesh width even for a constant target. [Variance formula](pooled-prime-variance.md) · [Transfer and actual-window tests](conditional-variation.md) | For the actual lifts, a uniform excess over the mesh floor on sufficiently late windows. |
| F. Aggregate inverse estimates | The product argument locates a sufficient bound on the mass above a fixed spike cutoff. Prime and position statistics give tests of what concentration forces on the complementary phase. [Cosine mass](fredholm-and-products.md#a-moving-parameter-still-cannot-recover-a-fixed-interior-deficit) · [Conditional variation and analytic inputs](conditional-variation.md) | An aggregate bound for the real logarithm over ordinary prefixes or all sufficiently late proportional shells. |
| G. Inducing on transitions | First returns to the middle half measure the lengths of runs. Elapsed-time sampling includes the unfinished run. [Return-time proofs and controls](projection-and-returns.md) | Bounded mean gaps between actual transitions, or an estimate on the total fraction of time spent in long runs that implies it. |

Here *D*∞ is the upper limit of the extreme half-open-interval discrepancy of the first $N$ binary shifts. For ln 2, strict discrepancy, the numerical bound 0.9999 and binary normality remain open in this work. The finite counts in the linked scripts concern their stated windows. Even a proof of strict discrepancy would still leave all-word frequencies to determine.

## An external comparison on the actual real orbit

Mira Cult's pinned result for the Erdős–Borwein constant supplies a hypothesis missing for ln 2. For every fixed word and 7/12 < *a* ≤ 1, there is a positive lower proportion throughout windows beginning immediately after digit *N*, for all large *N* and all lengths between *N*ᵃ and *N*. Taking the word 01 gives genuine transitions. Using a second-half window in each prefix gives positive ordinary lower transition density, hence strict binary discrepancy. More precisely, let *c* be Mira’s lower proportion for 01. The increase of the radial deficit over a window of length *H* is at least *cH* − 4. Subtract the two uniform radial comparisons and count one unit of cosine escape at each 01 transition. The fixed-parameter product deficit accumulated on the same window is at least *qcH*/2, where *q* = 2*s*/(1 + *s*)² for fixed product parameter 0 < *s* < 1. These are paper deductions for the actual Erdős–Borwein orbit using Mira’s external word estimate. The constants in this comparison give no stated bound of 0.9999. A limiting word law remains open. The public repository head checked during this phase was `357d26a23fbbee5c900098938744ab732b84d03a`. [Pinned theorem](https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/README.md) · [Independent source audit](../phase13/reviews/erdos-local-limit.md)

## Reproduction

Run `bash scripts/verify.sh` for Lean, the axiom audit, the declaration directory, archive statement checks, the repository tests and kernel replay. Run the following from the repository root for the Phase 15 experiments.

~~~sh
python3 -B scripts/phase15_fredholm.py
python3 -B scripts/phase15_pooled_primes.py
python3 -B scripts/phase15_affine.py
python3 -B scripts/phase15_arithmetic.py
python3 -B scripts/phase15_taylor.py
python3 -B scripts/phase15_variation.py --full
python3 -B scripts/phase15_projection.py
~~~

The Fredholm and affine lemmas are kernel-verified. The diagonal counterexample, fixed-parameter product estimates and pooled variance formula have paper proofs. The moving-prime power savings use external exponential-sum theorems. [Independent review and verification](review.md)
