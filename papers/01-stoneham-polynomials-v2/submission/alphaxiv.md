# Polynomial Images of Stoneham Numbers

**Christopher Anderson**, Independent Researcher

**Category** — math.NT. **MSC2020** — 11K16 (primary), 11J81 and 11A63 (secondary).

**Keywords** — Stoneham numbers, normal numbers, uniform distribution, discrepancy, p-adic valuation, Lean 4.

## Abstract

For coprime integers b ≥ 2 and c > 2, every nonconstant rational polynomial in the Stoneham number α(b,c) = Σ (1/(c^j b^(c^j))), summed over j ≥ 1, is normal in base b. Mira Cult’s October 7, 2026 public notes state a broader theorem with independent parameters. We give a kernel-verified proof for the ordinary Stoneham series. Distinct positive powers are jointly uniformly distributed. A nonintegral periodic geometric sum bounds the cancellation in rational prefixes, and Vandehey’s exponential-sum estimate gives an effective discrepancy rate. At c = 2 we determine the square’s prefix denominators. Exact finite certificates and cyclic descent prove polynomial normality in degrees 3 through 120, degree 128 and sixteen infinite families. A counting argument determines the least 2-adic valuation among the contributions of permutation orbits in every degree. Normality of the resonant quadratic α(b,2)^2 − 2α(b,2) remains open for each specified odd radix.

## Verification scope

Lean checks the complete coprime-parameter polynomial and joint-power theorems, the parameter-two square and selected dyadic degrees. The extended dyadic degree list uses exact Python certificates and a written transfer argument. The least-order formula has a paper proof. The scalar discrepancy estimate uses Vandehey’s Theorem 5.1 and the Erdős–Turán inequality. [Polynomial source](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PeriodicPolynomialNormal.lean#L145) · [Joint source](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PeriodicPolynomialNormal.lean#L170) · [Frozen verification record](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md) · [Manuscript verification map](../VERIFICATION.md)

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
