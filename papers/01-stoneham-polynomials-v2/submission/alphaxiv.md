# Polynomial Images of Stoneham Numbers

**Christopher Anderson**, Independent Researcher

**Category** — math.NT. **MSC2020** — 11K16 (primary), 11J81 and 11A63 (secondary).

**Keywords** — Stoneham numbers, normal numbers, uniform distribution, discrepancy, p-adic valuation, Lean 4.

## Abstract

Mira Cult’s S08 (Theorem 1.1 and Corollaries 1.2–1.3) proves polynomial normality and joint distribution for Stoneham series with a common good prime. We give a complete kernel-verified proof for the ordinary series α(b,c) = Σ c^(−j)b^(−c^j), summed over j ≥ 1, for coprime b ≥ 2 and c > 2. Every nonconstant rational polynomial in α(b,c) is normal in base b, and distinct positive powers are jointly normal. Inclusion–exclusion bounds cancellation in the leading denominator. S08 Theorem 1.1(b) already gives an effective power saving. We specify a scalar discrepancy exponent in each degree. At c = 2 we determine the square’s prefix denominators and give a normality criterion for quadratics. A written transfer from exact finite certificates proves normality for all rational polynomials of degrees 3 through 120, degree 128 and degrees ep^r for sixteen pairs (e,p) and r ≥ 0. A counting argument determines the least valuation of a permutation-orbit contribution in every degree. Normality of α(b,2)^2 − 2α(b,2) remains open for each specified odd radix.

## Verification scope

Lean checks the complete coprime-parameter polynomial and joint-power theorems, the parameter-two square and selected dyadic degrees. The extended dyadic degree list uses exact Python certificates and a written transfer argument. The least-order formula has a paper proof. The scalar discrepancy estimate uses a written proof of Vandehey’s estimate with a support-dependent auxiliary divisor and the Erdős–Turán inequality. [Polynomial source](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PeriodicPolynomialNormal.lean#L145) · [Joint source](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PeriodicPolynomialNormal.lean#L170) · [Frozen verification record](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md) · [Manuscript verification map](../VERIFICATION.md)

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
