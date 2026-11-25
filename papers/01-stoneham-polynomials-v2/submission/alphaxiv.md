# Polynomial Images of Stoneham Numbers

**Christopher Anderson**, Independent Researcher

**Category** — math.NT. **MSC2020** — 11K16 (primary), 11J81 and 11A63 (secondary).

**Keywords** — Stoneham numbers, normal numbers, uniform distribution, discrepancy, p-adic valuation, Lean 4.

## Abstract

For coprime integers b ≥ 2 and c ≥ 2 let α(b,c) = Σ c^(−j) b^(−c^j), summed over j ≥ 1. Mira Cult’s public, unrefereed notes S08 (2026, Theorem 1.1 and Corollaries 1.2–1.3) show that for c > 2 every nonconstant rational polynomial in α(b,c) is normal in base b and that the distinct powers of α(b,c) are jointly normal. We give a complete kernel-verified Lean 4 proof of this ordinary case; its arithmetic step is an inclusion–exclusion argument showing that the leading prefix denominators lose only a bounded power of each prime of c. S08, Theorem 1.1(b), already gives an effective power saving with an unspecified exponent; we give the explicit scalar exponent δ_d = 1/(2(2^(d+1) − 2)) in degree d. At c = 2 and odd b ≥ 3 we determine the prefix denominators of α(b,2)^2, prove its normality, and give a denominator criterion for quadratics. A written transfer from exact finite certificates proves normality of every rational polynomial of degree 3 through 120, of degree 128, or of degree ep^r for sixteen pairs (e,p) and r ≥ 0. We determine the least 2-adic valuation of the leading mass in every degree, and show that nonvanishing of this mass on a family of open intervals of full measure would suffice in each degree. Normality of the resonant quadratic α(b,2)^2 − 2α(b,2) remains open for every odd radix b ≥ 3.

## Verification scope

Theorems A and B are Mira Cult’s S08 results in the case q = c; the contribution for them is the complete Lean proof. Lean checks the complete coprime-parameter polynomial and joint-power theorems, the parameter-two square and selected dyadic degrees. The extended dyadic degree list uses exact Python certificates and a written transfer argument. The least-order formula and the plateau test are paper proofs. The explicit discrepancy exponent rests on Lemma 6.2, a paper proof of Vandehey’s all-length estimate (preprint Theorem 5.1) in which the auxiliary divisor of equation (12) is formed from the radical of the current modulus, together with the Erdős–Turán inequality. The resonant quadratic α(b,2)^2 − 2α(b,2) and whole-shell nonvanishing of the dyadic mass in general degree remain open. The verification-map link below is relative and will be pinned to the release commit when it exists. [Polynomial source](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PeriodicPolynomialNormal.lean#L145) · [Joint source](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PeriodicPolynomialNormal.lean#L170) · [Frozen verification record](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md) · [Manuscript verification map](../VERIFICATION.md)

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
