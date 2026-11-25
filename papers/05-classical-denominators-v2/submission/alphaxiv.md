# Denominator Growth and Rational Shadowing for Classical Constants

**Authors field:** [Confirm author entry] Christopher Anderson · Independent Researcher\
**Public contact:** [Repository issue tracker](https://github.com/eldernos/MathematicsResearch/issues)\
**Version:** 2.0, preprint draft\
**Categories:** math.NT (primary), math.CA (secondary)\
**Keywords:** reduced denominators, dyadic logarithms, Gaussian logarithms, Legendre polynomials, irrationality exponent, rational approximation, geometric rays\
**MSC2020:** 11J04 (primary), 11J82, 11K16, 11N05, 33C45

## Abstract

Fixed finite rational identities for log 2 built from balanced algebraic traces reduce, at every cutoff, to real and Gaussian logarithm sources. The least two exponential rates for the reduced denominators are 5/12 and 13/30, with a unique prefix function at each rate. The real dyadic minimum is 1/2. A Lean certificate checks a finite prime-band comparison used in the proof. We establish sufficient coefficient-height thresholds for varying identities and construct large-height identities that fall below the denominator floor with growing error. Chebyshev and Legendre kernels give smaller denominator-rate upper bounds. Legendre moment rounding yields linear rational shadowing windows at all sufficiently large binary shifts of log 2 and pi, with an explicit test for agreement with nearest-grid rounding. An irrationality-exponent inequality bounds the length of a window in terms of the shift and the reduced denominator. Positive Taylor groupings have a prime-dependent completion delay. We give exact geometric-ray decompositions and a differential-algebra obstruction for sparse generating functions. We determine the exact one-prime completion index, bound the mean Taylor denominator loss and prove superpolynomial growth of rational periods, and compute the limiting discrepancy of selected horizontal Taylor rows. Lower denominator exponents and longer rational shadowing windows do not establish limiting digit distribution. We obtain neither normality nor limiting binary discrepancy below one for log 2, pi, e, the square root of 2, or the golden ratio.

## Source and verification

- [Revised manuscript source](../paper.tex) and [theorem verification map](../VERIFICATION.md)
- [Balanced trace and kernel source at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase16/nonflat-approximants.md)
- [All-shift extension to π at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/phase17-transfer.md)
- [Finite prime-band certificate at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/AdaptiveLogarithmBounds.lean#L1158)
- [Kernel replay, axiom audit and exact computations at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md)
- [Taylor grouping and arithmetic source](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/notes/phase19/classical.md)
- [Horizontal cycle and period verification](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/notes/phase19/verification.md)

Lean verifies the first 71 half-cell comparison and specified arithmetic steps. The all-cutoff classification and passage from finite mass to optimal reduced-denominator rates use written proofs and published prime-divisor and prime-number theorems. The all-shift Legendre bounds and their rounding test have paper proofs, with exact rational computations at selected shifts. The exact completion, mean loss, period, signed transform and horizontal row claims in §9 have written proofs. Human specialist review is outstanding.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
