# Denominator Growth and Rational Shadowing for Classical Constants

**Authors field:** [Confirm author entry] Christopher Anderson · Independent Researcher\
**Public contact:** [Repository issue tracker](https://github.com/eldernos/MathematicsResearch/issues)\
**Version:** 2.0, preprint draft\
**Categories:** math.NT (primary), math.CA (secondary)\
**Keywords:** reduced denominators, dyadic logarithms, Gaussian logarithms, Legendre polynomials, irrationality exponent, rational approximation, geometric rays\
**MSC2020:** 11J04 (primary), 11J82, 11K16, 11N05, 33C45

## Abstract

For fixed finite rational identities for log 2 built from balanced algebraic traces, truncation at a common binary scale gives reduced denominators whose least two exponential rates are 5/12 and 13/30. In the real dyadic class the minimum is 1/2. We reduce all balanced traces to real and Gaussian sources, use a Lean certificate for a finite comparison of prime bands, quantify robustness under varying coefficients, and exhibit identities of larger height below the floor. These floors concern truncation without rounding. A second part rounds polynomial moments on the grid (1/lcm(1,...,D))Z and so realizes the nearest grid point to 2^N log 2 and 2^N pi by rational arithmetic. The resulting windows, the number of binary digits after position N that the rational model reproduces, have length at least log_2 of the grid denominator up to o(1). This is the benchmark available for every real number, so these windows are not compared with the floors. An irrationality-exponent inequality limits windows. A third part proves a prime-dependent completion delay for positive dyadic groupings of the logarithm series, gives exact geometric-ray decompositions, rules out sparse functional identities of a specified kind, and treats Taylor prefixes: the exact one-prime completion index, the average denominator loss, a superpolynomial period bound, and limiting discrepancies of individual horizontal rows. Lower denominator exponents and longer rational windows do not establish limiting digit distribution. The paper proves neither normality nor a limiting discrepancy bound below one for log 2, pi, e, sqrt(2) or the golden ratio.

## Source and verification

- [Revised manuscript source](../paper.tex) and [theorem verification map](../VERIFICATION.md)
- [Balanced trace and kernel source at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase16/nonflat-approximants.md)
- [All-shift extension to π at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/phase17-transfer.md)
- [Finite prime-band certificate at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/AdaptiveLogarithmBounds.lean#L1158)
- [Kernel replay, axiom audit and exact computations at the pinned checkpoint](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md)
- [Taylor grouping and arithmetic source](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/notes/phase19/classical.md)
- [Horizontal cycle and period verification](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/notes/phase19/verification.md)

Lean verifies the finite comparison on the first 71 prime-band cells and specified arithmetic steps. The all-cutoff classification and passage from finite mass to optimal reduced-denominator rates use written proofs and published prime-divisor and prime-number theorems. The linear height thresholds are a finite certificate computed in Python. The all-shift Legendre models and their rounding test have paper proofs, with exact rational computations at selected shifts. They are nearest-grid roundings, which exist for every real number, and are not compared with the floors. The geometric-ray theorem is a paper proof that uses one Lean-checked modular estimate. The exact completion, mean loss, period, signed transform and horizontal row claims in §9 have written proofs. Human specialist review is outstanding.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
