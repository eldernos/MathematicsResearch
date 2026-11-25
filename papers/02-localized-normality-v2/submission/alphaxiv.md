# Normality of localized logarithms and polylogarithms on finite prime supports

**Version 2.0** (supersedes version 1.1, `papers/02-localized-normality`). Preprint draft.

## Abstract

Let M(S) be the set of positive integers whose prime factors lie in a finite set S of primes. For integers b >= 2 and s >= 1 we show that the series sum over m in M(S) of m^{-s} b^{-m} has base-b interval discrepancy tending to 0 if some prime of S does not divide b, and to 1 otherwise. For a nonzero rational polynomial P, the series with numerator P(m) is normal exactly when P(X)/X^s has a pole at zero and such a prime exists. The proof shows that persistent cancellation at an off-radix prime has measure zero, using multiplicative differences on a logarithmic circle and separation of the remaining thresholds. The shifts of these series at distinct positive orders on one fixed support, with rational numerators nonzero at zero, are jointly equidistributed in the unit cube. For retained subsets of the support we bound the discrepancy by the missed density of retained prime-power windows and classify normality on a single prime-power axis. For a fixed prime, finitely many orders and a positive tolerance, a depth at which all finite certificates fall below the tolerance is computable. The principal classifications and the joint theorem are verified by the Lean kernel. Priority statements are provisional, and no human expert has reviewed the written proofs.

## Authors

Christopher Anderson, Independent Researcher.

## Categories and keywords

Primary: math.NT (Number Theory). Cross-list: math.DS, cs.LO.

Keywords: normal numbers, localized logarithm, polylogarithm, Stoneham numbers, smooth numbers, interval discrepancy, joint equidistribution, Lean 4.

MSC2020: 11K16 (primary); 11J71, 11A63 (secondary).

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.

## Source and verification links

All Lean links are pinned to commit `e4809cf561573aef588e6ffc491a35cdb79fd9ec`.

- Repository at the pinned commit: <https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec>
- Lean sources: <https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker>
- Manuscript directory (`paper.tex`, `paper.pdf`, `VERIFICATION.md`, `LEDGER.md`, `CHANGES.md`, `Statements.lean`, `Check.lean`): `papers/02-localized-normality-v2/` in the release that contains this version. The new files are not present at the pinned Lean commit; the owner should add the release link here.
- Principal declarations: [`unsigned_discrepancy_limit`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/UnsignedNormality.lean#L198), [`full_rational_normal_iff`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/FullPolynomialNormality.lean#L15), [`joint_full_polynomial_orders`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/LocalizedJoint.lean#L85), [`axis_normal_iff`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/MaskAxis.lean#L138), [`certificateModulus_spec`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/LocalizedCertificateModulus.lean#L44).

## Verification scope

The statements labelled "Kernel-verified" in the paper (Theorems A, B, C, D(ii),(iii), E, F, 4.1 and A.1, among others) are the types of Lean 4 declarations that passed kernel replay and an axiom audit permitting only `propext`, `Classical.choice` and `Quot.sound`; the unsigned classification, the polynomial classification and the joint theorem for rational numerators are additionally stated in definitions from mathlib alone and proved from the library. The Lean development checks series values and radix orbits, not the literature comparisons. Theorem D(i), Lemma 3.1, Corollary 6.1, Propositions 7.2 and 10.1, the outline of Theorem F and all priority statements are written arguments or comparisons that have been checked only by AI models. The Fourier-cancellation input of the written transfer lemma is a published theorem of Vandehey; the library contains an independent formalization. Comparisons with public work of Mira, Mira Cult and Captain Sude are against pinned versions that their authors describe as unreviewed.
