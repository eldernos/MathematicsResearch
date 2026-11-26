# Normality of localized logarithms and polylogarithms on finite prime supports

**Version 2.0** (supersedes version 1.1, `papers/02-localized-normality`). Preprint draft.

## Abstract

Let M(S) be the set of positive integers whose prime factors lie in a finite set S of primes, b >= 2 a radix and J the set of primes of S not dividing b. For s >= 1 the series sum over m in M(S) of m^{-s} b^{-m} has base-b interval discrepancy tending to 0 if J is nonempty and to 1 otherwise. For nonzero rational P, the series with numerator P(m) over all of M(S) is normal exactly when P(X)/X^s has a pole at zero and J is nonempty. Work of Captain Sude, Mira and Mira Cult covers order one for supports prime to the radix, binary supports containing 3 and two generators, and all orders for supports prime to the radix; their arguments extend further. The remaining cases use a measure-zero statement on persistent cancellation. If J is nonempty, the shifts of the series at distinct positive orders on one support, with rational numerators nonzero at zero, are jointly equidistributed in the unit cube. For p in J, a polynomial with a pole at zero and a retained subset of M(S), the discrepancy is bounded by the missed density of retained windows [p^k, 2p^k); on S = {p} normality holds exactly when infinitely many p^k are retained. For p in J, finitely many orders and a tolerance, a depth with every finite certificate below the tolerance is computable. Lean verifies the classifications and the joint theorem; written proofs and priority statements are provisional, without expert review.

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
- Manuscript directory (`paper.tex`, `paper.pdf`, `VERIFICATION.md`, `LEDGER.md`, `CHANGES.md`, `Statements.lean`, `Check.lean`, `AuditDeclarations.lean`): <https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/02-localized-normality-v2> (release `manuscripts-v2.0.0`). The directory is not present at the pinned Lean commit.
- Principal declarations: [`unsigned_discrepancy_limit`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/UnsignedNormality.lean#L198), [`full_rational_normal_iff`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/FullPolynomialNormality.lean#L15), [`joint_full_polynomial_orders`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/LocalizedJoint.lean#L85), [`axis_normal_iff`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/MaskAxis.lean#L138), [`certificateModulus_spec`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/LocalizedCertificateModulus.lean#L44).

## Verification scope

Labels are those of the paper. **Kernel-verified** means that one Lean declaration, in the library or in `Check.lean`, states the assertion, and that it passed kernel replay and an axiom audit permitting only `propext`, `Classical.choice` and `Quot.sound`. This applies to Theorem A; Theorem B(i) (`full_rational_normal_iff`), B(ii) (`rational_boundary`) and B(iii) (`integer_mask_maximal`); Theorem C(i), (ii) and (iii) (`joint_full_polynomial_orders`, `joint_axis_orders_iff`, `joint_late_twos_orders`); Theorem F (`discrepancy_rate` for `Localized.value`, with `series_normal` and `value_eq_series` for the displayed double series); Theorem 4.1; Theorem 11.1 (one declaration for each of its three assertions); Proposition 6.3; and Example 5.1. Example 11.2 is kernel-verified for four stated facts only, and its remaining arithmetic is a finite certificate (`check_order_two.py`). The mathlib-only restatements in `Check.lean` cover only the limit statement and the normality for J nonempty in Theorem A, the equivalence B(i), and C(i); the other statements are Lean statements in the library's own definitions. These files are run from the release that contains the manuscript directory, against a library build compatible with the pin; the bare checkpoint does not contain them. **Lean-supported paper proofs**, in which named Lean steps are combined by written steps, are Theorem D(i) (counting step), the two consequences in D(ii) and D(iii) (after the cancellation identity `masked_cancel`), the final inequality of Theorem E, Lemma 3.1 (valuation step), Corollary 6.1 and Remark 6.2. Lemma 2.1, Proposition 7.2 and Proposition 10.1 are paper proofs; the Fourier-cancellation input of Lemma 2.1 is a published theorem of Vandehey, with an independent formalization in the library. The outline of Theorem F is a description of the structure of a kernel-verified proof. The Lean development checks series values and radix orbits, not literature comparisons. Captain Sude's and Mira's public work, and Mira Cult's note, cover order one for supports prime to the radix, binary supports containing 3 and two generators, and all orders for supports prime to the radix, and their arguments extend to further cases listed in Section 1.2 of the paper; these comparisons are against pinned versions that their authors describe as unreviewed, and have been checked only by AI models.

## Licence

CC BY 4.0 (select it in the alphaXiv form). Copyright 2026 Christopher Anderson. The licence covers this manuscript and its designated accompanying files; code in the repository is MIT. See `LICENSE-MANUSCRIPTS.md` in the repository.
