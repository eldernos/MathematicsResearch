# Disjunctive but Nonnormal Multiplicative Lambert Series

**Authors:** Christopher Anderson (Independent Researcher)

**Version:** 1.0 (preprint draft), 25 November 2026

**Categories:** math.NT (primary)

**Keywords:** disjunctive numbers; normal numbers; Lambert series; binary expansion; discrepancy; multiplicative functions; sums of two squares; Selberg sieve; transcendence; Lean 4

**MSC2020:** 11K16 (primary); 11N36, 11N37, 11J81, 11N25, 11K38 (secondary)

## Abstract

Let c be a nonnegative integer-valued multiplicative function with c(pᵉ) ≤ e+1, equal to 2 on a set S of primes of reciprocal-sum density δ ∈ (0,1) that contains a full reduced residue class, and equal to 0 at the other primes not dividing a fixed modulus. Examples are c = χ∗1 for a nonprincipal real Dirichlet character χ (δ = 1/2; for χ₄ this is r₂(n)/4) and the analogous function supported on primes p ≡ 1 (mod 5) (δ = 1/4). We study the binary expansion of L = Σ c(n)2⁻ⁿ = Σ (c∗μ)(m)/(2ᵐ−1). For every fixed a > 7/12, every fixed binary word containing a one occurs between constant multiples of H/(log N)^{1−δ} times among the shifts in [N, N+H), uniformly for N^a ≤ H ≤ N, and the all-zero word occurs H − Θ(H/(log N)^{1−δ}) times. Hence L is irrational and disjunctive in base two, while the digit one has frequency zero. The extreme discrepancy satisfies 1 − D_N(L) ≍ (log log N)/(log N)^{1−δ}. Consequently translation by L changes the discrepancy of any real number by at most this amount, with equality at 0. For odd characters, L is transcendental by a theorem of Hamieh and Murty, which we extend to imprimitive characters. The proofs combine Shiu's Brun–Titchmarsh theorem for multiplicative functions, a planted-prime construction with a Selberg upper-bound sieve, and the short-interval prime number theorem of Perelli, Pintz and Salerno. The finite discrepancy transfer inequalities are verified in Lean 4.

## Source and verification

- Manuscript source, verification map and novelty ledger: `papers/06-multiplicative-lambert/` in https://github.com/eldernos/MathematicsResearch (pin this link to the release commit at integration).
- Lean declarations (pinned to commit e4809cf561573aef588e6ffc491a35cdb79fd9ec):
  - [`one_sub_discrepancy_le_one_bits`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L98)
  - [`one_sub_discrepancy_ge_of_separated_mass`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L123)
  - [`upper_freq_le_one_bits`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L77)
  - [`one_sub_discrepancy_ge_transition`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L28)
  - [`arrival_sum`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L41)
  - [`nonneg_one_bit_count_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L166)
  - [`sharp_translation_isGreatest`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386)
- Finite certificate: [`scripts/phase17_multiplicative_lambert.py`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_multiplicative_lambert.py) (`python -B scripts/phase17_multiplicative_lambert.py`).

## Verification scope

Lean checks only finite statements valid for every real number. These are the two discrepancy-gap transfer inequalities used for Theorem B, the transition inequality, the finite source-reindexing identity, the one-bit Markov inequality, and the sharp translation identity (a result of the companion manuscript *Synthetic Arithmetic Expansions and Prescribed Discrepancy*). The word-count theorem, the discrepancy order, and the transcendence theorem are written proofs. They rely on external theorems of Shiu (1980, Thm 1), Perelli–Pintz–Salerno (1985, Theorem p. 2), Montgomery–Vaughan (1973, Thm 2) and Hamieh–Murty (2016, Thms 1.1 and 3.1). The numerical digit statistics are finite certificates and carry no asymptotic information. Human specialist review is outstanding.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
