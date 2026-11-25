# Disjunctive but Nonnormal Multiplicative Lambert Series

**Authors:** Christopher Anderson (Independent Researcher)

**Version:** 1.0 (preprint draft), 25 November 2026

**Categories:** math.NT (primary)

**Keywords:** disjunctive numbers; normal numbers; Lambert series; binary expansion; discrepancy; multiplicative functions; sums of two squares; Selberg sieve; transcendence; Lean 4

**MSC2020:** 11K16 (primary); 11N36, 11N37, 11J81, 11N25, 11K38 (secondary)

## Abstract

Let c be a nonnegative integer-valued multiplicative function with c(pᵉ) ≤ e+1. Suppose that c(p) = 2 for the primes of a set S that contains a reduced residue class and satisfies Σ_{p≤x, p∈S} 1/p = δ log log x + O(1) with 0 < δ < 1, that c(p) = 0 at the other primes not dividing a fixed modulus, and that c(p₀^{2u}) = 2u+1 for one p₀ ∈ S and all u ≥ 0. Examples are c = χ∗1 for a nonprincipal real Dirichlet character χ (δ = 1/2; for χ₄ this is r₂(n)/4). We study the binary expansion of L = Σ c(n)2⁻ⁿ = Σ (c∗μ)(m)/(2ᵐ−1). For every fixed a > 7/12, each fixed word containing a one occurs between constant multiples of H/(log N)^{1−δ} times among the shifts in [N, N+H), uniformly for N^a ≤ H ≤ N, and the all-zero word occurs H − Θ(H/(log N)^{1−δ}) times. Hence L is disjunctive in base two, but the digit one has frequency zero. For 1 + 4L_{χ₄} = θ₃(1/2)², Bailey, Borwein, Crandall and Pomerance had already proved that the number of ones among the first M digits is asymptotic to C₀M/√(log M); the new content is the short windows, all words, the discrepancy order and the general class. The extreme discrepancy satisfies 1 − D_N(L) ≍ (log log N)/(log N)^{1−δ}, which by a companion paper is the exact worst-case effect of translation by L on discrepancy. For odd characters, L is transcendental by a theorem of Hamieh and Murty, extended here to imprimitive characters. Finite discrepancy inequalities are verified in Lean 4.

## Source and verification

- Manuscript source, verification map and novelty ledger: `papers/06-multiplicative-lambert/` in https://github.com/eldernos/MathematicsResearch (pin this link to the release commit at integration).
- Lean declarations (pinned to commit e4809cf561573aef588e6ffc491a35cdb79fd9ec):
  - [`one_sub_discrepancy_le_one_bits`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L98)
  - [`one_sub_discrepancy_ge_of_separated_mass`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L123)
  - [`upper_freq_le_one_bits`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L77)
  - [`one_sub_discrepancy_ge_transition`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L28)
  - [`arrival_sum`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L41)
  - [`nonneg_one_bit_count_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L166)
  - [`lambert_head_eq_taylor`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L21)
  - [`sharp_translation_isGreatest`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386)
- Finite certificate: [`scripts/phase17_multiplicative_lambert.py`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_multiplicative_lambert.py) (`python -B scripts/phase17_multiplicative_lambert.py`).
- Companion manuscript for the translation identity: C. Anderson, *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations*, version 1.0, same release (`papers/10-discrepancy-arithmetic/`), Theorem 3.1.

## Verification scope

Lean checks only finite statements valid for every real number. These are the two discrepancy-gap transfer inequalities used for Theorem B, the transition inequality, the finite source-reindexing identity, the one-bit Markov inequality, the finite Lambert–Taylor head identity, and the sharp translation identity (Theorem 3.1 of the companion manuscript *The Arithmetic of Extreme Discrepancy*). The word-count theorem, the discrepancy order, and the transcendence theorem are written proofs. They rely on external theorems of Shiu (1980, Thm 1), Perelli–Pintz–Salerno (1985, Theorem p. 2), Montgomery–Vaughan (1973, Thm 2) and Hamieh–Murty (2016, Thms 1.1 and 3.1). The extension of the lower bounds to a > 0.53 (Theorem 10.3) additionally uses Kumchev (2002, main Theorem), checked against the author's posted text. The one-bit asymptotic for θ₃(1/2)² is due to Bailey, Borwein, Crandall and Pomerance (2004, Theorem 9.4 and the remark after it). The numerical digit statistics are finite certificates and carry no asymptotic information. Human specialist review is outstanding; the manuscript has had AI model review only, which is not independent human peer review.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
