# Arrangement decisions for Manuscript C

Manuscript C is *Synthetic Arithmetic Expansions and Prescribed Discrepancy*, version 1.0 (unreleased), in `papers/07-synthetic-expansions/`. This file records which results it contains, which it leaves to other manuscripts, and why. The rule is that each substantive theorem appears as a theorem in exactly one manuscript.

## 1. The split of 25 November 2026 (owner decision)

**Decision.** The arithmetic of extreme discrepancy is separated into a focused standalone manuscript,

> **H.** *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations*, version 1.0, `papers/10-discrepancy-arithmetic/`.

Manuscript C cites H and no longer proves any of the moved results. This reverses the earlier arrangement (recorded in the previous version of this file), under which the translation identity stayed in C and no separate note was written.

**Reasons.**

1. *One home per theorem, with two citing manuscripts.* The sharp translation identity is used by C (once, in Proposition 8.5) and by the multiplicative Lambert manuscript (`papers/06-multiplicative-lambert`, Corollary 1.2 and Theorem 8.1 there), which until now cited it as a theorem of C. A separate manuscript gives both a neutral citation target and keeps C focused on its own subject, synthetic expansions.
2. *The moved material forms a coherent paper.* The identity, the classification of universal preservers, the discrepancy pseudometric, the exact addition spectrum (kernel-verified in Phase 19), the $d$-summand polytope, the rational-scalar ring $\mathbb Z[1/b]$, the residue test and the dilation boundary spectrum all concern the behaviour of $D_N$ under arithmetic operations. Together they make a 16-page paper with its own novelty questions (Kuiper, Lévy, Ky Fan, Prokhorov, Rauzy, Bergelson–Downarowicz), which were awkward to discuss inside C.
3. *C gains room for the Phase 19 nonlinear theorem.* The quadratic-image theorem (normality of $\xi^2$ and of every total-degree-two polynomial in distinct valuation orders) is a natural continuation of C's denominator method, and its full written proof needs about six pages.

**What moved from C to H** (old C numbering → H numbering):

| Old C | Result | New home |
| --- | --- | --- |
| Thm D, 7.1 | Sharp translation identity | H, Theorem A = Theorem 3.1 (kernel-verified) |
| 7.2 | Transfer corollary | H, Corollary 3.2 (kernel-verified) |
| 7.3 | Discrepancy pseudometric | H, Proposition 4.1 (kernel-verified), with the concentration and Ky Fan comparison as new Proposition 4.2 |
| 7.4, Remark 7.5 | Universal numerical preservers; comparison with Rauzy | H, Theorem 3.3, Remark 3.4 (new proof of (i)⇒(vi) without connectedness of limit sets) |
| Thm E, 8.1–8.3 | Addition spectrum, cubic rate, $d$ summands, six forms | H, Theorems 5.1, 5.3, 5.5, Proposition 5.6; computability and algebraic independence added as Theorem 5.4 |
| 9.1, 9.2 | Quadratic and factorial sparse remainders | H, Theorem 3.5, Proposition 3.6 |
| 9.3 | Lambert remainder corollary | **Dropped**: it is Corollary 1.2 of manuscript A (multiplicative Lambert); H only mentions it |

New in H (Phase 19, not previously in any manuscript): the asymptotic distance and kernel $K_b$ (Proposition 4.3), the rational-scalar ring $\mathbb Z[1/b]$ (Theorem 4.5), the residue-density test (Proposition 4.6), the finite dilation bounds and the boundary spectrum $[1/m_0,1]$ (Proposition 6.1, Theorem 6.2), the Moser–de Bruijn product example (Proposition 6.3) and the anchored and two-dimensional counterexamples (Remark 6.4).

**What C keeps or adds:**

- Kept: the normality switch and exact denominators (Theorems A, 4.2, 4.5), the rates (Theorem B), prescribed discrepancy, pairs and limit sets (Theorem C), the all-odd-prime normal Liouville series and its companions (Theorem E = Theorems 8.2–8.4), the exact prime-power grid (Lemma 2.4).
- Added: the all-prefix criterion as an explicit proposition (Proposition 4.4; previously only the written outline of the switch), the **quadratic-image theorem** (Theorem D = Theorem 7.1, Corollary 7.2), with its full proof (Section 7).
- Quoted once, not reproved: the sharp translation identity, as Theorem 2.6, citing H by title, same release, Theorem 3.1, with the Lean links.
- Proposition 8.5 (consecutive tails) now uses the quoted identity and holds in every base (previously stated in base 2 via the preserver classification).

**Shared elementary lemmas.** The arc lemma and the finite comparison lemma (C Lemmas 2.1, 2.2 = H Lemmas 2.1, 2.2) appear with short proofs in both manuscripts. They are standard tools, not results claimed by either paper, and each manuscript needs them to be readable on its own. H uses C's positive state recurrence (C Lemma 5.1) and prime-power orbit count (C Corollary 2.5) by citation as H Lemmas 2.5 and 2.4; H reproves the latter in three lines from the Lean full-period count and states the former with its Lean links only.

## 2. Coordination note for manuscript A (multiplicative Lambert)

Manuscript A currently cites the translation identity as a result of C (`SyntheticCompanion` in its bibliography). It should instead cite H. Suggested citation string:

> C. Anderson, *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations*, version 1.0, preprint, same release (manuscripts-v2.0.0), Theorem 3.1 (Sharp translation identity; Theorem A in the introduction). Lean: `NormalityChecker.SharpTranslation.sharp_translation_isGreatest`, https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386 (with `sharp_translation`, L343).

Suggested BibTeX key `DiscrepancyArithmetic`, directory `papers/10-discrepancy-arithmetic`. Manuscript A should keep its own Corollary 1.2 (translation by $L$, with its deficit order); H mentions that corollary without restating it, and C no longer contains a Lambert corollary. This worktree did not modify manuscript A.

## 3. Phase 19 material: what is included where

| Phase 19 result (registry) | Placement | Reason |
| --- | --- | --- |
| Exact addition spectrum, qualitative in every radix (OP-01, Lean) | H, Theorem 5.1 | Arithmetic of discrepancy. |
| Uniform cubic rate; computability; algebraically independent witnesses (OP-02) | H, Theorems 5.3, 5.4 | Written proofs, labelled Lean-supported (the coefficient recurrence is kernel-verified). |
| Spectrum for $d$ summands (OP-03) | H, Theorem 5.5, qualitative only | Realization by `mixtureRealizable`; the rate is not claimed. |
| Finite rational forms, polyhedral approximation; joint box rate (OP-04, OP-18) | Not included; six-form obstruction in H, Prop. 5.6 | Different techniques; listed as further work in H. |
| Pseudometric $1-D_N(x-y)$ (OP-05) | H, Propositions 4.1, 4.3 | Kernel-verified finite part. |
| Rational scalar ring, residue test (OP-06) | H, Theorem 4.5, Proposition 4.6 | Rational operations. |
| Integer-dilation boundary spectrum (OP-07) | H, Proposition 6.1, Theorem 6.2 | The inverse dilation estimate is not included. |
| Exact prime-power grid (OP-08) | C, Lemma 2.4 | Needed for Section 8; Lean steps `stride_order` and `crt_period_count` cited. |
| Normal Liouville series retaining every odd prime (OP-09) | C, Theorem 8.2 = Theorem E | Unchanged. |
| Superpolynomial denominators, accelerated schedules (OP-10) | Not included | Not needed for the main line. |
| Sparse preservers with visible product (OP-12) | H, Proposition 6.3 (product example only) | The sharp missing-digit rates are not claimed. |
| Flagship square and quadratic forms in distinct orders (OP-14) | **C, Theorem 7.1 and Corollary 7.2** (paper proof, full proof written) | Owner decision; supersedes the Phase 18 bound $2.94\cdot10^{-10}$ (SY-20), now a historical remark. |
| Rapidly varying schedules, polynomial-normal algebras (OP-15, OP-16, OP-17) | Not included | Assessed in `COMPANION-ASSESSMENT.md`. |
| Classical-constant results (OP-11, OP-13, OP-19 to OP-22) | Not included | Belong to the classical-denominators manuscripts. |

## 4. The withdrawn prime-5 grid inference

The Phase 19 handoff and GitHub issue 1 identify an invalid prime-5 valuation argument in the Phase 18 translation and summation review (now corrected in `notes/phase18/reviews/translation-summation.md`). **Manuscript C uses no prime-5 claim.**

- Theorem 8.2 uses the distinguished prime 3 with a doubled order. It bounds the loss $c=v_3(2^\tau-1)\le1+J_3$ through $v_3(\ell-1)<\log_3L$, which is a valid upper bound; no lower bound on an order valuation is inferred from a congruence.
- Theorem 8.3 uses a distinguished prime $\ell_0$ against a fixed finite set of other primes, so its loss is bounded by a constant.
- The remark after Theorem 8.2 on the support $\{3\}\cup\{\ell\equiv2\bmod3\}$ uses $3\nmid\mathrm{ord}_Q(2)$, which holds because $3\nmid\ell-1$ for those primes; it is an upper-bound argument.

## 5. Duplicate-publication safeguards

- The normality switch, the denominator identity and the geometric grouping (SY-01, SY-02, SY-11) are not theorems of any released paper (`papers/0[1-5]-*`). Paper I v1.1 contains the fixed-support short-orbit theorem, which C cites as Lemma 4.3 (kernel-verified) and attributes to Vandehey's Corollary 1.2 in qualitative form.
- The quadratic-image theorem is not stated in any other manuscript. Paper I v1.1 concerns polynomial images of standard Stoneham numbers, a different family.
- Mira Cult's joint-normality note and Captain Sude's sum results concern Stoneham series $\sum p^{-sj}b^{-p^j}$. Theorems 8.3–8.4 concern different series, and the ledger credits the overlap.
- Manuscript A owns the Lambert deficit estimate and its translation corollary. Manuscript H owns the translation identity. Manuscript C owns the synthetic constructions and the quadratic-image theorem.
