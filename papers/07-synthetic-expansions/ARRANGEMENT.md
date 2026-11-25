# Arrangement decisions for Manuscript C

Manuscript C is *Synthetic Arithmetic Expansions and Prescribed Discrepancy*, version 1.0, in `papers/07-synthetic-expansions/`. This file records which results it contains, which it leaves to other manuscripts, and why. The goal was a readable paper in which each substantive theorem appears in exactly one manuscript.

## 1. The sharp translation identity stays in this paper

**Decision.** The finite identity

$$
\sup_{x\in\mathbb R}\lvert D_N(x+z)-D_N(x)\rvert = 1-D_N(z),
$$

attained at $x=0$ (Theorem 7.1 = Theorem D), and the classification of universal numerical discrepancy preservers (Theorem 7.4) remain sections of this paper. There is **no separate translation note**, and `translation-note/` was not created.

**Reasons.**

1. *The paper uses the result itself.* The finite comparison behind the identity (Lemma 2.2) drives every quantitative proof here: the worked example (Theorem 3.1), the general rate (Theorem 4.6), the programming theorems (Section 5) and the infinite-sum estimate (Theorem 10.2). Necessity in the addition spectrum (Theorem 8.1) and its $d$-summand version (Theorem 8.3) are two applications of the identity. A split would force this paper to cite a separate note for its central tool, or to restate it, and restating it would be duplicate publication.
2. *The identity is elementary and short.* Its proof takes one paragraph once the arc lemmas are in place. The literature check (`LEDGER.md`, Theorem 7.1) identifies it as an exact reformulation in terms of classical objects: Kuiper's circular statistic (1960), Lévy's circular concentration function (1939), and Ky Fan and Lévy–Prokhorov distances to a point mass. A stand-alone note would be thin, and its novelty claim is necessarily modest. Inside this paper it has a natural role as the sharp form of the transfer step.
3. *The classification needs context from this paper.* The preserver theorem (Theorem 7.4) and its comparison with Rauzy's theorem (Remark 7.5) use the limit-set machinery of Section 6 (Lemma 6.2). They also gain from the programmed examples, for instance $D_N(1/3;2)\to2/3$.
4. *Companion citations stay simple.* The multiplicative Lambert paper (`papers/06-multiplicative-lambert/`) cites the identity as a result of this paper, so no new citation target is needed. Corollary 9.3 here states the Lambert consequence with the Lambert deficit estimate as an input from that manuscript. The deficit theorem itself stays in Paper 06.

**Coordination note for Paper 06.** Cite Theorem 7.1 (Theorem D in the introduction) of *Synthetic Arithmetic Expansions and Prescribed Discrepancy*. Corollary 9.3 here only *combines* that identity with Paper 06's two-sided deficit estimate. Paper 06 should prove its deficit estimate and may state the same combination as a remark citing Theorem 7.1. It should not reprove the identity.

## 2. Phase 19 material: what is included here and what is not

On the coordinator's instruction (owner decision), the Phase 19 results at commit `c2c9da683666b3b9368e5d4b5cb858caccf528f5` were reviewed for incorporation. Phase 19 Lean links in the paper are pinned to that commit with a local macro `\leanXIX`. When the shared `\leanat` macro is merged, the macro can be replaced mechanically.

| Phase 19 result (registry) | Placement | Reason |
| --- | --- | --- |
| Exact addition spectrum for $(x,y,x+y)$, qualitative in every radix (OP-01, Lean) | **Included**: Theorem 8.1 = Theorem E | It extends the programmed-discrepancy theme directly. Necessity is two applications of Theorem 7.1. |
| Uniform cubic rate for the addition spectrum (part of OP-02) | **Included**: Theorem 8.2 | It reuses Lemma 5.1, Proposition 5.2 and Corollary 2.5 verbatim, so the proof costs one page. |
| Algebraic independence and uniform computability of the witnesses (rest of OP-02) | Not included | It is a separate effective-construction theme. It would lengthen Section 8 without changing the spectrum. It remains in the research notes. |
| Spectrum for $d$ summands (OP-03) | **Included**: Theorem 8.3, qualitative only | Necessity follows from Theorem 7.1. Realization follows from the kernel-verified `mixtureRealizable`. The claimed rate is not included and is explicitly not claimed. |
| Finite rational linear forms, polyhedral approximation, joint box rate (OP-04, OP-18) | Not included | These involve a different technique (word flows, Hausdorff approximation, multidimensional exponential sums). A one-sentence remark records the six-form obstruction to show why triples alone do not suffice. |
| Pseudometric $1-D_N(x-y)$ (OP-05, finite part) | **Included**: Proposition 7.3 | Immediate from Theorem 7.1 and kernel-verified. It gives the identity its natural geometric statement. |
| Rational scalar ring, fixed-point lifts, integer-dilation boundary spectrum (OP-06, OP-07) | Not included | These concern multiplication, not translation. They are left for a later operations paper or the companion (see `COMPANION-ASSESSMENT.md`). |
| Exact prime-power grid with complementary modulus (OP-08) | **Included**: Lemma 2.4 | It is needed for Section 10. The Lean steps `stride_order` and `crt_period_count` are cited. |
| Normal Liouville series retaining every odd prime, $D_N=O(1/\log N)$ (OP-09) | **Included**: Theorem 10.2 = Theorem F | It completes item 8 and supersedes the Phase 18 construction on $\{3\}\cup\{\ell\equiv2\bmod3\}$ (SY-06). That construction is mentioned in one sentence as the case $c=1$. |
| Superpolynomial denominators, accelerated schedules (OP-10) | Not included | The extra sieve inputs are not needed for the main line. |
| Sparse preservers with visible product (OP-12) | Not included | It concerns products of remainders, a multiplicative question. It belongs to the companion assessment. |
| Flagship square and quadratic forms (OP-14) | **Mentioned, not claimed** (Section 11) | The proof is analytic and long, and it belongs with the nonlinear material. The paper says plainly that the square is normal, and that $(\xi,\xi^2)$ is jointly normal. It links the written proof and its independent audit at the pinned commit, says the result is not a claim of this paper, and asks for a rate. |
| Rapidly varying schedules, polynomial-normal algebras (OP-15, OP-16, OP-17) | Not included | Companion material. |
| Classical-constant results (OP-11, OP-13, OP-19 to OP-22) | Not included | These belong to the classical-denominators manuscripts. |

## 3. The Phase 18 prime-5 review claim

The Phase 19 handoff identifies an invalid prime-5 valuation argument in the Phase 18 translation and summation review. **This paper uses no prime-5 claim.**

- Theorem 10.2 uses the distinguished prime 3 with a doubled order. It bounds the loss $c=v_3(2^\tau-1)\le1+J_3$ through $v_3(\ell-1)<\log_3L$, which is a valid upper bound.
- Theorem 10.3 uses a distinguished prime $\ell_0$ against a **fixed finite** set of other primes, so its loss is bounded by a constant.
- No statement infers a lower bound on an order's valuation from a congruence of primes.

## 4. Duplicate-publication safeguards

- The normality switch, the denominator identity and the geometric grouping (SY-01, SY-02, SY-11) were not stated as theorems in any released paper (`papers/0[1-5]-*`). Paper I v1.1 contains the fixed-support short-orbit theorem, which this paper cites as Lemma 4.3 (kernel-verified) and attributes to Vandehey's Corollary 1.2 in qualitative form. It is not restated as a new result.
- Mira Cult's joint-normality note and Captain Sude's sum results concern Stoneham series $\sum p^{-sj}b^{-p^j}$. Theorems 10.3–10.4 concern different series, and the ledger credits the overlap.
- Paper 06 owns the Lambert deficit estimate. This paper owns the translation identity.
