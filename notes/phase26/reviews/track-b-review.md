# Phase 26 Track B — Independent Cross-Provider Referee Review (`B1`–`B7`)

**Audited material.**
- [`notes/phase26/arithmetic-hankel-determinants.md`](../arithmetic-hankel-determinants.md) (737 lines; "the note").
- [`scripts/phase26_hankel_ln2.py`](../../../scripts/phase26_hankel_ln2.py) (1,182 lines; "the script").
- Cross-references used only to check the note's citations: `CC-03`, `CC-05`, `GF-28` and `GF-47` in [`docs/results.md`](../../../docs/results.md), [`notes/phase25/classical-constants-frontier.md`](../../phase25/classical-constants-frontier.md) (`GF-47` Lemma 3.3, Theorem 3.6, Theorem 4.3, Open Question 4), and `NormalityChecker/LogTwo.lean` (`logPrefix`).

**Reviewer.** Claude `claude-opus-5-5`, acting as the review sub-agent on branch `research/phase-26-arithmetic-amplification`, 2026-11-28.

**Method.** The review was read-only, and this report is the only file written in the repository. Nothing was committed and WSL was not used. Python ran directly on Windows (`python -B`). I re-derived every proof by hand. I then wrote a separate verification script from scratch in a temporary scratch directory outside the repository. It uses its own plain-fraction Gaussian elimination, its own mod-*q* rank routine, its own expansion of the shifted Jacobi polynomials, and an integer-scaled ln 2 enclosure. It ran **358,608 independent assertions, all passing**. The audited script was imported only once, to rebuild the `GF-47` countermodel blocks for the size measurement in §6.

> **Cross-model review is not independent human peer review.** This report is a machine reading by a language model. It does not replace refereeing by human specialists in Padé approximation, orthogonal polynomials or Diophantine approximation. Nothing in it may be used to change the status of any benchmark constant (`BC-01`…`BC-50`) or of any arithmetic-family benchmark.

---

## Verdict: **REVISE** (targeted text revision; no theorem needs to be withdrawn)

| Severity | Count | Nature |
|---|---|---|
| Critical | 0 | — |
| Major | 2 | **M1:** the B5/B6 "reset-ratio barrier" uses the wrong threshold. It compares block ratios with the *activation* ratio ρ\* = 2.5897, but the ratio at which B1+B3+B4 could actually *exclude* a countermodel block is about 6.18. **M2:** several limitation claims carry a "Paper proof" label but are unproven or heuristic. |
| Minor | 14 | One wrong numerical value, one prior-art value I could not confirm, a missing script check, a missing one-line lemma, an off-by-one index, Lean-route details, hypotheses that need stating, and label or wording slips. |

The audit tried to invalidate every step. **None of the positive mathematics failed:**
- **B1** holds exactly as stated, including *p* = 2, *r* = 1, *r* = *p*, and arbitrary entries in ℤ<sub>(*p*)</sub> (rational and non-Hankel).
- **B2:** Lemma 2.2 and Theorem 2.1 hold.
- **B3:** Theorems 3.1–3.4 hold, including the exact Cauchy–Block-Rank integer identity. It holds for every *M* and *r*, not only at prime-centered windows, and the bound in Theorem 3.4(3) holds as well.
- **B4:** the Uvarov–Christoffel reduction (Theorem 4.3) has **no** sign, index or normalization error. All headline constants are correct: α\* = 0.442847, μ<sub>2</sub> = 6.178813, run constant 5.178813, transition constant 0.3806, and α<sub>C</sub> = 0.542211.
- **B5:** the survival statement (Theorem 5.1(1)) is correct.
- **B7:** all three B1-type valuation theorems are correct.

The two Major items concern **interpretation and evidence labels, not the mathematics**. Both are fixable in a few paragraphs.

---

## 1. Script run (mandate item 1)

`python -B scripts/phase26_hankel_ln2.py` exits **0** in about 1.2 s:

```
ALL CHECKS PASSED: 67645 total assertions (67367 exact, 278 rational enclosure).
```

The per-section counts match §11 of the note: 284 B1 matrices, 924 LCM pairs, 51 B2 matrices (17 of them strict), 877 + 839 rank windows (133 drop events), 6,272 Cauchy–block triples, 100 global identities (52 strict), 84 / 70 / 153 B4 cases, 36 + 61 enclosures, 18 + 1 B5 windows, and 30 / 53 / 15 B7 matrices.

**Floating point in exact sections.** I grepped every line before `print_finite_asymptotics` (line 1017) for `math.log`, `sqrt`, `exp`, `lgamma`, `float(` and decimal literals. The only hits are inside strings and docstrings. Each `[exact]` check uses `int` or `Fraction`. Each `[encl]` check uses a certified rational ln 2 enclosure, `ln2_enclosure(180)` with tail bound 1/((*K*+1)2<sup>*K*</sup>), which is correct, or an exact rational enclosure of *e*. The `[float]`/`[finite]` block is isolated and gates nothing. **No floating-point assertion occurs in an `[exact]` or `[encl]` section.**

---

## 2. B1 — v<sub>*p*</sub>(det *H*) = −*r* (mandate item 2)

**Proof.** The proof is correct. For 0 ≤ *i*, *j* < *r*, every index *n* = *M* + *i* + *j* lies in [*p* − *r* + 1, *p* + *r* − 1] ⊂ [1, 2*p* − 1]. Also *n* = *p* exactly when *i* + *j* = *r* − 1, and *k* = *p* is the only multiple of *p* in [1, *n*] when *n* ≥ *p*. Reversing the columns gives a lower-triangular matrix mod *p*. The reversal permutation has sign (−1)<sup>⌊*r*/2⌋</sup> = (−1)<sup>*r*(*r*−1)/2</sup>; I checked the parity identity for every *r* mod 4.

**Case *p* = 2.** This case is genuinely fine. Here *r* ∈ {1, 2}, and for *r* = 2 we have *M* = 1 with *s*<sub>1</sub> = 1, *s*<sub>2</sub> = 5/2 and *s*<sub>3</sub> = 16/3. Reducing 2*H* entrywise:
- 2(*s*<sub>1</sub> − *m*) ≡ 0;
- 2(*s*<sub>2</sub> − *m*) = 5 − 2*m* ≡ 1;
- 2(*s*<sub>3</sub> − *m*) = 32/3 − 2*m* ≡ 0, since 32/3 has an even numerator and an odd denominator.

So 2*H* mod 2 = [[0, 1], [1, 0]]. The (1, 1) entry 2<sup>1</sup> ≡ 0 does not matter, because that entry lies below the anti-diagonal. Signs are invisible mod 2. Hence v<sub>2</sub>(det *H*) = −2. The proof's parenthetical remark on *p* = 2 is accurate.

**Independent tests.** I ran **246 random matrices** with *p* ∈ {2, 3, 5, 7, 29, 31, 37}, all 1 ≤ *r* ≤ min(*p*, 8), and *r* = *p* for *p* ≤ 7. Each entry *m*<sub>*i*,*j*</sub> was an independent random rational with denominator prime to *p*, so the shift is neither integral nor Hankel. In every case det *H* ≠ 0, v<sub>*p*</sub> = −*r*, and *p*<sup>*r*</sup> det *H* ≡ (−1)<sup>*r*(*r*−1)/2</sup> (mod *p*).

**§1.2 and the Lean definition.** The warning in §1.2 (amplified pole ≠ numerator gain) is correct and important. `NormalityChecker.logPrefix` in `LogTwo.lean` is exactly *s*<sub>0</sub> = 0, *s*<sub>*n*+1</sub> = 2*s*<sub>*n*</sub> + 1/(*n*+1). Lean-route details are in m6.

---

## 3. B2 — row and double-difference denominators (mandate item 3)

**Theorem 2.1(1).** Correct. Row 0 has denominators dividing *L*<sub>*p*</sub>, because den(*s*<sub>*n*</sub>) divides *L*<sub>*n*</sub> and *M* + *j* ≤ *p*. Row *i* has denominators dividing *D*<sub>*i*</sub>.

**Theorem 2.1(2).** Correct. In *H*<sup>(2)</sup>, row *i* uses the integers {*M* + *i*, …, *M* + *i* + *r* − 1}. The multilinear split has denominators dividing *Q*<sub>*M*</sub>·∏*D*<sub>*i*</sub> and lcm(*M*+1, …, *p*)·∏*D*<sub>*i*</sub>, so *D*<sub>double</sub> divides *D*<sub>row</sub>. For *r* = 1 the formula reduces to *Q*<sub>*p*</sub>, as it should.

**Lemma 2.2.** Both divisibilities and both proofs are correct. In the first, *q*<sup>v<sub>*q*</sub>(*m*)</sup> divides *m* − *m*<sub>0</sub>, and the binomial coefficient C(*r* − 1, *k*<sub>1</sub>) is an integer. In the second, the excess is the sum over *e* with *c*(*q*<sup>*e*</sup>) ≥ 1 of (*c*(*q*<sup>*e*</sup>) − 1), and *c*(*q*<sup>*e*</sup>) ≥ ⌊*r*/*q*<sup>*e*</sup>⌋ whenever *q*<sup>*e*</sup> ≤ *r*. Re-checked on 39 × 17 extra pairs (*a*, *r*) with *r* < 40.

**Corollary 2.3(1).** The *O*(*p*) claim is correct. With *r* = *c*·√(*p*/log *p*), *r*<sup>2</sup> log(*p*/*r*) = (*c*<sup>2</sup>/2)·*p*·(1 + log log *p*/log *p* + …), while κ<sub>*D*</sub>*r*<sup>2</sup> = *O*(*p*/log *p*). So log *D*<sub>row</sub> = (1 + *c*<sup>2</sup>/2 + o(1))·*p*. The `[finite]` table shows 1.75–1.81 against the predicted 1.50. That gap is explained by the slow o(1) terms, about 0.25 at *p* ≈ 2000 (m11).

**Corollary 2.3(2) at *r* = *p*.** Correct: lcm(*i*+1, …, *i*+*p*) = *L*<sub>*i*+*p*</sub>, so the total is (3/2 + o(1))*p*<sup>2</sup>. The excess (3/2 − 2 ln 2) = 0.113706 is correct. The claim "for every α ∈ (0, 1]" is **not proved** (part of M2).

---

## 4. B3 — rank-sensitive lemma and exact Cauchy–Block-Rank identity (mandate item 4)

**Theorem 3.1.**
- (1)–(2): correct. Change of basis by *U*, *V* in GL<sub>*r*</sub>(ℤ<sub>(*q*)</sub>) preserves *q*<sup>*k*</sup>ℤ<sub>(*q*)</sub><sup>*r*</sup>. The quotient picks out exactly the indices with *v*<sub>*i*</sub> ≤ *k*. Then v<sub>*q*</sub>(det *B*) is at least the sum of min(*v*<sub>*i*</sub>, *e*), which is at least *er* minus the sum of the *s*<sub>*k*</sub>.
- (3): correct. *y*<sub>1</sub> = *Bx* − *q*<sup>*k*+1</sup>(*q*<sup>*j*−1</sup>*A*<sub><*j*</sub>)*x* is automatically *q*-integral, so *A*<sub>≥*j*</sub> need not be integral. Saturation gives *L*<sub>*k*</sub> ∩ *q*ℤ<sup>*r*</sup> = *qL*<sub>*k*</sub>. The additive corollary charges each term to exactly *e*<sub>*a*</sub> levels.

**Theorem 3.2.** Every subcase was re-derived.
- The global decomposition *H* = *s*<sub>*M*</sub>·*vv*<sup>T</sup> + Σ<sub>*t*</sub> *E*<sup>(*t*)</sup>/(*M*+*t*) − (*m*), and the identity *E*<sup>(*t*)</sup> = 2<sup>−*t*</sup>(*vv*<sup>T</sup> − *F*<sup>(*t*)</sup>), are correct.
- **Case *t* ≥ *r*.** Row 0 and column 0 of *E*<sup>(*t*)</sup> vanish, the anti-triangular block has rank 2*r* − 1 − *t*, and the pivot α at (0, 0) adds 1.
- **Case *t* ≤ *r* − 1.** The *vv*<sup>T</sup> coefficient is (α + β2<sup>−*t*</sup>) = γ2<sup>−*t*</sup>, and γ = α2<sup>*t*</sup> + β = *q·s*<sub>*mq*</sub> mod *q*. Row *t* of *F*<sup>(*t*)</sup> vanishes, so the pivot (*t*, *t*) = γ2<sup>*t*</sup> adds 1.
- **Part (3).** If *m* ≥ 2, uniqueness of the multiple forces *M* ≥ (*m* − 1)*q*. With `GF-47` Lemma 3.3, α = 0 holds exactly when *m* = 1 or *m* − 1 ∈ *D*(*q*), and γ = 0 exactly when *m* ∈ *D*(*q*). The *p* = 5 example (centre 10, 2 ∈ *D*(5) because *A*<sub>2</sub> = 5, *r* ≤ 5) is correct.
- **Part (4).** Correct, with ranks *t* and 2*r* − 1 − *t*.

I ran **1,008 independent windows** with *q* ∈ {29, 31, 41, 43, 47, 53}, *r* ≤ 8 and random integer shifts. In 168 of them ρ<sub>maj</sub> = 0. Each matched *s*(*t*) = min(*t*, 2*r* − 1 − *t*) + 1<sub>ρ<sub>maj</sub>≠0</sub> exactly.

**Theorem 3.3.** Correct, **including *q* = 2**. The row operation by *L* is unimodular over ℤ, and nothing in the proof uses that *q* is odd. Every entry of *A*<sub><*j*</sub> has valuation at least −(*j* − 1). The nonzero pattern of *A*<sub>≥*j*</sub> splits into blocks indexed by the residue class *c* mod *q*<sup>*j*</sup>, giving the bound Σ<sub>*c*</sub> min(*m*<sub>*c*</sub>, *n*<sub>*c*</sub>). Row 0 adds at most 1.

**Theorem 3.4 (the main B3 claim).**
- **(1)** The proof is correct. Write *r* = *ad* + *b*. The left side is *ad* + |*S*<sub>*n*</sub> ∩ *S*<sub>*m*</sub>|, and each *u* matches at most one *v* because *b* < *d*. On the right, Hermite's identity gives *b* for each full block of *d* consecutive *k*. Also 2Σ⌊*k*/*d*⌋ = *a*(*a* − 1)*d* + 2*ab*. Legendre's formula then gives v<sub>*q*</sub>(1/det *C*(*M* − 1, *r*)).
- **(2)** The proof is correct. Here *c*<sub>0</sub> = *d* − 1 − *u*<sub>1</sub>, and *c*<sub>0</sub> < *u*<sub>2</sub> holds exactly when *u*<sub>1</sub> + *u*<sub>2</sub> ≥ *d*. The split on whether *d* divides *r* is necessary: when *d* | *r*, δ = 1 while the floor expression is 0. Summing over *j* gives v<sub>*q*</sub>(*r*) + v<sub>*q*</sub>(C(*p*<sub>eff</sub>, *r*)).
- **(3)** The algebra det *C*(*M*, *r*)/det *C*(*M* − 1, *r*) = (*p*!)<sup>2</sup>/((*p* − *r*)!(*p* + *r*)!) is correct. Multiplying by *L*<sub>*p*</sub>(*r* − 1)!(*p* − *r*)!/*p*! gives *L*<sub>*p*</sub>/(*r*·C(*p* + *r*, *r*)).
- **(4)** Correct. Φ<sub>B3</sub>(1) = 1 − 2 ln 2 = −0.386294, and the root is α<sub>C</sub> = 0.542211 (bisection, 200 steps).

**Independent scratch tests of Theorem 3.4.**
- (1) and the δ formula of (2): **174,000 triples**, all *M* ≤ 60, *r* ≤ 40 and *d* ≤ *M* + 2*r* + 1, including non-prime *p*<sub>eff</sub>.
- The global integer identity ∏<sub>*q*</sub> *q*<sup>Σ<sub>*j*</sub> rk(*M*, *r*, *q*<sup>*j*</sup>)</sup> = 1/(*r*·C(*p*<sub>eff</sub>, *r*)·det *C*(*M* − 1, *r*)): **1,276 pairs** (*M* ≤ 44, *r* ≤ 29), with any *p*<sub>eff</sub>.
- (3), both the divisibility *D*<sub>B3</sub> | *L*<sub>*p*</sub>/(*r*·C(*p*, *r*)·det *C*(*M* − 1, *r*)) and the bound *D*<sub>B3</sub>·det *C*(*M*, *r*) ≤ *L*<sub>*p*</sub>/(*r*·C(*p* + *r*, *r*)): **1,593 pairs**, every prime *p* ≤ 113 and every 1 ≤ *r* ≤ *p*, using the generic *e*<sub>0</sub>.
- den(det *H*) | *D*<sub>B3</sub> (actual *e*<sub>0</sub>) | *D*<sub>row</sub>: **333 random integer Hankel windows** (*p* ≤ 41, *r* ≤ 11). The product over all primes includes *q* = 2.

---

## 5. B4 — Uvarov–Christoffel reduction and μ<sub>2</sub> (mandate item 5)

### Theorem 4.3: re-derivation

1. **Column step.** 2*T*<sub>*n*−1</sub> − *T*<sub>*n*</sub> = ∫*t*<sup>*n*−1</sup> d*t* = 1/*n*, and the ε-part cancels because 2·2<sup>*i*+*j*−1</sup> − 2<sup>*i*+*j*</sup> = 0. So the operation col<sub>*j*</sub> ← 2col<sub>*j*−1</sub> − col<sub>*j*</sub>, applied right to left, produces [**t** − ε*v*, **c**<sub>0</sub>, …, **c**<sub>*r*−2</sub>]. Each step negates the determinant, for a total factor (−1)<sup>*r*−1</sup>.
2. **Triangular structure.** Here *U* is lower-triangular, because φ<sub>*k*</sub> has degree *k*. *UC* = *U*<sup>−T</sup> is upper-triangular with diagonal 1/ℓ<sub>*k*</sub>. So row *r* − 1 of *U*·[**c**<sub>0</sub>, …, **c**<sub>*r*−2</sub>] is zero, and the complementary minor is upper-triangular with determinant equal to the product of 1/ℓ<sub>*k*</sub> for *k* < *r* − 1.
3. **Row expansion.** Expanding along row *r* − 1 gives the sign (−1)<sup>*r*−1</sup>, which cancels the column-step sign. With det *U* = (det *C*)<sup>−1/2</sup>, this gives det(*K* − ε*vv*<sup>T</sup>) = det *C*·ℓ<sub>*r*−1</sub>·(*U*(**t** − ε*v*))<sub>*r*−1</sub>.
4. **The last entry.** (*U*(**t** − ε*v*))<sub>*r*−1</sub> = √(2*r* + *M* − 1)·(*I* − ε·*P*<sub>*r*−1</sub>(3)), using φ<sub>*k*</sub>(2) = √(2*k* + *M* + 1)·*P*<sub>*k*</sub>(3).
5. **Normalization.** The leading coefficient of *P*<sub>*k*</sub><sup>(0,*M*)</sup>(2*t* − 1) is C(*M* + 2*k*, *k*). So ℓ<sub>*r*−1</sub>·√(2*r* + *M* − 1) = (*M* + 2*r* − 1)·C(*M* + 2*r* − 2, *r* − 1) = *r*·C(*M* + 2*r* − 1, *r*).
6. **Rodrigues formula.** I re-derived it from the standard Jacobi form with α = 0 and β = *M*: *t*<sup>*M*</sup>*P*<sub>*n*</sub> = (1/*n*!)·*D*<sup>*n*</sup>[*t*<sup>*M*+*n*</sup>(*t* − 1)<sup>*n*</sup>]. The norm is ∫*t*<sup>*M*</sup>*P*<sub>*n*</sub><sup>2</sup> = 1/(2*n* + *M* + 1).
7. **Integration by parts.** *D*<sup>*k*</sup>(2 − *t*)<sup>−1</sup> = *k*!(2 − *t*)<sup>−*k*−1</sup>, and the boundary terms vanish because the zeros at *t* = 0 and *t* = 1 have orders *M* + *r* − 1 and *r* − 1. This gives *I*<sub>*M*,*r*−1</sub> = ∫*t*<sup>*M*+*r*−1</sup>(1 − *t*)<sup>*r*−1</sup>(2 − *t*)<sup>−*r*</sup> d*t*.
8. **Parts (2)–(4).** Matching the linear coefficient in ε gives *v*<sup>T</sup>*K*<sup>−1</sup>*v* = *P*/*I*. The sign (−1)<sup>*r*</sup> in (3) agrees with Proposition 4.1(3). For (4), *c*<sub>*r*−1</sub> = C(*p* + *r* − 1, *r* − 1) has p-adic valuation 1 − 1 − 0 = 0 for *r* ≤ *p*, so v<sub>*p*</sub>(Λ) = −1.

**Verdict on 4.3: no sign, index or normalization error.**

**Independent Q[*X*] test.** I wrote *K*(*X*) = 2<sup>*M*</sup>*X*·*vv*<sup>T</sup> − *S* with *S* = (*s*<sub>*M*+*i*+*j*</sub>), so det *K*(*X*) is affine in *X*. I computed both coefficients exactly, using my own elimination and my own expansion of the Jacobi coefficients. Both match *r*·C(*M* + 2*r* − 1, *r*)·det *C*·(2<sup>*M*</sup>*P*<sub>3</sub>*X* − Σ*c*<sub>*j*</sub>*s*<sub>*M*+*j*</sub>) for **98 pairs** (*M* ≤ 13, *r* ≤ 7). The range includes non-prime-centered *M* and *M* = 0.

I also checked a consequence the note does not state: *v*<sup>T</sup>·adj(*K*(*X*))·*v* = det *K* − det(*K* − *vv*<sup>T</sup>) equals *r*·C(*M* + 2*r* − 1, *r*)·det *C*·*P*<sub>*r*−1</sub>(3), **independently of *X***. This holds at *X* = 0, 1 and 7/3. It gives an independent confirmation of Theorem 4.3(2).

**Lemma 4.4.**
- The saddle equation *t*<sup>2</sup> − (3 + α)*t* + 2 = 0 is correct. Substituting *t* = 1 − *x* gives *x*<sup>2</sup> + (1 + α)*x* − α = 0, and the root satisfies *x*\* ∈ (0, α). The generating-function bound with *y* = (1 − *x*\*)/*x*\* reproduces e<sup>*g*·*p*</sup> exactly.
- Checked with exact enclosures (ln 2 to 2<sup>−4000</sup>) on 35 cases, *p* ≤ 199 with *r* ∈ {1, 2, *p*/4, *p*/2, 2*p*/3, *p*}: *I* > 0, *I* ≤ e<sup>−*g*(α<sub>0</sub>)·*p*</sup> and *P*<sub>3</sub> ≤ e<sup>*g*(α<sub>0</sub>)·*p*</sup>. A Simpson quadrature of the integral form matches the exact *I* to 10<sup>−6</sup> relative error (`[float]` sanity check only).

**Theorem 4.5.** The chain |ε| ≥ (1 − *L*<sub>*p*</sub>*I*)/(*L*<sub>*p*</sub>*P*) is correct; it can also be read directly off |Λ| ≥ 1/*L*<sub>*p*</sub> with Λ = *I* − ε*P*. It needs only the **upper** bounds of Lemma 4.4, which are fully proved. The quantity (1 + *g*(α))/(1 − α) is increasing in α, so α\* (where *g* = 1) is optimal for this method. Recomputed independently:

| Quantity | Note | Independent |
|---|---|---|
| α\* (root of *g* = 1) | 0.442847 | 0.442847 |
| ρ\* = (1 + α\*)/(1 − α\*) | 2.5897 | 2.589679 |
| *c*<sub>run</sub> = 2/((1 − α\*) ln 2) | 5.178813 | 5.178813 |
| μ<sub>2</sub><sup>Hankel</sup> | 6.178813 | 6.178813 |
| 1/log<sub>2</sub> μ<sub>2</sub> vs `CC-05` 1/log<sub>2</sub> 34 | 0.3806 vs 0.1966 | 0.3806 vs 0.1966 |
| Loewner variant: α<sub>C</sub>, μ<sub>2</sub> | 0.542211, 8.258694 | 0.542211, 8.258694 |
| Alladi–Robinson 4 log(1+√2)/(2 log(1+√2) − 1) | 4.622101 | 4.622101 |
| *r*/*M* ratio ln 2/(2 log(1+√2) − 1) | 0.9088 | 0.9088 |

**Prior art.**
- Alladi–Robinson 4.6221 and Rhin 4.0765 agree with that same Numdam list. Rukhadze/Hata 3.8914 agrees with Zudilin's survey.
- Marcovecchio's 3.57455391 is confirmed by secondary citations.
- The note's **Chudnovsky value 4.269 could not be confirmed**. The published list in the Numdam source cited below (*Ann. Inst. Fourier*, item aif.1322) gives Chudnovsky's bound as 4.1344 (m2).
- The comparison is correctly framed. The dyadic exponent satisfies μ<sub>2</sub> ≤ μ, so the classical values do give *c*<sub>run</sub> = μ − 1. The note candidly says its μ<sub>2</sub> is **weaker** than Alladi–Robinson and Marcovecchio.
- §4.5 item 1 is honest and correct: the *r* × *r* Hankel apparatus reduces exactly to the one-dimensional asymmetric linear form Λ<sub>*M*,*r*</sub>. Its only gain over classical Padé is the one-shot nonvanishing v<sub>*p*</sub>(Λ) = −1.

**Propositions 4.1–4.2.**
- The bounds on *T*<sub>*n*</sub>, the rounding thresholds and the run-to-ε link (*L* ≥ 2*r* − 1) are correct.
- Loewner comparison, the Cauchy determinant, the *r* = o(*M*) and linear-regime asymptotics, and the Hadamard–Jacobi bound are correct. In particular (1 + *t*)(2 − *t*) = 2 + *t*(1 − *t*), and the diagonal Jacobi coefficient is *M*<sup>2</sup>/((2*k* + *M*)(2*k* + *M* + 2)).
- The Barnes-*G* bookkeeping has an off-by-one (m5).

---

## 6. B5 and B6 — the `GF-47` adversarial test and the ledger (mandate item 6)

**Theorem 5.1(1), survival: correct.**
- For *r* ≥ 2, *p* > *M* ≥ *n*<sub>*i*</sub>, so *p* does not divide *M*<sub>*i*</sub>. Then *H̃* = *s* − (*m̃* − 2<sup>*n*−*n*<sub>*i*</sub></sup>δ<sub>*i*</sub>) has a *p*-integral shift, and B1 applies directly.
- `GF-47` Theorem 3.6(1) gives den(*s̃*<sub>*n*</sub>) = *Q*<sub>*n*</sub>, so *e*<sub>0</sub>(*q*) is unchanged, and the in-block recurrence keeps rows *i* ≥ 1 of *LH̃* identical. Hence Theorem 3.3 applies verbatim.
- *s̃*<sub>*n*</sub> = 2<sup>*n*</sup>*y*<sub>*i*</sub> − *T*<sub>*n*</sub> with the **same** *T*<sub>*n*</sub>, so Theorem 4.3, an identity in ε, applies verbatim.
- The `[exact]` reconstruction of blocks [240, 360) and [360, 540) and the reset-crossing certificate at (359, 3) are sound. The second block has 31 top-band primes; the 30 of them below 357 are amplified.
- The divisibility *D*<sub>B3</sub> | *D*<sub>row</sub> is used but never proved (m4). It is true, and I verified it.

**Theorem 5.1(2), arithmetic.** α<sub>max</sub>(ρ) = (ρ − 1)/(ρ + 1) gives 0.2000, 0.2651 and 0.4191 for ρ = 1.5, 1 + 1/(2 ln 2) and 1 + 1/ln 2. These and the stated hierarchy 1.500 < 1.7213 < 2.4427 < 2.5897 are numerically correct. However, **1 − *g*(0.20) = 0.4301, not 0.4460** (m1).

**Ledger (§6).** I checked all 24 cells against §§1–5. Every quantitative entry is consistent with the proved statements, except the threshold interpretation in rows 7–8 (M1), the word "strictly" in row 6 and the word "needed" in row 3 (both m12).

### M1 (Major). The reset-ratio "barrier" uses the activation threshold, not the exclusion threshold

**The note's framing.** §5, the summary row for B5, ledger rows 7–8 and Open Question 3 present the following as the operative barrier:

```text
1.500 < 1.7213 < 2.4427 < 2.5897
```

It reads as a near miss, ρ<sub>info</sub> = 2.4427 against ρ\* = 2.5897. It suggests that a reset-free block of ratio above 2.5897 would be in danger from B1+B3+B4.

**Why that is the wrong threshold.** ρ\* is only the ratio at which the inequality becomes *nontrivial*. To *exclude* a countermodel block, the lower bound on |ε̃| must exceed the smallness the block forces:

1. **What the block forces.** Inside a block with clean rounding, *s̃*<sub>*n*</sub> − *m̃*<sub>*n*</sub> = −*T*<sub>*n*</sub> + 2<sup>*n*−*M*</sup>ε̃ exactly. Since |*s̃*<sub>*n*</sub> − *m̃*<sub>*n*</sub>| ≤ 1/2 throughout, |ε̃| ≤ 2<sup>−(*n*<sub>*i*+1</sub> − 1 − *M*)</sup>.
2. **What the method gives.** B1+B3+B4, valid verbatim in the block by Theorem 5.1(1), gives at best |ε̃| ≥ 2<sup>−(*c*<sub>run</sub>(α) + o(1))·*M*</sup>, with *c*<sub>run</sub>(α) ≥ 5.1788.
3. **The resulting threshold.** A contradiction therefore needs (*n*<sub>*i*+1</sub> − *n*<sub>*i*</sub>)/*n*<sub>*i*</sub> > 5.1788 + o(1) (take *M* = *n*<sub>*i*</sub>). So:

```text
rho_excl = min over alpha >= alpha* of max( (1+alpha)/(1-alpha), 1 + c_run(alpha) ) = 6.1802   (computed)
```

The minimizer is α\*, where the window constraint 2.59 is slack. Equivalently, a reset carrying at most log<sub>2</sub> *L*<sub>*n*<sub>*i*</sub></sub> ≈ 1.44·*n*<sub>*i*</sub> bits evades the method by **1.44 versus 5.18 bits per index**. This is not the near miss 2.4427 versus 2.5897.

**Measured on the note's own countermodel.** I rebuilt the blocks with the script's `build_gf47_block` and enclosed ln 2 to 2<sup>−3000</sup>. At *M* = 240 in block [240, 360), log<sub>2</sub>|ε̃| ≤ −165.7, which is about log<sub>2</sub>(1/*M*<sub>0</sub>) = −164.5. At *M* = 360 in block [360, 540), the value is −250.3, against log<sub>2</sub>(1/*M*<sub>1</sub>) = −249.3. The Hankel threshold 2<sup>−5.18*M*</sup> would be about 2<sup>−1243</sup> and 2<sup>−1864</sup>, so the margin is enormous.

**Required fix.**
- Keep Theorem 5.1(2) as a statement about *activation*; its literal text is correct.
- Add the exclusion criterion ρ − 1 > *c*<sub>run</sub> + o(1), that is, ρ<sub>excl</sub> ≈ 6.18, and state the bits comparison 1/ln 2 versus *c*<sub>run</sub>.
- Reword the B5 summary, ledger row 7 ("ratio ρ < 2.5897") and ledger row 8 ("ρ < 2.5897").
- Rewrite Open Question 3, which presently treats ρ\* as the line the Hankel test could cross.

The corrected statement is a **stronger** limitation theorem: no `GF-47`-type reset carrying at most about 1.44*n* bits can be excluded by B1+B3+B4 at any block ratio the information bound allows.

---

## 7. B7 — π, *e* and ζ(3) (mandate item 7)

**π (Theorem 7.1(1)).** Correct.
- I recomputed by brute force, for **every prime 3 ≤ *p* ≤ 600**, the first two indices *k* at which *p* divides one of 8*k* + 1, 2*k* + 1, 8*k* + 5 or 4*k* + 3. They agree with the table for *k*<sub>0</sub>, *k*<sub>1</sub> and *r*<sub>max</sub> in all four classes mod 8.
- The pole residues *u*<sub>*p*</sub> ∈ {4, −1, −1/2} follow from *r*<sub>*k*</sub> = 4/(8*k*+1) − 1/(2(2*k*+1)) − 1/(8*k*+5) − 1/(2(4*k*+3)).
- *P*<sub>π</sub> = (1 − *t*)(4 + 4*t* + 4*t*<sup>2</sup> + 2*t*<sup>3</sup> + *t*<sup>4</sup>) > 0 on [0, 1), so *K*<sup>(π)</sup> is positive definite.
- The transferred rank law in 7.1(2) is asserted without proof (m8).

***e* (Theorem 7.2(1)).** Correct. The Wilson computation (*k*!/*p*<sup>*m*</sup> ≡ (−1)<sup>*m*</sup>*m*!·(*k* − *mp*)!) applies whenever *K* < (*m* + 1)*p* ≤ *p*<sup>2</sup>. That makes *p* > √*K* automatic, so `GF-47` Theorem 4.3 applies as the note says.
- I checked 60 additional windows with random integer shifts, *p* ∈ {7, 11, 13}, bands *m* ≤ **5** and *r* ≤ 4. All have v<sub>*p*</sub> = −*mr*.
- The rank counterexample at *q* = 7, *M* = 5, *r* = 5 is certified by the script.
- *R*<sub>1</sub>*R*<sub>3</sub> − *R*<sub>2</sub><sup>2</sup> = −0.010573 < 0, so *K*<sup>(*e*)</sup> is not positive definite.

**ζ(3) (Theorem 7.3(1)).** Correct.
- **Coefficients.** Σ<sub>*k*<14</sub> 4096<sup>−*k*</sup>*c*<sub>*k*</sub>/672 agrees with ζ(3) to **51 digits**, which confirms all 23 values *a*<sub>*j*</sub>. Every unit residue mod 24 has *a*<sub>*j*</sub> = ±2<sup>*e*</sup>.
- **Window structure.** 24*k* + *j* < 2*p* on [0, *k*<sub>1</sub> − 1]. Hermite's identity gives *k*<sub>1</sub> − *k*<sub>0</sub> = ⌊(*p* + 12)/24⌋ ≤ *k*<sub>0</sub> + 1.
- **Extra windows.** 22 additional windows with *p* ∈ {97, 193, 241, 337} all give v<sub>*p*</sub> = −3*r*.
- **Sign of the weight polynomial.** *Q*(1/2) = −9403717869/4194304 exactly and *Q*(1) = 8190. On a 1001-point grid, *Q* < 0 for *t* ∈ [0.186, 0.789], that is, *u* = *t*<sup>24</sup> ∈ [3·10<sup>−18</sup>, 3.4·10<sup>−3</sup>].
- **Tail representation.** *T*<sub>*n*</sub> = ½∫*t*<sup>24*n*+24</sup>(ln *t*)<sup>2</sup>*Q*(*t*)/(4096 − *t*<sup>24</sup>) d*t* is correct.
- The indefiniteness claim needs a stated dependence on *M* (m9).

**Linear balances (`[float]`).** Recomputed: ln 2 gives −0.7627, π gives +1.87313, ζ(3) gives +62.2961, and 2 log(64 + √4095) = 9.7039. These are heuristics for the symmetric *M* = 0 integral (part of M2).

### M2 (Major). Limitation claims labelled "Paper proof" that are unproven or heuristic

The repository requires evidence labels to be kept strictly separate. The following assertions sit inside items labelled *Paper proof* but have no proof:

1. **Corollary 2.3(2), "for every α ∈ (0, 1]".** The claim is that log *D*<sub>row</sub>(*p*, α*p*) + log det *C* = +Θ(*p*<sup>2</sup>) > 0 for all α. It is proved only at α = 1. For small α the claim needs κ<sub>*D*</sub> > 3/2, but the note only shows 1 ≤ κ<sub>*D*</sub> ≤ 2, which cannot decide the sign.

   Numerically, at *p* = 1999, (total − ψ(*p*))/*r*<sup>2</sup> is about +0.067 to +0.075 for 0.1 ≤ α ≤ 0.8. That is consistent with γ − ½ = 0.0772: on average κ<sub>*D*</sub> tends to 1 + γ, by Σ Λ(*n*){*x*/*n*} ~ (1 − γ)*x*. But the value is **−0.08 at α = 0.02**, so at that size only the ψ(*p*) term keeps the total positive.

   *Fix:* prove κ<sub>*D*</sub> tends to 1 + γ > 3/2 (the averaging argument above), or downgrade the α < 1 part to a finite measurement or conjecture. This item is not load-bearing, because B3 supersedes B2.
2. **Theorem 7.1(3), quadratic failure for π.** "Grows as a multi-progression multiple of 2 ln 2·*r*<sup>2</sup>" comes with no derivation.
3. **Theorem 7.1(3) and 7.3(3), linear balances.** They are computed for the **symmetric *M* = 0** integral, not for the prime-centered asymmetric construction the theorems are about. They are heuristic obstructions to a natural analogue, not theorems about the method.
4. **Theorem 7.2(2), fourth bullet.** "Rank ≤ 1 and det = 0" holds only for clean (geometric) shifts *m*. With arbitrary integer shifts the determinant need not vanish.

*Fix:* label these items *heuristic obstruction / non-rigorous remark*, or supply proofs. None of them affects a positive result.

---

## 8. Minor findings

| # | Location | Finding and recommended fix |
|---|---|---|
| m1 | Thm 5.1(2) | 1 − *g*(0.20) = **0.4301** (*g*(0.2) = 0.569881). The value 0.4460 is wrong. The conclusion (> 0) is unaffected. |
| m2 | §4.5 table | Chudnovsky's "μ ≤ 4.269 (*c*<sub>run</sub> 3.269)" is not confirmed. The Numdam list (aif.1322) gives Chudnovsky's bound as **4.1344**. Correct it, or cite the exact source of 4.269. |
| m3 | §8 table | It claims a "50-digit numerical sanity check" of Broadhurst's 23 coefficients, but the companion script contains none (no `672` or ζ(3) value anywhere). The identity itself is right (51 digits, checked independently). Add the check or drop the claim. |
| m4 | Thm 5.1(1), ledger | *D*<sub>B3</sub> \| *D*<sub>row</sub> is used without proof. One-line proof: v<sub>*q*</sub>(*D*<sub>B3</sub>) ≤ *e*<sub>0</sub> + Σ<sub>*j*</sub> rk(*M*, *r*, *q*<sup>*j*</sup>) ≤ ⌊log<sub>*q*</sub> *p*⌋ + Σ<sub>*j*</sub> #{*i* ≥ 1 : row *i* contains a multiple of *q*<sup>*j*</sup>} = v<sub>*q*</sub>(*D*<sub>row</sub>), because rk ≤ Σ over classes with *n*<sub>*c*</sub> ≥ 1 of *m*<sub>*c*</sub>. Verified for every *p* ≤ 113 and *r* ≤ 40. |
| m5 | Prop 4.2(2) proof | The Barnes-*G* arguments are off by one. Since *M* + *r* = *p* + 1, the expression is 2 log *G*(*r*+1) + 2 log *G*(*p*+2) − log *G*(*M*+1) − log *G*(*p*+*r*+2). The leading term is unaffected. |
| m6 | §1.3 Lean route | `Matrix.det_reindex_self` with `Equiv.rev` reindexes rows **and** columns, and the result is still anti-triangular. Use a one-sided column permutation (`Matrix.det_permute'` with `Fin.revPerm`; sign (−1)<sup>⌊*r*/2⌋</sup>). "Four declarations" actually lists five. |
| m7 | Thm 3.2(1), summary | "Rank 0 exactly when *q* divides *A*<sub>⌊*M*/*q*⌋</sub> or *q* > *M*" needs the band regime *q*<sup>2</sup> > *M* of Lemma 3.3. State it. The B3 summary row omits the non-drop case *m* = 1, where α = 0 trivially. |
| m8 | Thm 7.1(2) | "Single simple insertions follow the exact rank law *s*(*t*)" for π has no proof or certificate. For *q* = 3 (8*k*+1 and 2*k*+1) and *q* = 5 (8*k*+1 and 4*k*+3, both at *k* ≡ 3 mod 5), two progressions can share an index. Then β is a combined residue that could vanish. Add the hypothesis β ≠ 0 or exclude *q* ∈ {3, 5}. |
| m9 | Thm 7.3(3) | The negative region of the weight is at *u* ≤ 3.4·10<sup>−3</sup>, where *u*<sup>*M*</sup> suppresses it. So "indefinite for sufficiently large *r*" means *r* ≥ *r*<sub>0</sub>(*M*). In the prime-centered family *M* and *r* are coupled. State the order of quantifiers. |
| m10 | script | Labels disagree with the note: "Theorem B3.1(1)" means Thm 3.1(1), "Theorem B3.3 product bound" means Thm 3.4(3), and "B3.2 & B3.3" means Thms 3.3–3.4. A comment says `r <= 12` but the code uses `r <= 10`. §11 quotes about 6 s; I observed 1.2 s. |
| m11 | `[finite]` B2 table | "pred ~ 1.50" against 1.75–1.81 observed. Annotate that o(1) ≈ (log log *p*)/(2 log *p*) + κ<sub>*D*</sub>/log *p* ≈ 0.25 at *p* ≈ 2000. |
| m12 | Ledger rows 3 and 6 | "α > α<sub>C</sub> needed" should read "sufficient", because it comes from an upper bound. "`GF-47` drop events strictly improve *D*<sub>B3</sub>": rk(*M*, *r*, *d*) is purely combinatorial, and drop events can only lower *e*<sub>0</sub>(*q*), weakly. The exact rank-drop law of Thm 3.2(2) is **not** built into *D*<sub>B3</sub> or used in Thm 4.5. |
| m13 | §2.1 "what double differencing saves" | The exact criterion is max(v<sub>*q*</sub>(*Q*<sub>*M*</sub>), max over *M* < *n* ≤ *p* of v<sub>*q*</sub>(*n*)) < ⌊log<sub>*q*</sub> *p*⌋. The text's "no multiple in (*M*, *p*]" is only an approximation of it. |
| m14 | Lemma 4.4, Thm 5.1(2) | The matching lower bounds (Laplace) are only sketched. Theorem 4.5 does not need them, but the claim *L*<sub>*p*</sub>*I* → +∞ in Theorem 5.1(2) does. A two-line lower bound (integrate over a 1/*p*-neighbourhood of *t*\*) would close this. |

---

## 9. What is established

| Item | Status after audit |
|---|---|
| **B1** Thm 1.1 (all primes incl. *p* = 2, all 1 ≤ *r* ≤ *p*, arbitrary ℤ<sub>(*p*)</sub> entries) | **Sound.** Paper proof plus finite certificate (284 + 246 independent matrices). |
| **B2** Thm 2.1, Lemma 2.2, Cor 2.3(1) and Cor 2.3(2) at *r* = *p* | **Sound.** Cor 2.3(2) for α < 1 is unproven (M2.1). |
| **B3** Thms 3.1–3.4 incl. the exact Cauchy–Block-Rank identity and *D*<sub>B3</sub>·det *C*(*M*, *r*) ≤ *L*<sub>*p*</sub>/(*r*·C(*p* + *r*, *r*)) | **Sound.** No PNT needed for (1)–(3). Independently certified on 174,000 triples, 1,276 identities and 1,593 bound cases. |
| **B4** Props 4.1–4.2, Thm 4.3 (exact; no sign or normalization error), Lemma 4.4 (upper bounds), Thm 4.5: μ<sub>2</sub>(ln 2) ≤ 6.178813 and at least 0.3806 log<sub>2</sub> *N* transitions | **Sound** (paper proof + PNT). Correctly stated to be weaker than Alladi–Robinson 4.6221 and Marcovecchio 3.5746. |
| **B5** Thm 5.1(1) survival; 5.1(3) reset-crossing certificate | **Sound.** The interpretation in 5.1(2) needs M1. |
| **B6** ledger | Consistent apart from M1 and m12. |
| **B7** Thms 7.1(1), 7.2(1), 7.3(1)–(2) and the non-PD / sign-change certificates | **Sound.** The "what fails" parts are heuristic (M2.2–M2.4, m8, m9). |

**Scope.** I confirm the note's scope statement. Nothing here proves normality, simple normality, simple nonnormality, *D*<sup>+</sup> < 1, *D*<sup>−</sup> > 0 or (non)membership in *K*<sub>*b*</sub> for ln 2, π, *e*, ζ(3) or any `BC-01`…`BC-50` constant. **No benchmark status may change on the basis of this track or this review.**

---

## 10. Bottom line

The mathematics of Track B is correct throughout. The B1 pole holds for every prime, *p* = 2 included. The B3 Cauchy–Block-Rank cancellation is an exact integer identity. The B4 Uvarov–Christoffel reduction is exact, and it honestly shows that the *r* × *r* Hankel determinant collapses to a one-dimensional asymmetric Jacobi–Padé form. The resulting dyadic bound μ<sub>2</sub> ≤ 6.1788 is correct and correctly placed below the classical records.

The verdict is **REVISE** for two text-level Major items:
- **M1.** Replace the "2.4427 < 2.5897" near-miss barrier with the true exclusion threshold ρ<sub>excl</sub> ≈ 6.18, equivalently 1.44 versus 5.18 bits per index. This makes B5 a *stronger* limitation theorem. Reword ledger rows 7–8 and Open Question 3 to match.
- **M2.** Relabel or prove the heuristic "what fails" assertions (Cor 2.3(2) for α < 1; Thms 7.1(3), 7.2(2) and 7.3(3)).

After these changes and the minor fixes m1–m14, the track would merit **ACCEPT**.

*Reminder: this cross-model review is not independent human peer review and authorizes no benchmark status change.*

**Sources consulted for prior-art values:** [Zudilin, "An essay on irrationality measures of π and other logarithms" (arXiv:math/0404523)](https://arxiv.org/pdf/math/0404523), [Numdam, Ann. Inst. Fourier item aif.1322 (historical list of μ(log 2) bounds)](https://www.numdam.org/item/10.5802/aif.1322.pdf), [Linear independence measures of logarithms II (cites Marcovecchio 3.57455391)](https://koreascience.kr/article/JAKO202410280801188.pdf).

---

## Post-Repair Verification

**Scope.** Claude `claude-opus-5-5`, acting as the review sub-agent, 2026-11-28. I re-checked every finding above against the repaired [`notes/phase26/arithmetic-hankel-determinants.md`](../arithmetic-hankel-determinants.md) (759 lines) and [`scripts/phase26_hankel_ln2.py`](../../../scripts/phase26_hankel_ln2.py) (1,312 lines). The check was read-only, except that I appended this section; every line above it is unchanged byte for byte. Nothing was committed and WSL was not used.

### PR-1. Script run

`python -B scripts/phase26_hankel_ln2.py` on Windows exits **0** in about 1.1 s:

```
ALL CHECKS PASSED: 67877 total assertions (67593 exact, 284 rational enclosure).
```

- **Counts.** They match §11 of the note and the summary table: 284 B1 matrices; 924 LCM pairs; 51 B2 matrices, 17 of them strict; 877 + 839 rank windows, with 133 drop events; 6,272 triples; 100 global identities, 52 of them strict; 84 / 70 / 153 B4 cases; 36 + 61 enclosures; 18 + 1 B5 windows plus 4 enclosures of |ε̃|; 30 + 124 π windows; 53 *e* matrices; 15 ζ(3) matrices.
- **No floating point in `[exact]`/`[encl]`.** I re-scanned every line before `print_finite_asymptotics` (line 1105). The only `math.*` calls are integer-valued (`isqrt`, `lcm`, `factorial`, `comb`). Every `/` acts on a `Fraction`, and decimal literals appear only in strings and comments.
- **The new `[encl]` checks are certified.**
  - **ln 2.** `ln2_enclosure_dyadic(1000)` loses less than 1 per floor over 1,000 terms, and the tail is less than 2<sup>−1000</sup>, so [*S*, *S* + *P* + 1]/2<sup>*P*</sup> is a valid enclosure.
  - **Apéry series.** It alternates with decreasing terms, and the cut-off *N* = 90 is even, so *S*<sub>*N*</sub> < ζ(3) < *S*<sub>*N*</sub> + *a*<sub>*N*+1</sub>.
  - **Broadhurst tail.** The tail is bounded by Σ|*a*<sub>*j*</sub>|·4096/(672·(24*K*+1)<sup>3</sup>·4096<sup>*K*</sup>·4095).
- **Isolation.** The `[float]`/`[finite]` block still gates nothing.

### PR-2. Finding-by-finding status

| Finding | Status | Evidence in the repaired note or script |
|---|---|---|
| **M1** activation vs exclusion | **Resolved** | Theorem 5.1(2) is now split. Part (a) is the *activation* threshold ρ\* = 2.5897, and its literal statement is kept. Part (b) is the *exclusion* threshold ρ<sub>excl</sub> = 1 + *c*<sub>run</sub>(α\*) = μ<sub>2</sub> = 6.178813…, with the bits comparison 1.44 versus 5.18. The proof is complete. The block forces \|ε̃\| ≤ 2<sup>−((ρ−1)*M*−1)</sup>, using *T*<sub>*n*</sub> < 1/(*n*+1). Also *g*′(α) = log((1+*x*\*)/*x*\*) > 0, because the coefficient of *x*\*′ vanishes by the saddle equation; I re-derived this. So *c*<sub>run</sub>(α) = (1+*g*)/((1−α) ln 2) is strictly increasing, and the infimum sits at α\*. The B5 summary row, ledger rows 3, 7 and 8, §9, §10 and Open Question 3 are all reworded to match, and the script prints the same hierarchy. *Correction to my §6:* I quoted ρ<sub>excl</sub> = 6.1802 from a grid search. The exact infimum is μ<sub>2</sub> = 6.178813…, which is the value the note now states. |
| **M2.1** Cor 2.3(2) for α < 1 | **Resolved** | Corollary 2.3(2) is now stated only at α = 1. The α ∈ (0, 1) material is a separate remark labelled *Finite measurement / Heuristic*, giving κ<sub>*D*</sub> → 1 + γ and quoting the *p* = 1999 values (−0.0796 at α = 0.02). The labels in the summary row and in ledger rows 4 and 8 are updated too. |
| **M2.2** π quadratic failure | **Resolved** | Theorem 7.1(3) carries the heading *Heuristic / M = 0 benchmark*, and the text says "no formal proof is given here". |
| **M2.3** linear balances | **Resolved** | Theorems 7.1(3) and 7.3(3b) are labelled as symmetric *M* = 0 benchmarks, explicitly "not a paper proof of prime-centered *M* > 0 failure". The B7 evidence column and the script's `[float]` line say the same. |
| **M2.4** *e* degeneration | **Resolved** | The obstruction is restricted to geometric (clean) shifts, and the note adds that with arbitrary integer shifts the determinant need not vanish. I re-checked that rows *i*<sub>0</sub> and *i*<sub>0</sub>+1 are proportional when *K* is constant. |
| m1 | Resolved | The value is now 0.4301 in Theorem 5.1(2)(a) and in the script. |
| m2 | Resolved | Chudnovsky is now listed as μ ≤ 4.1344 with *c*<sub>run</sub> 3.1344, and Rhin (1987) 4.0765 is added. No 4.269 remains anywhere. |
| m3 | Resolved | The script now contains an `[encl]` check of Broadhurst against Apéry to more than 52 digits (lines 1067–1088), and it passes. §8 still labels Broadhurst's identity *External input*, which is correct. |
| m4 | Resolved | The proof of *D*<sub>B3</sub> \| *D*<sub>row</sub> is now in Theorem 3.3. It uses rk ≤ Σ over classes with *n*<sub>*c*</sub> ≥ 1 of *m*<sub>*c*</sub> = #{*i* : *q*<sup>*j*</sup> \| *D*<sub>*i*</sub>} and *e*<sub>0</sub>(*q*) ≤ ⌊log<sub>*q*</sub> *p*⌋. I checked it, and it is correct. |
| m5 | Resolved | The arguments now read *G*(*r*+1), *G*(*p*+2), *G*(*M*+1) and *G*(*p*+*r*+2). I re-derived them from the Cauchy formula. |
| m6 | Resolved | The text now gives a one-sided column permutation via `Matrix.det_permute'` with `Fin.revPerm`, warns about the two-sided reindex, and says "five declarations". |
| m7 | Resolved | The band regime *q*<sup>2</sup> > *M* is now stated in Theorem 3.2(1). The B3 summary row includes the first-entry case *m* = 1. |
| m8 | Resolved | The rank law now requires *q* ≥ 7 or β ≠ 0. The proof uses resultants, whose only odd primes are 3 and 5. The β = 0 examples (*q* = 3, *k* = 7) and (*q* = 5, *k* = 23) are certified in the script; I checked both by hand. |
| m9 | Resolved | Theorem 7.3(3a) now gives *r* ≥ *r*<sub>0</sub>(*M*) for each fixed *M* and spells out the order of quantifiers along a coupled ray. |
| m10 | Resolved | The script labels now read Theorem 3.1(1), Theorem 3.3 and Theorem 3.4(3). The comment matches `r <= 10`, and §11 quotes about 1.1 s, which matches what I observed. |
| m11 | Resolved | The `[finite]` B2 table and Corollary 2.3(1) are annotated with the slow o(1) correction. |
| m12 | Resolved | Ledger row 3 says "sufficient", and row 6 says "weakly lower *e*<sub>0</sub>(*q*)… not built into *D*<sub>B3</sub> or used in Thm 4.5". |
| m13 | Resolved | §2.1 gives the exact max-valuation criterion, with the empty-max convention when *M* = *p*. |
| m14 | Resolved | Lemma 4.4 now has a non-asymptotic lower bound, *I* ≥ min(*t*\*, 1−*t*\*)/(2e*p*)·e<sup>−*g*(α<sub>0</sub>)*p*</sup>. I re-derived it: on [*t*\* − δ, *t*\* + δ] with δ = η/(2*p*), we have −φ″ ≤ 4/*t*\*<sup>2</sup> + 4α<sub>0</sub>/(1−*t*\*)<sup>2</sup>, the Taylor loss is at most (1+α<sub>0</sub>)/(2*p*<sup>2</sup>), and 1/(2−*t*) ≥ 1/2. The proof of Theorem 5.1(2)(a) uses it, together with *I*<sub>*M*,0</sub> = *T*<sub>*p*</sub> > 1/(*p*+2) for *r* = 1. |

### PR-3. Regression check

I found no new mathematical error and no evidence-label regression. Specifically:
- Theorems 1.1, 2.1, 3.1–3.4, 4.3 and 4.5 and Theorem 5.1(1) are unchanged in substance.
- Every claim newly labelled heuristic or *M* = 0 is clearly separated from the paper proofs.
- §8 lists PNT for Theorem 5.1(2) and Theorems 7.1(3) and 7.3(3b).
- The scope statement and the reminder about cross-model review remain, and no benchmark status is touched.

Three non-blocking observations remain, all optional:
1. **Open Question 3.** The parenthetical "Marcovecchio's μ(ln 2) ≤ 3.5746 requires ρ > 3.5746" is an analogy. Classical measures concern ln 2, whereas ε̃ is measured against *y*<sub>*i*</sub>. The analogy holds only if the classical linear-form argument transfers to the states *s̃* inside a reset-free block. Marking it "(heuristically)" would be cleaner.
2. **o(1) range.** The script's `[finite]` header says "~0.25–0.31", while Corollary 2.3(1) says 0.25–0.34. The script's own column implies about 0.34 at *p* = 2003. This is cosmetic.
3. **Wording.** "Confirms all 23 coefficients" means a 52-digit numerical cross-check of Broadhurst's identity, not a proof of it. Its *External input* status in §8 is correct.

### Verdict: **ACCEPT**

Both Major items (M1, M2.1–M2.4) and all fourteen minor items (m1–m14) are resolved. The script passes with 67,877 assertions (67,593 exact, 284 enclosure) and no floating point in any `[exact]` or `[encl]` section. Track B may proceed with the evidence labels as now stated.

> **Cross-model review is not independent human peer review.** This verification is a machine reading by a language model. It does not replace refereeing by human specialists, and it authorizes no change to any `BC-01`…`BC-50` or arithmetic-family benchmark status.
