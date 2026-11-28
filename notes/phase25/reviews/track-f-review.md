# Phase 25 Track F: cross-provider adversarial referee report

**Audited files.** [`notes/phase25/nonlinear-and-badly-approx.md`](../nonlinear-and-badly-approx.md) (519 lines, SHA-256 `0ec69849…3efdf`) and [`scripts/phase25_nonlinear_approx.py`](../../../scripts/phase25_nonlinear_approx.py) (689 lines, SHA-256 `48c29983…02ab`). Gemini 4 Neon wrote both files. Line numbers below refer to these exact versions.

**Reviewer.** Claude Opus 5.5, acting as a read-only cross-provider referee. **Cross-model review is not independent human peer review.** Nothing in this report establishes that a result is peer reviewed. Benchmark statuses must not change on the strength of this report.

## Verdict: **REVISE**

The verifier exits with code 0, and every number it prints matches §6 of the note. The F2 analytic core survives an adversarial line-by-line check: Lemma 2.1, Lemma 2.2, the Kaufman-type proof of Theorem 2.3 (including critical points), and the selection logic of Theorem 2.4. Theorem 3.1 also survives, as do Theorem 3.2(1), Theorem 3.2(3) and its injectivity claim. Three load-bearing claims fail as written:

* **C1.** The "if and only if" in Theorem 1.3(1) is **false whenever gcd(*Q*, *b*) > 1**. A concrete counterexample with real data is given below.
* **C2.** Theorem 1.1(3) states two discrepancy values that are **provably impossible**. The Objective-4 "barrier" drawn from it (line 80, line 519) does not follow from the theorem.
* **C3.** The unique-maximal-tuple argument for Theorem 3.2(2) **fails when *p* divides the binomial multiplicity**. I computed explicit instances, including degree 3 at *p* = 3, where the actual *p*-depth is smaller than the depth the argument asserts. The conclusion of Theorem 3.2(2) appears to survive with the repair sketched below, but the proof in the note does not establish it.

The F2 computability claim (Theorem 2.4) is sound in substance. However, one integer threshold, *J*<sub>*e*</sub> = ⌈2<sup>*e*+3</sup>*K*(*P*<sub>*e*</sub>)⌉ at line 335, is **not computable as literally written**. Several other comparisons need explicit rational majorants (Major M1). Each of these has a routine fix.

---

## 0. Reproduction

| Check | Result |
| --- | --- |
| `python -B scripts/phase25_nonlinear_approx.py` (Windows host, Python 3.13.13, about 11 s) | **exit 0**. Printed: 810 lifts, 68 lag grids, collapse `[1, 2, 4, 11, 31]`, 972 iff configurations, 5 cube drops, 448 rectangles, float ratios 0.2611 / 0.8493, distinct-*N* counts 550 612 / 8 439 / 337, 10 000 concatenations, 1 780 + 4 272 folds |
| Exact certificate totals (imported `certify_block_sum_exact`, *D* = 10<sup>18</sup>) | *T* = 1 018 523 069 631 799 680 (M=42, L=4); 1 014 769 247 165 126 215 (M=14, L=4); 1 025 743 393 489 645 808 (M=30, L=2). The exact rationals *T*/*D* exceed the six-decimal values at line 494, so the float display does not round upward into the claim |
| Flagship cube | *e*(1268) = 0, *e*(2186) = 4, *e*(2187) = 6, and 2187 is the first *M* with *e* = 6, matching line 490. The script itself asserts only *e*(2200) = 6 (script line 305) |
| Lag-grid count | 24 + 20 + 24 = 68 over (*p*, *B*) = (3, 4), (3, 10), (5, 16), matching line 489 |
| Exact/float separation | Certificate decisions use integers or `Fraction`. Floating point appears only in the Kloosterman sanity check (script lines 370–384), in the Newton seed inside `iroot_floor`, whose result is then certified exactly (script line 59), and in the printed ratios. The separation is honest |

The note was not re-run on Hail. The verifier is a pure-Python, platform-independent script. Independent checks used a scratch script outside the repository and are reproduced inline below.

---

## 1. Critical findings

### C1. Theorem 1.3(1) "iff" is false when gcd(*Q*, *b*) > 1

*Location:* note lines 98–111 (statement), 126 (proof), 34 (table), 490 and 519 (claims); script lines 255–290.

**Defect.** The proof characterizes when the data admit $Q(\widetilde A_M/p^e+\widetilde T)\in\mathbb Z$, that is, $Q\,B^M X\in\mathbb Z$. The statement asserts a characterization of when the data exclude $QX\in\mathbb Z$. These conditions differ. Let *X*′ be a hypothetical real consistent with the data, write $B^MX' = N+\varphi$ with $N\in\mathbb Z$ free, and set $Q' = Q/\gcd(Q,B^M)$. Then $QX'\in\mathbb Z$ is solvable in *N* exactly when $Q'\varphi\in\mathbb Z$. The correct threshold therefore uses *Q*′, which differs from *Q* exactly when gcd(*Q*, *b*) > 1, because *B* = *b*<sup>*t*</sup>. The "if" direction of (1.1) remains valid, since $Q'\varphi\in\mathbb Z\Rightarrow Q\varphi\in\mathbb Z$. The "only if" direction fails.

**Concrete counterexample with real data.** Take the square $C_1(2)^2$ with *b* = 2, *B* = 4, *p* = 3, *s* = 1 and *M* = 10. Exact convolution gives *R*<sub>10</sub> = 202802/3, so *e* = 1, and *T*<sub>10</sub> ≈ 0.01054. Supply the data *h* = 0, *Q* = 2 and *T*<sub>max</sub> = 1/6, which is a valid upper bound. Then *g*<sub>0</sub> = gcd(2, 3) = 1, so *r*<sub>min</sub> = 1 and $Qp^eT_{\max}=1\not<1$. Thus (1.1) fails, and the note asserts that the data do **not** exclude 2*X* ∈ ℤ. Its witness is the phase 1/3 + 1/6 = 1/2. But 2*X*′ ∈ ℤ forces 4<sup>10</sup>*X*′ ∈ ℤ, so the phase must be 0 mod 1. With unit numerator 1 or 2 over 3, the least admissible positive tail is 2/3 or 1/3, and both exceed 1/6. **The data do exclude 2*X* ∈ ℤ**, contradicting "only if".

**Systematic check.** I tested *b* ∈ {2, 3, 5, 6, 10}, *p* ∈ {3, 5, 7} with *p* ∤ *b*, *e* ≤ 3, all 0 ≤ *h* ≤ *e*, the note's nine values of *Q*, and *M* = 20. The note's threshold differs from the true threshold in **1 185 of 2 511** configurations. Every mismatch has gcd(*Q*, *b*) > 1, and the true exclusion threshold was never smaller than the note's. The verifier cannot detect this: its iff test (script 258–290) contains no *b* and no *M* and tests only the shifted condition.

**Fix.** Either (a) replace *Q* by *Q*′ = *Q*/gcd(*Q*, *B*<sup>*M*</sup>) in *g*<sub>0</sub>, *r*<sub>min</sub> and (1.1) when the target is *QX* ∈ ℤ, or (b) restate the theorem as a characterization of excluding *QB*<sup>*M*</sup>*X* ∈ ℤ. Under (a), the converse follows because multiplication by *B*<sup>*M*</sup>/gcd(*Q*, *B*<sup>*M*</sup>) permutes residues mod *Q*′. Part (2) is unaffected, since *r*<sub>min</sub>(*Q*′) ≤ *Q*′*p*<sup>*h*</sup> ≤ *Q* *p*<sup>*h*</sup>. Add *b* and *M* to the verifier and include the equality case above as a regression test.

### C2. Theorem 1.1(3): impossible discrepancy values, and the Objective-4 barrier does not follow

*Location:* note line 64 (statement), 80 (barrier paragraph), 32, 508 and 519 (claims).

1. **"another produces a balanced/de Bruijn word of local discrepancy *O*(*b*<sup>−*L*/2</sup>)" is impossible.** With the note's own definition (line 14), any sample of *L* points has extreme discrepancy at least 1/*L*: shrink a half-open interval onto one point. For large *L*, 1/*L* exceeds any fixed multiple of *b*<sup>−*L*/2</sup>. For example, 1/*L* > 10·*b*<sup>−*L*/2</sup> already at *L* = 16 for *b* = 2 and at *L* = 8 for *b* = 3.
2. **"some lift produces 0<sup>*L*</sup> (… local discrepancy 1 − *b*<sup>−*L*</sup>)" is wrong.** The first *L* digits of $\widetilde X_M$ being 0 only places $\{b^n\widetilde X_M\}$ in $[0,b^{-(L-n)})$, and the tail beyond digit *L* is uncontrolled. The provable bound is $\max_{1\le m\le L}\bigl[(L-m+1)/L-b^{-m}\bigr]$. For *b* = 2, *L* = 9 this equals 47/72 ≈ 0.653, not 0.998.
3. **The barrier is a non-sequitur.** Line 80 concludes that "no argument using only packet innovations, denominators, low residues, scaled phases, and aggregate difference denominators can establish *D*<sup>+</sup> < 1 or positive lower transition density". The theorem perturbs one packet at a time, and the perturbed lifts change the real number globally. No single object (a real number or an abstract digit sequence) is constructed that satisfies the listed information at every packet simultaneously and has *D*<sup>+</sup> = 1 or zero lower transition density. Logarithmic-length blocks such as 0<sup>*L*</sup> with *L* ≍ log *M* at shift ≍ *M* are compatible with normal sequences, so their mere realizability says nothing about limsup or liminf over *N*. The repository's own rule (`docs/research-objectives.md`, Objective 4) requires that "a limitation theorem names the method and the property, and proves that the method cannot reach the property". The unproved arrival counts on line 80 (≫ √log *M*<sub>*a*</sub> for *d* = 2 and ≫ (log *M*<sub>*a*</sub>)<sup>1/3</sup> for *d* = 3) are a further problem. Moreover, Phase 24's selected arrivals near *M*<sub>*a*</sub> are spaced by ≍ *U*<sup>*d*−1</sup> ≫ log *M*<sub>*a*</sub>.

**What survives.** Parts (1) and (2), and the per-packet word realization in (3), are correct. The translated grid of spacing *p*<sup>−(*e*−*h*)</sup> meets every *b*-adic cylinder of length ≥ *p*<sup>−(*e*−*h*)</sup>.

**Fix.** Delete both discrepancy parentheticals. Restate line 80 and §8 as a *local* limitation: the listed information does not determine any base-*b* word of length ≤ ⌊(*e* − *h*) log<sub>*b*</sub> *p*⌋ at the packet start. Alternatively, formalize an information class and construct a globally consistent counter-model with *D*<sup>+</sup> = 1. Downgrade the Objective-4 entries in lines 32 and 519 accordingly.

### C3. Theorem 3.2(2): the unique-maximal-tuple argument fails when *p* | C(*r*, *j*)

*Location:* note lines 428 (argument), 410–413 (statement), 497 (claimed verification); script lines 649–672.

**Defect.** On the *j*-th interval the unique maximal unordered tuple has ordered multiplicity C(*r*, *j*). When *p* divides this multiplicity, the top class loses valuation and can tie or cancel with the next classes. "Unique maximal tuple ⇒ exact depth *rM* − (*r* − *j*)" therefore fails. The flagship case *r* = 3, *p* = 3 already exhibits this, since C(3, 1) = C(3, 2) = 3.

**Computed instances.** I used *b* = 2, *p* = 3, *a*<sub>0</sub> = 1, κ = (2, 4, 7, 11, 16), *P*<sub>*k*</sub> from the note's formula, all-ones patterns, and μ = 1 (auxiliary primes do not affect *p*-adic valuation). I computed the exact regrouped degree-*r* shifted prefix at an interior shift of each interval.

| *M* | *r* | *j* | C(*r*, *j*) | shift *n* | actual *p*-depth | depth asserted by the argument |
| --- | --- | --- | --- | --- | --- | --- |
| 4 | 3 | 1 | 3 | 2 311 | **9** | 10 |
| 4 | 3 | 2 | 3 | 4 231 | **10** | 11 |
| 4 | 4 | 2 | 6 | 4 359 | **12** | 14 |
| 4 | 2 | 1 | 2 | 2 183 | 7 | 7 |
| 5 | 3 | 1 | 3 | 69 639 | **12** | 13 |
| 5 | 3 | 2 | 3 | 133 127 | **13** | 14 |
| 5 | 4 | 2 | 6 | 135 175 | **16** | 18 |
| 5 | 2 | 1 | 2 | 67 591 | 9 | 9 |

The losses agree with a limiting 3-adic model. Normalize each pole by *p*<sup>*M*</sup>. The current pole is 1 + *O*(*p*<sup>*M*−*a*<sub>0</sub></sup>), and the older poles sum to *t* ≡ *p*/(1 − *p*). The pure pole contribution is $\sum_{i\le j}\binom{r}{i}t^{r-i}$, whose valuation at *t* = −3/2 is 3, 2 and 4 for (*r*, *j*) = (3, 1), (3, 2), (4, 2). The argument predicts 2, 1 and 2. For (4, 2), 6*t*<sup>2</sup> + 4*t*<sup>3</sup> = 0 exactly. The verifier tests only (*r*, *j*) = (2, 1), (2, 2) and (3, 3). Its multiplicities 2, 1 and 1 are prime to *p*, so line 497's "unique-maximal-tuple pole retention in degrees *r* = 2, 3" overstates what was checked.

**Repair.** The bound "depth ≥ *rM* − *O*<sub>*P*,*p*</sub>(1)" that Theorem 3.2(2) needs probably survives. Modulo *p*<sup>*M*−*O*(1)</sup>, mixed tuples containing a non-pole index and all lower-degree terms of *P* vanish after normalization. The pure-pole factor is $t^{r-j}f_j(t)$ with $f_j(t)=\sum_{i=0}^{j}\binom{r}{i}t^{j-i}$, a **monic** integer polynomial. For odd *p*, *p*/(1 − *p*) is not an integer, so the rational root theorem gives $f_j(p/(1-p))\neq0$. Its *p*-adic valuation is a finite constant depending on (*r*, *j*, *p*). This gives depth ≥ *rM* − (*r* − *j*) − *v*<sub>*p*</sub>(*f*<sub>*j*</sub>(*p*/(1 − *p*))) − *O*<sub>*P*</sub>(1) for *M* large, which still exceeds *A*(*b*<sup>τ</sup>) + *M*/4. The congruence must be spelled out uniformly in the patterns **w**, with the leading coefficient of *P* included. Add tests with *p* | C(*r*, *j*) to the verifier, for example (*r*, *j*, *p*) = (3, 1, 3), (3, 2, 3) and (4, 2, 3).

---

## 2. Major findings

### M1. F2 computability: every threshold audited, and one integer threshold is non-computable as written

The brief asked for a threshold-by-threshold audit of Theorem 2.4 (lines 329–358) and of the constants it inherits from Theorem 2.3.

| Threshold or comparison | Line | Computable as written? | Required fix |
| --- | --- | --- | --- |
| *J*<sub>*e*</sub> = ⌈2<sup>*e*+3</sup>*K*(*P*<sub>*e*</sub>)⌉ | 335 | **No.** *K*(*P*<sub>*e*</sub>) = 1 + 2*C*(*P*<sub>*e*</sub>)/(1 − 2<sup>−η</sup>)<sup>2</sup> is irrational in general, and the ceiling of a computable real is not computable: one cannot decide whether 2<sup>*e*+3</sup>*K* is an integer | Compute a **rational** *K̄*<sub>*e*</sub> ≥ *K*(*P*<sub>*e*</sub>). For example, use 1 − 2<sup>−η</sup> ≥ η ln 2/(1 + η ln 2) with a rational lower bound for ln 2. Then set *J*<sub>*e*</sub> = ⌊2<sup>*e*+3</sup>*K̄*<sub>*e*</sub>⌋ + 1. The bound ∫Ψ dμ ≤ 1/4 is unchanged |
| *C*(*P*), ξ<sub>0</sub>(*P*) | 238, 249, 287, 301–310 | **Not specified.** The proof uses ≪<sub>*M*,*L*,*P*</sub> throughout Steps 4–5 and never writes *C*(*P*) or ξ<sub>0</sub>(*P*). Ingredients such as (*r*\|*c*<sub>*r*</sub>\|)<sup>−*s*/(*r*−1)</sup>, *C*<sub>*F*</sub><sup>1/2</sup>, log factors and (1 + ξ<sub>0</sub>)<sup>η</sup> are irrational | Add a lemma: "there is an algorithm that, given the rational coefficients of *P*, outputs rationals *C̄*(*P*) ≥ *C*(*P*) and ξ̄<sub>0</sub>(*P*)". Use rational majorants, and log *x* ≤ *x*<sup>ε</sup>/ε for the log absorption |
| *E*, *J* truncation | 345–349 | Only with rational *K̄*<sub>*e*</sub> | Use *K̄*<sub>*e*</sub> in the budget. The tail bounds are then rational and the strict inequality is decidable |
| Refinement depth *d* and Taylor degree | 350 | Only with rational bounds on π and φ<sup>−2(*dL*−1)</sup> | φ > 809/500 (already certified) gives φ<sup>−*k*</sup> < (500/809)<sup>*k*</sup>, and 22/7 bounds π. Budget the **sum** of the Lipschitz errors over the finitely many (*e*, *j*) |
| Partial sum of *S* for *X* − *S* | 350 | Yes | A geometric tail bound suffices |
| *B*<sub>*m*</sub> = 1 − 2<sup>−*m*−1</sup>, δ<sub>*m*</sub> = 2<sup>−*m*−4</sup>, test Ê < *B*<sub>*m*+1</sub> − δ<sub>*m*</sub>, lexicographically first child | 352 | **Yes.** All are rational comparisons, and the averaging argument guarantees a passing child, so the search halts | none |
| Weights *p*<sub>**u**</sub>, cylinder masses *w*(**a**) | 222, 344 | Yes. *D* can be found by computing *T*(*D*) for increasing *D*, which halts because Σ > 1. For *M* = 100, *L* = 52 this is finite but astronomically large | Note the cost honestly in §7 Q4 |
| Critical-point radii, roots ρ<sub>*i*</sub> | 251 | Never computed. Proof only | none |
| Base-*b* digits *d*<sub>*n*</sub> of *x* − *S* | 322 | Yes, since *x* − *S* is irrational (normal), so digit extraction never stalls at a *b*-adic rational | none |

**Conclusion.** No hidden non-computable *step* exists. The one non-computable *threshold* is *J*<sub>*e*</sub> as literally written, and every real-valued constant needs a stated rational majorant. The limit passage at lines 354–358 is valid and correctly avoids an illegitimate limit exchange: it applies the continuous finite truncation Ψ<sub>*T*</sub> before *m* → ∞, then uses monotone convergence in *T*.

### M2. Theorem 2.3: η is not uniform over a regime, the *r* = 1 case is malformed, and constants are not explicit

*Location:* lines 238, 247, 249, 306–310.

* Line 238 says η<sub>*r*</sub> depends "only on *r* and the regime". Eliminating β and θ from (2.5) gives 2(1 − *s*)/(1 − ρ) < α < *s* − 1/2. My recomputation confirms the thresholds *s* > 17/18 and *s* > 9/10, but the admissible interval collapses as *s* decreases to the threshold. No positive η exists uniformly over the open regime. Either state η = η(*r*, *s*, ρ) or restrict the theorem to the four listed measures.
* An explicit valid choice is η = min{2α + 4β − 1, 2α*s*, *s*θ/(*r* − 1), *m*<sub>*A*</sub>/2, *m*<sub>*B*</sub>/4}. Here *m*<sub>*A*</sub> = *s* − 2α − 2β − 3θ/2 and *m*<sub>*B*</sub> = (1 − ρ)α/2 − (1 − *s*) − θ/2. The square root in (2.6) halves both margins, and the quarter on *m*<sub>*B*</sub> absorbs log|ξ|. For the printed parameters the margins are (2α + 4β − 1, *m*<sub>*A*</sub>, *m*<sub>*B*</sub>) = (1/125, 959/76000, 33/38000) for *s* = 18/19; (1/50, 37/2000, 1/500) for *s* = 19/20; and (1/50, 177/11000, 17/5500) for *s* = 10/11.
* For *r* = 1, line 310 lists −*s*θ/(*r* − 1) as a "strictly negative" exponent, which is 0/0. Omit the critical-set term when *r* = 1, since Step 1 is skipped and θ = 0.
* "Explicitly computable *C*(*P*)" (line 238) is asserted but not exhibited. See M1.

### M3. Theorem 1.3(2)–(3): scope, sharpness and quantifiers

*Location:* lines 34, 112–124, 128–140, 507.

* **Depth hypothesis on the actual gap starts.** Part (2) assumes *e*<sub>*k*</sub> ∼ *s* log<sub>*p*</sub> *M*<sub>*k*</sub> along the gap starts. Remark line 140 applies the barrier to Ghidelli's starts using density-one depth growth (Phase 21 Prop. D). A density-one statement gives nothing on a specific sparse sequence. Drops such as *q*<sub>1268</sub> = 1 show that the depth can collapse. State the barrier as conditional on the depth hypothesis on those same starts.
* **Envelope.** The barrier assumes *T*<sub>max</sub> ≥ *B*<sup>−*g*<sub>*k*</sub></sup>, an envelope of the form *H*<sub>ub</sub>*B*<sup>−*g*</sup> with *H*<sub>ub</sub> ≥ 1. Part (1) allows any *T*<sub>max</sub>. Say explicitly that the barrier concerns this envelope class.
* **"Sharp" thresholds.** Lines 34 and 113 call the thresholds sharp, but only sufficiency is proved. Phase 24 eq. (2), the stated source, calls them "a sufficient gap-only condition". Remove "sharp", or prove necessity for the envelope test.
* **Abundant-gap case.** The Markov argument retains half of the gaps, but the length limsup is taken over the whole family, and the long gaps may fall in the discarded half. Require *N*<sup>1−*o*(1)</sup> disjoint gaps of length > (*s*/log *B* + ε) log *N* in the same dyadic ranges, and apply Markov to those.
* **Line 136.** The inequality truncates *H*<sub>*M*<sub>*k*</sub></sub> at *m* ≤ 2*N*, but the tail beyond 2*N* is positive. Add it: it is exponentially small by the polynomial coefficient bound.
* **Labels.** The residue-boosted item (line 120) is an implication from an unproved limsup hypothesis. Label it `Conditional` at the point of use, not only in the table.

### M4. Theorem 3.2(2): incorrect growth estimate in the complete-period step

*Location:* line 430.

The note asserts "log<sub>2</sub>(τ*p*<sup>*e*(*h*)</sup>) = *O*(*M*) = *O*(log log *N*) (since *M* = *e*<sub>*K*</sub> ≤ *K* ≤ log<sub>2</sub> *N*)". The inequality *e*<sub>*K*</sub> ≤ *K* gives only *O*(log *N*), and hence τ*p*<sup>*e*(*h*)</sup> = *N*<sup>*O*(1)</sup>, which is useless. The schedule κ<sub>*m*</sub> = *m*<sup>2</sup> + 1 is admissible, since its gaps tend to infinity, and gives *e*<sub>*K*</sub> ≍ √log *N*. The correct justification is that κ<sub>*m*+1</sub> − κ<sub>*m*</sub> → ∞ implies κ<sub>*m*</sub>/*m* → ∞, hence *e*<sub>*K*</sub> = *o*(*K*), and so exp(*O*(*e*<sub>*K*</sub>)) = *N*<sup>*o*(1)</sup>. The proof also treats only shifts in [2<sup>κ<sub>*M*</sub></sup>, 2<sup>κ<sub>*M*+1</sub></sup>). Shifts in [*r*·2<sup>κ<sub>*M*−1</sub></sup>, 2<sup>κ<sub>*M*</sub></sup>) belong to the saturated epoch *M* − 1 and contribute *p*<sup>−(*M*−1)/4</sup>, which leaves the stated rate unchanged once said. For an arbitrary computable schedule, the displayed rate is computable at each *N*, but its convergence to 0 need not have a computable modulus. Do not call it "effective" without that qualification.

### M5. Theorem 3.2(4): the irrationality claim is ill-posed

*Location:* line 419 and the proof at line 442.

"Non-eventually-periodic choices differ from the baseline by an irrational number" names no baseline and does not define periodicity for words of growing length *P*<sub>*k*</sub>. Take **w**<sub>*k*</sub> = (2, …, 2) for every *k*. As a sequence of words it is not eventually periodic, because the lengths change. Against the all-ones baseline, however, the difference is $\sum_{n\ge3}b^{-n}=b^{-2}/(b-1)$, which is rational. The proof at line 442 establishes injectivity, which I verified, including the *b* = 2 case via the repeat at 2<sup>*k*</sup> + *i*<sub>0</sub> + *P*<sub>*k*</sub>. It proves nothing about irrationality. Fix: take the all-ones baseline and require the **expanded site-by-site** 0/1 difference sequence to be non-eventually-periodic. That sequence is a base-*b* expansion with digits 0 and 1, so irrationality follows.

### M6. Prior-art and attribution errors

*Location:* lines 455–459 and 140.

* **Becher–Bugeaud–Slaman (2016, Proc. AMS 144, 1509–1521)** characterizes irrationality exponents of computable reals: *a* ≥ 2 is such an exponent if and only if it is the upper limit of a computable sequence of rationals. The cited theorem involves **no normality**, so line 456's "computable absolutely normal numbers with prescribed irrationality exponents (including Liouville numbers)" misattributes. The computable absolutely normal Liouville number is due to Becher–Heiber–Slaman (Math. Comp., 2015). [AMS page](https://www.ams.org/proc/2016-144-04/S0002-9939-2015-12841-9/) · [arXiv:1410.1017](https://www.arxiv.org/abs/1410.1017)
* Line 455 calls the Fourier-decay results of Sahlsten–Stevens, Algom–Rodriguez Hertz–Wang and Baker–Banaji "non-effective in the constants". This blanket claim is unsupported. Remove it or support it per theorem. Novelty claims must not rest on it, and repository rule 5 already makes priority provisional.
* **Ghidelli.** The Phase 24 note keeps the 2020 JLMS cubic-gap paper (doi 10.1112/jlms.12312) separate from the theta-series preprint (arXiv:1910.05076v1) that supplies the mild-tail bound. Line 459 ("Ghidelli (2020, JLMS; arXiv:1910.05076)") and line 140 conflate them. Follow Phase 24's attribution. I could not independently retrieve the arXiv listing, so I rely here on the repository's Phase 24 citation.
* **§5 item 2 (line 473).** Phase 24 states the tail as 60(log *T*)<sup>*C*</sup> with log *N* ≍ *T*. Restating it as 60(log log *n*)<sup>*C*</sup> in terms of the **start** *n* requires log *n* ≍ log *N*. Justify this, for example by choosing a start comparable to *N*.
* Turing's normal-number note is unpublished and is usually dated c. 1938, not 1937. Sierpiński's 1917 construction required the computable reformulation of Becher–Figueira (2002).

### M7. §6 overstates what the verifier certifies

*Location:* note lines 484–497.

The note states, "Exit code `0` certifies every check below". These items are not what the script checks:

* **Line 488** claims that all 810 lifts preserve every aggregate difference denominator and low residue. The script checks aggregates only for *u* < 25 and *v*<sub>1</sub> ≤ *M* + 6 (script lines 187–189). It checks site invariants only for *y* ≤ *M* + 6 (script line 180). The word test uses a proxy tail *T*<sub>end</sub> = 1/(7*B*<sup>4</sup>) (script line 156).
* **Line 491** speaks of "9 prime powers *p*<sup>*k*</sup> ≤ 32", but the list includes 81 and 125 (script line 336). The 448 "certified" rectangle bounds are vacuous: for *q* ≤ 30, 120τ(*q*)*q*<sup>3/4</sup> > *q* ≥ count, and the same holds for 90τ(*q*)*q*<sup>1/2</sup>. They certify nothing about (2.2) or (2.3).
* **Line 495** cites "all 6 strict rational exponent inequalities in (2.5)". (2.5) has five; the script adds 2α + 2β + θ < 1 (script lines 439 and 450).
* **Line 496.** The "10 000 depth-4 concatenations" use only digits 1–10 of the *M* = 30 alphabet. The "*L*<sup>2</sup> martingale selection invariant" is a single hand-picked three-child arithmetic example (script lines 491–503), not a test of the algorithm.
* **Line 497.** The auxiliary schedule in the script uses `bit_length` (script line 560) instead of ⌈log<sub>2</sub>⌉. For (*b*, *p*) = (3, 5), this gives *m*<sub>1</sub> = 9 where the note's formula gives 5. The fixture prescribes its own *P*<sub>*k*</sub> and pole depths (script lines 573–575), and *P*<sub>4</sub> = 4 with one pole contradicts the note's *P*<sub>*k*</sub> formula. The degree-3 "pole retention" test covers only *j* = *r*; see C3.

Each sentence of §6 must match the code exactly, or the code must be extended. This matters because these items carry the `Finite certificate` label.

---

## 3. Minor findings

1. **Theorem 2.3 Step 4, bin width (line 289).** With *u*′ = *u* − Δ′, the perturbed frequency lies in [*u*′, *u*′ + Δ + 2Δ′]. The interval [*u*′, *u*′ + 2Δ] requires Δ′ ≤ Δ/2, which holds for large |ξ| because 4α + 2β > 1, but ξ<sub>0</sub>(*P*) must enforce it. *W*<sub>0</sub> changes by a constant.
2. **Theorem 2.3 Step 1 (line 251).** A point can lie in two closed cylinders, so up to 4(*r* − 1) cylinders contain endpoints, not 2(*r* − 1). Step 2's 2*r* must change accordingly. Before replacing ⌈*q*/*K*⌉ by 2*q*/*K*, justify *K* ≤ *q*; it follows from θ < (1 + ρ)α.
3. **Lemma 2.2(4) (line 219).** At *R* = 1 the strict stopping rule leaves 𝒲(1) empty. The proof uses only *R* > 1, so state *R* > 1.
4. **Theorem 1.1 proof (line 76).** When *e* − *m* < *h*, the perturbation is an integer, and "pole order at least *h* smaller" is false although harmless. Treat that case separately.
5. **Theorem 1.2 (lines 86–90).** The remainder term is *p*<sup>*k*</sup>/(*G* − δ), so impose δ ≤ *G*/2 or fix δ. The actual consecutive selected-arrival gap is (*U* + *j* + 1)<sup>3</sup> − (*U* + *j*)<sup>3</sup>. The printed (*j* + 1)<sup>3</sup> − *j*<sup>3</sup> is its reduction mod 3<sup>*k*</sup>, valid for *a* ≥ *k*; say so. "(because 4·4<sup>7</sup> ≡ 1 (mod 3) kills…)" is vacuous, since every power of 4 is 1 mod 3. Delete it or replace it with an actual derivative computation.
6. **Theorem 3.2 proof (line 426).** |λ<sub>*k*</sub> − λ<sub>*k*−1</sub>| ≤ 1/(*b* − 1) holds only for *k* ≥ 2, since λ<sub>0</sub> = 0. Positivity at *k* = 1 holds anyway. Use 1 + *e*<sub>*k*</sub> in bounds that include *e*<sub>*k*</sub> = 0.
7. **Theorem 2.4(1) (line 320).** The listed constants omit 1/32 for *M* = 30.
8. **"Zero computer certificates" for *M* = 100 (line 315).** The inequality 809<sup>51</sup>·100<sup>520</sup> > 2<sup>19</sup>·500<sup>51</sup>·102<sup>520</sup> is verified by computer (script line 422). Either give a hand-checkable log bound (the margin in the tenth power is about 1.07 in natural log, with Σ ≳ 1.11) or label it as a finite certificate.
9. **§5 (line 467)** says "completely self-contained". Theorems 1.1–1.3, 2.4 and 3.2 rely on internal results from Phases 21–24: Phase 24 eqs. (2) and (4), Phase 24 §3 eq. (6), Phase 23 Lemma 5 and §2 Theorem (A), Phase 21 Prop. D. These are not external, but name them as dependencies with their own review status. I checked Phase 24 eqs. (1)–(2) and Phase 23 Lemma 5 against their sources. Lemma 5, B(*v*) ≥ min{|*z*|, B(*u*)/(2*c*<sup>2</sup>)}, supports the iteration at line 437.
10. **Labels.** The repository assigns exactly one proof label per result (`docs/research-objectives.md`, rule 4). For the registry, map "`Paper proof` + `External input`" to proof label `Paper proof` with the input named in `inputs`. Theorem 1.1 is `Paper proof` in its heading but "`Paper proof` (+ `Finite certificate`)" in the table. Harmonize them.
11. **Rendering.** Raw `|` inside table cells (lines 35, 37) breaks GitHub table rendering. Use `\lvert`/`\rvert` or move the formulas out of the table.
12. **Theorem 3.1 verification scope (line 497).** The verification is exhaustive in *u* only. State the *d*<sub>*z*</sub> ranges: 2 ≤ *d*<sub>*z*</sub> ≤ 11 for *c* = 1, and 2*c* < *d*<sub>*z*</sub> ≤ 2*c* + 9 coprime to *c* for 2 ≤ *c* ≤ 5.

---

## 4. Verified components (adversarial checks that passed)

* **Lemma 2.1(1).** Fourth-moment count 3(*p* − 1)(*p* − 2), recomputed by hand, and the orbit argument giving |*S*| ≤ 3<sup>1/4</sup>*p*<sup>3/4</sup>. Also: gcd extraction *S*(*u*, *v*; *p*<sup>*k*</sup>) = *p*<sup>*r*</sup>*S*(*u*′, *v*′; *p*<sup>*k*−*r*</sup>); the stationary-phase identity with 2(*k* − *m*) ≥ *k*; at most 2 square roots for odd *p* and at most 4 for *p* = 2; and (*k* + 1)/2 ≤ 3*k*/4 for *k* ≥ 2. CRT twisted multiplicativity, with 2<sup>ω(*q*)</sup> ≤ τ(*q*) and the extra factor 2 at *p* = 2, gives (2.1). The float check (max ratio 0.2611) agrees.
* **Lemma 2.1(2)–(3).** The trapezoid majorant has no wraparound (support 3*L* − 1 < *q*). |*B̂*(*u*)| ≤ min(2*L*, *q*<sup>2</sup>/(4*Lu*<sup>2</sup>)). The split sums are 3√2 ≈ 4.243 < 5 and √2π<sup>2</sup>/6 ≈ 2.326 < 5. The axis terms are at most 20τ(*q*). Grouping by gcd is a valid upper bound because Σ<sub>*d*\|*g*</sub> *d*<sup>1/4</sup> ≥ *g*<sup>1/4</sup>. The numerics are ζ(7/4) < 1.9905 (true value about 1.962), 50ζ(7/4) < 100 and 25ζ(3/2) + 20 ≈ 85.3 < 90. The external Weil–Estermann bound τ(*q*)(*u*, *v*, *q*)<sup>1/2</sup>*q*<sup>1/2</sup> is quoted correctly and used only in Regime B.
* **Lemma 2.2.** The rational weights construction is valid. The retained fraction is *M*/(*M* + 1 + *y*) ≥ *M*/(*M* + 2). |*I*<sub>**u**</sub>| ≤ min(*q*<sub>*L*</sub><sup>−2</sup>, φ<sup>−2(*L*−1)</sup>), so the analytic bound holds. φ > 809/500 follows from 5·500<sup>2</sup> > 1118<sup>2</sup>. The tenth-power inequality holds. The block formulas in the script match *q*<sub>4</sub> + *p*<sub>4</sub> = (*a*<sub>1</sub> + 1)*b*<sub>2</sub> + (*a*<sub>1</sub>*b*<sub>1</sub> + *b*<sub>1</sub> + 1)(*a*<sub>2</sub>*b*<sub>2</sub> + 1). Even-length uniqueness, det = +1, *pq*′ ≡ −1 (mod *q*), submultiplicativity, the stopping-set count, the Frostman constant 2*B*<sup>2</sup> + 2, and strong-Markov independence all check.
* **Theorem 2.3: nonlinear *P* and critical points.** The method needs **no** van der Corput or degree-*r* oscillatory-integral estimate. It linearizes *P* ∘ *T*<sub>**a**</sub> at cylinder scale *R*<sub>2</sub><sup>−2</sup> (|*f*″| ≤ (*L*<sub>*P*</sub> + 2*M*<sub>*P*</sub>)*R*<sub>1</sub><sup>−2</sup>), and on surviving cylinders |*P*′| ≥ δ. The product-formula excision is correct for repeated and complex roots, because |*x* − Re ρ| ≤ |*x* − ρ|. The Gallagher/Fejér constant is √(π<sup>2</sup>/2 + π<sup>3</sup>) = 5.995 < 6, which is tight but correct. Summation over 𝒲<sub>2</sub> cancels Δ. The hyperbola-curve argument checks: there are at most *r* components, |*F*<sub>*q*</sub>′| ≤ 2(*M* + 1)·*B*·*L*<sub>*P*</sub>/δ, and the strip width is *W*<sub>0</sub> (subject to minor 1). The Step 5 exponent bookkeeping is verified symbolically: the two exponents are 2α + 2β + 3θ/2 − *s* and 1 − *s* − (1 − ρ)α/2 + θ/2. The thresholds 17/18 and 9/10 follow, and all printed parameter triples satisfy (2.5).
* **Theorem 2.4.** The *L*<sup>2</sup> moment bound uses *h*(*b*<sup>*n*</sup> − *b*<sup>*m*</sup>) ≥ 2<sup>*n*−1</sup> and Σ*nx*<sup>*n*−1</sup> = (1 − *x*)<sup>−2</sup>. ∫Ψ dμ ≤ 1/4. Averaging guarantees a child with *E* < *B*<sub>*m*</sub>, and *B*<sub>*m*</sub> + δ<sub>*m*</sub> < *B*<sub>*m*+1</sub> − δ<sub>*m*</sub>. The limit passage via continuous Ψ<sub>*T*</sub> is valid. Square-subsequence interpolation gives at most 4/*j* (the note says ≤ 6/*j*). The bad-approximability constant 1/(*M* + 2) is correct. *Z* = *x* − ⌊*x* − *S*⌋ has prefix denominators ∏ℓ<sub>*n*</sub>, and integer translation preserves both properties.
* **Theorem 3.1.** The signed canonical appendages are correct in both sign cases, including the exceptional last digit *a*<sub>1</sub> − 1 when *n* = 1 and ε = −1. For *c* ≥ 2, the Lagrange best-approximation bound applied at denominator *cl*<sub>*i*</sub> gives the strict −1. The script's exhaustive check (1 780 + 4 272 folds) agrees.
* **Theorem 3.2(1), (3) and injectivity.** The CRT numerators, exact raw denominators *D*<sub>*k*</sub> = *p*<sup>*e*<sub>*k*</sub></sup>Λ<sub>*e*<sub>*k*</sub></sub>, and the telescoping identity (3.3) check, and Λ<sub>*m*</sub> ≤ 2<sup>*m*/4</sup>. LTE gives *v*<sub>*p*</sub>(*b*<sup>*P*<sub>*k*</sub></sup> − 1) ≤ *a*<sub>0</sub> for power-of-two *P*<sub>*k*</sub>, and the order valuations satisfy *v*<sub>*p*</sub>(ord<sub>*Q*<sub>0</sub><sup>*r*</sup></sub> *b*) = 0. The complete stride period cancels exactly: the *p*-part runs over a nontrivial additive coset of *p*<sup>*A*</sup>ℤ/*p*<sup>*e*(*h*)</sup>ℤ while the *Q*-part stays fixed. The Lemma 5 iteration gives (3.2). Irrationality for every **w** follows from the large-*q* bound, and compactness handles small *q*.
* **Theorems 1.1(1)–(2), 1.2(1), 1.3(1) for gcd(*Q*, *b*) = 1, 1.3(2) under its hypotheses, 1.3(3) sufficiency.** All verified, subject to the qualifications above. The flagship thresholds 2/(3 log 2) ≈ 0.9618 and 1/(2 log 2) ≈ 0.7213 are correct as *sufficient* constants.

---

## 5. Required research-note contents (Phase 25 brief §5, items 1–10)

| # | Item | Status |
| --- | --- | --- |
| 1 | Exact definitions | Present (lines 5–26). Missing: "local discrepancy" (line 64), the baseline and periodicity notion for Theorem 3.2(4), and a definition of "information excludes" in Theorem 1.3 |
| 2 | Precise statements | Present. Theorems 1.1(3), 1.3(1), 2.3 (quantifier on η) and 3.2(4) need restatement (C1, C2, M2, M5) |
| 3 | Complete proofs or explicit missing steps | **Not met** for Theorem 3.2(2) (C3) and the barrier at line 80 (C2). Constants for Theorem 2.3 are implicit (M1, M2) |
| 4 | Prior art | Present (lines 453–459). Corrections needed (M6) |
| 5 | External inputs with hypothesis checks | Present (lines 465–474). Ghidelli start-versus-*N* translation needed (M6) |
| 6 | Evidence labels | Present. Single-proof-label mapping and the `Conditional` tag at line 120 needed (M3, minor 10) |
| 7 | Reproduction instructions | Present (lines 478–484) and working (exit 0) |
| 8 | Exact finite tests | Present, but coverage is overstated (M7) |
| 9 | Open questions | Present (lines 505–511). Questions 1–2 must be updated after C1 and C2 |
| 10 | Objective numbers | Present (table, §8). The Objective-4 claims for Theorem 1.1 must be downgraded (C2) |

---

## 6. Revision checklist (in priority order)

1. **C1.** Replace *Q* by *Q*/gcd(*Q*, *B*<sup>*M*</sup>) in Theorem 1.3(1), or restate it for *QB*<sup>*M*</sup>*X*. Add *b* and *M*, and the *b* = 2, *Q* = 2 equality case, to the verifier.
2. **C2.** Delete the two discrepancy parentheticals in Theorem 1.1(3). Restate the line 80, 508 and 519 barrier as a local, per-packet limitation, or construct a global counter-model.
3. **C3.** Replace the unique-tuple argument with the monic-polynomial valuation argument. Add verifier cases with *p* | C(*r*, *j*).
4. **M1–M2.** Exhibit rational majorants *C̄*(*P*), ξ̄<sub>0</sub>(*P*) and *K̄*<sub>*e*</sub>, and redefine *J*<sub>*e*</sub> = ⌊2<sup>*e*+3</sup>*K̄*<sub>*e*</sub>⌋ + 1. State η = η(*r*, *s*, ρ) with the explicit minimum, and fix the *r* = 1 case.
5. **M3–M5.** Restrict the Theorem 1.3(2) barrier to its depth and envelope hypotheses, and remove "sharp". Fix the abundant-gap quantifier and the tail term at line 136. Correct the *e*<sub>*K*</sub> = *o*(*K*) justification at line 430. Define the baseline and periodicity in Theorem 3.2(4).
6. **M6–M7.** Correct the attributions, and make every §6 sentence match what the code checks.
7. Address the minor items.

*Cross-model review is not independent human peer review.*

---

## Post-Repair Verification

**Audited versions (read-only).** [`notes/phase25/nonlinear-and-badly-approx.md`](../nonlinear-and-badly-approx.md) (663 lines, SHA-256 `3cd8e700…9e37de`) and [`scripts/phase25_nonlinear_approx.py`](../../../scripts/phase25_nonlinear_approx.py) (1 088 lines, SHA-256 `1ce94387…f403c`). Neither file was modified by this verification. **Reviewer:** Claude Opus 5.5, cross-provider post-repair referee. **Cross-model review is not independent human peer review.** It authorizes no benchmark status change and no registry status change.

### Verdict: **ACCEPT**

Zero Critical and zero Major findings remain open. All three Critical findings (C1–C3), all seven Major findings (M1–M7) and all twelve minor items are closed. The independent checks below found no new mathematical error, broken formula or table defect. Four residual editorial nits are listed at the end. None of them blocks acceptance.

### P0. Reproduction

| Check | Result |
| --- | --- |
| `python -B scripts/phase25_nonlinear_approx.py` (Windows host, Python 3.13.13, no WSL, about 9 s) | **exit 0**, final line `All Phase 25 Track F exact finite certificates passed.` |
| F1 barrier | 810 lifts, 10 530 site checks (= 810 × 13 sites), 45 360 aggregate-pair checks (= 810 × 56 pairs with 3 ∤ *v*<sub>1</sub> − *u*<sub>1</sub>), all 512 + 64 words realized, zero-word bounds 47/72 (*L* = 9) and 7/12 (*L* = 6), 68 lag grids, collapse `[1, 2, 4, 11, 31]`. Matches §6 |
| F1 iff and cube drops | *R*<sub>10</sub> = 202802/3 and *Q*′ = 1 regression, 2 322 configurations (1 218 with gcd(*Q*, *B*<sup>*M*</sup>) > 1), drops at 783, 820, 953, 1161, 1268, *e*(1268) = 0, *e*(2186) = 4, first *e* = 6 at *M* = 2187. Matches §6 |
| F2 Kloosterman | 9 prime powers, 367 split-sum checks (maximum ratio 0.4952), 72 trapezoid-majorant checks, exact ζ(7/4) < 2 and ζ(3/2) < 14/5. Float measurements 0.2611 / 0.8493 / 0.4162 over 48 rectangles. Matches §6 |
| F2 block measures | 550 612 / 8 439 / 337 distinct *N*. Ratios 1.018523 / 1.014769 / 1.025743. Majorants for *r* = 1, 2, 3. 10 000 concatenations. 900-child step. Matches §6 |
| F3 | 1 780 + 4 272 folds. 6 literal `Fraction` and 117 *p*-adic depth checks (117 = 3 radices × 3 patterns × (10 monomial + 3 non-monomial)). Matches §6 |

### P1. Critical findings

| ID | Status | Evidence |
| --- | --- | --- |
| **C1** | **Closed** | Theorem 1.3 now defines "consistent with 𝓘" and "𝓘 excludes *QX* ∈ ℤ" explicitly (note line 120). (1.1) uses *Q*′ = *Q*/gcd(*Q*, *B*<sup>*M*</sup>), and *g*<sub>0</sub> = gcd(*Q*′, *p*<sup>*e*−*h*</sup>) = gcd(*Q*, *p*<sup>*e*−*h*</sup>) holds because *p* ∤ *B*. The converse solves *Q*′*N* ≡ −*k* (mod *B*<sub>0</sub>) with *B*<sub>0</sub> = *B*<sup>*M*</sup>/gcd(*Q*, *B*<sup>*M*</sup>) and gcd(*Q*′, *B*<sub>0</sub>) = 1 (line 152). I checked this proof line by line. The *C*<sub>1</sub>(2)<sup>2</sup> example now correctly says 2*X* ∈ ℤ **is** excluded. The script certifies *R*<sub>10</sub> exactly, gives a rigorous rational upper bound *T*<sub>10</sub> < 1/6, and builds the witness *X*′ = 1/2 at *T*<sub>max</sub> = 1/3. **Independent check:** a scratch brute force that never uses *Q*′ computed the true least admissible tail over all lifts and all *N* mod *B*<sup>*M*</sup>, directly from *Q*(*N* + *Ã*/*p*<sup>*e*</sup> + *T*) ≡ 0 (mod *B*<sup>*M*</sup>). It covered 2 180 configurations (*b* ∈ {2, 3, 5, 6, 10}, *p* ∈ {3, 5, 7}, *M* ≤ 3 with *B*<sup>*M*</sup> ≤ 7 000, *e* ≤ 2, ten values of *Q*, 1 312 of them with gcd(*Q*, *B*<sup>*M*</sup>) > 1). It found **0 mismatches** with *r*<sub>min</sub>(*Q*′, *A*<sub>0</sub>, *h*)/(*Q*′*p*<sup>*e*</sup>) |
| **C2** | **Closed** | §0 defines the local *L*-step discrepancy *D*<sub>*L*</sub> and states the universal floor *D*<sub>*L*</sub> ≥ 1/*L*. Both impossible values are gone. For 0<sup>*L*</sup>, the note proves *D*<sub>*L*</sub> ≥ max<sub>*m*</sub>[(*L* − *m* + 1)/*L* − *b*<sup>−*m*</sup>] ≥ 1 − ⌈log<sub>*b*</sub> *L*⌉/*L*. I rechecked 47/72 (*m* = 3) and 7/12 (*m* = 2). For an arbitrary target prefix, it proves \|*D*<sub>*L*</sub>(*y*) − *D*<sub>*L*</sub>(*x*\*)\| ≤ (*m* + 1)/*L*. I re-derived this bound by enlarging and shrinking the interval by 1/*L* and charging the *m* − 1 uncontrolled indices. The barrier is restated as a **local single-packet limitation** (lines 94–96, table line 34, §7 Q2, §8). An explicit scope boundary disclaims any global *D*<sup>+</sup> = 1 or zero-transition counter-model. The unproved arrival-count claims are gone |
| **C3** | **Closed** | Lines 528–552 replace the unique-tuple argument with an exact pure-pole identity (tuple inclusion iff 0 ≤ *i* ≤ *j*, verified), the congruence *p*<sup>*rM*</sup>*T*<sub>*r*</sub><sup>pole</sup> ≡ *t*<sub>*p*</sub><sup>*r*−*j*</sup>*f*<sub>*r*,*j*</sub>(*t*<sub>*p*</sub>) (mod *p*<sup>*M*−*a*<sub>0</sub></sup>), and nonvanishing of the monic *f*<sub>*r*,*j*</sub> at the non-integer rational *t*<sub>*p*</sub> = −*p*/(*p* − 1) by the rational root theorem. The argument is uniform in **w**, since *δ*<sub>*m*</sub> ∈ *p*<sup>−*a*<sub>0</sub></sup>ℤ<sub>*p*</sub> independently of the pattern. It carries the leading coefficient through *v*<sub>*p*</sub>(*γ*<sub>*r*</sub>) and the lower-degree terms through *v*<sub>min</sub>(*P*), with an explicit *M*<sub>0</sub>(*P*, *b*, *p*). By hand I get *f*<sub>3,1</sub>(−3/2) = 3/2, *f*<sub>3,2</sub>(−3/2) = 3/4 and *f*<sub>4,2</sub>(−3/2) = 9/4, so *ν* = 3, 2, 4. These values reproduce every "actual depth" entry of the original C3 table (for example 3·5 − 3 = 12 and 4·5 − 4 = 16). The script confirms them in literal `Fraction` arithmetic at *M* = 4 and in exact *p*-adic arithmetic at *M* = 6, where *M* − *a*<sub>0</sub> = 5 > max *ν* = 4, so the theorem's own threshold holds. The *p*-adic checks cover three patterns and the non-monomial *pX*<sup>3</sup> + 2*X*<sup>2</sup> + *X* |

### P2. Major findings

| ID | Status | Evidence |
| --- | --- | --- |
| **M1** | **Closed** | Step 5 of Theorem 2.3 defines integer thresholds *X*<sub>1</sub>–*X*<sub>5</sub> through the rule *A*\|*ξ*\|<sup>−*γ*</sup> ≤ 1 ⇐ \|*ξ*\| ≥ max(1, ⌈*A*⌉)<sup>⌈1/*γ*⌉</sup>, which I verified. It also defines rational *A*<sub>1</sub>, *A*<sub>2</sub>, *A*<sub>3</sub>, *K*<sub>*A*</sub><sup>(0)</sup> and *K*<sub>*B*</sub><sup>(0)</sup>, and *C̄*(*P*) = max(1 + *ξ̄*<sub>0</sub>, 2(*A*<sub>1</sub> + *A*<sub>2</sub> + *A*<sub>3</sub>)). I re-derived each threshold-to-inequality correspondence (Δ ≤ *u*<sub>min</sub>/2, Δ′ ≤ Δ/2, Δ′ ≤ *u*<sub>min</sub>/4, *S*<sub>0</sub> + 1 ≤ *q*<sup>1+*ρ*</sup>, Δ ≤ *U*), the exponent cancellation to −*m*<sub>*A*</sub> and −*m*<sub>*B*</sub>/2, the log absorption with *ε* = *m*<sub>*B*</sub>/2, and the constant 12 from √*X* ≤ *X*. *K̄*<sub>*e*</sub> = 1 + 2*C̄*(1 + 3/(2*η*))<sup>2</sup> follows from 1 − e<sup>−*x*</sup> ≥ *x*/(1 + *x*) and log 2 > 2/3, which is proved by hand from *e* < 11/4. The note sets *J*<sub>*e*</sub> = ⌊2<sup>*e*+3</sup>*K̄*<sub>*e*</sub>⌋ + 1. The truncation budget (*δ*/4 + *δ*/4), the refinement via *φ* > 8/5, the *S*-truncation and the Machin/Taylor trigonometric budget (6*ε*<sub>trig</sub>*N*<sub>𝓕</sub> ≤ *δ*/6) are all rational and sum correctly. `compute_f2_rational_majorants` implements these formulas literally. The script asserts the integer power inequalities at \|*ξ*\| = *ξ̄*<sub>0</sub> and 2*K̄*<sub>*e*</sub>/*J*<sub>*e*</sub> < 2<sup>−*e*−2</sup> for *r* = 1, 2, 3 |
| **M2** | **Closed** | The note writes *η*<sub>*r*,*s*,*ρ*</sub> with explicit dependence on (*r*, *s*, *ρ*<sub>Klo</sub>) and remarks that the admissible interval collapses at the threshold. The general midpoint solution satisfies all of (2.5); I re-derived each inequality, including 4*α* + 2*β* > 6/5. The three concrete triples and their margins are rechecked by hand and asserted by the script. The case *r* = 1 is separated cleanly (*θ* = 0, *δ* = \|*c*<sub>1</sub>\|, no critical-set term, *A*<sub>1</sub> = 0) |
| **M3** | **Closed** | Theorem 1.3(2) now assumes an explicit envelope *T*<sub>max,*k*</sub> = *H*<sub>ub,*k*</sub>*B*<sup>−*g*<sub>*k*</sub></sup> with *H*<sub>ub,*k*</sub> ≥ 1. It imposes the depth hypothesis on the actual gap starts and makes the Ghidelli application conditional on both *K*<sub>*k*</sub> = *o*(log *M*<sub>*k*</sub>) and *e*<sub>*k*</sub> ∼ *s* log<sub>*p*</sub> *M*<sub>*k*</sub> (line 142 and the Remark). "Sharp" is replaced by "sufficient". In the abundant-gap case each gap must have length > (*s*/log *B* + *ε*) log *N*. The Markov sum is split at 3*N*: distinct right endpoints *r*<sub>*k*</sub> ≤ 2*N* control the head, and the *j* > *N* tail is *O*(*N*<sup>2</sup>*B*<sup>−*N*</sup>). I checked both parts. All three items of (3) carry `Conditional` at the point of use |
| **M4** | **Closed** | Cesàro averaging gives *κ*<sub>*m*+1</sub> − *κ*<sub>*m*</sub> → ∞ ⇒ *κ*<sub>*m*</sub>/*m* → ∞ ⇒ *M* = *e*<sub>*K*</sub> = *o*(*K*) = *o*(log *N*), hence *τp*<sup>*e*(*h*)</sup> = *N*<sup>*o*(1)</sup>. The saturated interval [*r*·2<sup>*κ*<sub>*M*−1</sub></sup>, 2<sup>*κ*<sub>*M*</sub></sup>) of epoch *M* − 1 is handled explicitly with *ν*<sub>*r*,*r*,*p*</sub> = 0 and the factor *p*<sup>1/4</sup>. The transition-sliver proportion is accounted for in the rate. Statement (2) separates "computable at each *N*" from "effective modulus", and claims the latter only when the gaps of *κ* have a computable unbounded lower bound |
| **M5** | **Closed** | The note defines the all-ones baseline **w**<sup>**1**</sup> and the expanded site-by-site sequence *ε*<sub>*n*</sub>(**w**) ∈ {0, 1}. The sites 2<sup>*k*</sup> + *jP*<sub>*k*</sub> + *i* cover every *n* ≥ 3 exactly once. *V*(**w**) − *V*(**w**<sup>**1**</sup>) = Σ *ε*<sub>*n*</sub>*b*<sup>−*n*</sup> is irrational if and only if (*ε*<sub>*n*</sub>) is not eventually periodic. The example (*w*<sub>*k*,1</sub> = 1 + (*k* mod 2)) is correct: zero runs of length ≥ 2<sup>*k*</sup> occur in even shells while ones keep occurring |
| **M6** | **Closed** | Becher–Heiber–Slaman (2015, Math. Comp. 84) is credited for the computable absolutely normal Liouville number. Becher–Bugeaud–Slaman (2016, Proc. AMS) is described as characterizing irrationality exponents "without normality". The blanket "non-effective" claim about Sahlsten–Stevens, Algom–Rodriguez Hertz–Wang and Baker–Banaji is removed. Ghidelli 2020 JLMS (cubic gaps) is separated from arXiv:1910.05076v1 (mild-gap tail) throughout. Turing is dated c. 1938 (unpublished, *Collected Works* 1992). Sierpiński's construction is credited to Becher–Figueira (2002) for its computable reformulation. The start-versus-*N* issue is resolved: the criterion is stated directly in (log *T*<sub>*k*</sub>)<sup>*C*</sup>, without assuming log *n* ≍ log *N* |
| **M7** | **Closed** | Every §6 sentence now matches the code. F1 tests every site and every qualifying pair. The trapezoid, split-sum and zeta certificates are non-vacuous; the maximum split ratio of 0.4952 is a real constraint. The list of 9 prime powers is stated correctly, and the note counts "5 inequalities + 2 derived". The 10 000 concatenations are described as drawn from {1, …, 10}<sup>2</sup> × {1, …, 10}<sup>2</sup>. The martingale step uses the actual 900 certified weights. F3 uses the exact theorem formulas: *m*<sub>*j*</sub> via exact ⌈log<sub>2</sub>⌉ = `(prod - 1).bit_length()` (*m*<sub>1</sub> = 5 at (3, 5)), *P*<sub>*k*</sub> = 2<sup>⌊log<sub>2</sub>(1 + *e*<sub>*k*</sub>)⌋</sup>, and *κ* with gaps 2, 3, 4, 5, 6 |

### P3. Minor findings

| # | Status | Evidence |
| --- | --- | --- |
| m1 | Closed | Δ′ ≤ Δ/2 is enforced by *X*<sub>2</sub>, and the bin [*u*′, *u*′ + 2Δ] is justified (line 349) |
| m2 | Closed | 4(*r* − 1) endpoint cylinders. *K* ≤ *q* follows from *S*<sub>0</sub> + 1 ≤ *q*<sup>1+*ρ*</sup> (*X*<sub>4</sub>) |
| m3 | Closed | 𝓦(*R*) is stated for *R* > 1 |
| m4 | Closed | The cases *e* − *m* < *h* (integer perturbation) and *e* − *m* ≥ *h* are treated separately |
| m5 | Closed | 1 ≤ *δ* ≤ *G*/2 is imposed, giving the remainder 2*p*<sup>*k*</sup>/*G*. The actual gap (*U* + *j* + 1)<sup>3</sup> − (*U* + *j*)<sup>3</sup> and its reduction mod 3<sup>*k*</sup> are stated. The vacuous "4·4<sup>7</sup>" remark is replaced by explicit congruences mod 81 and mod 243. I confirmed 4<sup>9</sup> ≡ 190 = 1 − 54, 4<sup>27</sup> ≡ 82 and 4<sup>7</sup> − 1 ≡ 102 (mod 243), and the script asserts both identities for all *r* mod 27 |
| m6 | Closed | *k* = 1 is handled separately (*d*<sub>1</sub> = 2 + *λ*<sub>1</sub>), and the rate uses 1 + *e*<sub>*k*</sub> |
| m7 | Closed | The note includes 1/32 for *M* = 30 |
| m8 | Closed | The *M* = 100 parameter check is now genuinely by hand. I rechecked every step: *φ* > 8/5, *e* < 261/96 < 11/4, *e*<sup>2/5</sup> < 3/2, the reduction to 2<sup>155</sup> > 3·11<sup>10</sup>·5<sup>51</sup>, and the two Bernoulli factors whose product with 2 equals 3, with strict inequality. The 809/500 form is retained only as an extra exact certificate |
| m9 | Closed | §5 lists the internal Phase 21–24 dependencies with their review status |
| m10 | Closed | Each result has a single proof label, with inputs named separately. Theorem 1.1 is `Paper proof` in both the table and the heading |
| m11 | Closed | Table cells use `\lvert…\rvert` and `\lVert…\rVert`. A scan of every table row for raw `\|` inside math found none. The 162 display delimiters `$$` are balanced |
| m12 | Closed | §6 states the *d*<sub>*z*</sub> ranges for *c* = 1 and for 2 ≤ *c* ≤ 5 |

### P4. New-error sweep

No new mathematical error was found. Beyond the items above, I re-verified the following newly written material:

* The Lemma 2.1 split-sum constants 3√2 and √2π<sup>2</sup>/6, and the ζ tail bounds (Σ<sub>*n*≤5</sub> *n*<sup>−7/4</sup> + (4/3)·5<sup>−3/4</sup> ≈ 1.9906).
* The Theorem 2.4 Lipschitz majorant 16*h*<sub>*e*</sub>*b*<sub>*e*</sub><sup>*j*<sup>2</sup></sup>*M*<sub>*P*<sub>*e*</sub></sub> ≥ 4π*h*<sub>*e*</sub>*b*<sub>*e*</sub><sup>*j*<sup>2</sup>−1</sup>*M*<sub>*P*<sub>*e*</sub></sub>.
* The Theorem 3.2 coefficient range (0, rad(*b*) + 2].
* The injectivity argument for *b* = 2.
* The three-case depth bookkeeping (*M* − *a*<sub>0</sub> > *ν*<sub>*r*,*p*</sub>, *M* > *v*<sub>*p*</sub>(*γ*<sub>*r*</sub>) − *v*<sub>min</sub> + *ν*<sub>*r*,*p*</sub>, *rM* > *v*<sub>*p*</sub>(*γ*<sub>*r*</sub>) + *ν*<sub>*r*,*p*</sub>).

**Residual editorial nits (non-blocking, optional):**

1. §6, F1 item: *T*<sub>*M*+*K*</sub> = 1/(7*B*<sup>4</sup>) is a **synthetic** positive tail, not the true tail of *C*<sub>*s*</sub>(*d*)<sup>*d*</sup>. This is legitimate, because Theorem 1.1(3) holds for any fixed tail. Saying "synthetic" would prevent misreading.
2. The F2 "900-child martingale step" uses the real certified weights but synthetic child expectations. §6 accurately calls it "averaging algebra", but the script's console string ("martingale step verified") is slightly stronger than that.
3. Theorem 3.2(4) proof, line 574: "for every integer base *b* ≥ 2" should read "in the fixed base *b*".
4. The C1 iff verifier derives exclusion through the *Q*′ coset, not by an independent search over *N*. The independent brute force above closes this gap externally. The repository script could optionally add a small-*B*<sup>*M*</sup> direct search.

### P5. Scope statement

This post-repair verification establishes only that the audited note and script, at the hashes above, close the findings of this report. It is a cross-model review. **Cross-model review is not independent human peer review.** It does not establish peer-reviewed status, and it authorizes **no** change to any benchmark status in `docs/benchmarks/` or to any registry entry. Finite computations in the verifier remain `Finite certificate` evidence only. Nothing was committed.

*Cross-model review is not independent human peer review.*
