# Phase 26 Stage 0.2 — Independent Deep Analytic Audit I (`GF-42`)

**Audited material.**
- [`notes/phase25/generalized-lambert-and-eplus.md`](../../phase25/generalized-lambert-and-eplus.md) (927 lines; "the note").
- [`scripts/phase25_lambert_eplus.py`](../../../scripts/phase25_lambert_eplus.py) (1,701 lines).
- The `GF-42` entry of [`docs/registry/GF.toml`](../../../docs/registry/GF.toml) (lines 749–760), in its uncommitted Stage 0.1 form. That form already synchronizes the "*k* ≥ *k*<sub>0</sub>" wording and the B2.1 hypothesis text.
- [`notes/phase25/reviews/track-b-review.md`](../../phase25/reviews/track-b-review.md), read only for context. Every argument below was reconstructed independently from the note.

**Reviewer.** Claude `claude-opus-5-5`, acting as an audit sub-agent on branch `research/phase-26-arithmetic-amplification`, 2026-11-28.

**Method.** The audit was read-only, and this report is the only file written. Nothing was committed and WSL was not used. Python ran directly on Windows (`python -B`). Ad-hoc checks used stdin heredocs or `-c` and left no files in the repository.

> **Cross-model review is not independent human peer review.** This report is a machine reading by a language model. It does not replace refereeing by human specialists in sieve theory, multiplicative number theory or uniform distribution. Nothing in it may be used to change the status of any benchmark constant (`BC-01`…`BC-50`) or of any arithmetic-family benchmark.

**Note on labels.** The brief calls the fixed-window signed carry-cancellation barrier for *E*<sub>+</sub>(4) "Theorem B3.1". In the note this barrier is **Theorem B4.1**, and Theorem B3.1 is the *Universal Transducer Obstruction*. Registry item (3) of `GF-42` combines the two, so both are audited here (§7).

---

## Verdict: **VALIDATED WITH SCOPE/TEXT REFINEMENTS**

| Severity | Count | Nature |
|---|---|---|
| Critical | 0 | — |
| Major | 1 | Registry fidelity: the `inputs` field omits the principal analytic external theorems. This is a record-level error, not a mathematical gap. |
| Minor | 15 | Scope disclosure, definitional slips in the signed case, wording, and evidence labelling. |

The audit tried to invalidate every step, and none of the headline mathematics failed:

- **Lemma B1.2.** Exact displaced carry conservation, the dead-block run inequality and the universal exit-discrepancy bound all hold. A random falsification sweep of the exit bound over 3,000 rational orbits found 0 violations and 15 cases of equality.
- **Theorem B1.3.** The good-source sieve, the sharp second moment, Paley–Zygmund and the order of limits all hold. All four boundary applications at *k* = 2 are valid.
- **Theorem B1.4.** It holds as a statement for *sufficiently large k*. The constant *k*<sub>0</sub> its proof produces is astronomically large, above 3 × 10<sup>10</sup> (§4.4).
- **Theorem B2.1.** Both the (log *k*)/*k* rate and the *k*<sup>−1/2</sup> rate hold. The rate for general gcd can in fact be sharpened to (log *k*)/*k* (m10).
- **Theorems B3.1 and B4.1.** Both barriers hold as stated, with one overstatement in the prose (m6).
- **Theorems B5.2–B5.3.** The Fermat-product and odd-order coset extensions hold, and both moduli lists are reproduced exactly.

### Can *k*<sub>0</sub> be reduced? (Details in §4.4)

1. **Is *k*<sub>0</sub> explicit?** It is effective in principle, but not with its current parameters. The recipe is *k*<sub>0</sub> = ⌈800(2*B*<sub>0</sub> + 1)⌉ with *B*<sub>0</sub> ≥ ⌊1/η⌋ and η ≤ ε/32 < 1/(32 · 320<sup>2</sup>(*M*<sub>2</sub> + 1)). With *M*<sub>2</sub> = E[*U*<sub>+</sub><sup>2</sup>] ≈ 4.819 (independently computed), this gives *B*<sub>0</sub> > 1.9 × 10<sup>7</sup> and ***k*<sub>0</sub> > 3.05 × 10<sup>10</sup>**. Even if *B*<sub>0</sub> were 0, the recipe's fixed constants (*j*<sub>0</sub> = 9, thresholds 1/40, factor 80) would force *k*<sub>0</sub> ≥ 800.
2. **The precise obstruction.** Theorem B1.3 controls *V*(*m* + *d*) − *V*(*m*) only up to a bounded perturbation β ∈ [−*B*<sub>0</sub>, *B*<sub>0</sub>]. This perturbation comes from the primes ≤ *p*<sub>1</sub> and from the at most 1/η prime factors larger than *M*<sup>η</sup>. B1.3 absorbs β by smoothing over windows of width *G* ≫ *B*<sub>0</sub>. An isolated odd arrival, by contrast, is an exact-lag event, so the proof must take a union bound over β. That union bound multiplies the collision count by 2*B*<sub>0</sub> + 1.
3. **E<sub>+</sub>(8) cannot be reached by tuning the present proof.** Keep the note's per-position Markov step, but grant it every idealization: sharp collision constants and zero bad-source mass. The first-moment margin is then still negative at *k* = 3 (−0.305) and *k* = 4 (−0.106), and turns positive only at *k* = 5 (+0.035).
4. **E<sub>+</sub>(8) would follow from two new sharp upper-bound inputs.** The first is a sharp-constant exact-lag pair correlation for the landing process {*km* − *V*<sub>+</sub>(*m*)}, carrying the marks |*U*<sub>+</sub>|. The second is a source-conditioned far-tail first moment. With both, the first-moment threshold becomes *k*\* = (2 + Λ)δ ≈ 2.7204, where δ = 3/4 and Λ = *C*<sub>*U*,+</sub>/δ. Then *k* = 3 passes with margin 0.0932 per source, which tolerates at most an 18.6% loss on the collision term.
   - Both inputs are *upper* bounds, so the collision *lower*-bound barrier of `GF-36` §10 does not block them.
   - They do require joint control of the large-prime counts of *m* and *m* + *d* inside the sifted progressions. The Fundamental Lemma does not provide this control.
   - Neither the note nor this audit supplies these inputs.
5. **E<sub>+</sub>(4) is out of reach of this architecture.** At *k* = 2 every first-moment version of the isolated-odd-arrival method fails, with margin −0.36. Lower-bound or Poisson-approximation information would be needed.
6. **Cubic L<sub>±</sub>: same situation.** The note certifies neither δ<sub>±</sub> nor *C*<sub>*U*,χ</sub>, so as written *k*<sub>0</sub>(χ) is likewise ≫ 10<sup>10</sup>. *Heuristic* sharp-first-moment thresholds computed in this audit are:

   | Modulus | *L*<sub>+</sub> | *L*<sub>−</sub> |
   |---|---|---|
   | 7 | 2.26 | 1.51 |
   | 9 | 2.41 | 1.61 |
   | 13 | 2.34 | 1.56 |

   So *k* = 3 for *L*<sub>+</sub> and *k* = 2 for *L*<sub>−</sub> would fall within reach of the same two hypothetical inputs. These thresholds are heuristics, not results.

---

## 1. Reproduction and independent recomputation

### 1.1 Verifier run

`python -B scripts/phase25_lambert_eplus.py`, run from the worktree root on Windows:

```
ALL CHECKS PASSED in 3.98s: 186,311 [exact], 2,428 [encl], 27 [finite] (total 188,766).
```

The exit code was 0 and wall time was 4.1 s. The counts match note line 3, §7, and the registry `scope` field.

### 1.2 Independent recomputation

The following values were recomputed with fresh code that does not reuse the script. Floating-point arithmetic was used only as a cross-check of the certified intervals.

| Quantity | Note's certified interval | Independent value | Status |
|---|---|---|---|
| *L*<sub>2</sub><sup>odd</sup> | [1.480492, 1.480493] | 1.4804922 | ✓ |
| *L*<sub>2</sub><sup>+</sup> | [0.870123, 0.870124] | 0.8701231 | ✓ |
| *C*<sub>*U*,odd</sub> | [1.402443, 1.402514] | 1.402456 | ✓ |
| *C*<sub>*U*</sub> | [2.076306, 2.076411] | 2.076325 | ✓ |
| *C*<sub>*U*,+</sub> | [1.220298, 1.220360] | 1.220309 | ✓ |
| *C*<sub>*U*</sub><sup>(3)</sup>, *C*<sub>*U*</sub><sup>(5)</sup>, *C*<sub>*U*</sub><sup>(6)</sup> | as tabulated | 1.740230, 1.940566, 1.175440 | ✓ |
| *C*<sub>*U*</sub>(1/2), *C*<sub>*U*,odd</sub>(1/2), *C*<sub>*U*,+</sub>(1/2) | as tabulated | 1.316621, 1.133649, 0.895980 | ✓ |
| *L*<sub>3</sub><sup>odd</sup>: direct sum vs dyadic closed form | identity | 1.19313252901476 for both | ✓ |
| *M*<sub>2</sub> = E[*U*<sub>+</sub><sup>2</sup>] | finite (not evaluated in the note) | ≈ 4.819 (2-adic factor 1.38101) | ✓ finite; value needed for an explicit *k*<sub>0</sub> |
| *C*<sub>*U*</sub> for τ<sub>4</sub>, τ<sub>8</sub> in base 2 | [9.42224, 9.43286], [440.500, 444.397] | 9.42325, 440.704 | ✓ |
| *C*<sub>*U*</sub> for τ<sub>3</sub>, τ<sub>5</sub>, τ<sub>7</sub> in bases 3, 5, 7 | as tabulated | 3.65181, 13.51987, 66.18960 | ✓ |
| B2 table: all 56 nonzero entries, plus the zeros | as tabulated | identical after flooring to 4 decimals, using certified upper endpoints of *C*<sub>*U*</sub>(*s*) | ✓ |
| 148× improvement at *k* = 64 | 148× | 0.7769/0.00524 = 148.26 | ✓ |
| *E*<sub>+</sub>(32) in base 32, *s* = 1/2 | ub 0.432658 < 0.447125 ≤ unif | 0.432657 < 0.447126 | ✓ |
| Corollary B2.2 thresholds at *s* = 1 | *k* ≥ 6 (*E*<sub>+</sub>), 6 (*E*<sub>odd</sub>), 5 (*E*\*), 9 (*E*) | identical | ✓ |
| Moduli 2 ≤ *M* ≤ 257 with φ(*M*) = 2<sup>*t*</sup> | 37 values, as listed | 37 values, identical | ✓ |
| Moduli *M* ≤ 100 with odd(λ(*M*)) ∣ 3 | 50 values; first excluded 11, 19, 22, 23, 25, 27, 29, 31 | identical | ✓ |
| Theorem B1.4 cutoff *j*<sub>0</sub> = ⌈log<sub>2</sub>(320 *C*<sub>*U*,+</sub>)⌉ | 9 | 320 · 1.2203 = 390.5, so *j*<sub>0</sub> = 9 | ✓ |
| *E*<sub>+</sub>(*q*) = *E*(*q*) − 2*E*(*q*<sup>2</sup>) (used in §4.5) | — | holds termwise, since 1/(*x* + 1) = 1/(*x* − 1) − 2/(*x*<sup>2</sup> − 1) | ✓ |

The script's local-factor tails, the prime tail Σ<sub>*p*>*P*</sub> *p*<sup>−2</sup> < 1/(2(*P* − 1)) and the bound *e*<sup>*t*</sup> ≤ (1 − *t*)<sup>−1</sup> were each rederived and are valid. The same holds for the bound *L*<sub>*p*</sub><sup>odd</sup>(1/2) − 1 ≤ (2*p* − 1)/(2*p*<sup>2</sup>(*p* − 1)) ≤ 5/(4*p*<sup>2</sup>), which holds with equality at *p* = 3.

---

## 2. Lemma B1.2 and Corollary B1.2a (zero external inputs)

**(1) Carry identity.** Write *b*<sup>*n*</sup>*F* = *A*<sub>*n*</sub> + *Y*<sub>*n*</sub> with *A*<sub>*n*</sub> an integer and *Y*<sub>*n*</sub> = Σ<sub>*j*≥1</sub> *C*<sub>*k*</sub>(*n* + *j*) *b*<sup>−*j*</sup>. Then ⌊*b*<sup>*n*</sup>*F*⌋ = *A*<sub>*n*</sub> + *q*<sub>*n*</sub>. Combined with *d*<sub>*n*</sub> = ⌊*b*<sup>*n*</sup>*F*⌋ − *b*⌊*b*<sup>*n*−1</sup>*F*⌋ and *A*<sub>*n*</sub> − *bA*<sub>*n*−1</sub> = *C*<sub>*k*</sub>(*n*), this gives *C*<sub>*k*</sub>(*n*) + *q*<sub>*n*</sub> = *d*<sub>*n*</sub> + *b q*<sub>*n*−1</sub>.
- The tail bound *q*<sub>*N*</sub> ≤ Σ<sub>*m*>*N*/*k*</sub> *a*(*m*) *b*<sup>*N*−*km*</sup> = *O*(*N*<sup>ε</sup>) holds.
- The extra sources with *m* ∈ (*N*/*k*, *N*/*k* + *O*(log *N*)] contribute *o*(*N*), so the mean arrival rate is *C*<sub>*U*</sub>/*k*.

**(2) Dead positions.** The quantity *d*<sub>*n*</sub> + (*b* − 1)*q*<sub>*n*−1</sub> = *C*<sub>*k*</sub>(*n*) + *q*<sub>*n*</sub> − *q*<sub>*n*−1</sub> is nonnegative, and it vanishes exactly on the dead set 𝒟<sub>*N*</sub>.
- Nonnegativity of *C*<sub>*k*</sub> and *q* forces *C*<sub>*k*</sub>(*n*) = *q*<sub>*n*</sub> = 0 on 𝒟<sub>*N*</sub>, and exits from 𝒟<sub>*N*</sub> are (0, nonzero) transitions.
- The run-counting inequality follows from |*R*| = (*G* − 1) + #(empty *G*-windows inside *R*) for runs with |*R*| ≥ *G*, and #runs ≤ #exits + 1.
- **Nonnegativity is used essentially here, so the lemma does not apply to signed series** (see §4).

**(3) Exit-discrepancy bound.** Let *S* = {1 ≤ *n* < *N* : *d*<sub>*n*</sub> = 0, *d*<sub>*n*+1</sub> ≠ 0}, *M* = |*S*| and δ = (*b* − 1)/*b*<sup>2</sup>. The claim is *D*<sub>*N*</sub>(*x*; *b*) ≤ 1 − min(δ, *M*/*N*).
- The pairs {*n* − 1, *n*} with *n* ∈ *S* are pairwise disjoint.
- For each such pair, *y*<sub>*n*−1</sub> lies in [1/*b*<sup>2</sup>, 1/*b*), so the gap *y*<sub>*n*</sub> − *y*<sub>*n*−1</sub> = (*b* − 1)*y*<sub>*n*−1</sub> lies in [δ, 1 − 1/*b*), and 1 − 1/*b* < 1 − δ.
- The four-case interval analysis, including the wrap-around exclusion, is correct for every real *x*, every *b* ≥ 2 and every *N* ≥ 2.
- *Falsification sweep.* 3,000 random rationals *p*/*q* with gcd(*q*, *b*) = 1, *b* ∈ {2, 3, 4, 10} and *N* ≤ 60 were tested, with exact *D*<sub>*N*</sub> computed in `Fraction` arithmetic. There were **0 violations and 15 cases of equality**, so the bound is sharp.

**Corollary B1.2a.** The double count with *J*(*a*), Turán–Kubilius and *G* = *C*<sub>0</sub>√(log log *M*) gives #empty *G*-windows ≤ 16*kM*/*C*<sub>0</sub><sup>2</sup> + *O*(log log *N*), and the conclusion follows. Two small textual points are recorded as m5:
- an off-by-one: |*V* − μ| ≥ *G*/4 − 1 is what the argument gives;
- zeros *a*(*m*) = 0 are handled only implicitly. They have *V*(*m*) = 0, and with α > 0 the Turán–Kubilius hypothesis counts them as deviant automatically, but the text says that every *m* ∈ *J*(*a*) "must land outside the window", which is false for zeros.

---

## 3. Theorem B1.3 (sharp second moment, Paley–Zygmund, *k* = 2 boundary)

### 3.1 Reconstruction

**Step 1 (good sources).** The three exceptional sets each have density at most ε/4:
- *p*<sup>2</sup> ∣ *m* for some *p* > *p*<sub>1</sub>: density at most Σ<sub>*p*>*p*<sub>1</sub></sub> *p*<sup>−2</sup> < 1/*p*<sub>1</sub>;
- *V*<sub>≤*p*<sub>1</sub></sub>(*m*) > *K*<sub>0</sub>: small because this valuation is finite almost surely under the *p*-adic product measure;
- *u*(*m*) > *M*<sup>1/8</sup>: density at most 8η + *o*(1), by Mertens' first theorem and Markov's inequality.

On the good set, *V* = α ω<sub>(*p*<sub>1</sub>, *M*<sup>η</sup>]</sub> + *V*<sub>bdd</sub>, where 0 ≤ *V*<sub>bdd</sub> ≤ *K*<sub>0</sub> + α⌊1/η⌋ = *B*<sub>0</sub>. This decomposition uses *p*<sub>1</sub> ≥ *p*<sub>0</sub> and the fact that good *m* have no square factors above *p*<sub>1</sub>. ✓

**Step 2 (second moment and tail).** Σ<sub>*a*</sub> *Z*<sub>*a*</sub><sup>2</sup> = Σ<sub>*m*,*m*′</sub> (*G* − |*x*′ − *x*|)<sub>+</sub>. For *d* > *D*<sub>0</sub>:
- the window condition forces ω(*n*) > 10*L*;
- 4<sup>ω</sup> ≤ τ<sub>4</sub> gives 2<sup>−10*L*</sup> *M* (log *M*)<sup>3</sup> = *o*(*M*), since 10 ln 2 > 3. ✓

**Step 3 (sieve).**
- *Cancellation at d.* Primes *p* ∣ *d* in (*p*<sub>1</sub>, *M*<sup>η</sup>] cancel exactly from ω(*m* + *d*) − ω(*m*).
- *Coprimality.* gcd(*u*<sub>1</sub>, *u*<sub>2</sub>) = 1, because gcd(*m*, *m* + *d*) ∣ *d*.
- *Progression and density.* One progression modulo *u*<sub>1</sub>*u*<sub>2</sub>, with *g*(*p*) = 2/*p* on the primes being sifted.
- *Remainder.* |*r*<sub>*q*</sub>| ≤ 2<sup>ω(*q*)</sup>, and the total remainder is *O*(*M*<sup>5/8</sup>(log *M*)<sup>2</sup> *L*) = *o*(*M*).
- *Main term.* The main term equals the trinomial probability exactly, and extending to all pairs (*u*<sub>1</sub>, *u*<sub>2</sub>) is legitimate because every term is nonnegative.
- *Perturbation.* The substitution (*G* − |…|)<sub>+</sub> ≤ (*G*′ − |…|)<sub>+</sub> with *G*′ = *G* + *B*<sub>0</sub> is harmless **because the weight is smoothed over a window of width *G* ≫ *B*<sub>0</sub>**. This is the exact point that does not carry over to B1.4 (§4.4). ✓

**Step 4 (local bound).**
- *Tilted Fourier inversion.* The moment generating function is 1 + 2(cosh *z* − 1)/*p*.
- *Modulus bound.* Rederivation gives *a*<sup>2</sup> + *b*<sup>2</sup> = (4/*p*<sup>2</sup>)(cosh λ − cos *t*)<sup>2</sup> ≤ 16 cosh<sup>2</sup>λ/*p*<sup>2</sup>, and √((1 + *a*)<sup>2</sup> + *b*<sup>2</sup>) ≤ exp(*a* + (*a*<sup>2</sup> + *b*<sup>2</sup>)/2).
- *Bessel bound.* *e*<sup>−*A*</sup>*I*<sub>0</sub>(*A*) ≤ (1 + *O*(1/*A*))/√(2π*A*).
- *Ranges.* With λ = *h*/(2*E*<sub>*d*</sub>) the error is *O*(*E*<sup>−1/3</sup>) for *h* ≤ *E*<sup>2/3</sup>; beyond that, decay is *e*<sup>−*E*<sup>1/3</sup>/5</sup>.
- *Riemann sum.* The sum with step *k*/α, including its *d*′ = 1 boundary term, is legitimate by monotonicity.
- *Small d.* Shifts *d* ≤ *d*<sub>0</sub> = ⌊*G*′/*k*⌋ cost *O*(*G*′<sup>3</sup>/(*k*√*E*)) = *o*(1).
- *Uniformity.* *E*<sub>max</sub>/*E*<sub>min</sub> → 1, because Σ<sub>*p*∣*d*, *p*>*p*<sub>1</sub></sub> 1/*p* = *O*(log log log *L*) for *d* = *O*(*L*). ✓

**Paley–Zygmund.** Write E*Z* = (*G*/*k*)(1 − ε) and E*Z*<sup>2</sup> ≤ *G*/*k* + (1 + ε)<sup>4</sup>(*G* + *B*<sub>0</sub>)<sup>2</sup>/*k*<sup>2</sup>. With *k*/*G* < ε and *B*<sub>0</sub>/*G* < ε, the fraction of windows with *Z*<sub>*a*</sub> > 0 is at least (1 − ε)<sup>2</sup>/(ε + (1 + ε)<sup>6</sup>) = 1 − *O*(ε). Because all *U* ≥ 0 there is no cancellation, so *Z*<sub>*a*</sub> > 0 forces a nonzero *C*<sub>*k*</sub> in the window. #empty<sub>*G*</sub> is nonincreasing in *G*, so the limit in assertion (1) exists. ✓

**Sharp-constant remark.** The remark is correct: a non-sharp constant *C* would require *C* < *k*/*C*<sub>*U*</sub>, which is about 1.426 for *E*<sub>odd</sub>(4) and 2 for *E*\*(4).

### 3.2 Order of limits

The order used in the note is correct and contains no hidden uniformity in *N*:
1. fix ε, which fixes *p*<sub>1</sub>, *K*<sub>0</sub>, η and *B*<sub>0</sub>;
2. fix *G* ≥ *G*(ε), subject to *B*<sub>0</sub>/*G*, *k*/*G* and α*G*′/*G*′<sup>2</sup> all being less than ε;
3. let *N* → ∞ with *M* = ⌊*N*/*k*⌋;
4. let *G* → ∞;
5. let ε → 0.

The constraints on *G* are lower bounds only, so every *G* ≥ *G*(ε) works.

### 3.3 Applications at the *k* = 2 boundary and elsewhere

| Family | *a*(*m*) ≥ 1 | *V* additive, *V*(*p*) = α for *p* > *p*<sub>0</sub> | *km* − *V*(*m*) ≥ 1 | *k* > *C*<sub>*U*</sub> | Verdict |
|---|---|---|---|---|---|
| *E*<sub>odd</sub>(4) | ✓ | ✓ (α = 1, *p* > 2) | ✓ | 1.402514 < 2 | ✓ *D*<sup>+</sup> < 1, ∉ *K*<sub>2</sub> |
| *E*\*(4) | ✓ | ✓ (*V* = ω, *U* = 1) | ✓ | 1 < 2 | ✓ |
| *E*<sub>*b*</sub>\*(*b*<sup>2</sup>), every *b* ≥ 2 (composite *b* included) | ✓ | ✓ (*V* = ω, *U* = 1) | ✓ | 1 < 2 | ✓ *D*<sup>+</sup> < 1 in base *b*, ∉ *K*<sub>*b*</sub> |
| *E*(2<sup>*k*</sup>), *k* ≥ 3 | ✓ | ✓ | ✓ | 2.0764 < 3 | ✓ |
| *A*<sub>*r*,*M*</sub>(4), *M* = 3, 5 or even Fermat-product *M* | via *E*<sup>(*M*)</sup> | ✓ | ✓ | 1.7403, 1.9406, ≤ 1.4025 | ✓ |
| τ<sub>4</sub>, τ<sub>8</sub>, τ<sub>3</sub>, τ<sub>5</sub>, τ<sub>7</sub> thresholds (*k* ≥ 10, 445, 4, 14, 67) | ✓ | α = 2, 3, 1, 1, 1 | ✓ | from the certified upper endpoints | ✓ |

*D*<sup>−</sup> > 0 is not proved in this note:
- for *k* ≥ 3 it is inherited from `GF-36`(1), using *D*<sup>−</sup> ≥ 1/2 − lim sup *f*<sub>1</sub>;
- for *E*<sub>*b*</sub>\* it is inherited from the `GF-36` table.

The *k* = 2 claims are correctly limited to *D*<sup>+</sup> < 1 and ∉ *K*<sub>2</sub>.

**Theorem B1.5** was rechecked. *M*<sub>2<sup>*j*</sup></sub> ⊆ *M*<sub>2</sub> = *K*<sub>2</sub>, and blocks of density 1 carry the periodic digits because *R*/(2<sup>*j*</sup> − 1) is never a *j*-bit dyadic point. The phase-restricted mean *C*<sub>*U*</sub>/*k* follows from Halász applied on primes *p* ≡ 1 (mod *j*). The circulant system has the unique solution *x*<sub>*r*</sub> = *c* − *z*<sub>*r*</sub>, and max *z*<sub>*r*</sub> ≥ 2<sup>*j*−1</sup>/(2<sup>*j*</sup> − 1). All five applications are correct:
- *E*(16) passes at 0.519103 < 8/15 but correctly fails against 16/31;
- *E*\*(4) passes because 1/2 < 2<sup>*j*−1</sup>/(2<sup>*j*</sup> − 1) strictly.

---

## 4. Theorem B1.4 (signed isolated odd arrivals)

### 4.1 Part (1): the lemma

Write 2<sup>*n*−1</sup>*x* = *I* + (*C*<sub>*k*</sub>(*n*) + *Y*<sub>*n*</sub>)/2 with *I* an integer. If *C*<sub>*k*</sub>(*n*) is odd and |*Y*<sub>*n*</sub>| < 1/2, then the fractional part lies in (1/4, 3/4), which forces (*d*<sub>*n*</sub>, *d*<sub>*n*+1</sub>) ∈ {01, 10}. ✓

The strict inequality is needed: *C* = 1 with *Y* = +1/2 gives fractional part 3/4, which corresponds to digits 11 and no transition. No source of *E*<sub>+</sub>(2<sup>*k*</sup>) lands at a column *n* ≤ 0, because *V*<sub>+</sub>(*m*) ≤ log<sub>2</sub> *m* < *km*.

### 4.2 Part (2): ledger of the proof

Fix ε < min(1/40, 1/(320<sup>2</sup>(*M*<sub>2</sub> + 1))). With *M*<sub>2</sub> ≈ 4.819 this means ε < 1.68 × 10<sup>−6</sup>. Then:

| Loss term | Bound in the note | Audit |
|---|---|---|
| Good-support sources | \|𝒢<sub>+</sub>\| ≥ (3/4 − ε)*M* | ✓ only if 𝒢 is defined with \|*a*(*m*)\| ≥ 1. Line 235 literally requires *a*(*m*) ≥ 1, which excludes every 4 ∣ *m* because *a*<sub>+</sub> < 0 there (**m2**). |
| Positions hit directly by bad sources | ε*M* + *O*(log *M*) | ✓, but **omitted from the final count** on line 378 (**m3**; numerically harmless) |
| Bad-source tail mass *Y*<sup>bad</sup> | Σ ≤ η<sub>1</sub>*M* with η<sub>1</sub> = √(ε*M*<sub>2</sub>) < 1/320 (Cauchy–Schwarz); Markov at 1/8 gives at most *M*/40 | ✓ |
| Far good tail (*j* > *j*<sub>0</sub> = 9) | Σ ≤ 2<sup>−9</sup>*C*<sub>*U*,+</sub>*M* < *M*/320; Markov at 1/8 gives 8 · 2<sup>−9</sup> · 1.22036 *M* = 0.01907*M* < *M*/40 | ✓ |
| Sources *m* > *M* | *o*(*M*) positions | ✓ |
| Near collisions (0 ≤ *j* ≤ 9) | ((1 + ε)<sup>2</sup>(*j*<sub>0</sub> + 1)(2*B*<sub>0</sub> + 1)/*k*) *M* | ✓: per sign and per *j*, Σ<sub>*d*</sub> Pr(*S*<sub>*d*</sub> = *kd* − *c*) ≈ 1/(2*k*) for every *c*, multiplied by 2*B*<sub>0</sub> + 1 values of β |
| Conclusion | (3/4 − ε − 3/40 − *o*(1))*M* > *M*/2 for *k* ≥ 800(2*B*<sub>0</sub> + 1) | ✓ after m2 and m3: (3/4 − 2ε − 3/40)*M* ≥ 0.675*M*, so lim inf tr<sub>*N*</sub>/*N* ≥ 1/(2*k*) |

Distinct isolated sources occupy distinct columns, and each excluded column removes at most one source, so subtracting position counts from source counts is legitimate. *D*<sup>+</sup> < 1 then follows, because transitions alternate 01/10, so the (0, 1) exits have density at least about 1/(4*k*), and Lemma B1.2(3) applies. *D*<sup>−</sup> > 0 comes from `GF-40`/`GF-44`.

**Part (2) is valid for *k* ≥ *k*<sub>0</sub>.**

### 4.3 Part (3): cubic *L*<sub>±</sub>(2<sup>*k*</sup>)

The reduction is sound:
- the sieve runs over split primes only, at dimension κ = 2/3;
- E[*U*<sub>χ</sub><sup>2</sup>] < ∞, since the local factor is 1 + 8/*p*<sup>2</sup> + …;
- the 1-bit shift from ε<sub>+</sub> = ±2 is absorbed into *B*<sub>0</sub> + 1;
- the tail estimate for *d* > *D*<sub>0</sub> still forces ω(*n*) > 10*L*.

One point needs adding (m4a). The unscaled 1/40 thresholds remain sufficient for every cubic χ, because δ<sub>+</sub> ≥ ∏<sub>*p*</sub>(1 − *p*<sup>−2</sup>) = 6/π² ≈ 0.608 and δ<sub>−</sub> = (2/3)δ<sub>+</sub> ≥ 0.405. Hence δ<sub>±</sub> − 3/40 − 2ε > δ<sub>±</sub>/2, and the claimed lim inf tr<sub>*N*</sub>/*N* ≥ δ<sub>±</sub>/(2*k*) does follow. The note should say this explicitly, and should also give ε and η<sub>1</sub> relative to E[*U*<sub>χ</sub><sup>2</sup>].

The equidistribution δ<sub>−</sub> = (2/3)δ<sub>+</sub> requires Halász, as the note says. The sign pattern of *c*<sub>±</sub> over the six units was checked by hand: *c*<sub>−</sub> = 0 exactly when ζ = ±1.

### 4.4 Can *k*<sub>0</sub> be reduced? Explicitness, obstruction and thresholds

**(a) The recipe as written.** *k*<sub>0</sub> = ⌈80(*j*<sub>0</sub> + 1)(2*B*<sub>0</sub> + 1)⌉ with *B*<sub>0</sub> = *K*<sub>0</sub> + ⌊1/η⌋.
- The constraint η ≤ ε/32 (needed so that the exceptional set *u*(*m*) > *M*<sup>1/8</sup> has density at most ε/4) is the binding one.
- With ε < 1/(320<sup>2</sup>(*M*<sub>2</sub> + 1)) = 1.678 × 10<sup>−6</sup>, this gives *B*<sub>0</sub> ≥ 1.907 × 10<sup>7</sup> and **k<sub>0</sub> ≥ 3.05 × 10<sup>10</sup>**.
- *K*<sub>0</sub> is negligible by comparison: a Poisson-type tail at level 10<sup>−6</sup> needs *K*<sub>0</sub> of about 15.
- The fixed parts of the recipe alone force *k*<sub>0</sub> ≥ 800 even if *B*<sub>0</sub> = 0, and ≥ 2,400 if *B*<sub>0</sub> = 1.

*k*<sub>0</sub> is **effective in principle**. Computing it requires:
- an explicit Fundamental Lemma error constant at *s* = 3/(8η), since Halberstam–Richert's constants are effective but not stated numerically;
- an explicit *K*<sub>0</sub>;
- a certified *M*<sub>2</sub>, which the script does not certify.

The phrase "effective (but unspecified) *k*<sub>0</sub> ≥ 3" is therefore true but uninformative (**m1**).

**(b) The exact obstruction.** The proof never needs a lower bound. The obstruction is the **loss of sharpness at exact lags**.
- In B1.3, the perturbation β = *V*<sub>bdd</sub>(*m* + *d*) − *V*<sub>bdd</sub>(*m*) ∈ [−*B*<sub>0</sub>, *B*<sub>0</sub>] is absorbed because the window weight (*G* − |…|)<sub>+</sub> varies by a factor 1 + *O*(*B*<sub>0</sub>/*G*).
- For an isolated arrival the event is exact: 1[Δ*V* = *kd* − *j*] ≤ Σ<sub>|β|≤*B*<sub>0</sub></sub> 1[α*S*<sub>*d*</sub> = *kd* − *j* − β], which costs a factor 2*B*<sub>0</sub> + 1.
- Removing that factor requires knowing the joint law of β and *S*<sub>*d*</sub>. The small-prime part of β is a congruence condition and can be put into the sieve. The other part is the large-prime counts ω<sub>>*M*<sup>η</sup></sub>(*m*) and ω<sub>>*M*<sup>η</sup></sub>(*m* + *d*) inside the sifted progressions *A*<sub>*d*</sub>(*u*<sub>1</sub>, *u*<sub>2</sub>). The Fundamental Lemma is sharp only for sifting ranges with *s* → ∞, so it does not see these counts.
- Counting pairs (*m*, *m* + *d*) with prescribed numbers of large prime factors resembles almost-prime pair counting, where upper-bound sieves do not give sharp constants. Whether the convolution with the flat *S*<sub>*d*</sub>-law nevertheless admits a sharp-constant upper bound was **not settled** here, and no result supplying it is cited in the note.

**(c) Thresholds under successively idealized inputs.** These are *heuristic computations, not theorems*. They use δ = 3/4, *C* = *C*<sub>*U*,+</sub> ≤ 1.220360 and Markov's inequality at threshold 1/2.

| Architecture | Additional inputs needed (all upper bounds) | First-moment margin per source | Smallest admissible *k* |
|---|---|---|---|
| Note as written | none (proved) | — | *k*<sub>0</sub> > 3.05 × 10<sup>10</sup> |
| Note's skeleton with *B*<sub>0</sub> = 0 | (hypothetical) | — | 800 |
| Per-position Markov (note), with sharp exact-lag collisions and zero bad mass: δ − (*j* + 1)δ<sup>2</sup>/*k* − 2<sup>1−*j*</sup>*C* | sharp exact-lag pair correlation | *k* = 3: −0.305; *k* = 4: −0.106; *k* = 5: +0.035 | **5** |
| Source-conditioned far tail plus sharp exact-lag *marked* pair correlation: 1 − (*j* + 1)δ/*k* − 2<sup>1−*j*</sup>*C*/*k* | (★) below | *k* = 2: −0.360; *k* = 3: **+0.0932** (*j*<sub>0</sub> = 1); *k* = 4: +0.320 | **3** (threshold *k*\* = 2δ + *C* = 2.7204) |

(★) is a *sharp exact-lag marked pair-correlation upper bound* for the landing process 𝓝 = {*km* − *V*<sub>+</sub>(*m*) : *a*<sub>+</sub>(*m*) ≠ 0}. For each fixed lag *j*:
- (1/*M*) #{(*m*, *m*′) : *n*(*m*′) − *n*(*m*) = *j*} ≤ (1 + *o*(1)) δ<sup>2</sup>/*k*;
- (1/*M*) Σ |*U*<sub>+</sub>(*m*′)| · 1[*n*(*m*′) − *n*(*m*) = *j*] ≤ (1 + *o*(1)) δ *C*<sub>*U*,+</sub>/*k*.

At *k* = 3, the collision term tolerates a multiplicative loss below (1 − *C*/3)/(2δ/3) = 1.186 if the tail term is sharp. Conversely, the tail term tolerates a loss below 1.229 if the collision term is sharp.

**Conclusions.**
- *E*<sub>+</sub>(8) and *E*<sub>+</sub>(16) cannot be reached by optimizing the parameters of the present proof. The per-position Markov skeleton fails for every *k* ≤ 4 even under ideal inputs.
- *E*<sub>+</sub>(8) is not excluded by first-moment arguments as such. It is the boundary case for a sharpened version that needs (★).
- *E*<sub>+</sub>(4) at *k* = 2 lies beyond every first-moment version of the isolated-odd-arrival method. That matches note §8.2(3), and lower-bound or Poisson-approximation input would be needed.

**(d) Finite measurement (`[finite]` only, not evidence).** For *E*<sub>+</sub>(8), the fraction of support sources that have another source at lag 0 or +1 was measured directly:

| *M* | 10<sup>3</sup> | 10<sup>4</sup> | 10<sup>5</sup> | 10<sup>6</sup> |
|---|---|---|---|---|
| Collision fraction | 0.0547 | 0.0893 | 0.1123 | 0.1271 |

The Poisson-limit heuristic is 1 − *e*<sup>−2δ/*k*</sup> = 0.3935. The landing process is still in its near-lattice pre-asymptotic regime, because the spread √(2 log log *M*) is barely comparable to *k*. The script's high isolated-odd counts at *k* = 3 (570 of 2,400 bits, i.e. 95% of the about 600 sources) therefore say nothing about the asymptotics (**m11**).

**(e) Cubic L<sub>±</sub>.** Λ<sub>χ</sub> = *C*<sub>*U*,±</sub>/δ<sub>±</sub> = ∏<sub>split *p*</sub> *L*<sub>*p*</sub><sup>odd</sup> was computed for each modulus. The resulting heuristic sharp thresholds are *k*\* = (2 + Λ<sub>χ</sub>)δ<sub>±</sub>:

| Modulus | δ<sub>+</sub> | δ<sub>−</sub> | Λ<sub>χ</sub> | *k*\*(*L*<sub>+</sub>) | *k*\*(*L*<sub>−</sub>) |
|---|---|---|---|---|---|
| 7 | 0.7503 | 0.5002 | 1.0176 | 2.264 | 1.509 |
| 9 | 0.7981 | 0.5320 | 1.0163 | 2.407 | 1.605 |
| 13 | 0.7615 | 0.5076 | 1.0761 | 2.342 | 1.562 |

Under (★)-type inputs, *k* = 3 for *L*<sub>+</sub> and *k* = 2 for *L*<sub>−</sub> would therefore fall within reach. As written, *k*<sub>0</sub>(χ) inherits the astronomical size from (a). These are heuristics, not results, and they authorize no status change.

### 4.5 No linear shortcut

*E*<sub>+</sub>(8) = *E*(8) − 2*E*(64) exactly. Since *K*<sub>2</sub> = *M*<sub>2</sub> is a group, it would be tempting to deduce *E*<sub>+</sub>(8) ∉ *K*<sub>2</sub> from B1.3. But B1.3 gives *E*(8) ∉ *K*<sub>2</sub> *and* *E*(64) ∉ *K*<sub>2</sub>, so membership of the difference is undetermined. Kernel arithmetic alone cannot replace (★).

---

## 5. Construction-radix convergence: Theorem B2.1 and Corollary B2.2

**Hypotheses actually used:**
- (i) *a*(*n*) = *b*<sup>*V*(*n*)</sup>*U*(*n*) with *V* additive and *V*(*p*) = α for *p* > *p*<sub>0</sub>;
- (ii) *U* multiplicative ("depends only on prime powers"), with *U*(*p*) = 1 for *p* > *p*<sub>0</sub>;
- (iii) |*a*(*n*)| ≪ *n*<sup>ε</sup>;
- (iv) *C*<sub>*U*</sub>(*s*) < ∞.

The *weighted residue distribution* of *V* mod *k* is **derived** from (i)–(iv) via `GF-36` Lemma 3.2 and Halász; it is not an independent hypothesis. For gcd(α, *k*) = 1 it holds because *e*(*u*α/*k*) ≠ 1 for every 1 ≤ *u* < *k*. For general *g* = gcd(α, *k*) it holds on cosets of *g*ℤ/*k*ℤ. Uniform integrability of |*U*|<sup>*s*</sup> under the *y*-truncation follows from (iii), since the local factors converge.

**Part (1).** The displaced rewriting *a*(*n*)*b*<sup>−*kn*</sup> = *W*<sub>*k*</sub>(*n*)*b*<sup>−*k*ℓ<sub>*k*</sub>(*n*)</sup> holds, and ‖*x* + *y*‖<sup>*s*</sup> ≤ ‖*x*‖<sup>*s*</sup> + ‖*y*‖<sup>*s*</sup> for 0 < *s* ≤ 1. Exchanging the sums gives *b*<sup>−*s*(*k*−*r*)</sup>/(1 − *b*<sup>−*sk*</sup>), whose average over residues is 1/(*k*(*b*<sup>*s*</sup> − 1)). The coset average *g b*<sup>*g*−*u*<sub>0</sub></sup>/(*k*(*b*<sup>*g*</sup> − 1)) is also correct. ✓

**Part (2).** The layer-cake bound gives ∫‖*t*‖<sup>*s*</sup> dμ ≥ (1 − *D*)<sup>*s*+1</sup>/(2<sup>*s*</sup>(*s* + 1)). It is **sharp at *D* = 0**, with equality for Lebesgue measure. A falsification sweep over 3,000 random empirical measures with *s* ∈ {1, 1/2, 1/3} and exact *D* found **0 violations**. ✓

**Part (3).** Take *s* = 1/log *k*, and use *C*<sub>*U*</sub>(*s*) ≤ *C*<sub>*U*</sub> (since |*U*| ≥ 1 on the support) and *b*<sup>*s*</sup> − 1 ≥ *s* log *b*. This gives (log *k*)/*k*, with the exponent correction bounded by *e*. For general *g*, the *s* = 1 bound 2√(*g b*<sup>*g*−1</sup>*C*<sub>*U*</sub>/(*k*(*b*<sup>*g*</sup> − 1))) is valid. The *E*<sub>*b*</sub>\* bound 1 − 2/√(*k*(*b* − 1)) is exactly the *s* = 1 case. ✓

**A strengthening (m10, optional).** For bounded *g* the *s*-moment coset average is *g b*<sup>*s*(*g*−1)</sup>/(*k*(*b*<sup>*sg*</sup> − 1)), which is about 1/(*k s* log *b*) as *s* → 0. So **(log *k*)/*k* also holds for every bounded *g***, and the *k*<sup>−1/2</sup> rate stated for general gcd is valid but not sharp.

**Corollary B2.2.** The digit-cylinder minimum (1/*B*)Σ<sub>*d*</sub>(min(*d*, *B* − 1 − *d*)/*B*)<sup>*s*</sup> is correct and equals 1/4 − 1/(2*B*) at *s* = 1. All thresholds were reproduced (§1.2).

---

## 6. Corollary B5.4 and the transfers it uses

- **Subadditivity.** σ<sub>1</sub>(*x* + *y*; *N*) ≤ σ<sub>1</sub>(*x*; *N*) + σ<sub>1</sub>(*y*; *N*) + *O*(1). Merging two signed multisets never increases the count, and at most one carry crosses position *N*.
- **Window argument.** *D*<sup>−</sup>(*X*<sub>*k*</sub>; 2) ≥ 1 − 2<sup>1−*r*</sup> − *r*α<sub>*k*</sub>, which gives (log *k*)/*k*. ✓
- **Submultiplicativity.** The (−)(−) case uses 1 ≤ λ<sup>2</sup>. ✓

---

## 7. Barriers: Theorem B3.1 (universal transducer obstruction) and Theorem B4.1 (fixed-window barrier)

### 7.1 Theorem B3.1

`GF-03` (Lean and paper) states that *E*<sub>2</sub> is simply normal in base 2. The pentagonal expansion is an admissible signed representation, with integer offset *m* = −1. It has 51 + 51 = 102 nonzero fractional terms up to 4,000, giving σ<sub>*c*+,*c*−</sub>(*E*<sub>2</sub>; *N*) = *O*(√*N*). The theorem, that no **upper bound on σ<sub>*c*+,*c*−</sub>** can exclude base-2 simple normality, is therefore correct.

It is a weak, but valid, limitation on one method. The introduction to §3 (line 508) overstates it: "we prove why no signed-digit transducer can settle base-2 simple normality". The theorem covers only functionals of σ<sub>*c*+,*c*−</sub> type, which line 517 itself acknowledges (**m6**).

### 7.2 Theorem B4.1

**Lemma B4.2.** Signed odd parts whose NAF supports are separated by at least one zero digit concatenate to a NAF, and the NAF is unique and minimal. The collision criterion |*L*<sub>*j*</sub> − *L*<sub>*i*</sub>| ≤ ½ log<sub>2</sub> *L* + 2, valid when |*U*| ≤ √*L*, is correct, as is the reduction to sorted *L*-values. ✓

**Bad blocks.** With *M*-dependent parameters η = *L*<sup>−1/4</sup>, *p*<sub>1</sub> = √*L*, *K*<sub>0</sub> = *T* = *L*<sup>1/4</sup>, the individual exception probabilities are:
- *p*<sup>2</sup> ∣ *n* for some *p* > *p*<sub>1</sub>: ≪ *L*<sup>−1/2</sup>;
- *V*<sub>≤*p*<sub>1</sub></sub> > *K*<sub>0</sub>: ≪ (log log *L*)/*L*<sup>1/4</sup>;
- *u*(*n*) > *M*<sup>1/8</sup>: ≤ 8*L*<sup>−1/4</sup>;
- |*U*<sub>+</sub>| > *T*: ≪ *L*<sup>−1</sup>.

Cauchy–Schwarz with E[*w*<sub>±</sub><sup>2</sup>] ≤ *M*<sub>2</sub> then bounds the bad-block contribution by *O*((log log *L*)<sup>1/2</sup>/*L*<sup>1/8</sup>). ✓

**Good blocks.** The sieve has *s* = (3/8)*L*<sup>1/4</sup> → ∞ and its progressions are taken modulo *B u*<sub>1</sub>*u*<sub>2</sub>, where *B* < *p*<sub>1</sub> eventually. Collision probability is *O*(*W*/√*L*) = *O*(*L*<sup>−1/4</sup>), and each block saves at most *B*(log *L*). ✓

**Scope.** The barrier applies exactly to block grouping, since c̄<sup>NAF</sup> ≥ c̄<sup>block</sup> by subadditivity. It does **not** bound the full cancellation c̄<sub>2</sub><sup>NAF</sup>(*M*). Registry item (3)'s phrase "average signed carry-cancellation saving" should name the within-block rate (**m7**). The rate in the registry matches the note. ✓

---

## 8. Fermat-product and odd-order coset extensions of `GF-07`

### 8.1 Theorem B5.2

- **2-group structure.** φ(*M*) = 2<sup>*t*</sup> makes (ℤ/*M*ℤ)<sup>×</sup> a 2-group, so every nonprincipal character has even order. The combination Σ<sub>χ≠χ₀</sub> χ̄(*r*)*L*<sub>χ</sub> is integer-valued, and `GF-13` places it in *K*<sub>*b*</sub> for every *b*, with 1 − *D*<sub>*N*</sub> ≪ (log log *N*)/(log *N*)<sup>1/λ(*M*)</sup>. ✓
- **D<sup>±</sup> identity.** *D*<sup>±</sup>(*A*<sub>*r*,*M*</sub>(2<sup>*k*</sup>); 2) = *D*<sup>±</sup>(*E*<sup>(*M*)</sup>(2<sup>*k*</sup>); 2), because *K*<sub>2</sub> = *M*<sub>2</sub> translation preserves the orbit asymptotically and multiplication by 2<sup>*t*</sup> is a digit shift. ✓
- **Simple nonnormality for k ≥ 3.** The repaired proof is correct:
  - off the exceptional set ℰ<sub>*M*</sub> one has 2<sup>*t*</sup>τ<sub>*r*,*M*</sub> = τ<sup>(*M*)</sup>;
  - ℰ<sub>*M*</sub> has density ≪ (log *X*)<sup>−1/2<sup>*t*</sup></sup>, which is conservative, since 1/λ(*M*) would also do;
  - Cauchy–Schwarz with Σ(Ω + 2)<sup>2</sup> ≪ *X*(log log *X*)<sup>2</sup> controls ℰ<sub>*M*</sub>;
  - submultiplicativity of *s*<sub>2</sub> gives *C*<sub>true</sub><sup>(*M*)</sup> ≤ ∏<sub>*p*∤*M*</sub> *L*<sub>*p*</sub><sup>pop</sup> ≤ *C* < 29/20;
  - `GF-36`(1) then gives lim sup *f*<sub>1</sub> < 29/(20*k*) < 1/2, and hence *D*<sup>−</sup> ≥ 1/2 − lim sup *f*<sub>1</sub> > 0. ✓
- **k = 2.** Only *D*<sup>+</sup> < 1 is claimed, and only for *M* = 3, 5 and even Fermat-product *M*. ✓
- **Base-2<sup>k</sup> limit.** 2<sup>*k*−*r*<sub>0</sub></sup>*Z* ∈ *M*<sub>2</sub> = *M*<sub>2<sup>*k*</sup></sub>, and a constant shift of *V* preserves the residue law, so B2.1 applies to the shifted sequence even though *V* + const is not additive. The note states this. ✓

### 8.2 Theorem B5.3

- **Characterization.** odd(λ(*M*)) ∣ 3 holds exactly when every character order is 1, 3 or even. ✓
- **Cubic trace identity.** 4Re((*A* + *B*ω)(*x* + *y*ω)) = (2*A* − *B*)(2*x* − *y*) − 3*B y* was rederived symbolically. ✓
- **Scaling inequality.** *D*<sub>*N*</sub>(*mx*) ≤ *m D*<sub>*N*</sub>(*x*) gives the 1/*D*<sub>odd</sub> loss, and the example *x* = 1/3 is correct. ✓
- **Combinations of dilated series.** The base-2<sup>*k*</sup> part needs ‖·‖<sup>*s*</sup>-subadditivity across the Z-combination. A dilated series *F*<sub>2<sup>*kg*</sup></sub> in base 2<sup>*k*</sup> satisfies the B2.1(1)-type bound with an extra factor 1/*g*. This is acceptable, but it is compressed.
- **Registry gap.** The registry does not mention that only lim inf<sub>*k*</sub> *D*<sup>−</sup>(·; 2<sup>*k*</sup>) ≥ 1/*D*<sub>odd</sub> is proved, with limit 1 only when *D*<sub>odd</sub> = 1 (**m8**).

---

## 9. External inputs: exact hypotheses

| Input | Hypotheses required | Verified in the note? | Comment |
|---|---|---|---|
| **Fundamental Lemma, upper bound, κ = 2** (Halberstam–Richert Thm 2.5; Iwaniec–Kowalski §6.4; Friedlander–Iwaniec form with error 1 + *e*<sup>9κ−*s*</sup>*K*<sup>10</sup> for *s* ≥ 9κ + 1) | (Ω<sub>1</sub>) 0 ≤ *g*(*p*) ≤ 1 − 1/*A*<sub>1</sub>; (Ω<sub>2</sub>(κ)) ∏<sub>*w*≤*p*<*z*</sub>(1 − *g*(*p*))<sup>−1</sup> ≤ *K*(log *z*/log *w*)<sup>κ</sup>; remainder Σ<sub>*q*<*D*</sub>\|*r*<sub>*q*</sub>\| | ✓ *g*(*p*) = 2/*p* ≤ 2/7 (the note says ≤ 2/5, m16); *K* absolute; *s* = 3/(8η) ≥ 120 > 19; \|*r*<sub>*q*</sub>\| ≤ 2<sup>ω(*q*)</sup>; uniform in (*d*, *u*<sub>1</sub>, *u*<sub>2</sub>) | Sharp only as *s* → ∞, which is the root of the exact-lag obstruction (§4.4b). Page locators were **not verified** (m12). |
| **Fundamental Lemma, κ = 2/3** (split primes of cubic χ) | The same, with *K* = *K*(χ) | Partly | The note's form (1 + *K*/log *w*) needs Mertens for split primes with error *O*(1/log *w*), i.e. the prime number theorem in progressions. Dirichlet's theorem with *O*<sub>*M*</sub>(1) error, as stated in §6.2 line 887, suffices only for the multiplicative-*K* form. *K* depends on χ (**m4b, m4c**). |
| **Halász (1968)** | *f* 1-bounded multiplicative, with Σ<sub>*p*</sub>(1 − Re *f*(*p*)*p*<sup>−*it*</sup>)/*p* = ∞ for every *t* | ✓ after *y*-good squarefree-tail truncation; *f*(*p*) = *e*(*u*α/*k*) ≠ 1, or χ(*p*)*e*(−*u*/*j*) on *p* ≡ 1 (mod *j*); divergence for *t* ≠ 0 via *L*(1 + *it*, χ) ≠ 0 | Correct |
| **Wintner / squarefull convolution** (`GF-36` Lemma 3.1) | Σ\|(*f* ∗ μ)(*n*)\|/*n* < ∞ | ✓ local factors 1 + *O*(*p*<sup>−2</sup>) for *C*<sub>*U*</sub>(*s*), *M*<sub>2</sub>, E[*U*<sub>χ</sub><sup>2</sup>] | Not listed in the registry `inputs` (**MJ-1**) |
| **Paley–Zygmund (1932)** | *Z* ≥ 0 and E*Z*<sup>2</sup> < ∞ | ✓ (the θ = 0 case, i.e. Cauchy–Schwarz) | — |
| **`GF-13`** | Integer-valued combinations of even-order character Lambert series | ✓ (registry wording confirmed) | — |
| **`GF-03`, `GF-29`, `CC-04`, `GF-01`, `GF-23`** | As cited | ✓ | Several are missing from `related` (m13) |

---

## 10. Findings

### Critical

None.

### Major

**MJ-1 — Registry `inputs` omits the principal external theorems used on paper.**
- *Location.* `docs/registry/GF.toml:758`.
- *Problem.* The field lists only `GF-36`/`GF-40`, Koksma, Paley–Zygmund and `GF-01`/`07`/`13`/`23`. The note itself (Results table, lines 18–28, and §6.2) uses several more external theorems:
  - the **Fundamental Lemma of the combinatorial sieve** (upper bound, κ = 2 and κ = 2/3), in B1.3, B1.4, B4.1, B5.1 and B5.2;
  - **Halász (1968)**, in B1.4(3), B1.5, B2.1 and B5.1–B5.4;
  - **Dirichlet's theorem / the prime number theorem in arithmetic progressions** for split primes, in B1.4(3) and B1.5;
  - **Wintner's mean-value theorem**, via `GF-36` Lemma 3.1.
- *Why it matters.* `docs/registry/SCHEMA.md:33` requires `inputs` to list the external theorems used on paper. As written, the permanent record understates the result's dependencies, contrary to the evidence-label rules in `AGENTS.md`.
- *Fix.* Add these inputs, naming each source as §6.2 does. Optionally add `GF-03`, `GF-13`, `GF-29` and `CC-04` to `related`. This fix touches the record only; no proof changes.

### Minor

- **m1 — The size of *k*<sub>0</sub> is not disclosed** (note lines 20, 346, 378, 922; registry `scope`). State that the recipe gives *k*<sub>0</sub> = ⌈800(2*B*<sub>0</sub> + 1)⌉ with *B*<sub>0</sub> ≥ ⌊32/ε⌋. With *M*<sub>2</sub> ≈ 4.819 this means *k*<sub>0</sub> > 3 × 10<sup>10</sup>, and the fixed constants alone force *k*<sub>0</sub> ≥ 800. Give the value of *M*<sub>2</sub>. Sharpen open question §8.2(2) using §4.4(c): parameter tuning cannot reach *k* = 3; the input (★) could.
- **m2 — The signed good set is literally misdefined** (line 235, used at line 359). The B1.3 definition requires *a*(*m*) ≥ 1. Applied to *a*<sub>+</sub> it excludes 4 ∣ *m*, where *a*<sub>+</sub> < 0. Read literally, \|𝒢<sub>+</sub>\| ≈ *M*/2, and the final count 1/2 − 3/40 falls short of the claimed 1/(2*k*), though a positive density would still follow. Replace the condition by \|*a*(*m*)\| ≥ 1 (equivalently *a*<sub>+</sub>(*m*) ≠ 0).
- **m3 — Accounting slip** (line 378). The final count omits the ε*M* + *O*(log *M*) columns hit directly by bad sources. The correct count is (3/4 − 2ε − 3/40 − *o*(1))*M*. This is harmless numerically.
- **m4 — Compressed cubic extension** (line 380; §6.2, line 887).
  - (a) State that δ<sub>+</sub> ≥ 6/π² and δ<sub>−</sub> ≥ 4/π² make the unscaled thresholds sufficient, and give ε and η<sub>1</sub> relative to E[*U*<sub>χ</sub><sup>2</sup>].
  - (b) The dimension condition with factor (1 + *K*/log *w*) needs Mertens for split primes with error *O*(1/log *w*), i.e. the prime number theorem in progressions. Alternatively, cite the multiplicative-*K* form of the Fundamental Lemma.
  - (c) *K* = *K*(χ) is not absolute.
- **m5 — Corollary B1.2a** (line 204). Fix the off-by-one: |*V* − μ| ≥ *G*/4 − 1 is what the argument gives. Also state that zeros, which have *V* = 0, are deviant automatically, because the Turán–Kubilius hypothesis has α > 0.
- **m6 — Overstatement at line 508.** "No signed-digit transducer can settle base-2 simple normality" should read "no upper bound on σ<sub>*c*+,*c*−</sub> can …", which is consistent with Theorem B3.1 and line 517.
- **m7 — Registry item (3) wording.** Name the within-block rate c̄<sup>block</sup><sub>*k*,*B*</sub>(*M*), and say that the full NAF cancellation is not bounded by Theorem B4.1.
- **m8 — Registry item (4) wording.** State the conclusions:
  - the *D*<sup>±</sup> identity and full classification for *k* ≥ 3;
  - *D*<sup>+</sup> < 1 at *k* = 2 only for *M* = 3, 5 and even Fermat-product *M*;
  - the limit *D*<sup>−</sup>(·; 2<sup>*k*</sup>) → 1 for Fermat-product *M*;
  - for odd(λ(*M*)) ∣ 3, *D*<sup>−</sup>(·; 2) > 0 when *k* > 3*W*<sub>eff</sub>, and lim inf *D*<sup>−</sup>(·; 2<sup>*k*</sup>) ≥ 1/*D*<sub>odd</sub>.

  Also state that the theorems hold for *all* such *M*; the 37 and 50 values are finite enumerations.
- **m9 — Registry item (2) hypotheses.** Add that *U* is multiplicative and that |*a*(*n*)| ≪ *n*<sup>ε</sup>. The residue distribution is derived via Halász rather than assumed.
- **m10 — Optional strengthening.** The rate for general bounded *g* can be improved from *k*<sup>−1/2</sup> to (log *k*)/*k* via *s*-moments on cosets (§5).
- **m11 — Evidence weight of the script.**
  - About 90,000 of the 186,311 `[exact]` checks are the trivial inequality 2*m* − *V*(*m*) ≥ 1.
  - The isolated-arrival checks (570/450/360) are tautological consequences of exact arithmetic, just as line 192 already says of the carry identity.
  - In the script, "isolated" means only "*C*<sub>*k*</sub>(*n*) odd and |*Y*<sub>*n*</sub>| < 1/2", not isolation from other sources.
  - The finite counts are pre-asymptotic (§4.4d).

  Label these checks accordingly.
- **m12 — Citation locators unverified.** The theorem and page locators for Halberstam–Richert, Tenenbaum and Iwaniec–Kowalski were not checked in this audit. Cite one precise Fundamental Lemma statement, with (Ω<sub>1</sub>), (Ω<sub>2</sub>(κ)) and the remainder term written out.
- **m13 — Registry `related`.** Add the `GF-01`, `GF-03`, `GF-13`, `GF-23`, `GF-29` and `CC-04` dependencies.
- **m14 — B5.2 citation.** The *D*<sup>−</sup> > 0 claim for *A*<sub>*r*,*M*</sub> at *k* ≥ 3 cites "`GF-36` (*D*<sup>−</sup> > 0 for *k* ≥ 3)". Cite instead the general clause `GF-36`(1) together with *D*<sub>*N*</sub> ≥ 1/2 − *f*<sub>1,*N*</sub>, since `GF-36`'s main theorem concerns *E*(2<sup>*k*</sup>).
- **m15 — *M*<sub>2</sub> not certified.** *M*<sub>2</sub> (≈ 4.819) is not certified in the script. Finiteness suffices for existence, but an explicit *k*<sub>0</sub> needs an outward-rounded enclosure.
- **m16 — Nit** (line 277). Since *p* > *p*<sub>1</sub> ≥ 5, *g*(*p*) ≤ 2/7, not 2/5. The weaker bound is still valid.

---

## 11. Record of ad-hoc checks

All checks ran with `python -B` on Windows. Input came through stdin heredocs from the scratchpad working directory, and no files were written to the repository.

1. Independent floating-point products over primes up to 3 × 10<sup>5</sup> for *L*<sub>2</sub><sup>odd</sup>, *L*<sub>2</sub><sup>+</sup>, *C*<sub>*U*,odd</sub>, *C*<sub>*U*</sub>, *C*<sub>*U*,+</sub>, the *s* = 1/2 moments, *C*<sub>*U*</sub><sup>(3, 5, 6)</sup> and *M*<sub>2</sub>. All values lie inside the certified enclosures (§1.2).
2. Stripped means for τ<sub>4</sub>, τ<sub>8</sub>, τ<sub>3</sub>, τ<sub>5</sub> and τ<sub>7</sub>. All lie inside the enclosures.
3. Exact enumeration of the moduli with φ(*M*) = 2<sup>*t*</sup> up to 257 (37 values) and with odd(λ(*M*)) ∣ 3 up to 100 (50 values). Both match.
4. The B2 table recomputed from the closed form. All 56 nonzero entries and all zeros match. Also recomputed: the 148× ratio, *E*<sub>+</sub>(32) in base 32, and the Corollary B2.2 thresholds.
5. Lemma B1.2(3) falsification sweep: 3,000 exact rational orbits, 0 violations, 15 equalities.
6. B2.1(2) falsification sweep: 3,000 empirical measures, 0 violations.
7. *E*<sub>+</sub>(8) = *E*(8) − 2*E*(64): exact termwise identity.
8. First-moment threshold computations for the *k*<sub>0</sub> analysis, plus cubic δ<sub>±</sub> and Λ<sub>χ</sub> for moduli 7, 9 and 13. These are heuristic.
9. `[finite]` lag-{0, +1} collision fractions for *E*<sub>+</sub>(8) up to *M* = 10<sup>6</sup>. This is a pre-asymptotic measurement and proves nothing.

---

## 12. Bottom line

`GF-42` is **validated with scope and text refinements**:
- **Item (1).** For the nonnegative families (B1.3), the classification is fully supported by a sound proof whose only external input is the upper-bound Fundamental Lemma. For the signed families (B1.4), it is supported only for *k* ≥ *k*<sub>0</sub>, with *k*<sub>0</sub> > 3 × 10<sup>10</sup> as written.
- **Item (2)** (B2.1) is sound.
- **Item (3).** Both barriers are sound, and two wording fixes are needed (m6, m7).
- **Item (4)** (B5.2–B5.3) is sound, and its scope wording needs refinement (m8).

The single Major item is the incomplete registry `inputs` field. *D*<sup>+</sup>(*E*<sub>+</sub>(8); 2) < 1, small-*k* *D*<sup>+</sup> < 1 for signed cubic *L*<sub>±</sub>, and all *k* = 2 signed cases remain **Open**. The most direct route to *E*<sub>+</sub>(8) identified here is the sharp exact-lag marked pair-correlation upper bound (★) of §4.4.

*Reminder: this cross-model review is not independent human peer review and authorizes no benchmark status change.*
