# Phase 25 Track B — cross-provider adversarial referee review

**Audited files.** [`notes/phase25/generalized-lambert-and-eplus.md`](../generalized-lambert-and-eplus.md) (882 lines) and [`scripts/phase25_lambert_eplus.py`](../../../scripts/phase25_lambert_eplus.py) (1,515 lines), authored by Gemini 4 Neon, on branch `research/phase-25-carry-correlations`.

**Reviewer.** Claude `claude-opus-5-5`, a different provider from the author. The audit was read-only. No audited file was modified, nothing was committed, and WSL was not used. Independent reviewer checks ran in a scratch directory outside the repository.

> **Cross-model review is not independent human peer review.** This report is a second machine reading by a model from another provider. It does not replace refereeing by human specialists in sieve theory, multiplicative number theory or uniform distribution. None of its conclusions may be used to change a benchmark status.

## Verdict: **REVISE**

| Severity | Count |
|---|---|
| Critical | 0 |
| Major | 4 |
| Minor | 30 |

The headline mathematics survives adversarial checking. Each of the following was rechecked step by step and found sound in architecture:

- the exact displaced carry identity and the universal exit-discrepancy bound (Lemma B1.2);
- the second-moment and Paley–Zygmund proof of Theorem B1.3, including the *k* = 2 boundary cases *E*<sub>odd</sub>(4), *E*<sup>\*</sup>(4) and *E*<sub>*b*</sub><sup>\*</sup>(*b*<sup>2</sup>);
- the phase-averaged circulant argument for higher-kernel exclusion (Theorem B1.5);
- the Halász residue law and the *s*-moment integral inequality (Theorem B2.1);
- the circular Koksma inequality and exact circular variation (Theorem B3.3);
- the fixed-window barrier (Theorem B4.1).

No counterexample was found to any headline theorem.

The four Major findings are local, and each has a short fix:

- **M1.** Many numbers presented as certified, outward-rounded bounds are rounded to nearest, and therefore overstate what the script certifies.
- **M2.** A step in the proof of Theorem B1.4(2) asserts that an unbounded quantity is finite.
- **M3.** The simple-nonnormality clause of Theorem B5.2(2) does not follow from the stated proof.
- **M4.** The tier-1 lemma of the Lean blueprint cannot reach the blueprint's own target constant.

After these repairs, and with the Minor polish below, the note should be acceptable.

---

## 1. Verifier run and agreement between script and note

`python -B scripts/phase25_lambert_eplus.py` was run from the worktree root on Windows. It exited with code `0` in 6.0 s and printed:

```
ALL CHECKS PASSED in 5.99s: 173,919 [exact], 2,360 [encl], 27 [finite] (total 176,306).
```

The counts match note lines 3 and 859–862. Each printed constant was compared with the note:

| Note item | Note value | Script output | Status |
|---|---|---|---|
| L<sub>2</sub><sup>odd</sup>, L<sub>2</sub><sup>+</sup>, C<sub>U,odd</sub>, C<sub>U</sub>, C<sub>U,+</sub> (l. 124–128) | as tabulated | identical | ✓ (outward, `fmt_encl`) |
| C<sub>U</sub><sup>(3)</sup>, C<sub>U</sub><sup>(5)</sup>, C<sub>U</sub><sup>(6)</sup>, the three s = 1/2 moments (l. 129–134) | as tabulated | identical | ✓ |
| Isolated odd arrivals (l. 344) | 570, 450, 360 | 570, 450, 360 | ✓ |
| B2 table (l. 463–470) | as tabulated | identical **as printed** | ✗ rounding direction (M1) |
| E<sub>+</sub>(32) base 32 (l. 475) | ub ≤ 0.432657 < 0.447126 ≤ unif | same digits | ✗ rounding direction (M1) |
| W<sub>+</sub>, W<sub>+</sub><sup>maj</sup>, μ<sub>1,3/2</sub>, three Lean majorants (l. 497, 590, 625–627) | as stated | identical | ✓ (outward) |
| Automata: 7→4 and 13→7 states, π<sub>7</sub>, A<sub>∞</sub> = 12/31 (l. 571–586) | as stated | identical | ✓ exact |
| 7-state transition table (l. 573–581) | as tabulated | matches the script's `lump7` (reviewer extraction) | ✓ |
| A<sub>14</sub>(1, 3/2) = 80897/229376, V<sub>circ</sub> = 453 (l. 589) | as stated | reviewer recomputation agrees | ✓ (not asserted by the script, m4) |
| D<sup>−</sup>(E<sub>+</sub>(8); 2) values (l. 25, 540, 593, 625–627) | 1.4363e−5, 2.3643e−5, … | same digits | ✗ rounding direction (M1) |
| E<sub>+</sub>(4) deficit (l. 696) | [0.120705, 0.120797] | identical | ✓ (outward) |
| Tables 4.1 and 4.2 (l. 744–757) | as tabulated | identical | ✓ `[finite]` |
| τ<sub>r</sub> enclosures (l. 770–774) | as tabulated | identical | ✓ (outward) |

**Separation of evidence types.** `[exact]`, `[encl]` and `[finite]` checks are counted separately. The 27 `[finite]` checks are exactly the 20 block-cancellation cells and the 7 prefix-statistics rows, and neither table is used in any proof. All enclosures are computed in `Fraction` or in 2<sup>−96</sup> fixed-point arithmetic with directed rounding. The local-factor tails (script l. 244–255, 318–325, 778–782, 1318–1333) were rederived and are valid. The prime-tail bound Σ<sub>*p*>*P*</sub> *p*<sup>−2</sup> < 1/(2(*P* − 1)) is valid (it even holds with 1/(2*P*)).

Two exceptions to the separation claims are recorded as m1 and m5.

---

## 2. Critical audit of B1 (Theorems B1.2–B1.5)

### 2.1 Lemma B1.2: correct as stated, for all N and all b ≥ 2

- **(1) Carry identity.** The identity *C*<sub>*k*</sub>(*n*) + *q*<sub>*n*</sub> = *d*<sub>*n*</sub> + *b q*<sub>*n*−1</sub> follows from ⌊*b*<sup>*n*</sup>*F*⌋ = *A*<sub>*n*</sub> + *q*<sub>*n*</sub>. The definition *q*<sub>0</sub> = ⌊*F*⌋ − *C*<sub>*k*</sub>(0) is consistent because *C*<sub>*k*</sub>(0) is an integer. The bound *q*<sub>*N*</sub> ≤ Σ<sub>*m*>*N*/*k*</sub> *a*(*m*) *b*<sup>*N*−*km*</sup> = *O*(*N*<sup>ε</sup>) holds. The extra sources with *m* ∈ (*N*/*k*, *N*/*k* + *O*(log *N*)] contribute *o*(*N*), so the arrival mean tends to *C*<sub>*U*</sub>/*k*.
- **(2) Dead blocks.** Both claims check out:
  - *Exits.* An exit from a dead run forces *q*<sub>*v*</sub> = 0, hence *d*<sub>*v*+1</sub> ≠ 0.
  - *Run counting.* Each run contributes at most *G* − 1 elements beyond its empty *G*-windows, and at most one run ends at *N*. Together these give the stated inequality exactly, with *a* ≤ *N* − *G* + 1.
- **(3) Exit-discrepancy bound.** This holds for every real *x*, every *b* ≥ 2 and every *N* ≥ 2:
  - The pairs {*n* − 1, *n*} with *n* ∈ *S* are disjoint, since *n* and *n* + 1 cannot both lie in *S*.
  - The gap *y*<sub>*n*</sub> − *y*<sub>*n*−1</sub> = (*b* − 1)*y*<sub>*n*−1</sub> lies in [δ, 1 − 1/*b*), with δ = (*b* − 1)/*b*<sup>2</sup> < 1/*b*, so 1 − 1/*b* < 1 − δ.
  - The wrap-around case "*y*<sub>*n*−1</sub> < *u*, *y*<sub>*n*</sub> ≥ *v*" is correctly excluded by *y*<sub>*n*</sub> − *y*<sub>*n*−1</sub> < 1 − δ < ℓ.
  - There are no boundary or tail effects. *S* ranges over 1 ≤ *n* < *N*, and the orbit has exactly *N* points, indexed 0, …, *N* − 1.

### 2.2 Corollary B1.2a: correct

The window sets *J*(*a*) have size *G*/(2*k*) + *O*(1). Each *m* lies in at most *G*/2 + 1 of them. With Turán–Kubilius this gives at most 16*kM*/*C*<sub>0</sub><sup>2</sup> empty *G*-windows when *G* = *C*<sub>0</sub>√(log log *M*). The claimed *N*/√(log log *N*) bound follows with zero external inputs.

### 2.3 Theorem B1.3 under extreme scrutiny: no gap found

How the argument proves lim inf #{*d*<sub>*n*</sub> = 0, *d*<sub>*n*+1</sub> ≠ 0}/*N* > 0:

1. **Dead positions.** Their density is at least 1 − *C*<sub>*U*</sub>/*k* > 0, which uses *k* > *C*<sub>*U*</sub> and Lemma B1.2(2).
2. **Incoming carries.** These are controlled exactly by the identity, because dead positions have *q*<sub>*n*−1</sub> = 0. No probabilistic carry control is needed.
3. **Exits.** The only way dead positions could fail to produce exits at positive density is to clump into runs. The run-length inequality converts this into a bound by the density of empty *G*-windows.
4. **Empty windows.** Their density is driven to *O*(ε) by a second-moment (Paley–Zygmund) bound on good-source window counts *Z*<sub>*a*</sub>. This needs *E*[*Z*<sup>2</sup>] ≤ *E*[*Z*] + (1 + *O*(ε))*E*[*Z*]<sup>2</sup>, i.e. **the sharp constant is essential**. At *k* = 2, a non-sharp constant *C* would require *C* < *k*/*C*<sub>*U*</sub>, which is about 1.426 for *E*<sub>odd</sub>(4).

The sharp constant is delivered as follows.

- **Step 3 sieve.** The sieve is an upper-bound sieve of dimension κ = 2 with *g*(*p*) = 2/*p*:
  - *Condition at d.* Primes *p* | *d* are dropped from the sieve, which is legitimate for an upper bound. Their contribution to the difference of ω-counts cancels exactly.
  - *Coprimality and the progression.* *u*<sub>1</sub> and *u*<sub>2</sub> are coprime because gcd(*m*, *m* + *d*) | *d*. Together they define a single progression modulo *u*<sub>1</sub>*u*<sub>2</sub> ≤ *M*<sup>1/4</sup>.
  - *Remainder.* Each remainder term is at most 2<sup>ω(*q*)</sup>, and the total over *d* ≤ *D*<sub>0</sub> and all (*u*<sub>1</sub>, *u*<sub>2</sub>) is *O*(*M*<sup>5/8</sup>(log *M*)<sup>2</sup> log log *M*) = *o*(*M*).
  - *Main term.* The main term (1/(*u*<sub>1</sub>*u*<sub>2</sub>))∏(1 − 2/*p*) is exactly the trinomial probability, and summing over all pairs is legitimate.
  - *Uniformity.* The factor 1 + *O*(*e*<sup>−*s*</sup>) is uniform in (*d*, *u*<sub>1</sub>, *u*<sub>2</sub>), since *s* = 3/(8η) is fixed.
- **Step 4 local bound.** The saddle-point computation was rederived:
  - the moment generating function is *E e*<sup>*z*ξ</sup> = 1 + 2(cosh *z* − 1)/*p*;
  - the bound *a*<sup>2</sup> + *b*<sup>2</sup> ≤ 16 cosh<sup>2</sup>λ/*p*<sup>2</sup> holds;
  - the inequality √((1 + *a*)<sup>2</sup> + *b*<sup>2</sup>) ≤ exp(*a* + (*a*<sup>2</sup> + *b*<sup>2</sup>)/2) holds;
  - the choice λ = *h*/(2*E*<sub>*d*</sub>) yields the Gaussian bound with relative error *O*(*E*<sup>−1/3</sup>) + *O*(ε);
  - the range *h* > *E*<sup>2/3</sup> decays like *e*<sup>−*E*<sup>1/3</sup>/5</sup>.

  The Riemann sum with step *k*/α is valid as an upper bound because the summand is decreasing. The shift by |*r*| < *G*′ and the finitely many *d* with *kd* − *r* ≤ 0 cost only *O*(*G*′/√*E*) = *o*(1). This should be written out (m8).
- **Step 2 tail.** For *d* > *D*<sub>0</sub>, the conditions force ω(*n*) > 10 log log *M*, and 2<sup>−10*L*</sup> Σ 4<sup>ω(*n*)</sup> = *o*(*M*) since 10 ln 2 > 3.
- **Order of limits.** The argument is sound if the limits are taken as: *N* → ∞ first; then *G* → ∞ with *G* ≫ *B*<sub>0</sub>/ε and *G* ≫ *k*/ε; then ε → 0, with *p*<sub>1</sub>, *K*<sub>0</sub>, η and *B*<sub>0</sub> depending on ε. There is no hidden uniformity in *N*.

**The *k* = 2 boundary hypotheses all hold.**

| Hypothesis | *E*<sub>odd</sub>(4) | *E*<sup>\*</sup>(4) and *E*<sub>*b*</sub><sup>\*</sup>(*b*<sup>2</sup>) |
|---|---|---|
| *a*(*m*) ≥ 1 | ✓ | ✓ |
| *V* additive, *V*(*p*) = 1 for large *p* | *p* > 2 | all *p* |
| *V*(*p*<sup>*e*</sup>) = *O*(log(*e* + 1)) | ✓ | ✓ |
| 2*m* − *V*(*m*) ≥ 1 | ✓ (also checked to *m* = 30,000) | ✓ |
| *k* > *C*<sub>*U*</sub> | *C*<sub>*U*,odd</sub> ≤ 1.402514 < 2 | *C*<sub>*U*</sub> = 1 < 2 |

The theorem is also consistent with Phase 24 §10. That note only obstructs *D*<sup>−</sup> > 0, i.e. a lower bound on collisions, whereas B1.3 needs only the upper-bound side. Its Poisson heuristic, with intensity 1/2 and 1/4 expected later partners, is exactly the second-moment structure used here.

Theorem B1.3 is accepted as a *Paper proof with External input* (the upper bound of the Fundamental Lemma). Before registry promotion it should be expanded into a full write-up (m8, m9).

### 2.4 Theorem B1.4

- **(1)** The isolated-odd-arrival lemma is correct. The identity 2<sup>*n*−1</sup>*x* = *I* + (*C*<sub>*k*</sub>(*n*) + *Y*<sub>*n*</sub>)/2 holds, and the fractional part lies in (1/4, 3/4).
- **(2)** The architecture is sound, but one step is false as written (M2). The collision count via Steps 2–4 of B1.3 is correct up to a harmless factor of 2.
- **(3)** The cubic extension needs two clarifications: the sieve must run over split primes only, and *D*<sup>−</sup> > 0 is inherited only for some characters (m11).

### 2.5 Theorem B1.5: correct

- **Kernel decomposition.** The decomposition via GF-29 is correct. One missing line, *M*<sub>2<sup>*j*</sup></sub> ⊆ *M*<sub>2</sub>, is recorded as m14.
- **Digits on blocks.** Density-1 blocks carry the periodic digits, because *R*/(2<sup>*j*</sup> − 1) lies at distance at least 1/((2<sup>*j*</sup> − 1)2<sup>*j*</sup>) from the *j*-bit dyadic cut points.
- **Phase average.** The phase-restricted arrival mean equals *C*<sub>*U*</sub>/*k*, by Halász on primes *p* ≡ 1 (mod *j*). Restricting the nonnegative Halász sum to a subset of primes is a valid lower bound.
- **Circulant system.** The system 2*x*<sub>*r*</sub> − *x*<sub>*r*+1</sub> = *c* − *b*<sub>*r*+1</sub> has the unique solution *x*<sub>*r*</sub> = *c* − *z*<sub>*r*</sub>.
- **Contradiction.** Some *z*<sub>*r*</sub> ≥ 2<sup>*j*−1</sup>/(2<sup>*j*</sup> − 1), which contradicts *x*<sub>*r*</sub> ≥ 0.

All five applications were rechecked:

| Application | Check |
|---|---|
| (1) *E*(2<sup>*k*</sup>), *k* ≥ 5 | 2.076411/5 = 0.4152822 < 1/2 |
| (2) *E*(16) | 0.519103 < 8/15, but not < 16/31 |
| (3) *E*(8), *K*<sub>4</sub> | via *C*<sub>true</sub>/3 ≤ 0.446372 < 1/2 |
| (4) *E*<sub>odd</sub>(2<sup>*k*</sup>), *k* ≥ 3 | 0.467505 < 1/2 |
| (5) *E*<sup>\*</sup>(2<sup>*k*</sup>), *k* ≥ 2 | *C*<sub>*U*</sub>/*k* ≤ 1/2, and every 2<sup>*j*−1</sup>/(2<sup>*j*</sup> − 1) is strictly larger than 1/2 |

---

## 3. Audit of B2 (Theorem B2.1 and Corollary B2.2): correct

- **Displaced rewriting.** The identity *a*(*n*)*b*<sup>−*kn*</sup> = *W*<sub>*k*</sub>(*n*)*b*<sup>−*k*ℓ<sub>*k*</sub>(*n*)</sup> holds. Subadditivity of ‖·‖<sup>*s*</sup> holds for 0 < *s* ≤ 1, and the exchange of sums gives *b*<sup>−*s*(*k*−*r*)</sup>/(1 − *b*<sup>−*sk*</sup>).
- **Residue law.** When gcd(α, *k*) = 1, the weighted equidistribution of *V*(*n*) mod *k* is legitimate. After *y*-truncation the twist is *z*<sup>ω(*r*)</sup> with |*z*| = 1 and *z* ≠ 1, and Halász's condition holds for every *t*. Summing the geometric series gives *C*<sub>*U*</sub>(*s*)/(*k*(*b*<sup>*s*</sup> − 1)) exactly.
- **Coset factor.** The coset factor *g b*<sup>*g*−1</sup>/(*b*<sup>*g*</sup> − 1) is correct.
- ***s*-moment inequality.** The layer-cake inequality ∫‖*t*‖<sup>*s*</sup> *d*μ ≥ (1 − *D*)<sup>*s*+1</sup>/(2<sup>*s*</sup>(*s* + 1)) was rederived.
- **Rate.** The choice *s* = 1/log *k* gives (log *k*/*k*)<sup>1/(1+1/log *k*)</sup> = *O*(log *k*/*k*), because the exponent correction is bounded by *e*. It also uses *C*<sub>*U*</sub>(*s*) ≤ *C*<sub>*U*</sub>, since |*U*| ≥ 1 on the support.
- **Corollary B2.2.** The digit-cylinder minimum is correct.

There are no Halász pitfalls: no uniformity in *k* is needed, since each *k* is treated separately and the rate comes from the explicit formula. The 148× comparison at *k* = 64 (0.7769/0.00524 = 148.3) is correct, and 0.7769 is a valid floor. Many other table entries are rounded up (M1).

---

## 4. Audit of B3–B5

**B3.1** is correct. The registry entry GF-03 states that *E*<sub>2</sub> is simply normal in base 2. There are 102 pentagonal terms up to 4000, which bounds σ by *O*(√*N*). The theorem is elementary but is a valid Objective-4 limitation statement.

**B3.2** is correct:

- Restricting a global path to disjoint blocks costs at least σ<sub>free</sub>.
- Simple normality in base 2<sup>*mL*</sup> implies simple normality in base 2<sup>*L*</sup>, by marginalizing aligned blocks.
- The sequence *kA*<sub>*k*</sub> is strictly increasing for all *k*, since successive differences equal 1/3 − (−1/2)<sup>*k*−1</sup>/12.
- All four thresholds were recomputed: 15/16, 5/24, 1/8, and *A*<sub>13</sub> ≈ 0.303420 against *A*<sub>12</sub> ≈ 0.300924.

**B3.3** is correct:

- The ±1 jump counts follow from *b*<sub>*m*</sub>, and the script confirms them exhaustively for *L* ≤ 15.
- The discrete circular Koksma inequality follows from *D*<sub>*N*</sub> = sup *F* − inf *F* and summation by parts with the centring constant.
- The sliding-window inequality σ<sub>1</sub>(*x*; *N*) ≥ ∫*g*<sub>*L*</sub> *d*μ<sub>*N*</sub> − *O*(*L*/*N*) holds.

**B3.4** is correct:

- The (−)(−) case of submultiplicativity uses 1 ≤ λ<sup>2</sup>.
- The prefix bound holds.
- The DP overflow bound uses submultiplicativity of *s*<sub>2</sub> and *w*<sub>1,λ</sub>(*o*<sub>2</sub>*u*) ≤ *w*<sub>1,λ</sub>(*o*<sub>2</sub>)*s*<sub>2</sub>(*u*), and is valid.

**Lemma B3.5** is correct. The relation *H*<sub>*N*</sub> − *X*<sub>*N*</sub> ∈ (−11/12, 23/12) ∩ ℤ follows from the NAF low-part bound 2/3 and the tail bound 1/4. The script's check of *X*<sub>*N*</sub> includes every source and bounds the tail properly. The blueprint has a constant mismatch (M4).

**B4.1** is correct as a barrier:

- **Lemma B4.2.** NAF supports separated by a zero bit concatenate to a NAF, which is unique and hence minimal.
- **Bad blocks.** Their total contribution is bounded by Cauchy–Schwarz with *E*[*w*<sup>2</sup>] ≤ *E*[*U*<sub>+</sub><sup>2</sup>] < ∞.
- **Good blocks.** These collide only if |*V*<sub>*j*</sub> − *V*<sub>*i*</sub> − *kd*| ≤ ½ log<sub>2</sub> *L* + 2, which has probability *O*(*L*<sup>1/4</sup>/√*L*).
- **Block structure.** The sieve over *n* in a fixed residue class mod *B* is harmless, since *B* < *p*<sub>1</sub>.
- **Use of the inequality.** It is correct that c̄<sup>NAF</sup> ≥ c̄<sup>block</sup>, so the barrier applies exactly to the block-grouping method.
- **Rate.** The stated rate is true but loose (m22), and the Tenenbaum sharpening is unproved (m21).

**B5.1** is correct:

- The prime-tail coefficient *r* − 1 + C(*r*, 2)/(1 − *r*/(2*P*)) is valid because *u*<sub>*b*</sub>(*r*) = 1 in all five configurations (*r* a power of *b*).
- The *D*<sup>−</sup> > 0 thresholds agree with the Phase 24 table (*k*<sub>0</sub> = 2, 2, 1 in bases 3, 5, 7; *k* ≥ 4 for τ<sub>4</sub> and τ<sub>8</sub>).
- The multiplicative-independence argument *u*<sub>*b*</sub>(*r*<sup>*w*</sup>) ≥ (*r*/*b*<sup>θ</sup>)<sup>*w*</sup>, with *r*/*b*<sup>θ</sup> > 1, is correct.

**B5.2** has a correct structure:

- φ(*M*) = 2<sup>*t*</sup> forces every nonprincipal character to have even order.
- The combination Σ<sub>χ≠χ₀</sub> χ̄(*r*)*L*<sub>χ</sub> is integer-valued.
- GF-13 applies.
- *D*<sup>±</sup> transfer through *K*<sub>2</sub>.
- The base-2<sup>*k*</sup> limit transfers via *M*<sub>2</sub> ⊆ *M*<sub>2<sup>*k*</sup></sub>.

The simple-nonnormality clause is not supported by the stated proof (M3).

**B5.3** is correct:

- The cubic trace identity was rederived.
- The denominator clearing via φ(*M*′) | φ(*M*) is correct.
- *D*<sub>*N*</sub>(*mx*) ≤ *m D*<sub>*N*</sub>(*x*) holds by pulling back intervals.
- The example *x* = 1/3 gives *D*<sub>∞</sub> = 2/3, as recomputed.

**Corollary B5.4** has two defects (m26, m27).

---

## 5. Required research-note contents and labels

All ten required items are present:

1. definitions (§0);
2. precise statements;
3. proofs (some compressed, m8);
4. prior art (§6.1);
5. external inputs with hypothesis checks (§6.2);
6. evidence labels (Results table and every theorem header);
7. reproduction (§7);
8. exact finite tests (the script);
9. open questions (§8.2);
10. objective numbers (Results table and §8.1).

The disclaimer that cross-model review is not independent human peer review is at line 9. No benchmark status is changed (line 10), which is correct. The Lean material is labelled as an uncompiled blueprint (lines 8 and 605), which is correct.

---

## 6. Findings

### Critical

None.

### Major

**M1 — "Certified outward-rounded" numbers are rounded to nearest, overstating the certified bounds.**

*Lines:* 25, 463–470, 475, 540–543, 593–596, 625–627, 871 (also Results table l. 22).

*Defect:* The script prints lower bounds with `f"{float(x):.4f}"` or `.4e` (script l. 618, 638, 1486–1491), which rounds half to even and can therefore round up. The note copies these digits as certified bounds. Exact recomputation in `Fraction` shows the following overstatements:

| Item | Exact certified value | Correct statement |
|---|---|---|
| D<sup>−</sup>(E<sub>+</sub>(8); 2), 4-state (note: 1.4363e−5) | 1.4362998…e−5 | ≥ 1.4362e−5 |
| 7-state (note: 2.3643e−5) | 2.3642668…e−5 | ≥ 2.3642e−5 |
| Lean tier 3, *L* = 19 (note: 9.7267e−8) | 9.7266566…e−8 | ≥ 9.7266e−8 |
| Lean tier 2, *L* = 20 (note: 8.7330e−8) | 8.7329905…e−8 | ≥ 8.7329e−8 |
| Lean tier 1, *L* = 24 (note: 1.3045e−8) | 1.3044712…e−8 | ≥ 1.3044e−8 |
| E<sub>+</sub>(32) upper bound (note: ≤ 0.432657) | 0.4326570013… | ≤ 0.432658 |
| E<sub>+</sub>(32) uniform value (note: ≥ 0.447126) | lower bound 0.4471256773… | ≥ 0.447125 |
| 26 of the B2 table entries | e.g. 1 − 1/√2 = 0.292893… printed 0.2929 (E<sup>\*</sup>(2<sup>8</sup>), s = 1); 0.107664 printed 0.1077 (E(2<sup>8</sup>), s = 1/2) | floor to 4 decimals |

The 26 affected B2 entries are:

- *E*: (8, ½), (12, 1), (16, ½), (32, ½), (64, 1);
- *E*<sub>odd</sub>: (8, 1), (8, ½), (10, 1), (12, 1), (12, ½), (16, 1), (32, 1), (32, ½), (64, ½);
- *E*<sup>\*</sup>: (5, 1), (6, ½), (8, 1), (10, ½), (12, ½), (16, ½);
- *E*<sub>+</sub>: (5, ½), (6, ½), (8, 1), (10, ½), (16, 1), (16, ½).

No theorem's qualitative conclusion changes, and the margins remain positive. However, the note claims (l. 6, 459, 861) that these are outward-rounded certificates, and that is false as written.

*Fix:* Print every lower bound with `floor` and every upper bound with `ceil`, reusing `fmt_encl` (script l. 156). Then re-copy the digits. Also tighten the assertions to the stated digits; the script currently asserts only ≥ 143/10<sup>7</sup>, ≥ 225/10<sup>7</sup> and > 0 (l. 1058–1062). The "> 101×" boost survives: 2.3642e−5 / 2.34e−7 = 101.03.

**M2 — Theorem B1.4(2): the quantity U<sub>0</sub> is infinite.**

*Line:* 346.

*Defect:* The proof fixes *U*<sub>0</sub> = max<sub>*m*∈𝒢</sub> |*U*<sub>+</sub>(*m*)| < ∞ and sets *j*<sub>0</sub> = ⌈log<sub>2</sub>(320*U*<sub>0</sub>)⌉. Condition 2 of 𝒢 only bounds *V*<sub>≤*p*₁</sub>(*m*) = Σ<sub>*p*≤*p*₁</sub> *v*<sub>2</sub>(*v*<sub>*p*</sub>(*m*) + 1), not the exponents. For example, *m* = 3<sup>2*i*</sup>·(squarefree with *p* > *p*<sub>1</sub>) has *V*<sub>≤*p*₁</sub> = 0 and |*U*<sub>+</sub>(*m*)| ≥ 2*i* + 1. Likewise *v*<sub>2</sub>(*m*) = 2*i* gives odd(|1 − 2*i*|) = 2*i* − 1. So *U*<sub>0</sub> = ∞, and *j*<sub>0</sub>, *k*<sub>0</sub> are undefined. Separately, "fix a single concrete ε ∈ (0, 1/40)" cannot deliver η<sub>1</sub> < 1/320 by Cauchy–Schwarz. That requires √(ε *E*[*U*<sub>+</sub><sup>2</sup>]) < 1/320, i.e. ε of order 10<sup>−5</sup> or smaller.

*Fix:* *U*<sub>0</sub> is used only for the far tail, so replace it by the mean. Markov's inequality gives Σ<sub>*n*</sub>|*Y*<sub>*n*</sub><sup>far</sup>| ≤ 2<sup>−*j*₀</sup>(*C*<sub>*U*,+</sub> + *o*(1))*M*. Hence *j*<sub>0</sub> = ⌈log<sub>2</sub>(320 *C*<sub>*U*,+</sub>)⌉ works, with *C*<sub>*U*,+</sub> ≤ 1.220360 (so *j*<sub>0</sub> = 9). Alternatively, add |*U*<sub>+</sub>(*m*)| ≤ *T* to 𝒢, as in B4.1. Also state the ε constraint explicitly. With this repair the rest of the proof is unchanged.

**M3 — Theorem B5.2(2): the clause "simply nonnormal in base 2 and every base 2<sup>*j*</sup>" does not follow from the stated proof.**

*Lines:* 790 (statement), 794 (proof).

*Defect:* The proof transfers only *D*<sup>±</sup> through 2<sup>*t*</sup>*A* = *E*<sup>(*M*)</sup> + *Z* with *Z* ∈ *K*<sub>2</sub>. Translation by an element of *K*<sub>2</sub> does **not** preserve digit frequencies. For example, 0 and *E*<sub>2</sub> both lie in *K*<sub>2</sub>, yet *f*<sub>1</sub>(0) = 0 while *f*<sub>1</sub>(*E*<sub>2</sub>) → 1/2. Frequencies can change wherever the orbit of *E*<sup>(*M*)</sup>(2<sup>*k*</sup>) sits near 0 ≡ 1, and Lemma B1.2 shows that this happens on a set of positive density (dead runs). *D*<sup>−</sup> > 0 implies nonnormality but not simple nonnormality.

*Fix:* Either delete "simply nonnormal … every base 2<sup>*j*</sup>", or prove it directly by digit-mass transfer on *A*<sub>*r*,*M*</sub>(2<sup>*k*</sup>) = Σ *a*<sub>*r*,*M*</sub>(*n*)2<sup>−*kn*</sup> with *a*<sub>*r*,*M*</sub>(*n*) = #{*d* | *n* : *d* ≡ *r* (mod *M*)} ≥ 0. Off the density-zero set where some (1∗χ)(*n*) ≠ 0 (GF-13 support), *a*<sub>*r*,*M*</sub>(*n*) = τ<sup>(*M*)</sup>(*n*)/2<sup>*t*</sup>, so *s*<sub>2</sub>(*a*<sub>*r*,*M*</sub>(*n*)) = *s*<sub>2</sub>(τ<sup>(*M*)</sup>(*n*)). On the exceptional set, Cauchy–Schwarz with Σ(log τ)<sup>2</sup> ≪ *X*(log log *X*)<sup>2</sup> gives *o*(*X*). The GF-36 bound lim sup *f*<sub>1</sub> ≤ *C*<sub>true</sub><sup>(*M*)</sup>/*k* ≤ *C*<sub>true</sub>/*k* < 1/2 for *k* ≥ 3 then follows.

**M4 — The Lean blueprint's tier-1 lemma cannot reach the blueprint's own target.**

*Lines:* 625, 670–671, 674–675.

*Defect:* The target `erdosBorweinPlus_two_pow_lowerDiscrepancy_pos` asserts 13/10<sup>9</sup> ≤ *D*<sup>−</sup>. The tier-1 lemma `tsum_ePlusMajorant_lt_19_div_20` gives only *W* < 19/20. From *W* < 19/20 the best Koksma bound over all *L* is 4.967 × 10<sup>−9</sup>, at *L* = 25, which is below 13/10<sup>9</sup>. The tier-table value 1.3045e−8 silently uses the sharper certified constant 0.946830, not 19/20. A Stage-3 formalization following the blueprint would therefore fail.

*Fix:* Either state the tier-1 lemma as `ePlusMajorantMean < 23671/25000` (= 0.94684). That is above the certified 0.946830, and at *L* = 24 it yields 1.30145 × 10<sup>−8</sup> ≥ 13/10<sup>9</sup>. Or lower the target to 4/10<sup>9</sup> and keep 19/20. Assert whichever pairing is chosen in the script (see m4).

### Minor

| # | Lines | Finding | Concrete fix |
|---|---|---|---|
| m1 | 3, 192, 860; script 405–421, 528–538 | The B1 "certified prefixes" bound ⌊*b*<sup>*N*<sub>g</sub></sup>*F*⌋ by *S*<sub>lo</sub> + 1 (or ±1 or ±2). This ignores sources *m* ≤ *M*<sub>tot</sub> whose column exceeds *N*<sub>guard</sub>, whose carry *q*<sub>*N*<sub>g</sub></sub> can be ≥ 2. Reviewer recomputation with every source included found carry 0 at *N*<sub>guard</sub> in all seven series, so the digits are right, but the logic is not a certificate. Several `[exact]` checks are also tautological once *q*<sub>*n*</sub> is defined by the recurrence: mass conservation (l. 448–450) and *A*<sub>*n*</sub> + *q*<sub>*n*</sub> = prefix (l. 445). | Scale every *m* ≤ *M*<sub>tot</sub> by integer shifts, as script l. 1249–1256 already does, or add an explicit bound on *Y*<sub>*N*<sub>g</sub></sub>. Say in the note that only *q*<sub>*n*</sub> ≥ 0 and the dead-block properties carry content. |
| m2 | script 467–474 | The dead-block inequality is checked with −*G* and *a* ≤ *N* − *G*, not the lemma's −(*G* − 1) and *a* ≤ *N* − *G* + 1. This is slightly weaker than Lemma B1.2(2). | Check the lemma exactly as stated. |
| m3 | 499–500; script 1068–1070 | The note cites *W*<sub>+</sub><sup>maj</sup>/5 ≤ 0.187291 and *W*<sub>+</sub><sup>maj</sup>/8 ≤ 0.117057, but the script asserts the inequalities with the DP value *W*<sub>+</sub>. Both are true, but the stated ones are not checked. | Assert the majorant versions, or cite *W*<sub>+</sub> in the note. |
| m4 | 488, 589, 625; script 1033, 1062, 1142 | (a) A<sub>14</sub>(1, 3/2) = 80897/229376 and V<sub>circ</sub> = 453 are computed but never asserted. (b) D<sub>lean31</sub> is asserted only > 0. (c) The *E*<sub>2</sub> support check uses 2⌊√(2*N*)⌋ + 2 = 180, not the stated 2√(2*N*/3) + 2 ≈ 105.3. | Add `== Fraction(80897, 229376)`, `== 453` and `>= Fraction(13, 10**9)` (after M4), and `3·(n − 2)² ≤ 8N`, or equivalent. |
| m5 | 6; script 1107 | `math.log2` is used in floating point to choose *H* in the Lean prefix test. This conflicts with the "zero floating point" claim, although it only selects test parameters. | Compute the ceiling with integer `bit_length` arithmetic. |
| m6 | 217 | Theorem B1.3 needs *U*(*m*) ≥ 1 for all large *m*, i.e. full support, so that *Z*<sub>*a*</sub> > 0 forces *C*<sub>*k*</sub> > 0 and \|𝒢\| ≥ (1 − ε)*M*. This is not among the hypotheses. All applied families satisfy it. | Add "*a*(*m*) ≥ 1 for all large *m*" to the hypotheses. |
| m7 | 292 | "*E*<sub>*d*</sub> = *L* − *O*<sub>η</sub>(1)" should read *L* − *O*<sub>η,*p*₁</sub>(1) − *O*(log log log *L*), uniformly for *d* ≤ *D*<sub>0</sub>. This is harmless, since only *E*<sub>*d*</sub>/*L* → 1 is used. | Correct the expression. |
| m8 | 228–325 | The B1.3 proof is correct but compressed at the points where the sharp constant is decided. | Write out: the exact κ = 2 statement used, including the dimension condition and the uniformity of 1 + *O*(*e*<sup>−*s*</sup>) in (*d*, *u*<sub>1</sub>, *u*<sub>2</sub>); the shift by *r* and the small-*d* range in the Riemann sum; and the order of limits (*N* → ∞, then *G* → ∞ with *G* ≫ *B*<sub>0</sub>/ε, then ε → 0). State explicitly that a non-sharp, Erdős–Pomerance–Sárközy-type *O*(1/√*L*) bound would **not** suffice at *k* = 2. |
| m9 | 277, 840 | The sieve citation numbers could not be verified. The Fundamental Lemma is usually cited as Iwaniec–Kowalski Lemma 6.3 or Corollary 6.10, not Lemma 6.8. Tenenbaum's numbering depends on the edition. | Check against the editions used and cite edition and page. |
| m10 | 333 | "Effective constant *k*<sub>0</sub>" is given no value. It is astronomically large, since it depends on η(ε) and *B*<sub>0</sub>. | Say "effective but unspecified". §8.2 Q2 is appropriately phrased. |
| m11 | 353 | (a) *V*<sub>χ</sub>(*p*) = 0 at non-split primes violates B1.3's hypothesis *V*(*p*) = α for all large *p*. The sieve must run over split primes only (dimension 2/3, *E*<sub>*d*</sub> ≈ *L*/3). (b) *D*<sup>−</sup> > 0 is inherited from GF-36 only for moduli 7, 9, 13, or when *W*<sub>χ</sub> < 1 (Phase 24 A2.4), not for every cubic χ. | (a) State the split-prime sieve. (b) Add one sentence: the GF-36 signed transition-count transfer gives *D*<sup>−</sup> > 0 for *k* > 2*W*<sub>χ</sub>, since *W*<sub>χ</sub> < ∞. |
| m12 | 20, 329 | "Resolving GF-31's open *D*<sup>+</sup> < 1 question" is attached to *E*<sub>+</sub>. The *E*<sub>+</sub> question comes from GF-36 and GF-40; GF-31 concerns *L*<sub>±</sub>. | Attribute correctly. |
| m13 | 367 | *C*<sub>true</sub> is used without definition. | Define it: GF-36, *C*<sub>true</sub> ∈ [1.339103, 1.339116]. |
| m14 | 371 | Forcing 1 ≤ *R* ≤ 2<sup>*j*</sup> − 2 needs *M*<sub>2<sup>*j*</sup></sub> ⊆ *M*<sub>2</sub> = *K*<sub>2</sub>. | Add the one line: ‖2*y*‖ ≤ 2‖*y*‖, so the average of ‖2<sup>*n*</sup>*w*‖ is at most (2<sup>*j*</sup>/*j*) times the average over *n* ≡ 0 mod *j*. |
| m15 | 144 | "< 5/(4*p*<sup>2</sup>) for *p* ≥ 3" fails at *p* = 3, where equality holds. Only *p* > 6000 is used. | Say *p* ≥ 5. |
| m16 | 226, 775 | The *D*<sup>−</sup> > 0 threshold for *E*<sub>*b*</sub><sup>\*</sup> is written "*k* ≥ *k*<sub>0</sub><sup>\*</sup>(*b*)" in the table but stated precisely in the theorem. | Use Phase 24 Thm 5.2(1): *k* ≥ 1 for *b* ≥ 4, *k* ≥ 2 for *b* = 3, *k* ≥ 3 for *b* = 2. |
| m17 | 475 | "*E*<sub>+</sub>(64) (*k* ≥ 6 at *s* = 1)" and similar phrases are ambiguous. | Write "*E*<sub>+</sub>(2<sup>*k*</sup>) is simply nonnormal in base 2<sup>*k*</sup> for every *k* ≥ 6", and likewise for the others. |
| m18 | 625–627 | The window lengths in the tier table are not optimal. With the certified constants the best *L* gives: tier 1, 1.3409e−8 at *L* = 23; tier 2, 1.0146e−7 at *L* = 21; tier 3, 1.6829e−7 at *L* = 20; *W*<sub>+</sub><sup>maj</sup>, 1.9888e−7 at *L* = 20. | Re-optimize *L*, or state that *L* was not optimized. |
| m19 | 699 | The asymmetric relative deficit implicitly assumes sup<sub>*L*</sub> *A*<sub>*L*</sub>(1, 3/2) = *A*<sub>∞</sub> = 12/31. | State this and verify it, e.g. *A*<sub>*L*</sub>(1, 3/2) ↑ 12/31. |
| m20 | 703 | "Rise monotonically" overstates four sample points. | Write "increase at the four sampled *M*". |
| m21 | 721 | The Tenenbaum III.5.1 sharpening to *O*((log log log *M*)/√(log log *M*)) is asserted without proof. | Mark it as an unproved remark or remove it. |
| m22 | 718, 731 | The proof's bad-block term is ((log log *L*)/*L*<sup>1/4</sup>)<sup>1/2</sup> with *L* = log log *M*, i.e. (log log log log *M*)<sup>1/2</sup>/(log log *M*)<sup>1/8</sup>. The stated (log log log *M*)<sup>1/2</sup> is a true but loose upper bound, and the "=" sign is wrong. | Write ≤, or state the sharper form. |
| m23 | 736, 878 | "Precisely the same … sieve-parity obstruction" is heuristic. B1.3 itself shows that the upper-bound side is not obstructed. | Label it *Heuristic*, or say that what is missing is a lower bound on growing-shift collisions. |
| m24 | 786 | The list of φ(*M*) = 2<sup>*t*</sup> moduli omits 2, 64, 68, 80, 96, 102, 120, 128, 136, 160, 170, 192, 204, 240 before 255, and 256 between 255 and 257. | Mark it as a sample, or list it completely. |
| m25 | 799; script 1360–1364 | The list for odd(λ(*M*)) \| 3 with *M* ≤ 100 omits 32, 34, 35, 40, 45, 64, 65, 68, 70, 80, 90, 96, 97. The script checks only that the listed values are included, not that the list is complete. | List the full set, or write "for example", and make the script assert equality. |
| m26 | 822 | In Corollary B5.4(2), "*k* > 4*C*<sub>comb</sub>(1)" is insufficient. Corollary B2.2 needs *C*/*k* < 1/4 − 2<sup>−*k*−1</sup>; for example *C* = 1.999 and *k* = 8 give 0.249875 > 0.248047. | Use the exact condition. |
| m27 | 821 | "lim<sub>*k*→∞</sub> *D*<sup>−</sup>(*X*<sub>*k*</sub>; 2) = 1" is not given by Koksma, which caps near 1/4. | Add the short argument: if σ/*N* ≤ α, at most *r*α of the *n* have a nonzero signed digit in the next *r* places, so *D*<sub>*N*</sub> ≥ 1 − 2<sup>1−*r*</sup> − *r*α − *o*(1); take *r* ≍ log *k*. |
| m28 | 817 | GF-05 is cited for invariance under translation by *K*<sub>2<sup>*k*</sup></sub>, but GF-05's scope is base 2 only. | Cite GF-13 ("preserves discrepancy" in every *K*<sub>*b*</sub>) together with *M*<sub>2</sub> ⊆ *M*<sub>2<sup>*k*</sup></sub>. |
| m29 | 96, 832 | "Completely bypasses Perelli–Pintz–Salerno and Captain Sude" is misleading. B1.3 does not reach *E*(2), where *C*<sub>*U*</sub> > 1 = *k*. | Rephrase: a different route for *k* ≥ 2 that says nothing about *E*(2). |
| m30 | §6 | Some attributions are missing: Koksma's inequality (Koksma 1942; Kuipers–Niederreiter Thm 2.5.1, circular variant); uniqueness and minimality of the NAF (Reitwiesner 1960); Paley–Zygmund (1932). | Add them. Also fix the Lean comment at l. 632 ("0=A, 1=C, 2=B, 3=D" against constructor order A \| B \| C \| D) and define the helper `bitsOf`. |

---

## 7. Independent reviewer checks (outside the repository)

- **Exact *D*<sup>−</sup> values.** All six *D*<sup>−</sup>(*E*<sub>+</sub>(8); 2) lower bounds were recomputed in `Fraction` by importing the script's own certification functions. Five of the six printed values exceed the exact certified value (M1).
- **B2 table.** All 56 nonzero entries in the *k* range shown in the note were recomputed. 26 printed values exceed the certified lower bound (M1).
- **Lean tier 1.** The optimum over all *L* from *W* < 19/20 is 4.967e−9 at *L* = 25. The constant 23671/25000 is the largest five-decimal constant, and hence the weakest lemma, that still reaches 13/10<sup>9</sup> at *L* = 24. It also exceeds the certified 0.946830, so it is provable (M4).
- **B1 prefixes.** ⌊*b*<sup>*N*<sub>g</sub></sup>*F*⌋ was recomputed for all seven B1 series with every source included. The carry at *N*<sub>guard</sub> is 0 in each case, so the digits are correct (m1).
- **7-state automaton.** The script's `lump7` table matches note lines 573–581. *A*<sub>14</sub>(1, 3/2) = 80897/229376 and V<sub>circ</sub> = 453 hold exactly.
- **Moduli lists.** Both lists for *M* ≤ 300 and *M* ≤ 100 were enumerated (m24, m25).
- **By hand.** Every algebraic identity cited as "verified" was rederived: the dyadic closed form of *L*<sub>*p*</sub><sup>odd</sup>, the local excess bound, *L*<sub>2</sub><sup>+</sup>(*s*), the *s*-moment integral, the circulant solution, the jump counts, the cubic trace identity, and the counterexample *x* = 1/3.

Cross-model review is not independent human peer review.

---

## Post-Repair Verification

**Reviewer.** Claude `claude-opus-5-5`, a different provider from the author. This was a read-only verification of the repaired [`notes/phase25/generalized-lambert-and-eplus.md`](../generalized-lambert-and-eplus.md) (927 lines) and [`scripts/phase25_lambert_eplus.py`](../../../scripts/phase25_lambert_eplus.py) (1,701 lines). Neither audited file was modified, nothing was committed, and WSL was not used. Independent recomputations ran in a scratch directory outside the repository.

> **Cross-model review is not independent human peer review.** This verification is a second machine reading by a model from another provider. It authorizes no benchmark status change.

### Verdict: **ACCEPT**

| Severity | Open before repair | Open after repair |
|---|---|---|
| Critical | 0 | 0 |
| Major | 4 | 0 |
| Minor | 30 | 0 (six non-blocking nits below) |

### P1. Verifier run and agreement between script and note

`python -B scripts/phase25_lambert_eplus.py` was run on Windows (Python 3.13.13) from the worktree root. It exited with code `0` and printed:

```
ALL CHECKS PASSED in 4.61s: 186,311 [exact], 2,428 [encl], 27 [finite] (total 188,766).
```

These counts match note lines 3 and 904–907 exactly. The script contains no `float(` call, no `math.log`/`math.log2` call and no `math.ceil` call. Its only `math` uses are `isqrt`, `comb` and `lcm`. Every printed lower bound goes through the floor formatters `fmt_lb_dec`/`fmt_lb_sci`, and every printed upper bound goes through `fmt_ub_dec` or `fmt_encl`.

Each printed `[encl]` and `[exact]` line was compared with the note: the eleven B1.1 enclosures, *E*<sub>+</sub>(32), the B1 prefix statistics, the isolated arrivals 570/450/360, all 56 nonzero B2 entries, the seven B3 enclosures, π<sub>7</sub>, *A*<sub>∞</sub> = 12/31, the six *D*<sup>−</sup>(*E*<sub>+</sub>(8); 2) lines with their threshold variants, the *E*<sub>+</sub>(4) deficit and relative deficits, Tables 4.1–4.2, and the five τ<sub>*r*</sub> enclosures. All are identical.

### P2. Closure of the Major findings

| # | Status | Evidence |
|---|---|---|
| **M1** | **Closed** | All certified numbers are now floor/ceil formatted. Script l. 644–717 asserts `d ≥ Fraction(exp, 10^4)` for every nonzero B2 table entry; the dictionary holds exactly 56 nonzero endpoints (11 + 14 + 15 + 16). An independent high-precision recomputation from the certified *C*<sub>*U*</sub> upper endpoints, floored to 4 decimals, reproduces every entry of note l. 490–497 digit for digit. *E*<sub>+</sub>(32) base 32: ub = 0.43265700… gives ≤ 0.432658, and unif<sub>32</sub> = 0.44712567… gives ≥ 0.447125 (note l. 502, script line identical). The *D*<sup>−</sup>(*E*<sub>+</sub>(8); 2) bounds 1.4362e−5, 2.3642e−5, 1.9891e−7, 1.6830e−7, 1.0147e−7, 1.3412e−8 and the threshold variants 1.5894e−7, 8.9009e−8, 1.3354e−8, 1.3014e−8 are each asserted as exact `Fraction` lower bounds (script l. 1169–1184). The note copies them unchanged (l. 25, 567, 620, 652–656, 705, 916). The optimal windows were recomputed independently: 4-state *L* = 14, *W*<sub>+</sub><sup>maj</sup> and tier 3 *L* = 20, tier 2 *L* = 21, tier 1 *L* = 23. Relative deficits: 0.908260 · 3/2 − 1 = 0.36239, and 1.041984 · 31/24 − 1 = 0.345896…, printed ≤ 0.34590. Both are outward and asserted (script l. 1319–1322). The *E*<sub>+</sub>(4) deficit [0.1207056…, 0.1207966…] is printed [0.120705, 0.120797]. "> 101×" holds: 2.3642e−5 / 2.34e−7 = 101.03. |
| **M2** | **Closed** | The proof of B1.4(2) (note l. 359–378) no longer contains *U*<sub>0</sub> = max\|*U*<sub>+</sub>(*m*)\|. The far tail is now bounded by Σ<sub>*n*</sub> *Y*<sub>*n*</sub><sup>far</sup> ≤ 2<sup>−*j*₀</sup> Σ<sub>*m*∈𝒢</sub> \|*U*<sub>+</sub>(*m*)\| ≤ 2<sup>−9</sup>(*C*<sub>*U*,+</sub> + *o*(1))*M*, followed by Markov's inequality on the positions. The cutoff *j*<sub>0</sub> = ⌈log<sub>2</sub>(320 *C*<sub>*U*,+</sub>)⌉ = 9 is correct: 320 *C*<sub>*U*,+</sub> ∈ [390.495, 390.516] ⊂ (256, 512), asserted at script l. 323. Then 8 · 2<sup>−9</sup> · 1.220360 = 0.019068 < 1/40, asserted at l. 325. The *m* > *M* tail is now explicit. The constraint ε < min(1/40, 1/(320<sup>2</sup>(*M*<sub>2</sub> + 1))) gives √(ε*M*<sub>2</sub>) < 1/320 by Cauchy–Schwarz, so 8η<sub>1</sub> < 1/40. The final count is correct: 3/4 − ε − 3/40 − 1/40 > 1/2 with *k*<sub>0</sub> = 800(2*B*<sub>0</sub> + 1). |
| **M3** | **Closed** | The simple-nonnormality clause of B5.2(2) is now proved directly (note l. 826–836), no longer by translation in *K*<sub>2</sub>. Each step was rechecked. Orthogonality gives 2<sup>*t*</sup>τ<sub>*r*,*M*</sub> = τ<sup>(*M*)</sup> + Σ<sub>χ≠χ₀</sub> χ̄(*r*)(1∗χ). Every nonprincipal χ has even order *h*, so primes with χ(*p*) = −1 have density 1/*h* ≥ 2<sup>−*t*</sup>, which yields \|ℰ<sub>*M*</sub> ∩ [1, *X*]\| ≪ *X*/(log *X*)<sup>1/2<sup>*t*</sup></sup>. Off ℰ<sub>*M*</sub>, the popcounts *s*<sub>2</sub> agree by 2-scale invariance. On ℰ<sub>*M*</sub>, *s*<sub>2</sub>(τ<sub>*r*,*M*</sub>) ≤ Ω + 2, and Cauchy–Schwarz gives *o*(1). Submultiplicativity gives *C*<sub>true</sub><sup>(*M*)</sup> ≤ ∏ *L*<sub>*p*</sub><sup>pop</sup> = *C* < 29/20; the constant *C* ∈ [1.4035953, 1.4035958] is confirmed in the Phase 24 note, l. 14 and 213. Then 29/60 < 1/2 for *k* ≥ 3. Base-2<sup>*j*</sup> simple nonnormality follows by contraposition, because simple normality in base 2<sup>*j*</sup> implies simple normality in base 2. *D*<sup>+</sup> < 1 for *k* ≥ 3 also holds, since *C*<sub>*U*</sub><sup>(*M*)</sup> ≤ *C*<sub>*U*</sub> ≤ 2.076411 < 3. |
| **M4** | **Closed** | The tier-1 blueprint lemma is now `tsum_ePlusMajorant_lt_23671_div_25000` (note l. 702–703), paired with the target 13/10<sup>9</sup> (l. 706–707). An independent exact computation gives 1.33546e−8 at *L* = 23 and 1.30145e−8 at *L* = 24 from 23671/25000. Both exceed 13/10<sup>9</sup>. 23671/25000 is above the certified 0.946830, so the lemma is provable. From 19/20 the optimum is only 4.967e−9, at *L* = 25. The script asserts both the majorant pairing (l. 874) and both window values (l. 1181–1184). |

### P3. Closure of the Minor findings

| # | Status | Evidence (note line unless marked "script") |
|---|---|---|
| m1 | Closed | Script l. 446–471 scales every source *m* ≤ *M*<sub>tot</sub> directly. It adds a completeness check for displaced arrivals and a tail bound 4(*M*<sub>tot</sub> + 2). This tail bound is valid because Σ<sub>*r*</sub> 2(*M* + *r*)2<sup>−*r*</sup> = 2*M* + 4 and *a*(*m*) ≤ 2*m*, which also holds for 3<sup>ω</sup>. The note (l. 192) says which checks are tautological. |
| m2 | Closed | Script l. 503–511 checks the inequality with −(*G* − 1) and *a* ≤ *N* − *G* + 1. |
| m3 | Closed | Script l. 1191 and 1194 assert *W*<sub>+</sub><sup>maj</sup>/5 ≤ 0.187291 and *W*<sub>+</sub><sup>maj</sup>/8 ≤ 0.117057 (note l. 526–527). |
| m4 | Closed | Script l. 1139–1140 assert 80897/229376 and 453. Script l. 1181 asserts ≥ 13/10<sup>9</sup>. Script l. 1273 asserts 3(102 − 2)<sup>2</sup> ≤ 8 · 4000. |
| m5 | Closed | Script l. 1233 computes the exact integer ceiling; no `log2` remains. |
| m6 | Closed | The full-support hypothesis is added at l. 217. |
| m7 | Closed | l. 300 now reads *E*<sub>*d*</sub> = *L* − *O*<sub>η,*p*₁</sub>(1) − *O*(log log log *L*), uniformly in *d*. |
| m8 | Closed | The order of limits is at l. 228, the uniform κ = 2 dimension condition at l. 277–285, the small-*d*/shift-*r* range and the Riemann sum at l. 312–318, and the remark on the sharp constant at l. 338. The Paley–Zygmund algebra at l. 333 was rechecked. |
| m9 | Closed as requested | Editions and pages are now given (l. 285, 885). The reviewer could not check the page numbers offline (nit N5). |
| m10 | Closed | "effective (but unspecified)" (l. 346, 354). |
| m11 | Closed | The split-prime κ = 2/3 sieve is stated (l. 380). *D*<sup>−</sup> > 0 is claimed for *k* > 4*W*<sub>χ</sub>. This matches the Phase 24 transfer condition 2*W*/*k* < 1/2 (Phase 24 note l. 303). The original review's "2*W*<sub>χ</sub>" was a reviewer slip; the note's 4*W*<sub>χ</sub> is correct. |
| m12 | Closed | l. 20 and 342 attribute *E*<sub>+</sub> to GF-36/GF-40 and cubic *L*<sub>±</sub> to GF-31. |
| m13 | Closed | *C*<sub>true</sub> is defined at l. 394. |
| m14 | Closed | l. 398 adds *M*<sub>2<sup>*j*</sup></sub> ⊆ *M*<sub>2</sub> with the factor (2<sup>*j*</sup> − 1)/*j*, which is sharper than the factor suggested and correct. |
| m15 | Closed | l. 144 says "≤ for *p* ≥ 3, strictly < for *p* ≥ 5". Equality at *p* = 3 was checked. |
| m16 | Closed | The thresholds are stated precisely at l. 226 and 805. |
| m17 | Closed | The phrasing at l. 502 is fixed. The four thresholds *k* ≥ 6, 6, 5, 9 were rechecked against *C*/*k* < 1/4 − 2<sup>−*k*−1</sup>. |
| m18 | Closed | Optimal *L* values were re-derived and match (P2, M1). |
| m19 | Closed | l. 616 and 731 give superadditivity of *L A*<sub>*L*</sub> and Fekete's lemma, so sup *A*<sub>*L*</sub> = 12/31. The script checks monotonicity up to *L* = 14. |
| m20 | Closed | "increase at the four sampled *M*" (l. 735). |
| m21 | Closed | The Tenenbaum III.5.1 sharpening is removed. |
| m22 | Closed | l. 27, 750 and 761 give the sharp form (log log log log *M*)<sup>1/2</sup>/(log log *M*)<sup>1/8</sup>, with the looser form stated as ≤. |
| m23 | Closed | Labelled *Heuristic* at l. 766 and 923. |
| m24 | Closed | The complete 37-element list (l. 816) was enumerated independently and matches exactly. Script l. 1503 asserts equality. |
| m25 | Closed | The complete 50-element list (l. 843) was enumerated independently and matches exactly. The script asserts equality. |
| m26 | Closed | The exact condition *C*<sup>coset</sup><sub>comb</sub>(1)/*k* < 1/4 − 2<sup>−*k*−1</sup> is at l. 866. |
| m27 | Closed | The *r*-window argument (l. 868) was rechecked: *D*<sup>−</sup> ≥ 1 − 2<sup>1−*r*</sup> − *r*α<sub>*k*</sub>, and *r* ≍ log(1/α<sub>*k*</sub>) gives (log *k*)/*k*. |
| m28 | Closed | GF-13 with GF-01/GF-23 replaces GF-05 (l. 824). |
| m29 | Closed | Rephrased at l. 96 and 876. |
| m30 | Closed | Paley–Zygmund, Koksma/Kuipers–Niederreiter and Reitwiesner are attributed (l. 879). The Lean comment is fixed (l. 661), and `bitsOf` is defined (l. 676–677). |

### P4. New issues introduced by the repair

No new mathematical error, rounding slip or broken formula was found. Six non-blocking nits remain:

- **N1 (presentation).** The [`exact+finite`] and [`finite`] display statistics still use implicit float division (script l. 517–521, 594, 1392). Examples are `len(dead) / N_bits` and `bit_count() / N_bits`. These values are only printed, never asserted, and feed no certificate. The note's claim at l. 6 ("zero floating-point checks inside any certificate") and its §7 `[encl]` description are therefore accurate. A `Fraction` would remove the last float use entirely.
- **N2 (reproducibility).** Four tier values cannot be reproduced from the six-decimal upper bounds displayed in the note: 1.9891e−7, 1.6830e−7, 1.0147e−7 and 1.3412e−8. Recomputing from 0.936453, 0.937255, 0.939378 and 0.946830 gives 1.98885e−7, 1.68291e−7, 1.01467e−7 and 1.34095e−8. The stated values do follow from the script's sharper exact rational upper bounds, and the script asserts them. They are valid certified bounds, but a parenthetical saying so would help readers.
- **N3.** In B4.1 (l. 763), *B*<sub>0</sub> = ⌈*L*<sup>1/4</sup>⌉ + ⌊*L*<sup>1/4</sup>⌋ ≤ 2*L*<sup>1/4</sup> + 1, not ≤ 2*L*<sup>1/4</sup>. This is harmless inside *W*.
- **N4.** l. 540 attributes "> 61×" to the factor-2*L* gain at *L* = 14. At equal *L* that gain is only about 28×. The 61× compares against GF-40's quoted 2.34e−7, which used a different window and constant. This wording predates the repair.
- **N5.** The sieve citation pages (Halberstam–Richert Thm 2.5, pp. 82–85; Tenenbaum 3rd ed. I.4 Thm 3, p. 60; Iwaniec–Kowalski §6.4, pp. 158–160) should be checked by a human against physical copies.
- **N6.** In B1.4(2), the *m* > *M* tail is written *O*(*M*<sup>ε</sup> log *M*). Here ε is reused both as the sieve parameter and as the divisor-bound exponent.

### P5. Conclusion

All four Major findings (M1–M4) and all thirty Minor findings (m1–m30) are closed. No Critical or Major issue remains. **Verdict: ACCEPT.**

This acceptance concerns internal consistency and proof checking by a second model only. **Cross-model review is not independent human peer review.** It authorizes no change to any benchmark status in `docs/benchmarks/classical-constants.toml` or `docs/benchmarks/arithmetic-families.toml`. The evidence labels in the note stand as written: Paper proof, Finite certificate, External input, and an uncompiled Lean blueprint.
