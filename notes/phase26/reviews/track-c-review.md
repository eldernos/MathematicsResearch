# Phase 26 Track C — Independent Cross-Provider Referee Review (`C1`–`C5`)

**Audited material.**
- [`notes/phase26/mesoscopic-carry-correlations.md`](../mesoscopic-carry-correlations.md) (639 lines; "the note").
- [`scripts/phase26_mesoscopic_carries.py`](../../../scripts/phase26_mesoscopic_carries.py) (2,560 lines; "the script").
- I used these files only to check the note's citations and benchmark claims: `GF-41` ([`notes/phase25/e4-carry-correlations.md`](../../phase25/e4-carry-correlations.md), Theorem 4.3, `LLB(c)` and `PUB(C)`), `GF-42` ([`notes/phase25/generalized-lambert-and-eplus.md`](../../phase25/generalized-lambert-and-eplus.md), the definition of *K*<sub>*b*</sub>, B1.3–B1.5 and Open Question 4), `BC-37`/`BC-38`/`BC-39` in [`docs/benchmarks/classical-constants.toml`](../../../docs/benchmarks/classical-constants.toml), and [`docs/benchmarks/SCHEMA.md`](../../../docs/benchmarks/SCHEMA.md).

**Reviewer.** Claude `claude-opus-5-5`, acting as the review sub-agent on branch `research/phase-26-arithmetic-amplification`, 2026-11-28.

**Method.** The review was read-only. This report is the only file written in the repository; nothing was committed and WSL was not used. Python 3.13.13 ran directly on Windows (`python -B`). I re-derived every proof by hand and tried to break each step. I then wrote two verification scripts from scratch in a session scratch directory outside the repository. Neither imports the audited script.
- `c53_test.py` (with a driver, `c53_k1.py`) tests Theorem C5.3. It has its own Miller–Rabin and Pollard–Brent factoriser and its own divisor-sum coefficients taken from the Lambert definitions. Its digit expansions are computed directly from Σ 1/(2<sup>*kn*</sup> ∓ 1), so the τ-representation is never used for them.
- `c4_c1_test.py` cross-checks C1, C4.2, C4.3, C3.2, C5.1 and C5.2.

Float computations in those scripts are **referee cross-checks (numerical evidence)**, not certificates. The scripts are not committed; §2 describes them fully enough to reproduce.

> **Cross-model review is not independent human peer review.** This report is a machine reading by a language model. It does not replace refereeing by human specialists in sieve methods, probabilistic number theory or digit expansions. Under `AGENTS.md` and `docs/benchmarks/SCHEMA.md`, this review cannot by itself change the status of any benchmark constant (`BC-01`…`BC-50`) or arithmetic-family benchmark. A status changes only through a registered result (§6).

---

## Verdict

### Track C as a whole: **REVISE**

Major text revisions are needed, but no theorem has to be withdrawn.

| Severity | Count | Nature |
|---|---|---|
| Critical | 0 | No theorem was broken and no headline constant was refuted. |
| Major | 5 | **M1:** C4.2's written proof does not literally yield *k*<sub>0</sub> = 25. A dyadic decomposition is needed, and the certified margin at *k* = 25 is only 1.0%. **M2:** C5.1(4) uses a false lemma, and its general odd *m* ≥ 5 case is only sketched. **M3:** C5.2's *D*<sup>+</sup> < 1, ∉ *K*<sub>2</sub> and *D*<sup>−</sup>(2<sup>*k*</sup>) → 1 claims are unproven and do not state a *k*-range. **M4:** C1.4(3) claims a stronger dual-LP barrier, with a necessity statement, than it proves. **M5:** several sieve and probabilistic arguments labelled "Paper proof" are sketches (C1.4(2), C4.3(3), C3.3(3)). |
| Minor | 16 | Arithmetic slips in C5.3's counting, boundary terms, citation precision, labels, an undefined quantity, and script hygiene. |

### Theorem C5.3: **ACCEPT WITH MINOR POLISH**

C5.3 claims base-2 disjunctivity of *E*(2<sup>*k*</sup>), *E*<sub>odd</sub>(2<sup>*k*</sup>) and *E*<sub>+</sub>(2<sup>*k*</sup>) for every *k* ≥ 1. After a line-by-line attack and independent end-to-end tests, I found **no gap that invalidates it**, including in the signed case *E*<sub>+</sub>. Its slips (m1–m5) are local and affect only constants that the stated bound already absorbs. My advice on `BC-38` and `BC-39` is in §6.

---

## 1. Reproduction and zero-float audit

| Check | Result |
|---|---|
| `python -B scripts/phase26_mesoscopic_carries.py` | Exit code 0. Prints `ALL CHECKS PASSED: 20386 [exact] + 2780 [encl] = 23166 zero-float theorem checks (plus 3 [finite] prefix measurements).` It ran in about 5 s (the note says about 11 s). |
| AST scan of the script | There are **no** float literals and **no** `float`/`sqrt`/`log`/`exp`/`sin`/`cos` calls outside f-string failure messages. The six `pow` calls are all integer modular `pow`. |
| Instrumented re-execution | I wrapped every `+ − × / **` operation outside f-strings in a type trap and re-ran the whole script. **No operation produced a float.** The only augmented true division, `u /= 2` in `ln_encl_rat`, is reached only with `Fraction` arguments; all three call sites were checked. |
| Outward rounding | Every decimal endpoint quoted in the note is pinned by `assert_outward_dec` or `dec_floor`/`dec_ceil` in `main()`. |

The zero-float claim is therefore **verified**, with one caveat. The f-string failure messages call `float()` eagerly, but only to format text; no check outcome depends on them.

The count of 23,166 is accurate but inflated. Much of the `[exact]` count consists of per-index trivialities, such as ε<sub>*n*</sub> ∈ [−1/2, 1/2) and *a*′<sub>*n*</sub> ∈ {−1, 0, 1} for each *n* ≤ 1200 and each *k* ∈ {3, 4, 5}. The C5.3 certificate itself is thin (m13).

---

## 2. Theorem C5.3: line-by-line audit and independent tests

### 2.1 The proof, step by step

Let *F* = Σ *a*(*m*) 2<sup>−*km*</sup>, where *a* is τ, τ<sub>odd</sub> or *a*<sub>+</sub>. The planted index *m*<sub>0</sub> = 3<sup>*W*−1</sup> *P*<sub>0</sub> *u*(*t*) is odd, so all three coefficients equal *W* · 2<sup>*V*<sub>0</sub></sup>. Put *J* = *k m*<sub>0</sub> − *V*<sub>0</sub>. Then

```math
2^J F = A \cdot 2^{\ell+4} + W + \varepsilon, \qquad
\varepsilon = 2^{-V_0} \sum_{j \ge 1} a(m_0 + j)\, 2^{-kj},
```

where *A* is an integer that collects every term with *m* < *m*<sub>0</sub>. I checked each component.

1. **Target coefficient.** τ(3<sup>*W*−1</sup>) = *W*, and *u*(*t*) is squarefree and coprime to 6*P*<sub>0</sub>. Since *m*<sub>0</sub> is odd, τ<sub>odd</sub>(*m*<sub>0</sub>) = τ(*m*<sub>0</sub>). Also *a*<sub>+</sub>(*m*<sub>0</sub>) = (1 − 0) τ(*m*<sub>0</sub>) is **positive**, so the sign question never arises at the target. ✓
2. **Lower terms *m* = *m*<sub>0</sub> − *s* with 1 ≤ *s* ≤ *S*.**
   - From *m*<sub>\*</sub> ≡ *s* + *Q*<sub>*s*</sub> (mod *Q*<sub>*s*</sub><sup>2</sup>) we get *v*<sub>*p*</sub>(*m*<sub>0</sub> − *s*) = 1 for every *p* | *Q*<sub>*s*</sub>.
   - All three coefficient functions are multiplicative. For *a*<sub>+</sub> this holds because *a*<sub>+</sub> = 1 ∗ ((−1)<sup>*n*−1</sup>). Each takes the value 2 at an odd prime, so 2<sup>*R*−*ks*</sup> divides *a*(*m*<sub>0</sub> − *s*). This holds **regardless of sign and including the value 0** (which occurs when *m*<sub>0</sub> − *s* ≡ 2 (mod 4)).
   - The term's contribution is then (*a*/2<sup>*R*−*ks*</sup>) · 2<sup>*R*−*V*<sub>0</sub></sup>, which lies in 2<sup>ℓ+4</sup>ℤ because ω(*u*) ≤ ⌊3*L*⌋ gives *R* − *V*<sub>0</sub> ≥ ℓ + 4. ✓
   - **Negative arrivals for *m* < *m*<sub>0</sub> cannot touch the planted word.** They are exact integer multiples of 2<sup>ℓ+4</sup>, and any borrow happens entirely above the most significant bit of *W*.
3. **Lower terms with *s* > *S*.** Here *ks* ≥ *k*(*S* + 1) > *R*, so the exponent *ks* − *V*<sub>0</sub> is at least ℓ + 5 and no 2-adic information about *a* is needed. ✓
4. **Upper tail (*m* > *m*<sub>0</sub>), both signs.**
   - |*a*<sub>+</sub>(2<sup>*e*</sup>*u*)| = |1 − *e*| τ(*u*) ≤ (*e* + 1) τ(*u*) = τ(2<sup>*e*</sup>*u*), so a single **absolute** bound controls positive and negative tails together.
   - |ε| ≤ 2<sup>−*V*<sub>0</sub></sup> Σ τ(*m*<sub>0</sub> + *j*) 2<sup>−*kj*</sup>. Condition (3), with *V*<sub>0</sub> ≥ *r* ≥ 2 log<sub>2</sub> log *X*, makes the head at most 1/8. The bound τ(*n*) ≤ 2√*n* makes the part with *j* > *S*<sub>2</sub> = *O*(*X*<sup>−1/2</sup>). ✓
   - There is no need to make *a*<sub>+</sub>(*m*<sub>0</sub> + *j*) a "desired residue". The proof plants nothing to the right of *m*<sub>0</sub>; it only needs the Markov condition (3).
5. **Guard bit.** Because *W* is odd, ⌊*W* + ε⌋ ∈ {*W* − 1, *W*} for every ε ∈ (−1, 1), and *W* − 1 differs from *W* only in the least significant bit. The lemma is robust: it needs only |ε| < 1, while the proof supplies |ε| < 1/4. The leading 1 in *W* is not even needed; *W* = 2 val(*w*) + 1 works too (optional simplification). ✓
6. **Reading positions.** ⌊2<sup>*J*</sup>*F*⌋ ≡ ⌊*W* + ε⌋ (mod 2<sup>ℓ+2</sup>), so *d*<sub>*J*−ℓ</sub> ⋯ *d*<sub>*J*−1</sub> = *w*, that is, an occurrence at *n* = *J* − ℓ − 1. ✓
7. **CRT consistency for *E*<sub>odd</sub>.**
   - The planting uses odd primes only; *v*<sub>2</sub> is never controlled or needed.
   - *Q*<sub>*s*</sub> divides the odd part of *m*<sub>0</sub> − *s*, which is all that τ<sub>odd</sub> sees.
   - The moduli 2, 3<sup>*W*</sup>, *P*<sub>0</sub><sup>2</sup> and *Q*<sub>*s*</sub><sup>2</sup> are pairwise coprime. ✓
8. **Gcd claim behind condition (3).** A prime *p* | *Q*<sub>*s*</sub> divides *m*<sub>\*</sub> + *j* only if *p* | (*s* + *j*), and *s* + *j* ≤ *S* + *S*<sub>2</sub> < *p*. A prime *p* | *P*<sub>0</sub> divides *m*<sub>\*</sub> + *j* only if *p* | *j*. Both are impossible. ✓
9. **Exponent.**
   - *R* = (2/ln 2 + 3 + *o*(1)) *L*, and (2/ln 2 + 3)<sup>2</sup> = 34.6378… < 35.
   - log *M*<sub>0</sub> ≤ (*R*<sup>2</sup>/*k*)(1 + *o*(1)) *L* + *O*(*L*<sup>2</sup>).
   - The planted primes are ≍ log *X*. Since *T*<sub>pr</sub> = *O*(*L*<sup>2</sup>), each satisfies log *p* = *L* + *O*(1).
   - The final step from *N* exp(−(34.64/*k* + *o*(1)) *L*<sup>3</sup>)/*O*(*k*) to *N* exp(−(37/*k*)(log log *N*)<sup>3</sup>) is valid for fixed *k* and *w*. ✓
10. **Distinct positions.** *k*(*m*<sub>0</sub>(*t*<sub>2</sub>) − *m*<sub>0</sub>(*t*<sub>1</sub>)) ≥ *kM*<sub>0</sub> ≫ 3*L* ≥ |Δ*V*<sub>0</sub>|. ✓

The minor slips in this proof are m1–m5 in §5. **None affects validity.**

### 2.2 Independent tests

All tests below **pass**. (A)–(C) are exact; (D) and (E) are exact rational window evaluations.

| Test | What it checks | Result |
|---|---|---|
| (A) Coefficient formulas | τ, τ<sub>odd</sub> and *a*<sub>+</sub> = (1 − *v*<sub>2</sub>) τ(odd part), computed by brute divisor sums from the **Lambert definitions**, including *a*<sub>+</sub>(*m*) = Σ<sub>*d*\|*m*</sub> (−1)<sup>*m*/*d*−1</sup>; also \|*a*\| ≤ τ | 20,000 values of *m* × 3 families, all equal |
| (B) Multiplicativity | 2<sup>ω(*Q*)</sup> divides *a*(*n*) whenever *Q* is odd, squarefree and *Q* ‖ *n* | 59,398 values *n* ≤ 60,000 × 3 families |
| (C) Guard-bit lemma | Every word with ℓ ≤ 10; *W* in the note's encoding, the minimal encoding and a negative odd encoding; exact ε ∈ (−1, 1), including ±(1/2 ∓ 10<sup>−12</sup>) and 1 − 10<sup>−9</sup> | 73,656 cases |
| (D) Natural occurrences of the deterministic core | For every *m*<sub>0</sub> whose own coefficient structure meets the hypotheses (lower terms ≡ 0 mod 2<sup>ℓ+2</sup> and \|ε\| < 1), the predicted bits of ⌊*W* + ε⌋ are compared with digits computed **directly from Σ 1/(2<sup>*kn*</sup> ∓ 1)** to 9,000 bits | *E*, *k* = 3: 1,628/1,628 · *E*<sub>odd</sub>, *k* = 3: 1,934/1,934 · ***E*<sub>+</sub>, *k* = 1: 572/572** · *E*<sub>+</sub>, *k* = 3: 1,668/1,668. For *E* and *E*<sub>odd</sub> at *k* = 1, no natural instance occurs at this scale. |
| (E) Toy CRT planting, end to end | The note's recipe (encoding 1·*w*·1, 3<sup>*W*−1</sup>, *P*<sub>0</sub>, *Q*<sub>*s*</sub> with *R* − *ks* primes), with toy *r* = 2 and ω(*u*) ≤ 1. Every exactness condition is verified directly. Digits at *J* − ℓ … *J* − 1 are recomputed **from scratch**: for *k* = 3, the whole window and the tail out to *j* = 22 are fully factorised, with rigorous bounds beyond; for *k* = 1, the lower window uses multiplicativity (validated by (B)) and the tail uses rigorous τ upper bounds | ***k* = 3:** *E*(8), *E*<sub>odd</sub>(8) and *E*<sub>+</sub>(8) × words `0, 1, 00, 01, 10, 11` with non-square moduli, plus `0, 1` with the note's **square moduli**: 24/24 correct. This includes negative ε for *E*<sub>+</sub>(8), for example ε = −0.4843 for `00` and −0.2422 for `10`. ***k* = 1:** *E*(2), *E*<sub>odd</sub>(2) and ***E*<sub>+</sub>(2)** with *w* = `1` (*m*<sub>0</sub> of 30–31 digits, *V*<sub>0</sub> = 3; ε ∈ [−0.0185, −0.0068] for *E*<sub>+</sub>(2)): 3/3 correct. |

Test (E) at *k* = 1 found no admissible *t* for the other words within the toy search ranges: *t* ≤ 6,000 for *E* and *E*<sub>odd</sub>, and *t* ≤ 3,000 for *E*<sub>+</sub>, with words `0`, `01` and `10`. Every *t* that passed the toy filters gave the correct digits. This limits the **toy**, not the proof. The toy fixes *V*<sub>0</sub> = 3, so its tail condition Σ τ(*m*<sub>0</sub> + *j*) 2<sup>−*j*</sup> < 8 is rare. The theorem instead takes *V*<sub>0</sub> ≥ 2 log<sub>2</sub> log *X* precisely so that the Markov condition (3) excludes only *o*(*T*) values of *t*.

**Conclusion on the "hidden killers".**
- Negative arrivals for *E*<sub>+</sub> cannot reach the planted window from below, because those terms are exact multiples of 2<sup>ℓ+4</sup>.
- From above, they are controlled by the same absolute τ-bound as for *E*.
- *E*<sub>odd</sub> needs no 2-adic control.
- The constant 37/*k* and the exponent (log log *N*)<sup>3</sup> are correct.

---

## 3. Track C4

### 3.1 C4.1 (signed carry conservation and exponential carry growth)

The algebra is correct. *a*′<sub>*n*</sub> = *C*<sub>*k*</sub>(*n*) + *q*<sub>*n*</sub> − 2*q*<sub>*n*−1</sub> lies in (−3/2, 3/2) ∩ ℤ. The telescoping in (1) is right. In (2), *q*<sub>*n*</sub> is odd at an isolated odd arrival and doubles across *t* empty columns, and the intervals are disjoint. In (3), 2ε<sub>*n*−1</sub> − ε<sub>*n*</sub> = ±1 forces {2<sup>*n*−1</sup>*x*} ∈ [1/4, 3/4]. Sign flips and negative borrows are handled correctly, because every step uses only |·| and parity.

There is one boundary slip (m6). The exact constant in (2) should be 2(|*q*<sub>*N*</sub>| − |*q*<sub>0</sub>|)/(2<sup>*t*+1</sup>*N*), not (|*q*<sub>*N*</sub>| − |*q*<sub>0</sub>|)/(2<sup>*t*+1</sup>*N*). It is asymptotically irrelevant.

### 3.2 C4.2 (*k*<sub>0</sub> = 25)

**Constants recomputed independently (float cross-check):**

| Quantity | Note (certified) | Referee float |
|---|---|---|
| eff<sub>σ<sub>2</sub></sub> (10-shell Abel sum) | ≤ 1.05623 | 1.053392 |
| *p*<sub>sm</sub> | ≤ 0.000659 | 0.000658 |
| *p*<sub>*W*</sub> | ≤ 0.047083 (valid upper Riemann bound) | 0.044286 (grid with *N* = 96,000) |
| *C*<sub>*U*,+</sub> | [1.220305, 1.220322] | 1.220310 |
| *k*<sub>req</sub> | ≤ 24.75247 | 24.48 |
| 1 − *D*<sup>+</sup> at *k* = 25 | ≥ 4.36 × 10<sup>−5</sup> | about 9.2 × 10<sup>−5</sup> |

I also checked the ingredients one by one:
- **Selberg sieve function.** The σ<sub>2</sub> closed form on [2, 4], e<sup>−2γ</sup>(2*v*<sup>2</sup> − *v*<sup>2</sup> ln *v* − 2*v* + 1/2), satisfies the delay equation (*v*<sup>−2</sup>σ<sub>2</sub>(2*v*))′ = −2*v*<sup>−3</sup>σ<sub>2</sub>(2*v* − 2). The upper multiplier 1/σ<sub>κ</sub>(log *D*/log *z*) is the correct form of the Selberg Λ² sieve, not the β-sieve *F*/*f* functions.
- **Monotone stepping.** The script's integer recursion encloses σ<sub>2</sub> correctly in both directions. I re-derived both step bounds.
- **Abel summation.** Replacing *f*<sub>*i*</sub> by upper bounds needs the Rankin weights to be non-increasing, so that the summation-by-parts coefficients *R*<sub>*i*</sub> − *R*<sub>*i*+1</sub> are ≥ 0. They are: (0.732, 0.471, 0.253, 0.115, 0.0444, 0.0148, 0.00518, 0.00134, 8.0 × 10<sup>−5</sup>). The note should state this explicitly (m7).
- **Factors.** The factors 9/16 (joint density of *m* ≢ 2 and *m* + *d* ≢ 2 mod 4, averaged over *d* mod 4), 3 × 7 = (*t* + 1)(2*B* − 1), 7/8 = 1 − 2<sup>−3</sup> and the Σ<sub>*d*</sub> Gaussian sum 1/*k* are all correct. The 7 choices of Δ*W* are lossy but valid.
- I found **no missing factor of 2** and no misapplied β-sieve constant.

**M1 (Major): the written proof does not literally give *k*<sub>0</sub> = 25, and the margin is 1%.**
- The note defines *G*<sub>+</sub> ⊆ (*M*/2, *M*] and uses that range for the claim that "*W*(*m*) ≥ 1 is automatic". The 7-value Δ*W* range depends on this.
- Yet the count bound |*G*<sub>+</sub>| ≥ (3/4)(1 − 2(*p*<sub>sm</sub> + *p*<sub>*W*</sub>))*M* uses all *m* ≤ *M*, while Σ|*C*<sub>*k*</sub>| is taken over all *m* ≤ *M*.
- Read literally, with good sources only in (*M*/2, *M*], the bound gives **about 37**, not 25.
- Allowing *W* = 0 on [1, *M*] instead would widen Δ*W* to 9 values and give about 31.8.
- **Fix.** Define *G*<sub>+</sub> as a union over dyadic blocks (*M*/2<sup>*i*+1</sup>, *M*/2<sup>*i*</sup>], each with its own *z*<sub>0</sub>. Show that *p*<sub>sm</sub>, *p*<sub>*W*</sub> and eff are scale-invariant per block, that collisions across blocks are *O*(log *M*), and that blocks below *M*/2<sup>*K*</sup> contribute at most 2<sup>−*K*</sup>.
- **Fragility.** With the certified numbers, the collision term has a multiplicative slack of only **×1.0100** at *k* = 25 (×1.021 with the true value of *p*<sub>*W*</sub>). Any omitted factor ≥ 1.01 would push *k*<sub>0</sub> to 26. Every *o*(1) term must therefore genuinely vanish: the local-limit uniformity of the Cramér-tilted Gaussian sum over *d*, the *s*<sub>≤*p*<sub>1</sub></sub> conditioning, and the sieve remainders. This is plausible, but it must be written at the level of a paper proof (see M5).

The large-window barrier in C4.2(3) is correct. The sequence (−1)·2<sup>−12*m*</sup> + 2·2<sup>−(12*m*+1)</sup> = 0 has arrival rates 1/6 and 1/12 per column, matching *E*<sub>+</sub>(8). The conditional threshold *C* < (84 − 16*C*<sub>*U*,+</sub>)/63 = 1.02341 is correct.

The script contains a conditional assertion (line 1841): if *k*<sub>req</sub> ≥ 25 it falls back to checking < 26. It is harmless only because `main()` pins `k0_cert == 25` and the value 24.75247. Remove it (m13).

### 3.3 C4.3 (exact floor *m*<sub>1</sub><sup>(2<sup>*L*</sup>)</sup> and base-256 simple nonnormality of *E*<sub>+</sub>(8))

**Re-derived and verified exactly.**
- The automaton and the carry identity *s*<sub>*n*</sub> = *b*<sub>*n*</sub> + *c*<sub>*n*</sub> − 2*c*<sub>*n*−1</sub>, with *c* ∈ {0, 1}, are correct.
- **Brute force for *L* = 1…14:** min<sub>*c*<sub>0</sub>,*c*<sub>*L*</sub></sub> *d*<sub>*L*</sub> = min(*w*<sub>±</sub>(*w*), *w*<sub>±</sub>(*w* + 1), *w*<sub>±</sub>(2<sup>*L*</sup> − *w*), *w*<sub>±</sub>(2<sup>*L*</sup> − 1 − *w*)) for every *w*, and the average equals 1/3 − (2 + (−1/2)<sup>*L*−1</sup>)/(9*L*) **exactly**.
- **Attainment for *L* = 2…10.** I chose complement-symmetric optimal arcs, forced the arc 0 → 1 for *w* = 1 and built a Hierholzer circuit. The arcs are balanced, the circuit visits all 2<sup>*L*</sup> digits once starting from carry 0, and its weight equals *L* · 2<sup>*L*</sup> · *m*<sub>1</sub> exactly.
- **Values.** 135/448 at *L* = 7 and 313/1024 at *L* = 8. ✓

**Inputs.**
- The true *W*<sub>+</sub> is about 0.908182 by my independent float computation of the distribution of *U*<sub>+</sub>, inside the note's [0.908065, 0.908215].
- *W*<sub>+</sub><sup>maj</sup> is about 0.936414, inside [0.936413, 0.936420].
- So *W*<sub>+</sub>/3 ≈ 0.302727 lies strictly between *m*<sub>1</sub><sup>(128)</sup> = 0.301339 and *m*<sub>1</sub><sup>(256)</sup> = 0.305664.
- **Conclusions.** *E*<sub>+</sub>(8) is simply nonnormal in base 256, with the NAF-weight method sharp at *L* = 8. *E*<sub>+</sub>(2<sup>*k*</sup>), *k* ≥ 4, is simply nonnormal in bases 4 and 8. Both hold.

**Remarks.**
- The lower bound applies to every **non-dyadic** *x*, not only irrational *x*. Either extend the definition, or cite the irrationality of *E*<sub>+</sub>(2<sup>*k*</sup>) (P. Borwein 1991/92) (m8).
- C4.3(3), the multiscale block barrier, uses an undefined quantity *c*<sub>2,*B*(*M*)</sub><sup>block</sup> and gives no proof. It should be moved to a remark or properly defined and proved (part of M5).

---

## 4. Tracks C1–C3, C5.1–C5.2

### 4.1 C1 and C2

**Exact and numerical checks.**
- **C1.1(1)** holds on all 64 triples, with equality on 48 and slack +1 on 16 (exact).
- **Cesàro index shift.** The index shift in C1.1(2) is right: *u* sits at (*j* + 1, *j* + 2) and *v* at (*j* + 2, *j* + 3), so shifting *v* by one gives Ψ(*J*<sub>*j*+1</sub> mod 4, *J*<sub>*j*+2</sub> mod 8) + *O*(1/*N*).
- **Star mixture (C1.1(3)).** Its total mass is 1, its one-column marginal is *p*<sub>*J*</sub>, and its windows evaluate to (2*a* mod 8) and (5*a* mod 8).
- **Float cross-checks:**

| Quantity | Note | Referee float |
|---|---|---|
| μ | [2.076318, 2.076347] | 2.076324 |
| *t*<sub>3</sub> | [0.370228, 0.370231] | 0.370230 |
| E[Ψ<sub>2,adj</sub>] | [0.356817, 0.356889] | 0.356852 |
| Star converse | ≥ 0.380742 | 0.380759 |
| E<sub>*Q*<sub>3</sub></sub>[*R*<sub>3</sub>/8] | [0.323087, 0.323132] | 0.323110 |

- **C1.2.**
  - The 8-atom law matches all 10 factorial moments of order ≤ 2 exactly, and E[*f*<sub>iid</sub>] ≈ 0.400984 (note: ≥ 0.400955).
  - I re-derived the Shifted Split-Bonferroni polynomial. The binomial identity Σ<sub>*j*≤*K*</sub> (−1)<sup>*j*</sup> C(*t*, *j*) = (−1)<sup>*K*</sup> C(*t* − 1, *K*) and the product-kills-negatives argument both hold.
  - The Poisson expectation formula is correct: E[∏ C(*N*<sub>*i*</sub>, *k*<sub>*i*</sub>) C(*S* − |*k*|, *j*)] = ∏(λ<sub>*i*</sub><sup>*k*<sub>*i*</sub></sup>/*k*<sub>*i*</sub>!) · Λ<sup>*j*</sup>/*j*!.
- **C1.3 and C2.**
  - On a 200,000-point grid, *T*<sub>12</sub> − **1**<sub>[1/2,1)</sub> has minima 0.000455 and 0.000521, both positive and consistent with the Sturm root counts (0, 0).
  - I re-derived the Bonferroni excess formula. Its values are 0.017945 at *r* = 44, 0.006381 at *r* = 45 and 0.002219 at *r* = 46, matching the note.
  - The *M* = 11 countermeasure duality argument is sound: a probability measure with the same 11 Fourier coefficients defeats every majorant of degree 11.

**M4 (Major), C1.4(3).** C1.4(3) says the dual-LP maximum stays ≥ 0.380742 "even if the lattice-scale second moments were exact", and that crossing *t*<sub>3</sub> "**requires** at least one" of three listed inputs. Neither is proved.
- The star countermodel is defined on residues *J* mod 8. It has not been lifted to count processes (*N*<sub>*j*</sub>, marks) that also match E[*N*<sub>*j*</sub>(*N*<sub>*j*</sub> − 1)] = 1/4 and E[*N*<sub>*j*</sub>*N*<sub>*j*+*h*</sub>] = 1/4. Its alternating structure makes such a lift non-obvious.
- The three listed inputs are shown to be **sufficient**, not **necessary**.
- **Fix.** Restrict the statement to "one-column residue laws plus stationarity" and "order-3 marked moments at a single window", and replace "requires" with "is achieved by any of".

**M5 (part), C1.4(2).** The "explicit absolute constant *C*<sub>lat</sub>" is never stated, and the proof is a single sentence.

### 4.2 C3

**C3.1 (`PUB(C)`).** The statement matches `GF-41` Theorem 4.3 verbatim, and the structure of the proof is sound.
- *M*<sub>𝒬</sub> ≤ 30*L*<sup>3/2</sup>.
- Every prime outside 𝒬 divides at most one of *n*<sub>0</sub>, *n*<sub>1</sub>, *n*<sub>2</sub>.
- The 81<sup>2</sup> box is right.
- The identity 3 − cos(*t*<sub>1</sub> + *t*<sub>2</sub>) − cos *t*<sub>1</sub> − cos *t*<sub>2</sub> = 2Σ sin<sup>2</sup>(·/2) ≥ (2/π<sup>2</sup>)(*t*<sub>1</sub><sup>2</sup> + *t*<sub>2</sub><sup>2</sup>) holds.
- The shell bounds are right: ω(*V*<sub>*j*</sub>) ≥ *w*<sub>*j*</sub>/16, *W* ≤ *x*<sup>1/12</sup>, Σ 1/*p* over (*z*<sub>*j*</sub>, *z*<sub>*j*−1</sub>] equals ln 2, and the total remainder is *x*<sup>3/4+ε</sup>.

Hall–Tenenbaum Theorem 01 is **not needed** (m11). Because *u* is a squarefree radical, Σ<sub>*m*≤*X*</sub> *u*(*m*; *z*)<sup>θ</sup> ≤ *X* ∏(1 + (*p*<sup>θ</sup> − 1)/*p*) is elementary. Dropping this input would strengthen the evidence label.

**C3.2.** Correct.
- I verified the CRT identity ω(*m* + *i*) = 2*i* + ω(*L*<sub>*i*</sub>(*t*)) by factorisation on 113 pairs (*t*, *i*) at *k* = 3.
- The sum-of-squares identity is (*x* − 3)<sup>2</sup>(4*x* − 3) = 4*x*<sup>3</sup> − 27(*x* − 1)<sup>2</sup>.
- The reverse-Markov step needs 0.0026√*L* > 1, that is, log log *N* ≳ 1.5 × 10<sup>5</sup>. This is "sufficiently large" but worth stating.
- "Each prime ≪ *k*<sup>2</sup> log *k*" is wrong: the primes exceed *k*<sup>3</sup>. The bound log *p* = *O*(log *k*) is unaffected (m12).

**C3.3.** Admissibility is correct for every *p*, including planted primes, where all slopes vanish modulo *p* and the constants are ±1 or (*i* − *j*)*B* ≢ 0.
- The forms have **different slopes** *BQ*/*P*<sub>*i*</sub>. "*k* = 50" therefore needs the linear-forms formulation of the Maynard sieve combined with Polymath8b's computation *M*<sub>50</sub> > 4 at θ = 1/2 − ε, not the monic statement DHL[50, 2] as cited. The note should name the exact proposition it uses; I did not verify proposition numbers. GGPY likewise needs its general-forms statement (m14).
- The qualitative bound *N*/(log *N*)<sup>*O*(1)</sup> is robust either way.
- The parity discussion in (3) is heuristic and should be labelled as such (part of M5).

### 4.3 C5.1

- **Case *m* = 3.** *M* ∈ {31, 43, 109, 127} all have *p* = *x*<sup>2</sup> + 27*y*<sup>2</sup>, so χ(2) = 1, as claimed. The moduli {7, 9, 13, 19, 37} have χ(2) ≠ 1. The coefficient formula *c* = (1 − *e*)(2/√3) Im(1 ∗ χ)(*u*) checks out, and the ρ values rest on the `GF-44` lemma.
- **Case *m* even** (m9). "Dirichlet density 1/φ(*m*)" should read 1/*m*. The external-inputs column says "None", yet the proof invokes Selberg–Delange/Wirsing; Dirichlet's theorem plus an elementary sieve suffices for *o*(*X*). Membership in *K*<sub>*b*</sub> is fine under `GF-42`'s definition *K*<sub>*b*</sub> = {*D*<sub>*N*</sub> → 1}: runs of 0 and of *b* − 1 both cluster at 0 on ℝ/ℤ.
- **M2 (Major), case *m* ≥ 5 odd.** The proof asserts that "for each residue *t* mod 5, *u*<sub>*r*</sub><sup>(*t*)</sup> = Λ(ζ<sup>*t*</sup>φ<sup>*r*</sup>) is a non-degenerate binary recurrence". **This is false.**
  - **Explicit counterexample:** Λ(*a* + *b*ζ + *c*ζ<sup>2</sup> + *d*ζ<sup>3</sup>) = *c* − *d* gives Λ(φ<sup>*r*</sup>) = 0 for all *r*. I verified this exactly in ℤ[ζ<sub>5</sub>] for *r* = 0…39.
  - **Repair for *m* = 5.** Pick *t* with (Λ(ζ<sup>*t*</sup>), Λ(ζ<sup>*t*</sup>φ)) ≠ (0, 0); such *t* exists because the ζ<sup>*t*</sup> span. For this Λ, *t* = 2 gives the Fibonacci numbers. Then show that {*n* : *t*(*n*) ≡ *t*, |*r*(*n*)| → ∞} has positive density.
  - **General odd *m* ≥ 5.** The one-sentence appeal to Evertse must also exclude **degenerate** families of solutions. By Laurent / Evertse–Schlickewei–Schmidt these lie in finitely many cosets of lower-rank subgroups, and the unit random walk of *n* must be shown to avoid them with probability 1 − *o*(1). As written this is a sketch.

### 4.4 C5.2

The local closed forms C(*e* + 3, 3), C(*e* + 2, 2) and ⌊(*e* + 2)/2⌋⌊(*e* + 3)/2⌋ ≥ 1 are verified exactly for *e* < 40. The popcount conclusions follow from submultiplicativity of *s*<sub>2</sub>.

**M3 (Major).** The paragraph saying that `GF-42` B1.3/B2.1 "apply directly", giving *D*<sup>+</sup> < 1, ∉ *K*<sub>2</sub> and *D*<sup>−</sup>(*F*<sub>*D*</sub>(2<sup>*k*</sup>); 2<sup>*k*</sup>) → 1, has three problems:
- It states **no *k*-range**.
- It does not compute *C*<sub>*U*,*D*</sub>.
- Here *V*<sub>*D*</sub>(*p*) ∈ {1, 2} is not ω, and the note itself admits a "split/inert 2-D sieve" modification.

The claim is not established in the note. Either supply the computation and the *k*-range, or demote it to a conjectural remark. The Results row must change accordingly.

---

## 5. Findings

### Critical

None.

### Major

| ID | Where | Finding | Required action |
|---|---|---|---|
| M1 | C4.2(1) | *G*<sub>+</sub> ⊆ (*M*/2, *M*] contradicts the count (3/4)*M*. The literal reading gives *k*<sub>req</sub> ≈ 37. The certified slack at *k* = 25 is only 1.0%. | Write out the dyadic-block decomposition, and make every *o*(1) term explicit (local CLT over *d*, conditioning, remainders). |
| M2 | C5.1(4) | False lemma: "*u*<sub>*r*</sub><sup>(*t*)</sup> non-degenerate for each *t*" (counterexample above). General odd *m* ≥ 5 is a sketch. | Repair the choice of *t* and add the positive-density argument. Treat degenerate *S*-unit families explicitly, or restrict the claim to *m* = 5. |
| M3 | C5.2(2) and the Results row | *D*<sup>+</sup> < 1, ∉ *K*<sub>2</sub> and *D*<sup>−</sup> → 1 are asserted through "apply directly", with no *k*-range and no *C*<sub>*U*,*D*</sub>. | Prove them with an explicit *k*-range, or demote them. |
| M4 | C1.4(3) | The barrier claim is stronger than what is proved: count moments are not shown to be matched, and the necessity ("requires") is unproven. | Narrow the statement as in §4.1. |
| M5 | C1.4(2), C3.3(3), C4.3(3), C4.2 sieve steps | Results labelled "Paper proof" are proof sketches or heuristics. | Expand them to paper level, or relabel them as remarks or heuristics. |

### Minor

| ID | Where | Finding |
|---|---|---|
| m1 | C5.3, Step 3 | The interval (*T*/2, *T*] has only *T*/2 integers, so "≥ (3/4 − 1/3)*T* ≥ *T*/3" is wrong. The correct bound is ≥ (1 − 0.0911 − 1/3 − *o*(1))·*T*/2 ≈ 0.287*T* (or 5*T*/24 with the note's 1/4). This is harmless. |
| m2 | C5.3 | Since *m*<sub>\*</sub> < *M*<sub>0</sub>, *m*<sub>0</sub> can exceed *X* by up to *M*<sub>0</sub>, so *J* may exceed *N* by up to *kM*<sub>0</sub>. Use *t* ≤ *T* − 1. |
| m3 | C5.3, conditions (2) and (3) | The mean of ω(*u*(*t*)) needs truncation to primes ≤ *T*<sup>1/2</sup>; otherwise the per-prime *O*(1) errors sum to π(*X*) ≫ *T*. The average of τ over the progression is ≪ τ(gcd(*m*<sub>\*</sub> + *j*, *M*<sub>0</sub>)) log *X*, with gcd dividing 2 · 3<sup>*v*<sub>3</sub>(*j*)+1</sup>. It is therefore not uniform in *j*, but it is summable against 2<sup>−*kj*</sup>. |
| m4 | C5.3, Step 1 | "Certified for ε ∈ [−0.49, 0.49]" refers to 7 sample points. The lemma needs no certificate, and ε ∈ (−1, 1) suffices. |
| m5 | C5.3 and the Results row | `BC-38` (*E*<sub>odd</sub>(2), the case *k* = 1) is covered but never named; only `BC-39` is. The claim "*D*<sup>−</sup>(*F*; 2) > 0" for *k* ≥ 3 needs citations (`GF-36` for *E* and *E*<sub>odd</sub>; `GF-44`/`GF-40` for *E*<sub>+</sub>). The 70,000 constant being compared against is Lean-verified (Captain Sude, external), whereas 37 rests on a paper proof. Also check how close the method is to Captain Sude's elementary proof, for attribution. |
| m6 | C4.1(2) | The boundary term should carry the factor 2(|*q*<sub>*N*</sub>| − |*q*<sub>0</sub>|), and the script checks the factor-1 variant. |
| m7 | C4.2 | State that the *R*<sub>*i*</sub> are non-increasing; Abel summation with upper bounds on *f*<sub>*i*</sub> needs it. |
| m8 | C4.3(1) | Extend the definition to non-dyadic *x*, or cite the irrationality of *E*<sub>+</sub>(2<sup>*k*</sup>). |
| m9 | C5.1(2) | Replace density "1/φ(*m*)" with 1/*m*, and fix the external-input label. |
| m10 | C1.4(2) | *C*<sub>lat</sub> is called "explicit" but is never given. |
| m11 | C3.1 | Hall–Tenenbaum is unnecessary (an elementary Rankin bound suffices). The symbol θ is used both as the Rankin exponent and as an angle. |
| m12 | C3.2 | Planted primes are ≥ *k*<sup>3</sup>, not ≪ *k*<sup>2</sup> log *k*. State the size of "sufficiently large *N*". |
| m13 | Script | Section 6.6 contains stream-of-consciousness comments ("WAIT A SECOND!!") with an inconsistent parametrisation, *S* = ⌈4 log<sub>2</sub> log *X*/*k*⌉, and an incorrect intermediate claim ("for *s* ≥ 1 we DON'T EVEN NEED *Q*<sub>*s*</sub>"). The header of §5.2 still says "*k*<sub>0</sub> = 26". Line 1841 has the conditional fallback assertion. The C5.3 "finite certificate" covers only the trivial lemmas, not the CRT or tail steps. |
| m14 | C3.3 | Cite the linear-forms statements of Maynard and GGPY, since the slopes differ. |
| m15 | C1.4(3) | Replace "requires at least one" with "any one of these suffices" (see M4). |
| m16 | Note header | The runtime is about 5 s on this host, not 11 s (cosmetic). |

---

## 6. Advice on `BC-38` / `BC-39` disjunctivity

**Mathematical assessment.** Theorem C5.3 is, in my reading, sound for *k* = 1 and all three families. The cases relevant here are *E*<sub>odd</sub>(2) = `BC-38` (the formula Σ<sub>*n* odd</sub> 1/(2<sup>*n*</sup> − 1) agrees) and *E*<sub>+</sub>(2) = `BC-39`. **No gap I found blocks base-2 disjunctivity** of either constant. The issues m1–m5 are local repairs that leave the conclusion and the stated bound unchanged.

**Procedure.** This review **does not authorise** the update. `AGENTS.md` forbids status changes based on cross-model reviews, and `SCHEMA.md` states that "a status changes only when a result establishes it", meaning a registry entry or a named published theorem. I recommend the following steps.
1. Apply fixes m1–m5 to the note.
2. Register C5.3 as **its own registry entry**, separate from C5.1/C5.2. The proposed `GF-51` bundles C5.3 with the M2 and M3 material, and the weakest component would then define the entry. The entry's status would be `paper` with zero external inputs.
3. Only then may the coordinator set `disjunctivity = "proved_disjunctive"` with `evidence = "paper"` for **both** `BC-38` and `BC-39`, listing the new identifier in `registry_ids`. The cohort, the normality fields and `discrepancy_status` stay unchanged, since disjunctivity decides none of them.
4. Optionally, ask a human specialist to read C5.3 first. The argument is short and elementary; it is CRT plus Markov, close in spirit to the Captain Sude release for *E*(2).

The arithmetic-family entries for *E*(2<sup>*k*</sup>), *E*<sub>odd</sub>(2<sup>*k*</sup>) and *E*<sub>+</sub>(2<sup>*k*</sup>), *k* ≥ 3, can be updated by the same route, once the citations for *D*<sup>−</sup> > 0 (m5) are added.

---

## 7. Summary

- **Reproduction.** The script runs clean: exit 0, 23,166 checks. The zero-float claim was verified by an AST scan and an instrumented re-execution.
- **C5.3: ACCEPT WITH MINOR POLISH.** The CRT planting, the guard-bit lemma and the tail bound survived a line-by-line attack and independent tests. Coefficient formulas were checked on 20,000 values, multiplicativity on 59,398, the guard bit on 73,656 cases, and natural occurrences on 5,802 positions against digits computed directly from the Lambert series. End-to-end toy planting succeeded for *E*(8), *E*<sub>odd</sub>(8), *E*<sub>+</sub>(8), *E*(2), *E*<sub>odd</sub>(2) and *E*<sub>+</sub>(2), including negative ε. Signed arrivals for *E*<sub>+</sub> are harmless: those below the target are exact multiples of 2<sup>ℓ+4</sup>, and those above are bounded by τ. The constant 37/*k* is correct.
- **C4.2.** The numbers are right (*k*<sub>req</sub> ≈ 24.48 in floats; certified ≤ 24.75), but the written proof needs a dyadic decomposition, and the margin at 25 is 1%.
- **C4.3.** Exact and verified, including the Eulerian attainment and the sharpness at *L* = 8 vs *L* = 7.
- **C1–C3.** Constants reproduce. C1.4(3) overclaims.
- **C5.1(4).** Contains a false lemma; the conclusion is repairable for *m* = 5, and the general case is a sketch.
- **C5.2.** The *D*<sup>+</sup> claims are unproven.
- **Overall: REVISE.** There are 0 Critical, 5 Major and 16 Minor findings. **Cross-model review is not independent human peer review.**

---

## Post-Repair Verification

**Scope.** Claude `claude-opus-5-5` checked the Gemini 4 repair of Track C on 2026-11-28 on branch `research/phase-26-arithmetic-amplification`. Audited material: the repaired [`notes/phase26/mesoscopic-carry-correlations.md`](../mesoscopic-carry-correlations.md) (757 lines) and [`scripts/phase26_mesoscopic_carries.py`](../../../scripts/phase26_mesoscopic_carries.py) (2,844 lines). For citations I also read `GF-36`, `GF-40`, `GF-44` in `docs/registry/GF.toml`, Theorem B1.3 of `GF-42`, and `BC-37`…`BC-39` in `docs/benchmarks/classical-constants.toml`. The check was read-only: this appended section is the only change, nothing was committed, and WSL was not used.

> **Cross-model review is not independent human peer review.** This verification is a machine reading by a language model. It cannot by itself change any benchmark status (§6 above still governs the procedure).

### Verdict: **ACCEPT**

| Severity | Remaining | Notes |
|---|---|---|
| Critical | 0 | — |
| Major | 0 | M1–M5 are all resolved. |
| Minor | 2 (non-blocking) | n1 and n2 below; both are cosmetic or ε-bookkeeping. m1–m16 are all resolved. |

### P1. Reproduction and zero-float audit

| Check | Result |
|---|---|
| `python -B scripts/phase26_mesoscopic_carries.py` (Windows, CPython 3.13) | Exit code **0**. Prints `ALL CHECKS PASSED: 24497 [exact] + 2828 [encl] = 27325 zero-float theorem checks (plus 3 [finite] prefix measurements).` This matches the note's header and §6.1 exactly. |
| AST scan (whole file, f-strings included) | **0** float or complex literals and **0** `float()` calls. `math` is used only for `comb`, `factorial`, `gcd`, `isqrt` and `lcm`, all integer functions. All 7 `pow` calls are integer modular (`pow(a, -1, p)`, `pow(2, k, 11)`, Euler's criterion). No `sqrt`, `log`, `exp`, `sin` or `cos`. |
| Instrumented re-execution | I rewrote every `+ − × / **` operation (including augmented ones, but not f-strings) to call a type trap and re-ran the script end to end. It again printed 27,325 checks, and **0 operations produced a float or complex value**. |

The zero-float claim is **verified**. It is now stronger than at first review, because the failure messages no longer call `float()` either.

### P2. Theorem C5.3: independent re-verification of the repaired proof

I re-derived every step by hand. All of them hold.

1. **Coefficients.** From the Lambert definitions: τ<sub>odd</sub>(*m*) = τ(odd part of *m*); *a*<sub>+</sub>(*m*) = Σ<sub>*q*|*m*</sub> (−1)<sup>*q*−1</sup> = (1 − *e*)τ(*u*) for *m* = 2<sup>*e*</sup>*u*; and |*a*| ≤ τ. All three functions are multiplicative and take the value 2 at odd primes. The `BC-38` formula 2 Σ 1/(4<sup>*m*</sup> − 2) = Σ<sub>*n* odd</sub> 1/(2<sup>*n*</sup> − 1) is the case *k* = 1 of *E*<sub>odd</sub>(2<sup>*k*</sup>). ✓
2. **CRT structure.** gcd(*m*<sub>\*</sub>, *M*<sub>0</sub>) = 3<sup>*W*−1</sup>*P*<sub>0</sub>, because every *p* | *Q*<sub>*s*</sub> exceeds *s*. Writing *u*(*t*) = *a*<sub>0</sub> + *b*<sub>0</sub>*t*, we have gcd(*a*<sub>0</sub>, *b*<sub>0</sub>) = 1 and *u*(*t*) coprime to 6*P*<sub>0</sub>∏*Q*<sub>*s*</sub>. So τ(*m*<sub>0</sub>) = τ<sub>odd</sub>(*m*<sub>0</sub>) = *a*<sub>+</sub>(*m*<sub>0</sub>) = *W* · 2<sup>*V*<sub>0</sub></sup> whenever *u*(*t*) is squarefree. Since *W* ≥ 2<sup>ℓ+1</sup> + 1 ≥ 5, we get 3<sup>*W*−1</sup> ≥ 81, so 3 is never a planted prime. ✓
3. **Range *t* ∈ [1, *T*′] and the count.**
   - *Squarefree condition, small primes.* For 5 ≤ *p* ≤ *Y* = *T*′<sup>1/2</sup>, the bound is *T*′/*p*<sup>2</sup> + 1. I checked Σ<sub>*p*≥5</sub> *p*<sup>−2</sup> ≤ 1/25 + Σ<sub>*k*≥3</sub> 1/((2*k* − 1)(2*k* + 1)) = 1/25 + 1/10 = 7/50 (the true value is about 0.0911).
   - *Squarefree condition, large primes.* For *p* > *Y* we have *p*<sup>2</sup> > *T*′, so there is at most one *t* per prime, giving π(√*X*) = *o*(*T*′) since *T*′ ≥ *X*<sup>3/4</sup>/2.
   - *Condition on ω.* ω<sub>>*Y*</sub>(*u*) ≤ 2 holds deterministically, because log *X*/log *Y* → 8/3. Mertens gives a mean of at most (1 + *o*(1))*L*, and Markov then excludes at most (1/3 + *o*(1))*T*′ values of *t*.
   - *Total.* 1 − 7/50 − 1/3 = 79/150 > 1/2. ✓
4. **No overshoot.** *t* ≤ *T* − 1 gives *m*<sub>0</sub>(*t*) < *M*<sub>0</sub>*T* ≤ *X* − *S*<sub>2</sub>. So *J* − 1 = *n*(*t*) + ℓ < *k*(*X* − *S*<sub>2</sub>) ≤ *N* − log<sub>2</sub> *X* < *N*, and *n*(*t*) ≥ *kM*<sub>0</sub> − *r* − 3*L* − ℓ − 1 > 0. The occurrence lies wholly inside [0, *N*). ✓
5. **Condition (3), with explicit *g*<sub>*j*</sub>.**
   - The planted primes exceed *S* + *S*<sub>2</sub> + 10 > *s* + *j*. Hence *g*<sub>*j*</sub> = gcd(*m*<sub>\*</sub> + *j*, 2 · 3<sup>*W*</sup>) and τ(*g*<sub>*j*</sub>) ≤ 2(*W* + 1), uniformly in *j*.
   - *Hyperbola step.* τ(*v*) ≤ 2#{*d* < √*X* : *d* | *v*}. A divisor *d* with gcd(*d*, *b*<sub>*j*</sub>) > 1 never divides *a*<sub>*j*</sub> + *b*<sub>*j*</sub>*t*. Each remaining *d* divides it for at most *T*′/*d* + 1 values of *t*. This gives a mean of at most 4(*W* + 1) log *X*.
   - Markov against 2<sup>*r*</sup>/8 ≥ (log *X*)<sup>2</sup>/8 then excludes *O*<sub>*w*</sub>(*T*′/log *X*) = *o*<sub>*w*</sub>(*T*′) values. ✓
6. **Lower terms.**
   - For 1 ≤ *s* ≤ *S*: 2<sup>*R*−*ks*</sup> | *a*(*m*<sub>0</sub> − *s*) by multiplicativity at *Q*<sub>*s*</sub>. This holds for either sign and when the value is 0. The contribution therefore lies in 2<sup>*R*−*V*<sub>0</sub></sup>ℤ ⊆ 2<sup>ℓ+4</sup>ℤ, using ω(*u*) ≤ ⌊3*L*⌋.
   - For *s* > *S*: *k*(*S* + 1) > *R*, so the exponent is at least ℓ + 5.
   - Hence ⌊2<sup>*J*</sup>*F*⌋ ≡ ⌊*W* + ε⌋ (mod 2<sup>ℓ+4</sup>), even when the accumulated integer *A* is negative. ✓
7. **Upper tail.** The head is at most 2<sup>−*V*<sub>0</sub></sup> · 2<sup>*r*</sup>/8 ≤ 1/8. For the tail, τ(*n*) ≤ 2√*n* and 2<sup>−*kS*<sub>2</sub></sup> ≤ 1/*X* give at most 4*X*<sup>−1/2</sup>. Altogether |ε| < 1/4. ✓
8. **Guard-bit lemma.** *W* is odd, so ⌊*W* + ε⌋ ∈ {*W* − 1, *W*} for every ε ∈ (−1, 1), and *W* − 1 differs from *W* only in bit 0. Bits 1…ℓ of ⌊2<sup>*J*</sup>*F*⌋ are the digits *d*<sub>*J*−ℓ</sub>…*d*<sub>*J*−1</sub>, which spell *w*. The two-line algebraic proof is complete, and the script check is labelled as a sanity check only. ✓
9. **Exponent.**
   - The number of planted primes is *T*<sub>pr</sub> ≤ *r* + *R*<sup>2</sup>/(2*k*), because *SR* − *kS*(*S* + 1)/2 ≤ *R*<sup>2</sup>/(2*k*).
   - Chebyshev puts every planted prime in (4 log<sub>2</sub> *X*, 8 log<sub>2</sub> *X*].
   - *R* = (2/ln 2 + 3)*L* + *O*<sub>*w*</sub>(1), and (2/ln 2 + 3)<sup>2</sup> = 34.6378… < 35.
   - Therefore *M*<sub>0</sub> ≤ exp(35*L*<sup>3</sup>/*k*) ≤ *X*<sup>1/4</sup>, and *X*/(4*M*<sub>0</sub>) ≥ *N* exp(−(37/*k*)(log log *N*)<sup>3</sup>) for fixed *k* and *w*. ✓
10. **Distinct starts.** *J*(*t*<sub>2</sub>) − *J*(*t*<sub>1</sub>) ≥ *kM*<sub>0</sub> − 3*L* > 0. ✓
11. **Inputs and scope.** The proof uses only CRT, Chebyshev, Mertens, Markov and τ(*n*) ≤ 2√*n*. It has **zero external inputs and no gaps.** The scope statements are accurate:
    - `BC-37`, `BC-38` and `BC-39` are each named.
    - *D*<sup>−</sup> > 0 for *k* ≥ 3 is correctly cited: `GF-36` gives *D*<sup>−</sup>(*E*(2<sup>*k*</sup>)), *D*<sup>−</sup>(*E*<sub>odd</sub>(2<sup>*k*</sup>)) > 0, and `GF-44` gives *D*<sub>*N*</sub>(*E*<sub>+</sub>(2<sup>*k*</sup>); 2) ≥ 0.042, with `GF-40` as background.
    - Captain Sude's release (8 September 2026) is correctly credited as an external **Lean-verified** result for *E*(2), with constant 70,000. C5.3 is correctly labelled a **Paper proof** in the same CRT lineage.

**C5.3 standalone readiness: CONFIRMED.** The proposed standalone entry `GF-52` (note §6.3) is separate from `GF-51` (C5.1–C5.2). It can be registered with evidence `paper` and zero external inputs. Once `GF-52` is registered, it is a registered result that establishes base-2 disjunctivity of `BC-38` (*E*<sub>odd</sub>(2)) and `BC-39` (*E*<sub>+</sub>(2)). The coordinator may then set `disjunctivity = "proved_disjunctive"` (evidence `paper`, `registry_ids` including the new identifier) for **both** constants, following §6 steps 2–3 above.
- The cohort, normality fields and `discrepancy_status` stay unchanged.
- In the working tree, `BC-38` and `BC-39` currently still read `disjunctivity = "open"`, which is correct until registration.
- This review alone does not make the change. The authority is the registry entry, as `AGENTS.md` and `SCHEMA.md` require.

### P3. Major findings

| ID | Status | Verification |
|---|---|---|
| M1 (C4.2, *k*<sub>0</sub> = 25) | **Resolved** | See the M1 detail below the table. |
| M2 (C5.1(4), odd *m* ≥ 5) | **Resolved** | See the M2 detail below the table. |
| M3 (C5.2, τ<sub>3</sub> ∗ χ<sub>*D*</sub>) | **Resolved** | See the M3 detail below the table. |
| M4 (C1.4(3)) | **Resolved** | The residue-level star-orbit witness is now explicitly limited to ℤ/8ℤ ("not lifted to a count process"). The count-level barrier is C1.2(1): all 120 order-≤ 3 marked moments, which force the column-count moments E[*N*<sub>*i*</sub>(*N*<sub>*i*</sub> − 1)] = E[*N*<sub>*i*</sub>*N*<sub>*i*′</sub>] = 1/4, since each column is Pois(1/2) because ν<sub>1</sub> + ν<sub>3</sub> + ν<sub>5</sub> + ν<sub>7</sub> = 1. The script asserts these moments. The three inputs are stated as "achieved by any one … proved sufficient, not claimed necessary". |
| M5 (sketches) | **Resolved** | See the M5 detail below the table. |

**M1 detail.**
- *Limit order.* The order is fixed ε → (*K*, *p*<sub>1</sub>, *S*<sub>0</sub>, δ), then *N* → ∞, then ε → 0. This is explicit and correct.
- *Dyadic blocks.* The blocks *I*<sub>ℓ</sub> = (*M*<sub>ℓ</sub>/2, *M*<sub>ℓ</sub>] cover (*M*/2<sup>*K*</sup>, *M*], and the bottom tail is at most (3/4)2<sup>−*K*</sup>*M*. On every block, 1 ≤ *W*<sub>ℓ</sub> ≤ 4 holds automatically, because *m*/(*s*<sub>≤*p*<sub>1</sub></sub>*u*<sub>ℓ</sub>) > *M*<sub>ℓ</sub><sup>1−α</sup>/(2*S*<sub>0</sub>) > 1. This justifies the 7-value range for Δ<sub>*W*</sub>.
- *Fixed parameters.* *S*<sub>0</sub>(*p*<sub>1</sub>, ε) and *Q*<sub>0</sub> = *O*<sub>*p*<sub>1</sub>,ε</sub>(1) are fixed, so the periodic Gaussian Riemann sum over *d* mod *Q*<sub>0</sub> gives 1/(*kQ*<sub>0</sub>) + *o*(1).
- *Scale invariance.* *p*<sub>sm</sub> and *p*<sub>*W*</sub> are scale-invariant: *z*<sub>ℓ</sub> = *M*<sub>ℓ</sub><sup>1/12</sup>, the Rankin bound has an *O*(*M*<sub>ℓ</sub><sup>11/12</sup>) error, and the *Q* ≤ *M*<sub>ℓ</sub><sup>1−δ</sup> split leaves a remainder of *O*(δ).
- *Collisions and sieve remainders.* Cross-block collisions are *O*<sub>*K*</sub>(log *M*). The 10-shell 2-D Selberg remainder is *O*(*M*<sub>ℓ</sub><sup>1−δ</sup>(log *M*<sub>ℓ</sub>)<sup>7</sup>) = *o*(*M*<sub>ℓ</sub>), and the Rankin weights are certified to be non-increasing.
- *Arithmetic.* I recomputed 10.9171/0.441049 = 24.7525 < 25, and the script now asserts `k_req_hi < 25` and `k0_cert == 25` directly, with no fallback. Every *o*(1), *O*(ε), *O*(δ) and *O*(1/*p*<sub>1</sub>) term vanishes in the stated limit order, so the 1% margin is no longer fragile.
- *Conclusion.* *D*<sup>+</sup>(*E*<sub>+</sub>(2<sup>*k*</sup>); 2) < 1 for all *k* ≥ 25 is proved. ("*k*<sub>0</sub> = 25" is an explicit threshold, not a claim of minimality.)

**M2 detail.**
- *False lemma removed.* The note now explicitly flags the old lemma as false, using the null direction Λ = *c* − *d* at *t* = 0 with Λ(φ<sup>*r*</sup>) ≡ 0. For *m* = 5 it uses *t*\* with Λ(ζ<sup>*t*\*</sup>) ≠ 0, and then α, β ≠ 0.
- *General odd m: trace form and units.* Λ = Tr(*c*·) with all *c*<sub>σ</sub> ≠ 0. I verified the inverse (1 + ζ<sup>*j*</sup>)<sup>−1</sup> = Σ<sub>*s*≤(*m*−1)/2</sub> ζ<sup>2*sj*</sup> for **every** 1 ≤ *j* ≤ *m* − 1, including gcd(*j*, *m*) > 1, since (1 + *x*)Σ*x*<sup>2*s*</sup> = Σ<sub>*i*≤*m*</sub>*x*<sup>*i*</sup> = 1.
- *Conjugate pairs.* *u*<sub>σ̄</sub>/*u*<sub>σ</sub> = σ(ζ)<sup>−*t*</sup>, so each pair cancels on at most one class of *t* mod *m*. There are φ(*m*)/2 < *m* pairs, so *t*\* exists.
- *Case split.* The four cases for a minimal vanishing subsum are exhaustive:
  - The case *I* = {σ<sub>0</sub>, σ̄<sub>0</sub>}, *J* = ∅ is excluded by the choice of *t*\*.
  - The other three cases reduce to finitely many affine hyperplanes, using Evertse (1984, Thm 1) on non-degenerate subsums.
  - The hyperplanes are nonzero: the *j*<sub>1</sub>-coordinate compares 2cos(π/*m*) with 2sin(π/2*m*), or with 2cos(π*b*′/*m*) for *b*′ ∈ [2, (*m*−1)/2].
- *Densities.* Halász plus orthogonality gives the density δ<sub>*M*</sub>/*m* of ℰ(*t*\*). The bound 1<sub>*y*=0</sub> ≤ sinc<sup>2</sup> together with Halász for a.e. θ (divergence at *s* = 0 from χ(*p*) = ζ<sup>*j*\*</sup>, and at *s* ≠ 0 from χ(*p*) = 1 together with *L*(1 + *is*, χ<sup>*r*</sup>) ≠ 0) and dominated convergence shows every hyperplane has density 0.
- *Conclusion.* The proof is complete, with external inputs stated correctly.

**M3 detail.**
- *Certified means and k-ranges.* The *C*<sub>*U*,*D*</sub> enclosures are certified in pure integers. I checked the tail bound *L*<sub>*p*</sub> ≤ 1 + 4/*p*<sup>2</sup> + 17/*p*<sup>3</sup> by hand: the split factor is 1 + 4/*p*<sup>2</sup> + 0/*p*<sup>3</sup> + *O*(*p*<sup>−4</sup>) and the inert factor is 1 + 2/*p*<sup>3</sup> + …. The explicit ranges follow from *k* > *C*<sub>*U*,*D*</sub>:
  - *D* = +5: 2.6029 < 3, so *k* ≥ 3.
  - *D* = −3: 3.3222 < 4, so *k* ≥ 4.
  - *D* = +8: 3.9450 < 4, so *k* ≥ 4.
  - *D* = −4: 4.3480 < 5, so *k* ≥ 5.
- *Sieve adaptation.* The note adapts `GF-42` B1.3, whose threshold is *k* > *C*<sub>*U*</sub>, to two-valued *V*<sub>*D*</sub>(*p*) ∈ {1, 2}. It uses variance 2*E*<sup>−</sup> + 8*E*<sup>+</sup> ∼ 5*L*. The secondary peak at *t* = ±π is excluded by the inert primes. The construction-radix limit uses Halász with *g* = 1.
- *D*<sup>−</sup> > 0 on these ranges follows from the *C*<sub>pop</sub> thresholds.

**M5 detail.**
- *C1.4(2).* The note now gives a full four-piece proof. I recomputed the bracket 49 + Σ<sub>*j*</sub>(2*w*<sub>*j*</sub> + 1)(e<sup>−*w*<sub>*j*</sub>/8+2Ein(1)</sup> + (2 ln 2)<sup>2<sup>*j*</sup></sup>/(2<sup>*j*</sup>)!) as about 173.2. The script's certified bound is ≤ 175.41, and dividing by σ<sub>2</sub>(10) still gives less than 180.
- *C4.2* is written out in full (see M1).
- *C3.3(3)* is now a Remark labelled "Structural / heuristic diagnosis".
- *C4.3(3).* The former multiscale block claim is now a Remark that names its `GF-42` B4.1 input, so Theorem C4.3 has **zero external inputs**.

### P4. Minor findings

| ID | Status |
|---|---|
| m1–m5 | Resolved; see P2 (counting is now 79/150, the range is *t* ≤ *T* − 1, *Y* = *T*′<sup>1/2</sup> truncation and *g*<sub>*j*</sub> \| 2 · 3<sup>*W*</sup> are explicit, the guard bit is algebraic on (−1, 1), and scope and attribution are complete). |
| m6 | Resolved: 2(\|*q*<sub>*N*</sub>\| − \|*q*<sub>0</sub>\|) appears in the statement and the proof, and the script checks this exact form. |
| m7 | Resolved: the non-increasing *R*<sub>*i*</sub> are stated and certified. |
| m8 | Resolved: the domain is now all non-dyadic *x*, and Borwein (1991) is cited for irrationality. |
| m9 | Resolved: the density is now 1/*m*, and the external inputs for even *m* are listed. |
| m10 | Resolved: *C*<sub>lat</sub> = 180. |
| m11 | Resolved: Hall–Tenenbaum is removed (an elementary Rankin bound is used instead), and the Rankin exponent is now α<sub>*j*</sub>, separate from the angle φ. |
| m12 | Resolved: the planted primes satisfy *k*<sup>3</sup> < *p* ≤ 2*k*<sup>3</sup>, and the size of "sufficiently large" is stated (*L* ≳ 1.52 × 10<sup>5</sup>, or *O*(1) with *k* = ⌊6√*L*⌋). |
| m13 | Resolved in substance. Section 6.6 is clean. The §5.2 header no longer says "*k*<sub>0</sub> = 26". The direct assertions `k_req_hi < 25` and `k0_cert == 25` replace the fallback. The C5.3 certificate is described honestly as sanity checks for an algebraic proof. A residual cosmetic issue remains (n2). |
| m14 | Resolved: the general linear-forms statements of Maynard (2015, 2016), Polymath8b and GGPY are cited. |
| m15 | Resolved: "is achieved by any one … proved sufficient, not claimed necessary". |
| m16 | Resolved: the header now says 27,325 checks and about 5–6 s. |

**Remaining non-blocking minors.**
- **n1 (C4.2 ε-bookkeeping).** The bound (3/4)(2ε)|*I*<sub>ℓ</sub>| for conditions (ii) and (iii) together treats Pr(*s*<sub>≤*p*<sub>1</sub></sub>(*m*) > *S*<sub>0</sub>) as independent of the class *m* ≢ 2 (mod 4). The 2-part of *s*<sub>≤*p*<sub>1</sub></sub> is correlated with that class, so the honest conditional bound is (4/3)ε. Either choose *S*<sub>0</sub> so that the conditional probability is below ε, or replace 6ε by 7ε. This does not matter, because every ε-term vanishes in the limit.
- **n2 (script comments).** Sections 1–5 still contain stream-of-consciousness comments ("Wait: …", and "WAIT A SECOND!!" at about line 1873 in the *C*<sub>*U*,+</sub> derivation). The arithmetic they annotate is correct (*L*<sub>2</sub>(*U*<sub>+</sub>) = 1/2 + *L*<sub>2</sub>(*U*)/4), and no check depends on them. They are worth cleaning before release.

### P5. Summary

- **ACCEPT.** 0 Critical, 0 Major and 2 non-blocking Minor findings remain. All of M1–M5 and m1–m16 are resolved.
- **Script.** Exit code 0 with 24,497 [exact] + 2,828 [encl] = 27,325 checks plus 3 [finite]. The zero-float claim was confirmed by an AST scan and an instrumented re-execution (0 float-producing operations).
- **Theorem C5.3.** Correct, complete, and free of external inputs. It is ready to be its own registry entry, `GF-52`. Registering it authorises the coordinator to promote `BC-38` and `BC-39` to `disjunctivity = "proved_disjunctive"` (evidence `paper`). The authority for that promotion is the registry entry, not this review.
- **Cross-model review is not independent human peer review.**
