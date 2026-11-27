# Review of Phase 23 Track B1–B2: dense character carries and non-fundamental forms

**Reviewer:** `claude-opus-5-5` (cross-provider referee). **Author under review:** `gpt-6.2-astra`.
**Audited files (read-only, not modified):** `notes/phase23/dense-characters-and-nonfundamental-forms.md` (cited below as "Note *L*", where *L* is a line number) and `scripts/phase23_dense_forms.py` (cited as "Script *L*").

> **Status of this review.** This is a cross-model review. It is **not** an independent human peer review and it does not replace one. Finite computations reported here, in the note or in its script are finite measurements or finite certificates of finite statements. They do not prove any asymptotic theorem. Every verdict below rests on checking the paper arguments line by line.

## Verdicts

| Sub-track | Verdict | Critical | Major | Minor |
|---|---|---:|---:|---:|
| **B1** (dense odd-order character Lambert series, Theorem 4A and §§1–3) | **ACCEPT AFTER REVISION** (minor revisions only) | 0 | 0 | 8 |
| **B2** (non-fundamental discriminants, imprimitive forms, §§4–5) | **ACCEPT AFTER REVISION** (minor revisions only) | 0 | 0 | 6 |

I found no gaps, circularity or numerical error in the proofs of Theorem 4A, Theorem 4, Propositions 1–4B, Corollary 5, Lemmas 6–7, Theorem 8, Corollary 9, or the eleven table entries. The required revisions concern how evidence is labelled, how scope is stated, notation, one ambiguous definition, and making the inherited Audit 1 hypotheses explicit.

---

## 1. Re-run of the verifier

Command: `python -B scripts/phase23_dense_forms.py`. I ran it locally on the Windows host with the standard library only. It is a standalone script, not part of `scripts/verify.sh`, so I did not use Hail.

```
Cubic mod 7 at 8192 (support, absolute mass, square mass): [(6154, 12176, 34416), (4081, 5662, 9324)]
Certified cubic dyadic thresholds for moduli 7, 9, 13: plus k >= 4, minus k >= 3
Quadratic discriminants checked through 4096: 11
```

The script exits with status 0 after about 1.2 s. Every number shown in the note matches:

- the triples at Note 327, asserted at Script 219;
- the inequality 3/4 < δ < 751/1000 at Note 329, asserted at Script 170;
- C_odd < 4/5 (modulus 7) and C_odd < 21/25 (moduli 9 and 13) at Note 140 and Note 331, asserted at Script 171;
- the threshold inequalities at Note 164, asserted at Script 172–173;
- the digit-cylinder identity Σ min(*d*, *b*−1−*d*)/*b*² = 1/4 − 1/(2*b*), asserted at Script 177;
- the eleven class numbers and the C_Q/C_K and η(*Q*) columns of the table at Note 296–308, asserted at Script 284–322.

**My own independent numerics (finite measurements only).** I took Euler products over primes up to 3·10⁶ in a separate scratch script:

| Modulus | δ | C_odd | plus C_odd/4 | minus (2/3)C_odd/3 |
|---|---:|---:|---:|---:|
| 7 | 0.75033 | 0.76357 | 0.1909 | 0.1697 |
| 9 | 0.79806 | 0.81104 | 0.2028 | 0.1802 |
| 13 | 0.76146 | 0.81945 | 0.2049 | 0.1821 |

The thresholds are 1/4 − 1/32 = 0.21875 at *k* = 4 and 1/4 − 1/16 = 0.1875 at *k* = 3. All certified bounds therefore hold with margin. The thinnest margin is the minus component at *k* = 3 modulo 13: 0.1821 with the true constant, and 14/75 ≈ 0.18667 with the certified bound, against 0.1875. Even the true constants do not extend the method to plus at *k* = 3 (0.2545 > 0.1875) or minus at *k* = 2 (0.2545 > 0.125). So the certified bounds 4/5 and 21/25 lose no radix in the stated ranges.

I also ran a finite orbit check for modulus 7 with *N* = 4·10⁵ and a 25-term tail. The empirical mean of ‖*b*^*j* *z*‖ stayed below mean|*U*|/(*b*−1) in every case, for example 0.1049 ≤ 0.1086 for plus at *k* = 4 and 0.0502 ≤ 0.0522 for minus at *k* = 4. Both sit well below the asymptotic bound C_Φ/*k*. This is expected: at log log *N* ≈ 2.6 the residues of ν mod *k* are far from equidistributed, and the twist error decays only like (log *X*)^{Re *z* − 1}, with Re *z* − 1 = −1/3 at *k* = 4. These figures are consistent with the theorem but are not evidence for it.

---

## 2. Sub-track B1: detailed audit

### 2.1 Theorem 4A, the central claim: how the superlinear mass is overcome

The audit brief asks how a bounded mean circular distance can follow when Σ_{n≤X} |c_±(n)| grows like *X*(log *X*)^{1/3}. Every step below checks out.

1. **Structure of the coefficients (Note 32, 142).** For a cubic χ, c(p^e) is e+1 when χ(p)=1; 1, e^{±iπ/3}, 0 periodically in e when χ(p)=ω^{±1}; and 1 when p | M. So on the support c(n) = A(n)·e^{iπt(n)/3}, with A(n) = Π_{χ(p)=1}(v_p(n)+1). Because Φ is additive and A(n) ∈ ℤ, a(n) = Φ(c(n)) = A(n)·Φ(e^{iπt(n)/3}). I verified the phase tables (2,1,−1,−2,−1,1) for c_+ and (0,1,1,0,−1,−1) for c_- directly.
2. **The odd part is bounded on average (Note 119, 142).** odd(a(n)) = odd(A(n))·odd(Φ(ζ_t)). The weight w(n) = 1_{c(n)≠0}·odd(A(n)) is multiplicative with w(p) = 1 at **every** prime: at χ(p)=1, odd(2)=1; at χ(p)=ω^{±1}, 1+χ(p) is a unit; at p | M the value is 1. Also |w(p^e)| ≤ e+1. Wintner's mean-value theorem applies and gives the product C_odd. I checked the local factors: the P-factor is (1−1/p)Σ_{e≢2 (mod 3)} p^{−e} = 1 − 1/(p²+p+1). **This is the whole mechanism.** The (log *X*)^{1/3} growth of the raw mass comes entirely from the factors 2^{#{p∥n : χ(p)=1}} inside A(n). The radix 2^k absorbs those factors.
3. **Residues equidistribute under the weight (Note 142–148).** I recomputed the twist g(n) = w(n)·e^{2πiuν(n)/k}·e^{iπjt(n)/3} at primes: e^{2πiu/k} at χ(p)=1, e^{±iπj/3} at χ(p)=ω^{±1}, and 1 at p | M. The mean over primes is (e^{2πiu/k} + 2cos(πj/3))/3, as printed. Its real part is 1 only when u ≡ 0 (mod k) and j ≡ 0 (mod 6). g(p) depends only on p mod M, so Selberg–Delange gives O(X(log X)^{Re z − 1}) = o(X) for every nontrivial twist. A vanishing 1/Γ factor does not matter for an upper bound. Finite Fourier inversion then gives C_odd/(6k) per residue pair.
4. **Mean of the reduced coefficient (Note 148).** |U(n)| = odd(A)·odd(Φ(ζ_t))·2^{(ν + v₂Φ(ζ_t)) mod k}. A fixed phase offset permutes the residues, and Σ_{r<k} 2^r = b−1. So the mean of |U| converges to (b−1)C_Φ/k. Correct.
5. **Orbit bound (Note 150–156).** a(n)b^{−n} = U(n)b^{−l(n)} with l(n) = n − ⌊v₂(a(n))/k⌋. Terms with l(n) ≤ j are integers after multiplying by b^j, and ‖x + m‖ = ‖x‖ ≤ |x| for integers m. So ‖b^j z‖ ≤ Σ_{l(n)>j} |U(n)|b^{j−l(n)}. Exchanging sums, each n contributes at most |U(n)|Σ_{m≥1} b^{−m} = |U(n)|/(b−1), with no assumption about signs or collisions. The truncation is also right: H = ⌈3 log_b(2N)⌉ makes b^{−H} ≤ (2N)^{−3}, |a(n)| ≪ τ(n) = n^{o(1)}, and the H boundary terms contribute o(N). So the limsup of the mean distance is at most C_Φ/k.
6. **From mean distance to discrepancy (Note 158–162).** For x ∈ [0,1), ‖x‖ = ∫_0^{1/2} 1[t ≤ x < 1−t] dt (the endpoints have measure zero in t), and μ_N([t,1−t)) ≥ 1−2t−D_N. Substituting s = 1−2t gives (1−D_N)²/4 ≤ ∫‖x‖dμ_N. Hence D⁻ ≥ 1 − 2√(C_Φ/k). Correct.
7. **Simple nonnormality (Note 133–138, 164).** On the cylinder with leading digit d, ‖x‖ ≥ min(d, b−1−d)/b. Uniform digit frequencies would force the mean to converge to (1/b²)Σ min(d, b−1−d) = 1/4 − 1/(2b) for even b (checked at Script 177). That contradicts limsup ≤ C_Φ/k < 1/4 − 1/(2b). Negative z (possible for c_-, since c_-(2) = −1 modulo 7) causes no trouble because only fractional parts enter.
8. **Thresholds.** For c_+, C_Φ = C_odd: all six odd parts equal 1. For c_-, C_Φ = (2/3)C_odd: odd parts (0,1,1,0,1,1). Plus at k=4: C_Φ/4 < 21/100 < 7/32. Minus at k=3: C_Φ/3 < 14/75 < 3/16. Both inequalities are exact. For larger k the left sides decrease and the right sides increase. Since C_Φ/k < 1/4 in each case, D⁻ > 0 as well.
9. **Certificate for C_odd (Note 331, Script 121–140).** The split local factor is at most 1 + (2p−1)/(p²(p−1)) ≤ 1 + 3/p². This follows directly from odd(e+1) ≤ e+1, using (1−x)(1 + x + Σ_{e≥2}(e+1)x^e) = 1 + (1−x)Σ_{e≥2} e x^e. The integer arithmetic rounds outwards (floor for the lower δ product, ceiling for the upper products). The tail factor (1 − 3/Y)^{−1} ≥ exp(3/Y) ≥ Π_{p>Y}(1 + 3/p²) is valid. The δ-product truncated at Y is a valid upper bound because every factor is below 1. Conjugating χ does not change the set {χ(p)=1}. The certificate is rigorous.
10. **Rate (Note 166–172).** I checked the s-moment version. Subadditivity of x^s for s ≤ 1, the geometric factor 1/(b^s − 1), the mean (b^s − 1)C_Φ(s)/(k(2^s − 1)) with C_Φ(s) ≤ C_Φ, Markov on [1/k, 1−1/k) with s = 1/log k (so k^s = e and 2^s − 1 ≥ s log 2), and the truncation H = ⌈(3/s)log_b(2N)⌉ are all correct for k ≥ 3. The radix is fixed before N → ∞, as the note says, so no uniformity is needed.

**Conclusion on Theorem 4A.** The proof is complete. It proves simple nonnormality and D⁻ > 0 for L_+(2^k) when k ≥ 4 and for L_-(2^k) when k ≥ 3, each in its own construction radix 2^k, for the cubic characters modulo 7, 9 and 13. It also proves lim_{k→∞} D⁻(F_{2^k}(a); 2^k) = 1 for every nonzero projection. I found no hidden gap or circularity. The one external input is the standard Selberg–Delange theorem for multiplicative functions whose prime values depend on p mod M.

**Scope.** The note confines the claim to the construction radix 2^k (Note 5, 133, 140, 335). It makes no claim about L_±(2^k) in any other radix or about non-dyadic radices. It keeps K_b membership, D⁺ < 1 and positive lower frequency of every word open (Note 11, 335). One observation the authors may want to record without claiming anything: Theorem 4A shows the orbit mass concentrating near ℤ as k grows. That is the configuration in which D⁺ < 1 is hardest to prove, so it is a reason for caution, not a result.

### 2.2 Theorem 4 (signed-tail normal order), Propositions 1–4B, Corollary 5

- **Proposition 1.** κ_3(r) = (2^r+2)/3. The phase factors are (2^r+2)/3 for c_+ and 2/3 for c_-. The twist exponents (2^r + 2cos(πj/3))/3 are correct. So are κ_h(1) = 2/(h sin(π/(2h))) (κ_3(1) = 4/3), κ_h(2) = 2, and Π(1+ζ^j) = 2.
- **Proposition 2.** The Turán–Kubilius mean γ_h log log X uses Π|1+ζ^j| = 2. The lower bound 2^{m(n)} | a(n) holds because A(n) ∈ ℤ and Φ is additive. The spanning and norm-equivalence argument is valid: if Φ(c(d_i)z) = 0 for all i, then Φ vanishes on Ez = E. Correct.
- **Proposition 3.** The densities, the inequality 1 − 1/(p²+p+1), P_2, and R_- = 3/7 modulo 7 (residues 2, 3, 4) are correct. So are the positive density of zero blocks and the ergodicity of translation on the profinite integers, which gives q_R → 0.
- **Theorem 4.** The upper bound via (2^r − 1)/(3r) → γ is correct. For the lower bound I checked: the CLT for U(n+i) − U(n+j), whose summands are mean-zero automatically, with variance 2Σ_{χ(p)=1, p≤y} 1/p ~ (2/3)log log X and CRT moment error (2y)^k/X = o(1) at y = X^{1/log log X}; uniqueness of the minimum 2-adic valuation; the threshold (1/3 − η)log 2 > γ − ε; and the block packing, including the point that o(X) exceptional starts hit only an ε-fraction of the X/H blocks. Correct. The identity b^d T_n − T_{n+d} = Σ b^{d−i}a(n+i) is also checked exactly at Script 207–216.
- **Proposition 4B.** I checked the trace reduction a = Tr_{E⁺/ℚ}(A_u y) with u² = χ(n°), and the uniqueness of the phase where A_u = 0: squaring is injective on μ_h for odd h. The variance argument for distinct embeddings is right, because |1+ζ^a| = |1+ζ^{a'}| iff a' ≡ ±a. Archimedean dominance then bounds the sum, and the conductor factor depends only on the M-adic coordinates, so it is independent of the other primes under Haar measure. Correct. The quintic trace identity and the phase-zero test (β = ζ − ζ⁻¹ gives A_u = 0 iff u = 1) are checked at Script 49–65.
- **Corollary 5.** For the minus case with b = 2, the inequality 2δ/3 > 1/2 needs δ > 3/4, which is certified. Non-atomicity follows by ergodic factor arguments, the limiting discrepancy is below 1 for a non-atomic limit, and Pólya's theorem gives D⁻ = D⁺. Correct.

### 2.3 B1 findings (all Minor)

1. **Minor: evidence label for Theorem 4A (Note 5, 116, 140).** The stated radix thresholds use the numerical bounds C_odd < 4/5 and C_odd < 21/25, which are established by the finite certificate in §6. AGENTS.md asks for strict separation of labels. *Fix:* label the headline result "Paper proof; numerical constants by Finite certificate (`scripts/phase23_dense_forms.py`)". Keep the k → ∞ statement and the inequality D⁻ ≥ 1 − 2√(C_Φ/k) as pure Paper proof.
2. **Minor: open-range statement is incomplete (Note 11).** "This note does not settle simple normality in the remaining construction radices modulo seven" should cover all three moduli, and it should name the dyadic radices that remain open (b = 2, 4, 8 for L_+ and b = 2, 4 for L_-) and every non-dyadic radix. *Fix:* "For the cubic characters modulo 7, 9 and 13, simple normality of L_+(b) for b ∈ {2,4,8}, of L_-(b) for b ∈ {2,4}, and of L_±(b) in every radix that is not a power of two remains open. The k-ranges are those of the method; with the exact constants the method does not reach plus at k = 3 or minus at k = 2."
3. **Minor: notation clash for *U*(*n*) (Note 94 vs Note 148).** In Theorem 4, U(n) counts primes p | n with χ(p)=1. In Theorem 4A, U(n) is the radix-reduced coefficient. *Fix:* rename the prime count, for example ω₁(n).
4. **Minor: two-interval criterion needs circular separation (Note 112).** "Positive lower mass in two separated orbit intervals" does not suffice when the intervals are [0, ε) and [1−ε, 1). Those are separated in [0,1) but adjacent on the circle, so concentration at ℤ, which is exactly what Theorem 4A detects, would not be excluded. *Fix:* "two intervals at positive distance on ℝ/ℤ", or "positive lower mass in some closed interval contained in (0,1) together with a second interval at positive circular distance from it".
5. **Minor: ambiguous sentence in Proposition 1 (Note 28).** "the ratios of the two sums tend respectively to 2 and 3" means the ratio of the c_+ sum to the c_- sum for r = 1 and r = 2. *Fix:* say so explicitly. The finite values at 8192 are 12176/5662 ≈ 2.15 and 34416/9324 ≈ 3.69, consistent with slow convergence. If quoted, they should carry the finite-measurement label.
6. **Minor: non-sequitur (Note 34).** "In particular the typical exponent and the first-mean exponent differ for the quintic character modulo eleven." They already differ for h = 3 (γ_3 ≈ 0.231 against κ_3(1) − 1 = 1/3). *Fix:* "for every odd h > 1, including h = 5 modulo 11", or delete the sentence.
7. **Minor: the script's local-factor check cannot certify anything (Script 179–182).** `partial <= bound` with a 20-term truncation bounds a truncated sum, which is smaller than the full series, so it cannot certify an upper bound on the series. The paper argument at Note 331 is complete, so nothing depends on this check. *Fix:* call it a consistency check, or add the exact tail through odd(e+1) ≤ e+1 and the closed form (1−x)Σ_{e≥2} e x^e = x²(2−x)/(1−x).
8. **Minor: displaced-polynomial check covers only the first 80 coefficients (Script 183–206).** The check is correct and useful, but it tests only the deterministic inequality on a prefix, not the averaged bound. *Fix (wording, Note 331):* "checks the deterministic displaced identity and the pointwise orbit inequality on the first 80 coefficients". The present wording is close to this already.

---

## 3. Sub-track B2: detailed audit

### 3.1 Lemma 6 (exact descent) and the conductor Euler factor

- **Local argument.** I re-derived it. At p^a ∥ f, I_p = R_a = ℤ_p + p^a 𝒪_{K,p}. If α ∈ R_a has maximal-order content t < a, then α/p^t ≡ (unit scalar) mod p, so v_p(Nα) = 2t. Also R_a ∩ p^t𝒪_K = p^t R_{a−t}. This gives the forbidden odd exponents below 2a and the bijection α ↦ α/d onto vectors of norm m·N(I_g) in I_g when (m,g) = 1. Correct, and it is an equality of lattice counts with all units included.
- **Shear construction (Script 266–278).** p ∤ A after swapping, by primitivity. The shear exists for odd p because p | 2aj + b forces p² | 4a·last. It exists for p = 2 by a parity argument modulo 4 (squares are 0 or 1 mod 4, matching D″ ≡ 0, 1). The identity r_Q(p²m) = r_{Q′}(m) together with r_Q(n) = 0 when p ∥ n is then immediate: p | Q(x,y) forces p | x. The script checks it for every class and every m, and checks simultaneous descent for the principal class. For the non-principal classes of −108, the iterated descent is covered too, because the lower discriminants −27 and −12 are themselves rows of the table.
- **Euler factor (Note 233).** I recomputed the unit indices [𝒪_{K,p}^× : R_a^×] = p^{a−1}(p − ξ) from the unit proportions (1−1/p)², 1 − 1/p², 1 − 1/p, and [R_{a−t}^× : R_a^×] = p^t. Correct. Checked against class-summed counts through 4096 at Script 339–348.

### 3.2 Lemma 7 (ring class groups) and Audit 1 compatibility

- **Prime-to-conductor reduction.** Extension and contraction biject invertible 𝒪_g-ideals prime to g with 𝒪_K-ideals prime to g. The ring class characters are Hecke characters of conductor dividing g. The Chebotarev density |A|/(2|G_g|) for inverse-stable sets is right, as are the deleted-factor constants u_p (1 − p⁻² inert, 1 − p⁻¹ split or ramified). Ramified ideals 𝔮 with q | D, q ∤ g still satisfy 𝔮² = q𝒪_g, so their classes have order at most 2 in G_g and project trivially to the odd part, as GF-21 requires.
- **Survival law.** I checked it for |G_odd| = 3: E_p ≡ 2 (mod 3) has probability 1/(p²+p+1), all nontrivial characters die together, and η_g = 2P_g/3. For 2-groups η_g = 0, because each m is represented by exactly one class when G is elementary abelian of exponent 2 (X_m is a single group element times an integer).
- **Uniform integrability (Note 262).** The bounded support mean of r^{1/log log X}, combined with y² ≤ 2e^y, is correct.
- **Audit 1 requirements.** The repaired GF-21 now states Lemma 2.7 with P₀ ≥ max_{p|Δ} p, and Lemma 2.8′ (common finite modulus) is used inside Proposition 2.10 (Radix 323, 339–353, 367, 395). Lemma 7 imports both through "as there" and "GF-21 Proposition 2.10 now applies", and its last sentence ("All equidistribution used here is modulo fixed moduli before passing to larger cutoffs") states the common-modulus principle. Both hypotheses are therefore satisfied by citation, but the note does not state them in its own text. See Findings B2-1 and B2-2.

### 3.3 Theorem 8 and the eleven discriminants

I recomputed every entry by hand from C_Q = Σ_{d|f} B_{f/d}/d², with B_g = (C_K/e_g)Π_{p|g} u_p:

| Δ | Components (g: weight in units of C_K) | C_Q/C_K | η(Q) |
|---:|---|---:|---:|
| −12 | 2: 3/4; 1: 1/4 | 1 ✓ | 0 ✓ |
| −16 | 2: 1/2; 1: 1/4 | 3/4 ✓ | 0 ✓ |
| −27 | 3: 2/3; 1: 1/9 | 7/9 ✓ | 0 ✓ |
| −28 | 2: 1/2 (2 split in ℚ(√−7)); 1: 1/4 | 3/4 ✓ | 0 ✓ |
| −32 | 2: (1/2)/2; 1: 1/4 | 1/2 ✓ | 0 ✓ |
| −36 | 3: (8/9)/2; 1: 1/9 | 5/9 ✓ | 0 ✓ |
| −44 | 2: 3/4 (h=3); 1: 1/4 | 1 ✓ | (3/4)(2/3)P₂ = P₂/2 ✓ |
| −64 | 4: 1/4; 2: 1/8; 1: 1/16 | 7/16 ✓ | 0 ✓ |
| −75 | 5: (24/25)/2; 1: 1/25 | 13/25 ✓ | 0 ✓ |
| −92 | 2: 1/2 (h=3); 1: 1/4 (h=3) | 3/4 ✓ | [(1/2)(2/3)(7/6) + (1/4)(2/3)]P₁/(3/4) = 20P₁/27 ✓ |
| −108 | 6: 1/2 (h=3); 3: 1/6; 2: 1/12; 1: 1/36 | 7/9 ✓ | (9/14)(2/3)P₆ = 3P₆/7 ✓ |

The class numbers 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3 match my enumeration of reduced primitive forms. For −92, P₂ = P₁/(1 − 1/7) is correct: 2 splits in ℚ(√−23) (−23 ≡ 1 mod 8) into nonprincipal ideals, since [1,1,6] misses 2 and [2,1,3] represents it. The g = 2 component has m odd, so E₂ = 0 there. The map G₂ → G₁ is an isomorphism, so the other nonprincipal split primes agree.

Theorem 8 then follows from the Phase 21 mixture form (radix-lambert Theorem 1, Remark 5), with these checks:

- (W0) holds with κ = 1/2.
- (W1) holds by lattice counting, and r_Q(n) = n^{o(1)}.
- (W2): Phase 21 Proposition 2.1 (E2) needs only even valuations at inert primes away from f, so it covers pairs drawn from different components.
- The width laws, (1 − 1/d*)log 2 for dyadic radices and log 2 otherwise, are supported in [0, log 2] ⊂ [0, 1). Their first moments converge by uniform integrability.

### 3.4 Corollary 9 (imprimitive forms)

r_{kQ}(n) = 1_{k|n}·r_Q(n/k), so Θ_{kQ}(1/b) = Θ_Q(1/b^k). The support density becomes C_Q/(k√log N). The shift log_b k in λ is lower order. The widths in radix b are unchanged, and isolation passes through the dilation. So the left-hand equivalent is (C_Q/k)·log log N/(2 log b √log N)·(1 + η log 2 or 1 + log 2). The right-hand side, Theorem 8 in radix b^k at ⌊N/k⌋, gives the same leading term, and b^k has the same dyadic type as b. The note correctly says the identity of real numbers does not by itself identify the finite discrepancies (Note 323). Correct. The dilation identity is checked through 4096 for k = 2, 3 at Script 336–338.

### 3.5 B2 findings (all Minor)

1. **Minor: state the fixed-ramified-prime hypothesis in Lemma 7 (Note 252–256, especially "Conditioning on the genus imposes precisely the compatible parity coset").** As written, that sentence is false unless the exponents at the ramified primes q | D, q ∤ g are fixed in the local pattern. This is the Δ = −15 phenomenon of Audit 1 Major 2. It matters here for −92, where 23 is ramified and does not divide g. The citation "as there" imports GF-21 Lemma 2.7, which now requires P₀ ≥ max_{p|Δ} p, so the proof is correct as cited. I would grade it Major had the cited lemma not been repaired. *Fix:* insert "with P₀ ≥ max{p : p | D}, so that every ramified prime of K not dividing g is recorded in the pattern; conductor primes are excluded by (m,g) = 1".
2. **Minor: cite the common-modulus lemma explicitly (Note 260).** "Its inputs are the group-ring factors, the multiplicity equidistribution just verified, and the finite-group Strassmann lemmas 2.8–2.9" leaves out Lemma 2.8′, which is the Audit 1 Major 1 repair through which Proposition 2.10 combines Lemmas 2.7 and 2.8. *Fix:* "…Strassmann Lemmas 2.8–2.9, combined only through the common finite modulus of Lemma 2.8′ (no conditioning on exact counts)".
3. **Minor: ambiguous "its order" in the definition of d_g* (Note 248).** "Discard ψ if ψ(c_p) ≠ 1 and its order divides E_p + 1." The local geometric sum vanishes exactly when ord ψ(c_p) | E_p + 1 (Audit 1, line 37), not when ord ψ | E_p + 1. The two agree for the order-3 groups in the table but differ for, say, ℤ/9. *Fix:* "…and ord ψ(c_p) divides E_p + 1".
4. **Minor: section pointer (Note 9).** "§4 gives the leading constant … primitive or imprimitive." The imprimitive case is Corollary 9 in §5. *Fix:* "§§4–5".
5. **Minor: the script reproduces the table from the same formula; it does not confirm it independently (Note 333, Script 294–313).** The table check recomputes Σ B_{f/d}/d² with the formula of Theorem 8, and the survival ratio 7/6 for (−23, 2) is hard-coded at Script 311. Script 357–359 does independently confirm the arithmetic facts behind it. This is legitimate as an arithmetic consistency check, but "It checks the rational factors in the examples" could be read as independent confirmation. *Fix:* "It recomputes the rational factors from the formulas of Lemma 7 and Theorem 8, and separately checks the facts used for −92 (2 split; [1,1,6] misses 2; [2,1,3] represents 2). Support constants and η are not measured, and at this range they could not be."
6. **Minor: lattice-identity checks stop at norm 4096 (Note 333).** The descent and dilation checks are exact finite identities. Their role is to catch convention errors (inverse class, unit count, orientation), not to support the analytic constants. The note says this ("These checks establish finite identities in the stated ranges"). No change is needed beyond keeping this sentence.

---

## 4. Items specifically requested in the brief

- **Exact match of displayed numbers:** yes (§1).
- **Superlinear mass against bounded mean distance:** resolved by the factorisation a = A·Φ(ζ_t). All of the growth sits in powers of 2 that a 2^k-radix shift absorbs, and the odd part has a finite mean C_odd by Wintner. I checked every valuation, the displacement l(n), the geometric arrival bound 1/(b−1), the Markov and quadratic discrepancy steps, and every constant (§2.1).
- **Radix thresholds k ≥ 4 (plus) and k ≥ 3 (minus) for moduli 7, 9, 13:** verified exactly from the certified bounds, and confirmed numerically with margin (§1, §2.1 item 8).
- **Simple nonnormality and D⁻ > 0 without hidden gaps:** confirmed (§2.1).
- **Construction-radix scope; K_b and D⁺ < 1 open:** stated correctly. Only the open-range sentence needs widening (B1-2).
- **Ring class decomposition, weighted lower orders, Audit 1 compatibility, Θ_{kQ}(1/b) = Θ_Q(1/b^k):** confirmed. The Audit 1 hypotheses should be stated explicitly (B2-1, B2-2).
- **All eleven discriminants:** recomputed by hand, all correct (§3.3).

## 5. Required revisions (summary)

- **B1:** B1-1 (evidence label), B1-2 (complete open-range statement), B1-3 (rename U(n) in Theorem 4), B1-4 (circular separation at Note 112), B1-5 and B1-6 (wording), B1-7 (call Script 179–182 non-certifying, or make it rigorous). B1-8 is optional wording.
- **B2:** B2-1 (P₀ ≥ max p | D in Lemma 7), B2-2 (cite Lemma 2.8′), B2-3 (ord ψ(c_p)), B2-4 (§§4–5), B2-5 (describe what the script's table check actually does).

None of these changes alters a theorem statement, a constant or a radix range.

---

*Reminder:* this cross-model review is not independent human peer review. The finite verifier and my scratch numerics are finite certificates and finite measurements. They do not prove the asymptotic statements, which rest only on the paper arguments checked above.
