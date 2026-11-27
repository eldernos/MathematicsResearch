# Independent Referee Report — Phase 23, Track D (sub-tracks D1, D2, D4)

- **Audited files (read-only, not modified):**
  - `notes/phase23/convergent-reciprocals-and-schedules.md` (714 lines)
  - `scripts/phase23_reciprocals_v2.py` (1,142 lines)
- **Cross-referenced (read-only):** `NormalityChecker/RadixPowerTower.lean` (lines 36–52, 924–933, 1067–1070, 1206–1262), `NormalityChecker/Phase23Cores.lean` (theorem list), `notes/phase22/normal-reciprocals-and-signs.md` (line 3 definitions, line 967 Open Problem #5), `notes/phase21/euler-scalings-and-reciprocals.md` (line 3), `docs/results.md` (lines 2133–2135).
- **Reviewer:** Claude Opus 5.5 (Anthropic), acting as the cross-provider referee sub-agent. Review date 2026-11-27.
- **Execution environment:** Local Windows host, Python 3 with standard library. The independent probes also used `numpy` 2.4.6 and `sympy` 1.14.0. The probe scripts lived in a session scratchpad and are not committed; the key probes are reproduced in Appendix B.
- **Disclaimer:** Cross-model review is not independent human peer review.

## Verdicts

| Sub-track | Content | Verdict |
|---|---|---|
| **D1** | Theorem 1, Lemma 1.1, Corollary 1.2, Propositions 1.3–1.4 | **ACCEPT AFTER REVISION** |
| **D2** | Theorems 2 and 3, Lemmas 2.1–2.2 | **ACCEPT AFTER REVISION** |
| **D4** | Theorems 4, 5 and 6, Lemmas 3.1 and 5.1, Corollary 5.2 | **ACCEPT AFTER REVISION** |

**Summary.** I found **no Critical error**. Every headline theorem survives line-by-line checking and independent computation:

- the +1 and repunit inversions, including A > 1;
- the sharp 2b^(−L) ceiling and its attainment;
- the all-base L-normal nonnormal reciprocal, which does resolve Phase 22 Open Problem #5;
- Bang–Zsigmondy rigidity, with no exceptions;
- the anchored coprime non-tetration normal reciprocals and their (ln N)^(−A) rate;
- the fully coprime squaring recursions and all-prefix normality;
- the p-adic grid bound for R_k^(E).

The audit records **5 Major** and **18 Minor** findings, and each has a local repair:

- M1: the definitions of K_b and M_b conflict with the rest of the repository, and the proofs for Theorems 5 and 6(b) as written only reach the weaker notion.
- M2: Lemma 2.1 is false as stated.
- M3: the note miscites the Lean lemma `orderOf_mul_pow_sub_one` as needing only the Hull–Dobell hypothesis.
- M4: the evidence labels fall outside the repository's vocabulary, and the `External input` label is missing for Zsigmondy.
- M5: two "obstruction/barrier" claims are heuristic but are presented as proved limitations.

### Response to the specific alarms raised in the review brief

1. **"If A > 1, is x ∈ M_b false?"** — **No; this is a false alarm.** The rational part D/A of X₀ is not stationary. It survives only on band i = 0 of each stage. Bands i ≥ 1 are cancelled exactly, because den(X_{k−1}) divides b^{m_k} − 1, and A divides den(X₀), which divides b^P − 1, which divides b^{m₁} − 1 (note lines 112–124). Hence W₁(μ(X_k), δ₀) ≤ ½·W₁(μ(X_{k−1}), δ₀) + C₁/m_k (+1 case), or with factor 1/b (repunit case). Independent check (Appendix B, P1/P2): for r = 3/11 in base 2, W₁(μ(X_k), δ₀) = 0.333 → 0.220 → 0.110 → 0.055. For r = 5/17 in base 3 the sequence is 0.300 → 0.166 → 0.083 → 0.041. For repunit inversion in base 3 with r = 5/7 it is 0.123 → 0.041 (ratio 1/3), and in base 4 with r = 3/7 it is 0.113 → 0.028 (ratio 1/4). Both Theorem 1 and Proposition 1.3 are valid for every reduced A/D with gcd(b, AD) = 1.
2. **Bang–Zsigmondy exceptions (Lemma 3.1).** All are handled correctly:
   - m = 1: trivial.
   - m = 2 with b + 1 = 2^t: rad\*(b² − 1) contains 4 and b ≡ 3 (mod 4), which forces 2 | n. Examples: b = 3 gives rad\*(8) = 4; b = 7 gives rad\*(48) = 12; b = 15 gives rad\*(224) = 28; b = 31 gives rad\*(960) = 60.
   - (b, m) = (2, 6): rad\*(63) = 21, with ord₃(2) = 2 and ord₇(2) = 3.

   The rad\* convention is essential: with the plain radical, (b, m, n) = (3, 2, 1) would be a counterexample. I independently confirmed rad\*(b^m − 1) | (b^n − 1) ⇔ m | n on **113,400 triples** (2 ≤ b ≤ 64, 1 ≤ m ≤ 30, 1 ≤ n ≤ 60) with no exception (Appendix B, Q1).
3. **"Could d̃_k = (b^{sq_k} − 1)/M share a prime with M? Is M | T_{k−1}/s at k = 2?"** — **No gap.** At k = 2, M does not divide T₁/s = q₁. The note instead treats k = 2 separately through the hypothesis sM | ω₁ (line 398), so q₂ = ω₁q₁ + 1 ≡ 1 (mod sMq₁). For k ≥ 3, M divides T_{k−1}/s = M^{k−2}·∏q_j and s divides ω_{k−1}. So gcd(q_k, sM·∏_{j<k} q_j) = 1, and the lifting-the-exponent lemma (LTE) gives v_p(b^{sq_k} − 1) = v_p(M) for every p | M. This includes p = 2, because 4 | M whenever 2 | M. On **seven genuine recursive schedules** with ω_k = sM^k, I verified every gcd condition, the exact orders T₁ and T₂, and T₃ where feasible. For example, (b, s, q₁) = (2, 2, 5) gives q = [5, 31, 8371] and T₃ = 23,355,090 exactly (Appendix B, Q3).
4. **D^−(1/x; b) > 0 for every convex combination (Theorem 3(b)).** — **Correct.** The single interval I_R = [η_R, 1 − η_R) misses at least 2(R − k_R) points of every orbit μ(sr; b), 1 ≤ s ≤ b − 1. The quantity |I_R| − ν(I_R) is affine in ν. Exact integer check for (b, L, R) = (3, 1, 80), (2, 2, 40) and (4, 1, 400) (Appendix B, P4): the proven lower bound (0.0315, 0.1500 and 0.0128) is at most the true minimum over s (0.0356, 0.1750 and 0.0129).
5. **Loop-deleted de Bruijn digraph G\*_{b,L} at b = 2, L = 1.** G\*_{2,1} is empty and W_R^exact = 0^R1^R. Simple normality holds and D(μ(r_R)) → 1 = 2·2^(−1). Exact check at R = 50: D = 0.86875, above the proven lower bound 0.84875 (Appendix B, P5).

---

## 1. Summary of Findings

| ID | Severity | Location | Issue |
|---|---|---|---|
| **M1** | **Major** | Note line 5; proofs at lines 190, 366, 444, 565 | The note redefines K_b := {D⁺ = 1} (limsup) and M_b := {δ₀ is a weak\* limit point}. The repository's standing definitions are K_b = {D_N → 1} (Phase 21 line 3, Phase 22 line 3, the Lean set `{x | Tendsto (radixDiscrepancy b x N) atTop (𝓝 1)}`) and M_b = {(1/N)Σ‖bⁿx‖ → 0} (docs/results.md:2133). Theorems 5 and 6(b) and Theorem 4's x are proved only along subsequences, which is too weak for the repository meaning of K_b. Open Problem #5 is posed with the strong K_b. |
| **M2** | **Major** | Note lines 277, 294 (Lemma 2.1) | Lemma 2.1 is **false as stated**. Strict interiority does not follow from "not constant at 0 and not constant at M − 1". G_{b,M} has further self-loops labelled 0 or b − 1, e.g. vertex 3 with digit 0 and vertex 2 with digit 2 in G_{3,6}. Constant walks there give r = 1/2, exactly on a cell boundary. The proof's claim "Δ_n = 0 ⇔ all d_j = 0 (forcing u_n = 0 identically)" is false. Theorem 3(b) is unaffected. |
| **M3** | **Major** | Note lines 336, 358 | The note miscites `RadixPowerTower.orderOf_mul_pow_sub_one` as "requir[ing] only the Hull–Dobell hypothesis (HD1)". The kernel theorem's hypothesis is `hdvd : D ∣ b ^ m - 1`, i.e. full divisibility (RadixPowerTower.lean:1247–1248). The period identity T_k = m_k·D_{k−1} under (HD1) is true (I checked 208 chains), but it is currently justified only by this miscitation. |
| **M4** | **Major** | Note lines 66–77 (evidence table), 68–74 | The labels `Paper proof + Exact arithmetic` are not in the repository vocabulary; exact script checks are `Finite certificate`. Theorem 4 rests on Bang (1886) and Zsigmondy (1892) without an `External input` label. Its Weyl bound is imported "exactly as in Phase 22 Theorem 2" (line 362) without being recorded as a dependency. |
| **M5** | **Major** | Note lines 21, 203–213; 42, 368–372; 612 | Heuristic statements are presented as proved limitations. (a) The "Q(1) = 1 cyclotomic obstruction" proves only a coefficient identity and max S_i ≥ 2. The surrounding claims about δ₀-mass and "confirming" from a finite L ≤ 50 search are not theorems. (b) "Persistence of the tetration barrier" shows only that the *sufficient* condition (HD2) forces tetration growth. It does not show that slower-growing Hull–Dobell products fail to be normal. |
| m1 | Minor | Note line 29 | The Theorem 3(a) statement omits the connectivity hypothesis on the support, which line 259 does include. Counterexample: L = 2, p₀₀ = p₁₁ = ½, p₀₁ = p₁₀ = 0. |
| m2 | Minor | Note lines 175, 192, 197 | The interior blocks of Proposition 1.3 reuse Δ_k. With Theorem 1's Δ_k = ⌊√m_{k+1}⌋, these blocks can be empty, since √m_{k+1} may exceed m_k. A separate cutoff Δ′_k = ⌊√m_k⌋ is needed. |
| m3 | Minor | Note line 199 | Symbol clash: δ₀ := ε²/(32b) is used in the same sentence as the Dirac mass δ₀. |
| m4 | Minor | Note lines 113, 130, 150, 163 | Small rigor gaps in Theorem 1: gcd(b^m − 1, b^m + 1) is 1 or 2, not 1; the band-0 tail must be capped at ½; the edge case D = 1 is not covered; the irrationality step ignores the growth of the integer part of A∏(1 + b^{−m_j}). |
| m5 | Minor | Note lines 234, 246, 252, 258 | Theorem 2: the strong-connectivity argument is wrong as worded, though the conclusion is true. Block concatenation needs a common (L−1)-prefix. The notation σ_ext({1⁻}) is undefined. |
| m6 | Minor | Note lines 42, 370 | "m_k > T_{k−1} (k ≥ 3)" holds only eventually under (HD2). The "Consequently" on line 42 is a non-sequitur. |
| m7 | Minor | Note lines 57, 509, 511, 519, 567 | Theorem 6(b): ω₁ ≥ 2 is needed but missing from the statement. "m_{k+1} ≥ 2m_k²" is false. "Exact squaring recursions" are inequalities. |
| m8 | Minor | Note lines 55, 60–61, 578, 600, 610 | Theorem 6(c): defining s_b := ord_p(b) is inconsistent for p = 2. "≤ p^(−r_k) = O(…)" should read ≤. The title says "equidistribution of P_b" when the result concerns the partial products. "T_k ≈ exp(ck²)" is unproven. |
| m9 | Minor | Note lines 5, 444 | The space carrying weak\* limits is unspecified. Theorem 5's x accumulates at 1⁻, which converges to δ₁ on [0, 1] and to δ₀ only on 𝕋. |
| m10 | Minor | Note lines 616–681 | None of the six "Lean blueprint" statements exist in `NormalityChecker/`. Two are false as written: P = 0 and k = 0 are unguarded. |
| m11 | Minor | Script lines 827–836; note line 697 | Only 2 of the 8 "anchored coprime schedules" in §5a satisfy the recursion. Two violate q₁ ≥ 5. |
| m12 | Minor | Script lines 343–375 (esp. 347) | The repunit section tests only A = 1, and the gcd(b, b + 1) branch is dead code. |
| m13 | Minor | Script lines 195–209, 104–119; note lines 68, 693 | Check counts are inflated: 37,063 of the 38,059 "§1 exact checks" are per-coefficient assertions inside `poly_div_exact`. |
| m14 | Minor | Script lines 542, 568, 657–660; note lines 77, 703 | Floating-point discrepancies (§2b, and §3a for P > 100) are listed under "exact verification highlights" and are missing from the floating-point list on line 77. |
| m15 | Minor | Note line 213; script line 415 | "All 562 cyclotomic divisors" is in fact the degree-capped subset (deg Q ≤ ⌊L/2⌋). The uncapped count is **1,050**. The ρ ≥ ½ conclusion holds for all 1,050. |
| m16 | Minor | Script lines 755–758 | The "Zsigmondy exception" check for b ∈ {15, 31} asserts only that 4 | rad\*; it does not test the equivalence. |
| m17 | Minor | Script lines 956–1058; note line 698 | The §6b schedule uses ω ∈ {2, 3, 2}, so the E_k recursion's 7/ω term exceeds 1 and the data does not test the recursion. |
| m18 | Minor | Note lines 14, 223–252, 316–323 | There is no literature attribution for the classical ingredients: the 2b^(−L) ceiling, exact L-uniformity of 1/p for full-reptend primes p ≡ 1 (mod b^L), and the quadratic-reciprocity obstruction. "D odd" in the hypotheses is redundant. |

---

## 2. Detailed Findings and Concrete Repairs

### Major Findings

#### [M1] The definitions of K_b and M_b conflict with the repository, and the proofs of Theorems 5 and 6(b) reach only the weaker notion (note lines 5, 190, 366, 444, 565)

**Defect.** Line 5 defines K_b := {x : D⁺(x; b) = 1} and M_b := {x : δ₀ is a weak\* limit point of μ_N^emp(x; b)}. Elsewhere in the repository:

- Phase 21 (line 3) and Phase 22 (line 3), where Open Problem #5 is posed, define K_b = {z : D_N(z; b) → 1}.
- The Lean kernel uses the set `{x : ℝ | Tendsto (fun N => radixDiscrepancy b x N) atTop (𝓝 1)}` (RadixPowerTower.lean:348).
- docs/results.md:2133 defines M_b = {x : (1/N)Σ_{n<N}‖bⁿx‖ → 0}, the zero-orbit subgroup, with K_b = M_b + Fix_b.

The note's classes are strictly larger, because they use limsup and weak\* *limit points*. Its headline statements "x ∈ M_b ⊂ K_b" therefore look weaker than the registered meaning, which risks confusion in the registry.

**Impact per theorem.**
- **Theorem 1 and Proposition 1.3.** These prove W₁(μ_N^emp(x), δ₀) → 0 and lim D_N(x) = 1 along *all* N (lines 136–141), which is the strong notion. **Correct.** However, for the repunit case, line 190 only says "the identical nonnegativity argument on [bm_k, bm_{k+1})" and gives no details.
- **Theorem 3(b), the Open Problem #5 resolution.** This inherits Proposition 1.3, so it does resolve OP #5 in the Phase 22 sense, provided line 190 is written out.
- **Theorem 5 (line 444).** The proof states only D_{m_{k+1}}(x; b) ≥ 1 − O(S_k/m_{k+1}) → 1, a subsequence. **Theorem 6(b) (line 565)** and **Theorem 4 (line 366)** have the same issue. The strong statement is true: for N ∈ [m_{k+1}, m_{k+2}), every n < N outside at most 2S_k + Δ_k + Δ_{k+1} transition indices satisfies ‖bⁿx‖ ≤ b^(−Δ). As written, however, the proofs establish only D⁺ = 1.

**Repair.**
1. Replace line 5 with the repository definitions: K_b := {x : lim_N D_N(x; b) = 1} and M_b := {x : (1/N)Σ_{n<N}‖bⁿx‖_𝕋 → 0}. Equivalently, M_b is the set of x with μ_N^emp → δ₀ in W₁ on 𝕋. Keep D^± as defined.
2. In Proposition 1.3 Step 1 (line 190), write out the two regimes N ∈ [bm_k, m_{k+1}] and N ∈ (m_{k+1}, bm_{k+1}), as lines 137–139 do for b = 2.
3. Lines 444, 565 and 366: add the one-paragraph all-N argument. The bad-index count is O(S_k + Δ_k + Δ_{k+1}) = o(N) for N ∈ [m_{k+1}, m_{k+2}). Conclude (1/N)Σ‖bⁿx‖ → 0, hence x ∈ M_b ⊂ K_b in the repository sense. The rate becomes 1 − D_N(x; b) = O(N^(−1/2)) uniformly for Theorem 5 with ω_k = sM^k.
4. State that weak\* limits are taken on 𝕋 (see also m9).

#### [M2] Lemma 2.1 is false as stated (note lines 277, 294)

**Defect.** The lemma assumes only that the closed walk "is not constant at 0 and not constant at M − 1". The proof (line 294) asserts "Δ_n = 0 ⇔ all d_j = 0 (forcing u_n = 0 identically)" and "Δ_n = 1 ⇔ all d_j = b − 1 (forcing u_n = M − 1 identically)". Both "forcing" clauses are false. Vertex u carries a 0-labelled loop exactly when (b − 1)u ≡ 0 (mod M), and a (b − 1)-labelled loop exactly when (b − 1)(u + 1) ≡ 0 (mod M). Such vertices exist apart from u = 0 and u = M − 1 whenever gcd(b − 1, M) > 1, i.e. for every b ≥ 3.

**Counterexample** (b = 3, L = 1, Q = 2, M = 6). Vertex 3 has the loop 3 → 3·3 + 0 ≡ 3 (mod 6). The constant walk at 3 is not constant at 0 or at M − 1. It has α = ⌊9/6⌋ = 1, so r = 1/(3 − 1) = 1/2, and {bⁿr} = 1/2 = u/M exactly. Strict interiority fails. Likewise vertex 2 with digit 2 gives r = 1/2 = (u + 1)/M. Further examples (Appendix B, P3):

| b | M | non-extreme loops labelled 0 | non-extreme loops labelled b − 1 |
|---|---|---|---|
| 4 | 24 | 8, 16 | 7, 15 |
| 5 | 60 | 15, 30, 45 | 14, 29, 44 |
| 10 | 25,200 | 2800, 5600, … | 2799, 5599, … |

In each case the constant walk lands on a cell boundary j/(b − 1).

**Impact.** Theorem 3(b) is **unaffected**. Its walk traverses every edge of 𝒢_{b,M} R times, so its digit sequence contains 0, b − 1 and every other digit. The script's exact interiority check (script lines 640–644) confirms this. The Lean blueprint on line 656 already uses the correct hypotheses `hnon0 : ∃ n, d n ≠ 0` and `hnonmax : ∃ n, d n ≠ b - 1`. The prose and the blueprint are therefore inconsistent.

**Repair.**
- Line 277: replace "not constant at 0 and not constant at M − 1" with "whose digit labels (d_n) are not all 0 and not all b − 1".
- Line 294: replace the two parenthetical "forcing" clauses with "Δ_n = 0 ⇔ d_j = 0 for all j, and Δ_n = 1 ⇔ d_j = b − 1 for all j".
- Add a remark that 𝒢_{b,M} has additional self-loops at u with (b − 1)u ≡ 0 or (b − 1)(u + 1) ≡ 0 (mod M).
- Line 305 (Step 1) then needs the observation that C\*_M uses every digit.

#### [M3] Miscitation of the Lean period-lifting lemma under (HD1) (note lines 336, 358)

**Defect.** Line 336 states that "the period-lifting theorem of `RadixPowerTower.lean` (`orderOf_mul_pow_sub_one`) requires only the Hull–Dobell hypothesis (HD1) rad\*(D_{k−1}) | (b^{m_k} − 1)". Line 358 says "Under (HD1), iterating `orderOf_mul_pow_sub_one` gives T_k = m_k D_{k−1}". The kernel theorem (RadixPowerTower.lean:1247–1248, docstring at lines 46–48) has the hypothesis `hdvd : D ∣ b ^ m - 1`, i.e. full divisibility. It does not apply to strict Hull–Dobell chains, and those strict chains are the entire point of §3.

**Mathematical status.** The claim is true. Set q = b^m. If rad\*(D) | (q − 1), then LTE gives D | S_{t−1}(q) ⇔ D | t, so ord_{D(q−1)}(q) = D. Since b^n ≡ 1 (mod q − 1) forces m | n, ord_{D(q−1)}(b) = mD. I verified T₃ = m₃D₂ exactly on **208 (HD1) chains** (b ≤ 7, m_i ≤ 12), including the six strict chains of script §4b (Appendix B, Q2). The note's only justification for this step, however, is the miscited Lean lemma plus a one-line LTE remark embedded in the band argument.

**Repair.**
- Line 336: replace with "The period-lifting theorem `orderOf_mul_pow_sub_one` requires full divisibility D_{k−1} | b^{m_k} − 1; we prove its Hull–Dobell analogue as Lemma 3.2."
- Insert **Lemma 3.2**: for b ≥ 2, m, D ≥ 1 with rad\*(D) | (b^m − 1), ord_{D(b^m − 1)}(b) = mD. Give the LTE proof, including the case v₂(D) = 1.
- Line 358: cite Lemma 3.2 instead.
- Label the result `Paper proof`, or add a Lean lemma generalising `mul_pow_sub_one_dvd_pow_sub_one_iff` to the rad\* hypothesis.

#### [M4] Evidence labels and dependencies (note lines 66–77)

**Defect.**
1. `Exact arithmetic` (lines 68, 70–74) is not one of the repository's evidence labels (Kernel-verified, Lean-supported paper proof, Paper proof, Finite certificate, Conditional, External input, Open). Exact `int`/`Fraction` script checks are `Finite certificate`.
2. Theorem 4's rigidity half rests on Bang–Zsigmondy, a published theorem. It must carry `External input` (Bang 1886; Zsigmondy 1892) alongside `Paper proof`.
3. Theorem 4's all-prefix Weyl bound is "exactly as in Phase 22 Theorem 2" (line 362). Under (HD1), m_K need not be a multiple of T_{K−1}, so the incomplete-period bookkeeping that yields 2T_{K−1}/m_K is new. The dependency on Phase 22 Theorem 2 should be explicit in the table, and the modified band count should be written out (two lines).
4. Theorem 3(c) is unconditional as an implication. Its *examples* (11 primes) are finite certificates, and infinitude in the admissible cases is an Artin-type question that the note does not address. The table should say so.

**Repair.** Replace each "`Paper proof` + `Exact arithmetic`" with "`Paper proof`" and put "`Finite certificate`: scripts/… §k" in the anchor column. Add "`External input` (Bang–Zsigmondy)" to the Theorem 4 row. Add "depends on Phase 22 Theorem 2 (band argument)". Describe floating-point checks as "finite measurements (not evidence)" rather than as a label.

#### [M5] Heuristic "obstructions" and "barriers" presented as proved limitations (note lines 21, 203–213, 42, 368–372, 612)

**(a) The Q(1) = 1 obstruction (Theorem 1 bullet 4, Proposition 1.4).** What is proved is correct. Since A(1) = L, Σ(S_i − 1) = 0, which gives the excess identity. The top deg Q coefficients vanish, so max S_i ≥ 2. The Lean blueprint would formalise this immediately. But three surrounding claims are neither defined nor proved:
- "No pure R₀ = 1 cyclotomic product … can maintain a stationary nonzero δ₀-mass without blowing up previous zero-bands" (line 21);
- "amplifying previous non-zero bands rather than preserving a stationary mixture" (line 209);
- "confirming that no low-degree |S_i| ≤ 1 cyclotomic factor can yield a convergent product ∏(1 − ρ_j) = 1 − α ∈ (0, 1)" (line 213).

A band multiplier S_i ≥ 2 applied to near-zero points keeps them near zero, so the heuristic is not even obviously right. The finite search (L ≤ 50) cannot "confirm" a general statement under the repository's rules.

**(b) Tetration barrier persistence (Theorem 4, lines 42 and 368–372).** The argument shows that the *sufficient* hypothesis (HD2), T_{k−1}/m_k → 0, combined with (HD1)'s period T_k = m_kD_{k−1}, forces tetration growth. It does **not** show that Hull–Dobell products with sub-tetration growth are non-normal. "Cannot escape tetration growth" (line 372) and "persists across the entire Hull–Dobell family" (line 42) overstate a method limitation as a barrier. Objective 4 in `docs/research-objectives.md` requires rigorous limitations. Line 612 ("leaving solely the short-orbit gap") is a similar narrative overstatement.

**Repair.**
- Retitle Proposition 1.4 as a "coefficient excess identity". Move the δ₀-mass interpretation into a clearly labelled *heuristic remark*.
- Rephrase line 213 as "in a finite search (L ≤ 50, deg Q ≤ ⌊L/2⌋; see m15) every divisor with |S_i| ≤ 1 had ρ ≥ ½".
- On lines 42 and 368–372, write: "the sufficient condition (HD2) used in Theorem 4 forces tetration growth; normality of Hull–Dobell products with slower growth is not addressed."
- On line 612, add "heuristically".
- Do not register (a) or (b) as Objective-4 barriers.

### Minor Findings

- **[m1] Line 29** (Theorem 3(a) statement): add "whose support digraph on {0,1}^{L−1} is connected and which assigns positive mass to words containing both digits", as line 259 does. Counterexample to the statement as written: L = 2, p₀₀ = p₁₁ = ½. This p is flow-consistent, but no single periodic orbit realises it, since p₀₁ = 0 forces a constant word. The all-ones word also fails: r = 1 gives {2ⁿr} = 0.
- **[m2] Lines 175, 192, 197** (Proposition 1.3): the interior blocks [sm_k + (b − 1)S_{k−1}, (s + 1)m_k − Δ_k) use Theorem 1's Δ_k = ⌊√m_{k+1}⌋. That cutoff can exceed m_k, which would make the blocks empty, and then "O(b²S_{k−1} + bΔ_k) = o(m_k)" fails. Use Δ′_k := ⌊√m_k⌋ for the internal block ends. This needs b^k·r·b^(−Δ′_k) → 0, which holds because m_k ≥ b^k·k!·P. Keep Δ_k only for the last block.
- **[m3] Line 199**: rename the tolerance (e.g. ϑ := ε²/(32b)) to avoid the clash with the Dirac mass δ₀ in μ_α. The inequality |D(ν) − α| ≤ 4√W₁ is correct: smoothing at width η gives |D(ν) − D(μ_α)| ≤ 2η + W₁/η ≤ 3√W₁.
- **[m4] Theorem 1 rigor.**
  - Line 113: for odd p, the point is that p cannot divide both b^m − 1 and b^m + 1, since their gcd is 1 or 2.
  - Line 130: the band-0 tail b^{r₀}X₀b^(−m_k) exceeds ½ for r₀ near m_k. Cap it with min(½, ·), as was done for band 1.
  - Line 150: "[1/D, 1 − 1/D]" needs D ≥ 2. For D = 1, μ(r) = δ₀, and the positive perturbation still gives the conclusion; say so.
  - Line 163: A∏_{j<k}(1 + b^(−m_j)) has integer part up to 2^{k−1}A, so the zero-run length is m_k − S_{k−1} − log_b A − (k − 1)log_b 2. This still tends to infinity.
- **[m5] Theorem 2.**
  - Line 234: "pushing the L − 1 digits of v avoids the deleted loops unless u = v" is false as worded. For b = 2, L = 3, u = 10, v = 00, the second push uses 000. Replace it with "shortest paths never use self-loops, and G_{b,L} is strongly connected".
  - Line 246: concatenated blocks must share the same (L − 1)-prefix, e.g. 0^{L−1}. Ending in 1 is not what matters. Alternatively note that the boundary windows are an o(1) proportion.
  - Line 252: replace σ_ext({1⁻}) with "σ_ext as a measure on [0, 1] has mass b^(−L) at 1". The script's §2b word w2_ext does start with 0, so it is consistent for L = 2.
- **[m6] Lines 42, 370**: "m_k > T_{k−1} (k ≥ 3)" holds only for k ≥ k₀ under (HD2), which is a limit hypothesis. The "Consequently" on line 42 attributes the growth bound to S_i ≡ i + 1, whereas it comes from (HD2) together with T_k = m_kD_{k−1}.
- **[m7] Theorem 6(b).**
  - The partial-fraction identity (line 519) needs m₂ ≥ 2m₁ + 1, i.e. ω₁ ≥ 2. Line 511 says "for concreteness", but the theorem statement on line 57 lists only ω_k → ∞. Add ω₁ ≥ 2 to it.
  - Line 567: "m_{k+1} ≥ 2m_k²" is false, since m_{k+1} = 2m_k² − 2m_k + 1. Use m_{k+1} ≥ m_k². The remaining constants survive: m_{j₀+2} ≥ m_{j₀}⁴, and c₂(h) = O(m_{j₀}).
  - Lines 57 and 509: call these "squaring inequalities", not "exact squaring recursions".
- **[m8] Theorem 6(c).**
  - Lines 60 and 578: for p = 2, ord₂(b) = 1, yet the note uses s_b = 2 when b ≡ 3 (mod 4). Define s_b := ord₄(b) when p = 2.
  - Lines 61 and 600: "≤ p^(−r_k) = O_b(…)" should be "≤ p^(−r_k) ≤ C_b·k·p^(−e₀k/s_b)".
  - Line 55: the title should read "of the partial products R_k^(E)", not "of P_b = 1/E_b".
  - Line 610: "T_k ≈ exp(ck²)" is unproven. Elementary bounds give k·log²k ≪ ln T_k ≪ k², so label it heuristic.
- **[m9] Lines 5, 444**: state that μ_N^emp lives on 𝕋. On [0, 1], Theorem 5's x has orbit accumulating at 1⁻, i.e. at δ₁, not δ₀.
- **[m10] Lean blueprint (lines 616–681).** `Phase23Cores.lean` contains none of `den_mul_repunit_inv_dvd`, `poly_unit_eval_excess_eq`, `disc_le_two_mul_inv_pow_of_exact_L_normal`, `refined_markov_strict_interiority`, `orderOf_anchored_coprime_prod` or `norm_binary_orbit_sum_le`. Statement defects:
  - (3) lacks `0 < P`. With P = 0 the conclusion |0 − (v − u)| ≤ 2/b^L is false for u = 0, v = 1, b^L ≥ 3.
  - (5) lacks `0 < k`. For k = 0 the left side is `orderOf` in `ZMod 1`, which is 1, while the right side is s·M^0 = s ≥ 2 by `hs` (e.g. b = 2).
  - (4) uses `(M := Q * b ^ L)` as a binder. An optParam would let a caller supply another M.
  - (2) mixes a ℕ `card` with a ℤ sum without casts.

  Mark the section clearly as *unformalised* and fix these before any formalisation claim.
- **[m11] Script §5a (lines 827–836); note line 697.** Only (4, 1, [4, 13]) and (5, 1, [5, 21]) satisfy q₂ = ω₁q₁ + 1 with sM | ω₁. The others imply non-integral ω₁, e.g. 19 = 5ω₁ + 1. (4, 1, [4, 13]) and (3, 2, [3, 5]) also violate q₁ ≥ 5. The section validly tests the generic pairwise-coprime factorisation (Steps 1–2), but "8 anchored coprime schedules" mislabels it. Add genuine schedules such as (2, 2, 5) → [5, 31, 8371] and (4, 1, 5) → [5, 16, 2161] (Appendix B, Q3).
- **[m12] Script §1d (lines 343–375).** A = 1 in every case, and `b + 1 if gcd(b, b + 1) == 1 else b + 2` (line 347) is dead code because gcd(b, b + 1) = 1. Add A > 1 seeds; my probe P2 supplies (3, 5, 7), (3, 2, 5), (4, 3, 7) and (5, 2, 3).
- **[m13] Check-count inflation.** Attribution of the 49,819 checks: `poly_div_exact` 37,063 (§1, per-coefficient divisibility asserts while building Φ_n and dividing); `order_mod` helper asserts 848; `dfs` 562; the remainder are substantive. The note's "38,059 exact checks" for §1 (line 68) should be replaced by a substantive count (≈ 930) or explained.
- **[m14] Float vs exact.** `disc_float_orbit` is used for §2b (line 568) and for §3a when P > 100 (lines 657–660). Line 703 nevertheless presents "D ∈ [0.1033, 0.1458]" and similar values among "exact verification highlights". Line 77's floating-point list omits §2b and §3a. Relabel these values.
- **[m15] Line 213 / script line 415.** The DFS prunes at `cur_deg + phi_d < L // 2 + 1`, so 562 counts only divisors with deg Q ≤ ⌊L/2⌋. My uncapped enumeration finds **1,050** cyclotomic divisors with |Q(1)| ≥ 2 and all |S_i| ≤ 1 (L ≤ 50). All of them have ρ ≥ ½, so the cap is harmless: deg Q > L/2 forces ρ > ½ because the top deg Q coefficients vanish. The wording "all 562" is still inaccurate.
- **[m16] Script lines 755–758.** The b ∈ {15, 31} check asserts only `rad_star(b**2-1) % 4 == 0` and (b − 1) ≡ 2 (mod 4). It does not test the equivalence. The "incl. all Zsigmondy exceptions" claim (line 760) therefore rests on b ∈ {2, 3, 7} only. My brute force (Q1) covers b ≤ 64.
- **[m17] Script §6b (lines 956–1058).** With ω = (2, 3, 2), 7/ω ≥ 2.33, so the E_k recursion is vacuous on this data. The data is a finite measurement of decay, not a test of the recursion. My probe Q4 confirms the |Ĉ_k| inequality on [2, 5, 31, 621] and on [2, 9, 145, 41761] (ω = 4, 8, 16). In the second schedule it is nearly tight at k = 4, h = 3 (0.21478 ≤ 0.2152).
- **[m18] Attribution and hypotheses.**
  - The sharp ceiling 2b^(−L) for L-normal numbers and the exact L-uniformity and discrepancy 2/p of 1/p for full-reptend primes p ≡ 1 (mod b^L) are classical-style facts. So is the quadratic-reciprocity obstruction (b a square mod p ≡ 1 (mod b^L) in the stated residue classes). Add a literature search and attribution, or an explicit statement that no prior source was located.
  - "D odd" (line 14) is redundant: 2 ∈ ⟨b⟩ (mod D) forces gcd(2, D) = 1. Moreover, for D ≥ 2, 2 ∈ ⟨b⟩ (mod D) holds iff D | 2b^L − 1 for some L ≥ 1, so the parenthetical on line 14 is in fact a characterisation.
  - Script line 250 contains a leftover exploratory comment ("2/3? Let's compute exact!"). The exact value is 11/20.

---

## 3. Verification Checklist (Independent Line-by-Line Audit)

### 3.1 D1 — Theorem 1, Lemma 1.1, Corollary 1.2, Propositions 1.3–1.4

| Item | Status | Notes |
|---|---|---|
| den(X_k) divides b^{2m_k} − 1 (lines 112–116) | ✅ | Valid for every prime, including p = 2 and any parity of A or b. Independently confirmed for A > 1 (P1). |
| Signed band identity (lines 118–124) | ✅ | b^m·b^m/(b^m + 1) = (b^m − 1) + 1/(b^m + 1). |
| W₁ contraction with factor ½ and all-N upgrade (lines 126–141) | ✅ (m4) | Needs m_{k+2}/(2m_{k+1}) → ∞ for b^{2m_{k+1}−m_{k+2}} → 0, which is assumed. Markov step: D_N ≥ 1 − √(8W₁) is exact. |
| x ∈ M_b when A > 1 | ✅ | False alarm (see the alarm response). Numerical halving in P1. |
| Subset-sum orbit lock b^nY_k ≡ 2^k·b^n·r (line 147) | ✅ | Each b^{n−m_I}r − b^n r is an integer because D | b^{m_I} − 1. |
| No wrap-around, Lemma 1.1, word frequencies (lines 149–160) | ✅ | The perturbation is positive and below 1/(2D). `coprime_rat_cylinder_margin` exists (RadixPowerTower.lean:928) with hypotheses d ≥ 2, 1 ≤ r < d, matching the use. |
| Lemma 1.1 (lines 89–101) | ✅ | Both directions re-derived, including empty I⁻ and clipped I⁺. |
| Irrationality (line 163) | ✅ (m4) | Zero runs tend to infinity, which contradicts eventual periodicity. |
| Corollary 1.2, base-2 density | ✅ | The order-m de Bruijn part is m-normal, so discrepancy ≤ 2^{1−m}, with O(m/(z + 2^m)) wrap error. |
| Proposition 1.3: den(X_k) divides b^{bm_k} − 1, band identity, τ_i | ✅ | Re-derived S₀ = 1, S_{i≥1} = 0, and τ_i. Contraction factor 1/b confirmed for A > 1 (P2). |
| Proposition 1.3 block structure | ✅ (m2) | Block s tracks μ((s+1)r). Block b − 1 returns to μ(br) = μ(r). Requires a separate interior cutoff. |
| Proposition 1.3 localisation | ✅ (m3) | s_*μ_α = μ_α, W₁ scales by at most s, and |D(ν) − α| ≤ 3√W₁. |
| Proposition 1.4 excess identity | ✅ / (M5) | The identity and max S_i ≥ 2 are correct. The "obstruction" reading is heuristic. |

### 3.2 D2 — Theorems 2–3, Lemmas 2.1–2.2

| Item | Status | Notes |
|---|---|---|
| Upper bound D⁺ ≤ 2b^(−L) (lines 222–230) | ✅ | Inner and outer cylinder covers. |
| G\*_{b,L} balanced and strongly connected, Eulerian circuit of length b^L − 2 | ✅ (m5) | Conclusion true. b = 2, L = 1 handled (empty G\*). |
| W_R^exact is exactly L-normal and D → 2b^(−L) | ✅ | Formula lower bound verified exactly for 5 cases (P5). |
| Exact attainment and the affine law D((1−t)λ + tσ) = tD(σ) | ✅ (m5) | |
| Theorem 3(a) word distributions | ✅ (m1) | Connectivity needed in the statement. |
| Lemma 2.1 cell tracking and the identity bu_n + d_n = α_nM + u_{n+1} | ✅ | |
| Lemma 2.1 recurrence Δ_{n+1} = bΔ_n − d_n and its periodic solution | ✅ | Re-derived. |
| Lemma 2.1 hypothesis | ❌ **(M2)** | False as stated. The application is fine. |
| Lemma 2.2 simultaneous exact L-normality of sr | ✅ | The preimage of C_w under ×s is a union of Q cells, since s | Q. The script verifies it exactly for 6 (b, L) cases. |
| Theorem 3(b) steps 1–4 | ✅ | In-degree b (each residue is hit b times by bu + d). The rotation for b = 2 may split the (M−1)-loop block, which is harmless cyclically. |
| Theorem 3(b) step 5, D⁻ > 0 for every convex combination | ✅ | Exact checks in P4. |
| Resolution of Phase 22 OP #5 | ✅ (conditional on the M1 repair) | OP #5 (Phase 22 line 967) asks for x ∈ K_b with K_b = {D_N → 1}, b ≥ 3, and 1/x simply normal but nonnormal. Theorem 3(b) at L = 1 delivers this. |
| Theorem 3(c), full-reptend 1/p | ✅ | Cylinder count k is exact. D(μ(1/p)) = 2/p (max 1/p, min −1/p). |
| QR obstruction, three regimes | ✅ | Each Legendre-symbol step re-derived. |
| Theorem 3(d), the R₀ = 1 obstruction | ✅ | Portmanteau on the open arc (−b^(−L), b^(−L)) in 𝕋. |

### 3.3 D4 — Theorems 4–6, Lemmas 3.1 and 5.1, Corollary 5.2

| Item | Status | Notes |
|---|---|---|
| Lemma 3.1 Bang–Zsigmondy rigidity | ✅ | All exceptions correct. 113,400-triple brute force (Q1). |
| (HD1) characterisation, including 2 \| m_k (k ≥ 3) for b ≡ 3 (mod 4) | ✅ | Equivalent in every case. 11,520-chain brute force (Q2). |
| T_k = m_kD_{k−1} under (HD1) | ✅ (M3) | True by LTE (208 chains), but miscited. |
| Ĉ_{K−1} vanishes off D_{K−2}ℤ under (HD1) | ✅ | i ↦ S_i(q) mod D_{K−2} is a bijection because ord_{(q−1)D}(q) = D. |
| Theorem 4 Weyl bound with 2T_{K−1}/m_K | ✅ (M4) | Incomplete periods per band plus the final band. Import from Phase 22. |
| Barrier persistence | ⚠️ **(M5b)** | Limits only the method. |
| Theorem 5 conditions s_b and M | ✅ | 4 \| M whenever 2 \| M, rad\*(M) \| M, ord_{M^k}(b) = sM^{k−1}. |
| gcd(q_k, sM∏_{j<k} q_j) = 1, including k = 2 | ✅ | Seven genuine schedules (Q3). |
| d̃_k coprime to M and pairwise coprime | ✅ | Via LTE and gcd(b^{sq_j} − 1, b^{sq_k} − 1) = M. |
| Exact period T_k | ✅ | Exact for T₁, T₂ on all seven schedules, and T₃ ∈ {23,355,090; 1,555,920; 42,201,264}. |
| CRT grid: Ĉ_k = 0 off M^{k−1}ℤ and D ≤ M^(−(k−1)) | ✅ | Genuine k = 3 schedule (4, 1, 5): D(μ(R₃)) ≈ 0.0406 ≤ 1/9, and max_{h<9}|Ĉ₃(h)| ≈ 8.4·10⁻¹⁷ (Q3). |
| Band identity, LTE v_p(S_i(b^s)) = v_p(i+1), d′-vanishing | ✅ | Stage-3 band averages for h = 1, 2: ≈ 5·10⁻⁴ (within the tail error (s + c_b)/m₃ ≈ 0.006) on every band with 3 ∤ i + 1, and non-zero (0.15, 0.17, …) when 3 \| i + 1. For h = 3 (d′ = 1), all bands are non-zero, exactly as predicted (Q3). |
| All-prefix Weyl bound: partial band, incomplete cycle, s extra steps, tail, approximation | ✅ | The inequality (m − 1 + θ)/(md′ − 1 + θ) ≤ 1/d′ was checked. |
| Growth ln T_k = (c\* + o(1))·2^k; m_{k+1} ≍ (M²/s)m_k² | ✅ | Recursion T_k = M^kT_{k−1}² + MT_{k−1} re-derived. Script constants match the series (e.g. c\* ≈ 2.807 for (2, 2, 5)). |
| Rate O((ln ln N)^{ω(M)+1}(ln N)^(−log₂M)) | ✅ | 2^K ≍ ln N on [m_K, m_{K+1}). Erdős–Turán with H = M^{K−2}. Σgcd(h, H)/h ≤ τ(H)(1 + ln H). |
| Lemma 5.1, the 01-transition bound | ✅ | x ∈ [¼, ½) strictly, y − x = x, so |e(x) + e(y)| ≤ √2. |
| Corollary 5.2, prime product | ✅ | Non-monotone |Ĉ_k(1)| in script §6c is consistent, because ν_j^(k) depends on k here. |
| Theorem 6(b): k-independence of ν_j, partial-fraction identity | ✅ (m7) | a_j^(k) ≡ 2a_j^(k−1). The identity needs ω₁ ≥ 2. |
| Squaring inequality for |Ĉ_k| | ✅ | Re-derived (|ν̂_k − conj Ĉ_{k−1}| ≤ c₂/m_k). Numerically confirmed (Q4). |
| E_k = ∏e_j, autocorrelation, constants 7/ω + 4c₂/m | ✅ | Weights per residue class re-derived. Total error ≤ 6/ω + (4c₂ + 1)/m ≤ 7/ω + 4c₂/m. |
| E_j → 0 via L ≤ L² | ✅ | e_{j₁} < 1 from the gcd bound 2^{gcd(m,s)} − 1 ≤ 2^{m/2} − 1. |
| All-prefix normality (§5.3), partial bands | ✅ | Leftover below T_{K−1}/N < 1/ω. Periodicity in i with period T_{r\*}. Cauchy–Schwarz against E_{r\*}. |
| Complete-period rate O(exp(−c₀(ln T_k)^{1/4})) | ✅ (m7) | (7/4)-growth phase, then squaring phase. Exponent ln 2/ln(7/4) ≈ 1.239, so 2^{k₂} = O((ln H)^{2.5}). |
| R_k^(E): e_k ≥ e₀⌊k/s_b⌋, v_p(T′_k) ≤ ⌊log_p k⌋, grid bound | ✅ (m8) | No violations for k ≤ 40 in b ∈ {2, 3, 4, 5, 6, 7, 10, 11} (Q5). The sign-coset formula for p = 2, b ≡ 3 (mod 4) was re-derived. The b = 3, k = 2 example (D = 3/8) was checked by hand. |

### 3.4 Script execution, numerical claims and evidence separation

- `python -B scripts/phase23_reciprocals_v2.py`: **exit 0, "Total: 49819 checks passed in 0.73 s"**. The note says 0.83 s, which is immaterial. Per-section counts 38,059 / 142 / 4,280 / 2,254 / 4,480 / 604 match note lines 68–74 and 693–699 exactly.
- Every number quoted in note §7 (lines 693–705) matches the printed output: D_∞(1/15; 2) = 11/20; D_N(X₃) = 0.8672 and 0.8555; D_N(Y₃) = 0.6283 and 0.3905; de Bruijn+zeros range 0.118877–0.884293; 2-normal range 0.11888–0.35417; refined-Markov ranges; c\* = 2.807411, 5.728742, 4.273538, 4.272705; |C₄(1)| = 0.00279; E₄(1) = 0.00231; R_k^(E) values at (2, 3, 6), (3, 2, 5), (5, 2, 5); counts 562 and 427.
- Exact versus floating-point separation is mostly respected in the code. The exceptions are labelling issues m14 and m13, plus the scope issues m11, m12, m15, m16 and m17. No floating-point output is used as a proof substitute in the note's arguments.

---

## 4. Required Revisions for Acceptance

1. **M1:** adopt the repository definitions of K_b and M_b. Write the all-N arguments for Proposition 1.3 (line 190), Theorem 4 (line 366), Theorem 5 (line 444) and Theorem 6(b) (line 565).
2. **M2:** correct the hypothesis and proof of Lemma 2.1, and add a remark on the extra self-loops.
3. **M3:** remove the miscitation and add the Hull–Dobell period lemma with its LTE proof (Lemma 3.2).
4. **M4:** bring the evidence table into the repository vocabulary, add `External input` for Bang–Zsigmondy, and record the Phase 22 Theorem 2 dependency.
5. **M5:** relabel the Q(1) = 1 "obstruction", the Hull–Dobell "barrier persistence" and the §5.5 "solely" claim as heuristic or method limitations.
6. **m1–m18:** apply the local repairs above. Statement-level corrections (m1, m2, m7, m8, m10) have priority over script relabelling (m11–m17).

On completion of items 1–5, all three sub-tracks should be re-checked and can be upgraded to **ACCEPT**. No mathematical result needs to be withdrawn.

---

## Appendix A — Reproduction of the audited script

```
python -B scripts/phase23_reciprocals_v2.py
...
Per-section check counts:
  1. D1 Convergent reciprocals              :  38059
  2. D2 Exact D_max(b,L) = 2/b^L            :    142
  3. D2 All-base L-normal reciprocals       :   4280
  4. D4 Hull-Dobell rigidity & barrier      :   2254
  5. D4 Anchored coprime schedules          :   4480
  6. D4 Coprime CRT, primes & 1/E_b         :    604
Total: 49819 checks passed in 0.73 s
```

Check attribution (instrumented `check`, by calling function): `poly_div_exact` 37,063; `order_mod` 848; `dfs` 562; `verify_exact_L_word_counts` 58; `build_*` 42; section bodies 11,246.

## Appendix B — Independent probes (summary of outputs)

**P1 (Theorem 1, A > 1).** W₁(μ(X_k), δ₀) for k = 1, 2, 3, with schedule m = [P, 6P, 48P]:

| b | r | W₁(μ(X₀), δ₀) | k = 1 | k = 2 | k = 3 |
|---|---|---|---|---|---|
| 2 | 3/11 | 0.3333 | 0.21997 | 0.11004 | 0.05502 |
| 3 | 5/17 | 0.3000 | 0.16576 | 0.08288 | 0.04144 |
| 5 | 7/9 | 0.2857 | 0.19600 | 0.09800 | 0.04900 |
| 2 | 7/1 | 0.2857 | 0.16402 | 0.08246 | 0.04123 |

**P2 (Proposition 1.3, A > 1).** W₁ by stage:

| b | r | k = 1 | k = 2 | ratio |
|---|---|---|---|---|
| 3 | 5/7 | 0.12265 | 0.04088 | 1/3 |
| 3 | 2/5 | 0.16836 | 0.05612 | 1/3 |
| 4 | 3/7 | 0.11263 | 0.02816 | 1/4 |
| 5 | 2/3 | 0.10000 | 0.02000 | 1/5 |

In every case the period divisibility den(X_k) | b^{bm_k} − 1 held exactly.

**P3 (Lemma 2.1 counterexamples).** Self-loops labelled 0 or b − 1 at non-extreme vertices of 𝒢_{b,M} (L = 1). Each constant walk gives r on a cell boundary:

| b | M | 0-labelled loops at | (b−1)-labelled loops at | constant walks give r = |
|---|---|---|---|---|
| 3 | 6 | 3 | 2 | 1/2 (both) |
| 4 | 24 | 8, 16 | 7, 15 | 1/3, 2/3 |
| 5 | 60 | 15, 30, 45 | 14, 29, 44 | 1/4, 1/2, … |
| 6 | 360 | 72, 144, 216, 288 | 71, 143, … | 1/5, 2/5, … |
| 10 | 25,200 | 2800, 5600, … | 2799, 5599, … | 1/9, 2/9, … |

Minimal reproduction:

```python
b, M = 3, 6                      # Q = lcm(1,2) = 2, L = 1
assert (b*3 + 0) % M == 3        # 0-labelled self-loop at u = 3
alpha = (b*3)//M                 # = 1
r = alpha/(b-1)                  # constant walk => r = 0.111..._3 = 1/2
assert r*M == 3                  # {b^n r} = u/M exactly: strict interiority fails
```

**P4 (Theorem 3(b), D⁻ lower bound).** Exact integer test for every s:

| (b, L, R) | proven lower bound | min_s(\|I_R\| − μ_s(I_R)) |
|---|---|---|
| (3, 1, 80) | 0.031481 | 0.035648 |
| (2, 2, 40) | 0.150000 | 0.175000 |
| (4, 1, 400) | 0.012760 | 0.012943 |

**P5 (Theorem 2 attainment formula).**

| (b, L, R) | D | formula lower bound | ceiling 2b^(−L) |
|---|---|---|---|
| (2, 1, 50) | 0.86875 | 0.84875 | 1 |
| (2, 2, 25) | 0.39396 | 0.33750 | 0.5 |
| (3, 1, 30) | 0.58148 | 0.55309 | 0.667 |
| (3, 2, 10) | 0.17767 | 0.08148 | 0.222 |
| (5, 1, 20) | 0.34645 | 0.28000 | 0.4 |

**Q1 (Lemma 3.1).** 113,400 triples (2 ≤ b ≤ 64, m ≤ 30, n ≤ 60). rad\*(g) | N was tested without factorisation, as g | N^{bitlen(g)} together with (4 | g ⇒ 4 | N). No exception.

**Q2 ((HD1) characterisation).** 11,520 chains (2 ≤ b ≤ 11, m₁ ≤ 8, m₂, m₃ ≤ 12) agree with the stated equivalence. T₃ = m₃D₂ holds exactly on 208 (HD1) chains (b ≤ 7, m₃ ≤ 8).

**Q3 (Theorem 5, genuine schedules ω_k = sM^k).** All gcd and coprimality conditions held.

| (b, s, q₁) | q | exact orders |
|---|---|---|
| (2, 2, 5) | [5, 31, 8371] | T₃ = 23,355,090 |
| (3, 2, 5) | [5, 81, 414721] | T₂ = 6,480 |
| (4, 1, 5) | [5, 16, 2161] | T₃ = 1,555,920 |
| (5, 1, 7) | [7, 29, 12993] | T₃ = 42,201,264 |
| (10, 1, 7) | [7, 64, 326593] | T₂ = 4,032 |
| (7, 2, 5) | [5, 481, 531947521] | T₂ = 230,880 |
| (2, 4, 7) | [7, 421, 39784501] | T₂ = 176,820 |

For (4, 1, 5) at k = 3: D(μ(R₃)) ≈ 0.04064 ≤ 1/9, and max_{h<9}|Ĉ₃(h)| ≈ 8.4·10⁻¹⁷. Stage-3 band averages, i = 0…8, for h = 1: 0.0005, 0.0005, **0.1519**, 0.0006, 0.0007, **0.0096**, 0.0005, 0.0005, **0.0087**. The bold entries are exactly the bands with 3 | i + 1, as predicted.

**Q4 (Theorem 6(b)).** |Ĉ_k(1)| on [2, 5, 31, 621] is 0.50000, 0.21879, 0.05204, 0.00279, reproducing script §6b. The inequality |Ĉ_k| ≤ |Ĉ_{k−1}|² + c₂/m_k holds for h ∈ {1, 3, 5} on [2, 5, 31, 621] and on [2, 9, 145, 41761] (ω = 4, 8, 16). In the second schedule at k = 4: h = 1 gives 0.00248 ≤ 0.0028, and h = 3 gives 0.21478 ≤ 0.2152. The E_k inequality holds but is vacuous at these ω.

**Q5 (Theorem 6(c)).** e_k ≥ e₀⌊k/s_b⌋ and v_p(T′_k) ≤ ⌊log_p k⌋ hold for all k ≤ 40 in each base:

| b | p | s_b | e₀ |
|---|---|---|---|
| 2 | 3 | 2 | 1 |
| 3 | 2 | 2 | 3 |
| 4 | 3 | 1 | 1 |
| 5 | 2 | 1 | 2 |
| 6 | 5 | 1 | 1 |
| 7 | 2 | 2 | 4 |
| 10 | 3 | 1 | 2 |
| 11 | 2 | 2 | 3 |

No violations.

**m15 recount.** The uncapped enumeration of cyclotomic divisors Q of (1 − q^L)/(1 − q) with L ≤ 50, |Q(1)| ≥ 2 and all |S_i| ≤ 1 gives 1,050 divisors (562 with deg Q ≤ ⌊L/2⌋). None has ρ < ½.

---

*Cross-model review is not independent human peer review.*

---

## Post-Repair Verification

- **Re-audited (read-only, not modified):** `notes/phase23/convergent-reciprocals-and-schedules.md` (768 lines) and `scripts/phase23_reciprocals_v2.py` (1,289 lines).
- **Reviewer and date:** Claude Opus 5.5 (Anthropic), 2026-11-27.
- **Reproduction:** `python -B scripts/phase23_reciprocals_v2.py` exits **0** and prints "Total: 12193 exact checks + 510 float measurements (12703 total) passed in 0.88 s".
  - Exact counts per section: 1,482 / 125 / 3,732 / 2,343 / 4,431 / 80.
  - Float counts per section: 4 / 17 / 11 / 0 / 8 / 470.
  - Both rows match the note's §7 table and the evidence table on lines 72–81 exactly.

### Major findings

| ID | Status | Evidence in the repaired note |
|---|---|---|
| **M1** | ✅ Closed | Lines 5–8 now use the repository definitions: K_b = {lim D_N = 1} and M_b = {(1/N)Σ‖bⁿx‖ → 0}, with weak\* limits on 𝕋. Each proof now covers all N, not just a subsequence: <br>• **Theorem 1** (lines 140–145): two regimes on [2m_k, 2m_{k+1}). <br>• **Proposition 1.3** (lines 196–200): regimes N ∈ [bm_k, m_{k+1}] and (m_{k+1}, bm_{k+1}); bands 1…b−1 contribute ≤ (b−1)C₁/N. <br>• **Theorem 4** (§3.2, lines 396–406): a general four-range bound W₁ ≤ (S_k + 4)/N for every N ∈ [m_{k+1}, m_{k+2}). It applies whenever m_{j+1}/m_j → ∞, which (HD1)–(HD2) imply via T_j ≥ m_j. <br>• **Theorem 5** (lines 484–488): reuses the four-range bound. <br>• **Theorem 6(b)** (line 613): reuses the four-range bound. <br>• **Uniform rate for Theorem 5** (lines 502–506): 1 − D_N(x; b) ≤ (2S_k + 2⌈log_b N⌉ + 2)/N. Since m_{k+1} ≍ (M²/s)m_k², S_k = O(N^{1/2}), so the rate is O_{b,s}(N^(−1/2)) uniformly. I re-derived the bad-index count 2S_k + 2Δ. |
| **M2** | ✅ Closed | **Hypothesis** (line 288): the edge labels (d_n) are not all 0 and not all b − 1. **Proof** (line 305): Δ_n = 0 ⇔ every d_j = 0, and Δ_n = 1 ⇔ every d_j = b − 1. The false "forcing" clauses are gone. **New remark** (line 307): non-extreme self-loops sit at (b−1)u ≡ 0 and (b−1)(u+1) ≡ 0 (mod M). It gives the exact 𝒢_{3,6} examples (u = 3 with label 0; u = 2 with label 2; both give r = 1/2). **Theorem 3(b) Step 2** (line 319) now observes that the walk uses every digit. The prose agrees with blueprint hypotheses `hnon0`/`hnonmax`. |
| **M3** | ✅ Closed | **Citation** (line 351): now says `orderOf_mul_pow_sub_one` assumes full divisibility D_{k−1} \| b^{m_k} − 1. **New Lemma 3.2** (lines 369–380) is self-contained and correct. I checked each case: <br>• (b^m − 1) \| (b^N − 1) ⇔ m \| N; <br>• odd-p LTE; <br>• the v₂(D) = 1 parity case (q odd, so Σq^j ≡ t mod 2); <br>• 2-adic LTE when 4 \| D, which forces 4 \| rad\*(D) \| q − 1; <br>• the conclusion ord_{D(b^m−1)}(b) = mD; <br>• the bijection of the partial sums S_i mod D. <br>Line 386 now cites Lemma 3.2 for T_k = m_kD_{k−1} and for vanishing of Ĉ_{k−1} off D_{k−2}ℤ. The lemma is labelled `Paper proof`. |
| **M4** | ✅ Closed | **Labels** (lines 70–79): only `Paper proof`, `Open` and `External input` appear; script checks sit in the anchor column as `Finite certificate`. **Theorem 4** carries `External input` (Bang 1886; Zsigmondy 1892) and records its dependency on Phase 22 Theorem 2. **Incomplete-period bookkeeping** (2T_{K−1}/m_K) is written out on line 390. **Theorem 3(c)** examples are marked finite, and infinitude is flagged as an open Artin-type question. **Floats** are described as "finite measurements (not evidence)" (line 81 and §7). |
| **M5** | ✅ Closed | **(a)** Proposition 1.4 is retitled "coefficient excess identity" and proves only the identity and max S_i ≥ 2. The δ₀-mass reading moved to a *Heuristic remark* (line 222). That remark disclaims any general impossibility theorem and states the finite search as a `Finite certificate`, with 1,050 uncapped divisors and 562 under the degree cap. The overstated sentence formerly in Theorem 1 is removed. **(b)** Lines 46 and 408–412 now say the *sufficient* conditions (HD1)–(HD2) force eventual tetration growth, and that slower-growing products are "not addressed". Line 660 reads "Heuristically, … for this product-approximation approach". Neither (a) nor (b) is presented as an Objective-4 barrier. |

### Minor findings

| ID | Status | Evidence |
|---|---|---|
| m1 | ✅ | Connectivity and both-digit hypotheses added to the Theorem 3(a) statement (line 33) and proof (line 270). |
| m2 | ✅ | Interior blocks use Δ′_k = ⌊√m_k⌋ (lines 181, 202–208). The inactive-term bound 2y·b^(−Δ′_k) uses Y_{k−1} < y, so it needs no extra b^k factor. |
| m3 | ✅ | Tolerance renamed ϑ := ε²/(32b) (line 210). |
| m4 | ✅ | Four fixes, all present: <br>• gcd ∈ {1, 2} (line 117); <br>• min(½, ·) band-0 cap (line 134); <br>• D = 1 case (line 156); <br>• integer-part growth in the irrationality step, ⌈log_b A⌉ + k (line 169). |
| m5 | ✅ | Three fixes: <br>• shortest paths avoid self-loops (line 245); <br>• common 0^{L−1} prefix at block junctions (lines 257, 269); <br>• σ_ext defined on [0, 1] with mass b^(−L) at both 0 and 1 (line 263). |
| m6 | ✅ | "for all sufficiently large k ≥ k₀" added. The non-sequitur "Consequently" is replaced by "Independently", and the growth is attributed to (HD2) + T_k = m_kD_{k−1} (lines 46, 408). |
| m7 | ✅ | Three fixes: <br>• ω₁ ≥ 2 is in the statement (lines 61, 559); <br>• m_k² ≤ m_{k+1} ≤ 2m_k² (line 615), with m_{j₀+2} ≥ m_{j₀}⁴ retained; <br>• the term "squaring inequalities" is used throughout. |
| m8 | ✅ | Four fixes: <br>• s_b := ord₄(b) for p = 2 (lines 64, 626); <br>• the chain reads "≤ p^(−r_k) ≤ C_b·k·p^(−e₀k/s_b)" (lines 65, 648); <br>• the title now refers to "the partial products R_k^(E)" (line 59); <br>• T_k ≈ exp(ck²) is replaced by the elementary bounds k·log²k ≪ ln T_k ≪ k², labelled heuristic (lines 658, 660). |
| m9 | ✅ | Weak\* limits are on 𝕋 (line 9). The δ₁ on [0, 1] versus δ₀ on 𝕋 remark appears on lines 406 and 488. |
| m10 | ✅ | §6 is retitled "Unformalized — Not Yet in `NormalityChecker/`" and opens with a status note. Statement fixes: <br>• (3) gains `hP : 0 < P`; <br>• (5) gains `hk : 0 < k`; <br>• (4) states `hM : M = Q * b ^ L` as a hypothesis; <br>• (2) casts `card` to ℤ. |
| m11 | ✅ | §5a has 9 genuine recursive schedules, each checked in code (script lines 881–917) for q₁ ≥ 5, gcd(q₁, sM) = 1, sM \| ω₁ and s \| ω_{k−1}. I recomputed every printed q-vector from its ω-vector. Examples: 421 = 60·7 + 1; 8371 = 18·465 + 1; 2161 = 9·240 + 1. |
| m12 | ✅ | §1d includes the A > 1 seeds (3, 5/7), (3, 2/5), (4, 3/7) and (5, 2/3). The dead `gcd(b, b + 1)` branch is gone. |
| m13 | ✅ | Helper invariants in `order_mod` and `poly_div_exact` go through `internal_assert`, which is uncounted. The headline total fell from 49,819 to 12,193 substantive exact checks, and the note states the exclusion (line 735). |
| m14 | ✅ | §2b now computes exact `Fraction` discrepancies; the output reads "exact Fraction D". §3a values for P > 100 are printed as "D (float)" and listed only under the floating-point finite measurements in note §7. The float list on line 81 is accurate. |
| m15 | ✅ | The note states the 1,050 uncapped divisors and the 562 capped ones, and the script output confirms both counts. |
| m16 | ✅ | Script lines 799–813 now test the full equivalence on 124 triples: b ∈ {3, 7, 15, 31, 63} at m = 2 with n ≤ 20, and (2, 6) with n ≤ 24. |
| m17 | ✅ | §6b-i is labelled a finite decay measurement (7/ω ≥ 2.33). §6b-ii adds [2, 21, 421] with ω = (10, 10), where the bound E₃(1) = 0.02188 ≤ 0.84025 < 1 is non-vacuous. §6b-iii adds the tight [2, 9, 145, 41761] case, reproducing my probe Q4 (0.21478 ≤ 0.21515). |
| m18 | ✅ | **Literature notes** cover Theorem 2 (line 230) and Theorem 3(c) with the QR obstruction (line 329). Each says either that no prior source for the attainment construction was located, or names the classical sources. **"D odd"** is now a consequence, not a hypothesis, and the characterisation D \| 2b^L − 1 is stated (line 18). **The leftover script comment** is gone. The book-chapter pointer (Bugeaud, Ch. 4) was not independently checked. |

### §7 numerical cross-check

I grepped the captured output for every value quoted in §7. Each appears with the stated context:

- exact discrepancies 2/3, 2/5, 11/20, 2/7, 54/155, 2/49 and 2/19;
- de Bruijn range 0.118877–0.884293;
- §2b values 0.11888, 0.13167, 0.17955, 0.23301, 0.31076 and 0.35417;
- §3a exact values 0.3021 and 0.1883, and float ranges [0.1033, 0.1458], [0.0361, 0.0642], [0.0207, 0.0559] and [0.0067, 0.0250];
- primitive-root discrepancies 2/163 and 2/701;
- the Theorem 5 periods and discrepancies: 930 / 0.146872, 23,355,090, 240 / 0.187867, 1,555,920, 420 / 0.151982 and 812 / 0.169659;
- the R_k^(E) values (615195, 3780, 0.00208), (8053760, 3840, 0.00444) and (23205371904, 30720, 0.00042);
- §1b floats 0.8672 / 0.6283 and 0.8555 / 0.3905;
- growth constants c\* = 2.807411, 5.728742, 4.273538 and 4.272705;
- §6b values 0.00279, 0.00231, 0.02188 ≤ 0.84025, 0.00248 ≤ 0.00277, 0.21478 ≤ 0.21515 and 0.00026 ≤ 0.00064;
- counts 427, 4,246, 1,542 and 124, and the Weyl bound ≤ 2.3·10⁻¹⁶.

There are no mismatches.

### Residual non-blocking nits (no re-review needed)

- Line 386: "S_i(b^{m₂}) ≡ i + 1 (mod 2)" should read b^{m_k}. This is a typo; the argument is unaffected.
- The approximation constants |y − R_K| ≤ 16b^(−m_{K+1}) (Theorem 4) and ≤ 4b^(−m_{K+1}) (Theorems 5 and 6(b)) differ. Both are valid under the respective hypotheses, since R_∞ is bounded by ∏(1 − 2^(−j))^(−1) in general and is close to 1 once m₁ ≥ 5.

### Final verdict

All five Major findings (M1–M5) and all eighteen Minor findings (m1–m18) are cleanly closed. The script reproduces exactly: exit 0, 12,193 exact checks + 510 float measurements = 12,703 total.

| Sub-track | Verdict |
|---|---|
| **D1** | **ACCEPT** |
| **D2** | **ACCEPT** |
| **D4** | **ACCEPT** |

Evidence status: Theorems 1–6 are `Paper proof`, and Theorem 4 additionally rests on `External input` (Bang–Zsigmondy). The script sections are `Finite certificate`. The floating-point outputs are finite measurements, not evidence. The §6 Lean blueprint is unformalized and carries no kernel-verification claim.

*Cross-model review is not independent human peer review.*
