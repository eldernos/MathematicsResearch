# Verification map: Digit-Mass Transfer and Nonnormality of Dense Arithmetic Lambert Series (v1.1, candidate draft)

This file maps every numbered statement of the candidate draft to its evidence labels: **Kernel-verified**, **Lean-supported paper proof**, **Paper proof**, **Finite certificate**, **Conditional**, **External input**, or **Open**. Prefix digit statistics quoted in the draft (Table 7 and the base-10 example after it) are finite measurements. They are not evidence for any asymptotic statement.

**Cross-model review is not independent human peer review.** The written proofs, and the repository notes they come from, have been checked only by AI models from different providers. No human specialist has read them, and the assembled manuscript has not been reviewed as a whole.

**Status.** This is an unreleased candidate draft (Candidate Paper XIV, v1.1). It has no entry in `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml`, or `docs/registry/papers.toml`, and no `metadata.toml` or `submission/` directory. **No `paper.pdf` is committed.** The draft was typeset on 28 November 2026 in two independent clean builds on `hail` that produced byte-identical PDFs (record in [Reproducible compilation](#reproducible-compilation-track-h3)); the PDFs lived only in `/tmp/paper14-build` on `hail`, which was deleted afterwards. Release still needs owner authorization and independent human review.

**What changed in v1.1 (Phase 26 Track H2).** v1.0 covered the Phase 24 results `GF-36` and `GF-40`. v1.1 adds the Phase 25 kernel-verified non-adjacent geometric transfer (`GF-44`, `NormalityChecker/NafGeometricTransfer.lean`) and its consequences for `E_+(2^k)`, `k ≥ 3`:

- New **Theorem B**, **Theorem 6.1**, **Theorem 6.2**, **Corollary 6.3**, **Lemma 7.6**, **Remark 7.12**, **Table 1** (summary of both families) and **Table 4** (merged `E_+(2^k)` bounds). The former Theorems B–E are now **C–F**, Section 6 is now Section 7, Sections 7–10 are now 8–11, and Tables 1–6 are now 2–7 (old Table 3 is merged into the new Table 4).
- **Lemma 2.3** is now **Kernel-verified** in full: the identification of the recursion `signedWeight` with the minimal signed weight is proved in Lean (`signedWeight_natAbs_le_card_of_signed_sum`, `exists_naf`).
- **Lemma 7.7** (old 6.6) no longer uses Reitwiesner (1960) as **External input**: the non-adjacent form and its tail bound are kernel-verified (`exists_naf`, `three_mul_abs_sum_add_one_le`). `Reitwiesner1960` is kept only as a historical citation.
- Theorem A(iv) now also states the kernel-verified `D^-(E(2^k);2) ≥ 1/2 − 29/(20k)` (from the eventual-`ε` form `erdosBorwein_two_pow_radixDiscrepancy_eventually_ge`), which gives `1/60` at `k = 3`; the uniform eventual `1/120` bound is unchanged.
- No `D^+ < 1` statement is claimed anywhere. `D^+(E_+(8);2) < 1` and the binary simple normality of `E_+(8)` are stated as **Open** (Theorem F(iv), Remark 7.13, Question 9.5).

## Pinned Lean sources

- **T** = `8ca43095887858bf9697b6a8332c6a6dd0b0cda3` (Phase 22): `Phase22Cores.erdosBorweinPlusCoeff_eq` (L1052).
- **U** = `cb395159c6e343c60c1413719cdfc8429e15af2c` (Phase 23): the definitions `Basic.shift` (L15), `Basic.frequency` (L18), `Basic.NormalIn` (L23), `BinaryDiscrepancy.radixDiscrepancy` (L11), `HigherOrderTower.OrderNormal` (L69) and `SimpleNormalityKernel.wordFreq` (L73), and the theorem `BinaryDiscrepancy.discrepancy_lt_one_iff_transitions` (L229), cited in Question 9.5. These six definitions sit at the same lines at **W** and **X**.
- **W** = `04969b91f0c897ce55d21cb62c6b2c5aa3affe97` (Phase 24, committed and CI-verified): `NormalityChecker/DigitMassTransfer.lean` (2,506 lines, 62 exported theorems, 0 `sorry`, SHA-256 `103cdb48ca87fbcb3e9d01c933bce5a772c5d65d65778a58d67be8b3164d6880`). Imported by `NormalityChecker.lean` and audited in `Audit.lean` (standard axioms `propext`, `Classical.choice`, `Quot.sound` only). Built and independently replayed via `leanchecker` on `hail`, passed remote GitHub Actions `Lean verification` run `46117198083` (`success`) and `Manuscript verification` run `46117198078` (`success`), and independently re-verified in Phase 25 Stage 0.2 Audit A (`notes/phase25/reviews/phase24-analytic-audit-gf36-gf37-gf40.md`, 0 Critical, 0 Major). Cited through `\leanW{name}{line}`.
- **X** = `c06c97dd7d942bdf46d727aa58309869af88d5e7` (Phase 25, committed and CI-verified): `NormalityChecker/NafGeometricTransfer.lean` (2,034 lines, 106 top-level `theorem` declarations, 0 `sorry`, SHA-256 `cb0267a72f9334aeba1a8684549c40fbe1f1ba35b8f601a0a68957b4e59440d4`). Imports `DigitMassTransfer` and `Phase22Cores`; 39 of its declarations are listed in `Audit.lean` (standard axioms only). Per `notes/phase25/verification.md` §1 it was built on `hail` (`lake build`, 8,792 jobs), audited (`lake env lean Audit.lean`, 2,307 declarations), and independently replayed (`lake env leanchecker NormalityChecker.NafGeometricTransfer`, `replayFromImports`). `gh run list --commit c06c97dd7d942bdf46d727aa58309869af88d5e7` (checked 28 November 2026) shows `Lean verification` run `46129564650` (`success`) and `Manuscript verification` run `46129564641` (`success`). The commit is on `origin/research/phase-25-carry-correlations`, so the pinned links resolve. Cited through the new macro `\leanX{name}{line}`, which expands to `\leanat{c06c97dd7d942bdf46d727aa58309869af88d5e7}{NafGeometricTransfer}{line}{name}`.

## Lean pin verification (mechanical)

A Python checker (session scratchpad, not committed) parsed every `\leanW`, `\leanX`, `\leanU` and `\leanT` citation in the body of `paper.tex`, read each file at its pinned commit with `git show <commit>:NormalityChecker/<File>.lean`, and required the cited line to begin a `theorem`/`lemma`/`def`/`noncomputable def` declaration of exactly the cited name.

| Macro | Commit | File | Citations | Distinct (name, line) | Mismatches |
| --- | --- | --- | --- | --- | --- |
| `\leanW` | **W** `04969b9…` | `DigitMassTransfer.lean` | 76 | 38 | 0 |
| `\leanX` | **X** `c06c97d…` | `NafGeometricTransfer.lean` | 86 | 41 | 0 |
| `\leanU` | **U** `cb39515…` | `Basic`, `BinaryDiscrepancy`, `HigherOrderTower`, `SimpleNormalityKernel` | 15 | 13 (7 distinct targets) | 0 |
| `\leanT` | **T** `8ca4309…` | `Phase22Cores.lean` | 2 | 1 | 0 |
| **Total** | | | **179** | | **0** |

Negative control: shifting `\leanX{exists_naf}{367}` to L366 and `\leanW{digitSum_add_le}{196}` to L197 in a scratch copy made the checker report exactly those 2 mismatches and exit 1. Raw macro counts equal the parsed counts, so no citation escaped the parser, and no `\leanat` is used directly in the body.

The compiled PDF was checked independently (see below): all 87 distinct commit-pinned Lean URLs in its link annotations (38 at **W**, 41 at **X**, 7 at **U**, 1 at **T**) land on declaration lines, and its 4 commit links resolve to commits of the repository.

## Exact scope of the Lean declarations used

### Phase 24 module (W)

| Declaration | Source, line | What it states | What it does **not** state |
| --- | --- | --- | --- |
| `digitSum_add_add_carries` | W L191 | Kummer, two summands: s_b(a+c) + (b−1)·`carries b 0 a c` = s_b(a) + s_b(c) for b ≥ 2. | The many-summand carry identity (Lemma 2.1, a paper proof) or the exact transfer identity (3). |
| `digitSum_add_le`, `digitSum_mul_pow`, `digitSum_mul_le` | W L196, L202, L216 | s_b(a+c) ≤ s_b(a)+s_b(c), s_b(a·b^t) = s_b(a), s_b(ac) ≤ s_b(a)s_b(c). | — |
| `nonzeroDigits_add_le`, `nonzeroDigits_mul_le`, `nonzeroDigits_pred_sq` | W L258, L338, L387 | w_b(a+c) ≤ w_b(a)+w_b(c); w_b(ac) ≤ min(s_b(a)w_b(c), 2w_b(a)w_b(c)); w_b((b−1)²) = 2 and w_b(b−1) = 1 for b ≥ 3. | — |
| `digitSum_two_succ` | W L405 | s₂(m+1) + v₂(m+1) = s₂(m) + 1. | — |
| `signedWeight_two_mul`, `signedWeight_mul_two_pow`, `signedWeight_le_digitSum`, `signedWeight_add_le`, `signedWeight_sub_le`, `signedWeight_mul_le` | W L444, L459, L465, L538, L543, L549 | Shift invariance, w_± ≤ s₂, subadditivity, the difference bound and submultiplicativity for `signedWeight`, defined by the recursion of Lemma 2.3. | The identification of the recursion with the minimal signed weight: that is the Phase 25 pair `signedWeight_natAbs_le_card_of_signed_sum` + `exists_naf` (X). |
| `transitions_rec`, `transitions_add_two_pow`, `transitions_add_le` | W L610, L682, L738 | T(A) = [A₀ ≠ A₁] + T(⌊A/2⌋); \|T(A ± 2^m) − T(A)\| ≤ 2; T(A+c) ≤ T(A) + 2·`signedWeight` \|c\|. | — |
| `floor_pow_mul_eq_head_add_floor_tail` | W L756 | Exact prefix identity ⌊b^N x⌋ = A_N + ⌊τ_N⌋ for x = Σ a(n) b^{−kn}, a: ℕ → ℤ absolutely summable. | The tail bound \|τ_N\| ≤ b^{k−1} Θ_M in Theorem 2.5 (paper proof). |
| `digitSum_prefix_le` | W L798 | s_b(A_N + t) ≤ Σ_{n ≤ N/k} s_b(a(n)) + s_b(t) for a ≥ 0. | The exact identity (3) with the carry total κ(N). |
| `transitions_prefix_le` | W L819 | T(A_N + t) ≤ 2 Σ_{n ≤ N/k} w_±(a(n)) + 2 w_±(t) for base 2. | The asymptotic transition bound of Theorem 7.1 (paper proof). |
| `interval_le_radixDiscrepancy`, `radixDiscrepancy_ge_nonzero_freq`, `binaryDiscrepancy_ge_half_sub_transition`, `radixDiscrepancy_ge_zero_run`, `radixDiscrepancy_descent` | W L827, L863, L883, L959, L2417 | The finite criteria D_N ≥ (b−1)/b − F_N([1/b,1)), D_N(x;2) ≥ 1/2 − F_N([1/4,3/4)), the base-2 zero-run bound, and radix descent D_{kN}(x;b) ≤ (b^k−1)/(k(b−1))·D_N(x;b^k). | Proposition 2.10(1), the general-m window bound in (4), zero runs for b ≥ 3, and the statement that simple normality descends (all paper proofs). |
| `tendsto_average_of_summable_conv_mobius` | W L1021 | If Σ \|(G∗μ)(n)\|/n < ∞, then X⁻¹ Σ_{n ≤ X} G(n) → Σ (G∗μ)(n)/n. No multiplicativity is assumed. | The Euler-product form or the majorant bound Σ_{n ≤ Y} G ≤ HY (paper proof). |
| `local_factor_digitSum_two` | W L1142 | (1 − p⁻¹) Σ_e s₂(e+1) p^{−e} = Σ_j p/(p^{2^j}+1) for every integer p ≥ 2. | — |
| `tauDigitKernel_prime_pow`, `tauDigitMajorant_mul_moebius`, `digitSum_card_divisors_le`, `summable_abs_tauDigitKernel_div` | W L1283, L1308, L1313, L1517 | h(p^e) = s₂(e+1) − s₂(e), G∗μ = h, s₂(τ(n)) ≤ G(n), Σ \|h(n)\|/n < ∞. | The enclosure H ∈ [1.903838, 1.903848] (finite certificate). |
| `tsum_tauDigitKernel_div_le` | W L1663 | C = Σ h(n)/n ≤ 29/20, via local bounds L(p) ≤ (1−p⁻²)⁻¹ − p⁻³ − 2p⁻⁷, an exact product over p < 37 (≤ 1.3958) and Σ_{n ≥ 37} n⁻² ≤ 1/36. | The enclosure C ∈ [1.4035953, 1.4035958], or anything about C_true (finite certificates). |
| `erdosBorweinPow_eq_divisor_series` | W L1770 | E(2^k) = Σ τ(n) 2^{−kn} for k ≥ 1. | — |
| `erdosBorwein_two_pow_digitFreq_limsup_le` | W L2143 | limsup_N f₁(N; E(2^k)) ≤ 29/(20k) for every k ≥ 1. | The sharp bound C_true/k (Theorem 4.2). |
| `erdosBorwein_two_pow_radixDiscrepancy_eventually_ge`, `erdosBorwein_two_pow_lowerDiscrepancy_pos` | W L2161, L2194 | For every k ≥ 1 and ε > 0, D_N(E(2^k);2) ≥ 1/2 − 29/(20k) − ε eventually (hence D^-(E(2^k);2) ≥ 1/2 − 29/(20k), which is 1/60 at k = 3); for k ≥ 3, D_N(E(2^k);2) ≥ 1/120 eventually. | The values of Table 2, D⁻ → 1, bounds in base 2^k, or D⁺ < 1. |
| `erdosBorwein_two_pow_not_simplyNormal_pow`, `erdosBorwein_two_pow_not_simplyNormal` | W L2277, L2334 | For k ≥ 3 and j ≥ 1, ¬`OrderNormal (2^j) 1 (E(2^k))`. | Anything about E_odd, τ_r, unitary or base-b families. |
| private `ebTail_bounds`, `digitSum_two_le_log`, `erdosBorwein_count_le`, `popcount_word_identity` | W L1951, L1935, L2028, L2237 | 0 ≤ τ_N ≤ N + 2 for a = τ; s₂(T) ≤ ⌊log₂ T⌋ + 1; the finite count N f₁(N) ≤ Σ s₂(τ(n)) + ⌊log₂(N+2)⌋ + 1; the base-2^j popcount identity. Kernel-checked inside the module, not exported, not linked from the paper; used for Theorem A(ii) and Theorem 4.1. | — |

### Phase 25 module (X)

| Declaration | Source, line | What it states | What it does **not** state |
| --- | --- | --- | --- |
| `signedWeight_parity_mono` | X L85 | w_±(2q) ≤ w_±(2q+1) and w_±(2q+2) ≤ w_±(2q+1). | — |
| `signedWeight_natAbs_add_le` | X L94 | w_±(\|u+v\|) ≤ w_±(\|u\|) + w_±(\|v\|) for u, v ∈ ℤ. | — |
| `signedWeight_natAbs_le_card_of_signed_sum` | X L137 | If A = Σ_{i∈S} ε_i 2^{m_i} with ε_i = ±1 (repeated exponents allowed), then `signedWeight` \|A\| ≤ \|S\|. | — |
| `nafWeight_eq_signedWeight`, `exists_naf`, `nafWeight_le_card_support` | X L360, L367, L376 | The canonical NAF digits lie in {−1,0,1}, are non-adjacent, vanish at i ≥ \|A\|, reconstruct A, and have exactly `signedWeight` \|A\| nonzero entries; every representation A = Σ_{i<K} c_i 2^i with \|c_i\| ≤ 1 has at least that many nonzero digits. | Uniqueness of the NAF (not needed). |
| `three_mul_abs_sum_add_one_le`, `abs_nafLow_div_lt` | X L386, L442 | 3\|Σ_{i<K} d_i 2^i\| + 1 ≤ 2^{K+1} for non-adjacent digits; ℓ vanishing NAF digits just below position r force \|low_r(A)/2^r\| < (2/3)·2^{−ℓ}. | — |
| `naf_dyadic_count_le`, `naf_orbit_count_le` | X L541, L579 | For s, r ≥ 1 and sN ≤ M, at most r·w_±(\|A\|) of the points {2^{sm}A/2^M}, m < N, lie in [c, 1−c], c = 2/(3·2^{sr}); binary form with ℓ. | — |
| `frequency_naf_interval_le` | X L594 | F_N([c + 2^{−R}, 1 − c); x, 2^s) ≤ r·w_±(⌊2^{sN+R}x⌋)/N for every real x. | — |
| `NafDensityLE` (definition) | X L662 | ∀ ρ' > ρ, eventually w_±(⌊2^M x⌋) ≤ ρ'M ("prefix NAF density at most ρ"). | — |
| `eventually_frequency_le_of_nafDensity`, `radixDiscrepancy_eventually_ge_of_nafDensity`, `binary_radixDiscrepancy_eventually_ge_of_nafDensity`, `binary_radixDiscrepancy_eventually_ge_two_thirds`, `base4_radixDiscrepancy_eventually_ge_two_thirds` | X L680, L716, L745, L753, L762 | Under `NafDensityLE x ρ`: eventually F_N([c+2^{−R},1−c); x, 2^s) ≤ rsρ + ε and D_N(x;2^s) ≥ 1 − (4/3)2^{−sr} − rsρ − ε; the binary form with ℓ; D_N(x;2), D_N(x;4) ≥ 2/3 − 2ρ − ε. | Any statement about D⁺. |
| `not_orderNormal_two_four_of_nafDensity`, `not_orderNormal_four_two_of_nafDensity` | X L847, L863 | ρ < 5/16 implies ¬`OrderNormal 2 4 x` and ¬`OrderNormal 4 2 x`. | Anything about order 3 or simple normality. |
| `signedWeight_le_log` | X L902 | w_±(T) ≤ ⌊log₂ T⌋ + 1. | — |
| `nafDensityLE_of_series` | X L1026 | If \|a(n)\| ≤ C₀ n^B and, for every C' > C, Σ_{n ≤ X} w_±(a(n)) ≤ C'X eventually, then Σ_{n≥1} a(n) 2^{−kn} satisfies `NafDensityLE` with ρ = C/k. | The mean of any particular sequence: that is a hypothesis. |
| `aPlus_eq_erdosBorweinPlusCoeff`, `erdosBorweinPlusPow_eq_signed_series`, `abs_aPlus_le` | X L1129, L1148, L1421 | a_+(n) = (1 − v₂(n))τ_odd(n) agrees with `Phase22Cores.erdosBorweinPlusCoeff`; E_+(2^k) = Σ a_+(n) 2^{−kn} (k ≥ 1); \|a_+(n)\| ≤ n. | — |
| `signedWeight_aPlus_le`, `ePlusMajorant_mul_moebius`, `summable_abs_ePlusKernel_div`, `tendsto_average_ePlusMajorant`, `ePlusMean_le` | X L1439, L1343, L1591, L1661, L1836 | w_±(a_+(n)) ≤ G₀(n); G₀ ∗ μ = h₀; Σ\|h₀(n)\|/n < ∞; X⁻¹Σ G₀ → W_+^maj; **W_+^maj ≤ 93694/100000** via an exact product over the 72 primes below 361 and an elementary ±1 (mod 6) prime tail. | The enclosure W_+^maj ∈ [0.936414, 0.936415] or anything about the sharp mean W_+ (finite certificates, Theorem 7.2). |
| `erdosBorweinPlusPow_nafDensityLE` | X L1916 | E_+(2^k) satisfies `NafDensityLE` with ρ = W_+^maj/k (k ≥ 1). | — |
| `erdosBorweinPlus_two_pow_radixDiscrepancy_eventually_ge`, `erdosBorweinPlus_two_pow_radixDiscrepancy_base4_eventually_ge` | X L1945, L1962 | For k ≥ 1 and ε > 0, eventually D_N(E_+(2^k); b) ≥ 2/3 − 2(937/1000)/k − ε, b ∈ {2, 4}. | — |
| `erdosBorweinPlus_two_pow_lowerDiscrepancy_ge`, `erdosBorweinPlus_two_pow_lowerDiscrepancy_pos`, `erdosBorweinPlus_two_pow_lowerDiscrepancy_base4_ge` | X L1978, L1988, L1993 | For k ≥ 3, **D_N(E_+(2^k);2) ≥ 21/500** and **D_N(E_+(2^k);4) ≥ 21/500** for all large N. | 17431/300000, 11477/187500, bounds in bases 2^j with j ≥ 3, or D⁺ < 1 (Corollary 6.3 is a Lean-supported paper proof; D⁺ < 1 is open). |
| `erdosBorweinPlus_two_pow_not_orderNormal_four`, `…_not_orderNormal_base4_two`, `…_not_normalIn_two`, `…_not_normalIn_four`, `erdosBorweinPlus_eight_not_orderNormal_four`, `erdosBorweinPlus_eight_not_orderNormal_base4_two` | X L2003, L2010, L2016, L2021, L2026, L2030 | For k ≥ 3 (and explicitly k = 3): ¬`OrderNormal 2 4`, ¬`OrderNormal 4 2`, ¬`NormalIn 2`, ¬`NormalIn 4`. | Simple normality (`OrderNormal 2 1`) or 3-normality of E_+(8); normality in bases 2^j, j ≥ 3 (Corollary 6.3(1), Lean-supported paper proof). |

### Other pinned sources (T, U)

| Declaration | Source, line | Role |
| --- | --- | --- |
| `Phase22Cores.erdosBorweinPlusCoeff_eq` | T L1052 | a₊(n) = (1 − v₂(n))·τ_odd(n) for n ≥ 1. |
| `Basic.shift`, `Basic.frequency`, `Basic.NormalIn` | U L15, L18, L23 | Orbit, interval frequency, normality predicate. |
| `BinaryDiscrepancy.radixDiscrepancy` | U L11 | D_N(x; b). |
| `HigherOrderTower.OrderNormal`, `SimpleNormalityKernel.wordFreq` | U L69, L73 | L-normality in base b and word frequencies. |
| `BinaryDiscrepancy.discrepancy_lt_one_iff_transitions` | U L229 | D⁺(x;2) < 1 iff the lower transition density is positive; cited only to motivate Question 9.5. |

## Statement map

Statement numbers are taken from `paper.aux` of the compiled PDF (one counter per section shared by all theorem-like environments; a separate counter for Theorems A–F). "Track A" is `notes/phase24/dense-digit-mass-and-lambert.md`; "Track E" is `notes/phase24/classical-constants-and-joint-numerators.md`; "P25-I" is `notes/phase25/naf-geometric-transfer.md`; "P25-D" is `notes/phase25/digit-complexity-and-lp-witnesses.md`.

| No. | Statement (short) | Evidence | Lean | External inputs | Source note and finite checks |
| --- | --- | --- | --- | --- | --- |
| A | (i) Kummer, s_b/w_b inequalities, failure of w_b submultiplicativity, binary successor law; (ii) prefix identity, prefix mass bound, carry tail τ_N ≤ N + 2 for E(2^k); (iii) mean-value limit, majorant, local identity, C ≤ 29/20; (iv) limsup f₁ ≤ 29/(20k), D⁻(E(2^k);2) ≥ 1/2 − 29/(20k), eventual 1/120 and not simply normal in any base 2^j for k ≥ 3; (v) discrepancy criteria and radix descent | **Kernel-verified** (all parts) | W L191–L2417 | — | Track A §13; `DigitMassTransfer.lean` |
| B | (i) NAF existence, minimality, tail bound, orbit covering; (ii) real and series transfer, 5/16 order exclusion; (iii) E_+(2^k): W_+^maj ≤ 93694/100000, eventual 2/3 − 2(937/1000)/k − ε in bases 2, 4, and for k ≥ 3 D_N ≥ 21/500 in bases 2 and 4, not 4-normal in base 2, not 2-normal in base 4, not normal in bases 2, 4; (iv) not normal in any base 2^j with D⁻ ≥ j/(2^j−1)·21/500, D⁻(E_+(8);b) ≥ 17431/300000 and ≥ 11477/187500 (b ∈ {2,4}), D⁻(E_+(8);8) ≥ 11477/437500 | (i)–(iii) **Kernel-verified**; (iv) **Lean-supported paper proof** + **Finite certificate** | X L85–L2030; W L2417 for (iv) | — | P25-I §§A–B (Lean-blueprint Theorems A.2, B.1, B.2); P25-D Thm 2.5; `scripts/phase25_naf_transfer.py` |
| Table 1 | Summary of both families with evidence labels | Summary of the rows' own labels | — | — | — |
| C | (i)–(ii) C_true ∈ [1.339103, 1.339116], C ∈ [1.4035953, 1.4035958], limsup f₁ ≤ C_true/k, explicit D⁻ in bases 2, 2^j, 2^k, D⁻ → 1; (iii) E_odd, τ₄, τ₈, τ₁₆, E\* in base 2; (iv) base-b unitary and τ_b families | **Paper proof** + **Finite certificate** | — | — | Track A §§3–6; `scripts/phase24_digit_mass.py` |
| D | (i) Barrier for b not a power of 2; (ii) τ_r multiplicative-dependence dichotomy; (iii) failure of w_b(ac) ≤ w_b(a)w_b(c) for b ≥ 3 | (i)–(ii) **Paper proof** + **External input**; (iii) **Kernel-verified** | `nonzeroDigits_pred_sq` W L387, `nonzeroDigits_mul_le` W L338 | Senge–Straus (1973); Stewart (1980); Turán–Kubilius | Track A §5 (Theorem 5.1), §6 (Theorem 6.2), Lemma 1.2(c) |
| E | (i) Signed transition-count transfer; (ii) E₊(2^k) for k ≥ 4 (W₊ ∈ [0.908174, 0.908184], D⁻(E₊(16);2) ≥ 0.0459) and L_± for k ≥ 4; (iii) four-state transducer, A_L formula, floor inequalities, E₊(2^k) not normal for k ≥ 3 with D⁻ ≥ 2.34 × 10⁻⁷ (an independent route, quantitatively superseded by Theorem B) | (i) **Lean-supported paper proof**; (ii)–(iii) **Paper proof** + **Finite certificate** | `transitions_prefix_le` W L819, `transitions_add_le` W L738, `signedWeight_*`, `binaryDiscrepancy_ge_half_sub_transition` W L883, `radixDiscrepancy_descent` W L2417; NAF in Lemma 7.7 via X L367, L386 | Maxfield (1953), as an alternative to radix descent only | Track A §§7–8; Track E §§3.1(c), 3.2; `scripts/phase24_digit_mass.py`, `scripts/phase24_classical.py` |
| F | (i) E(4) carry-density criterion; (ii) direct base-4 obstruction; (iii) E\*(4) criterion and conditional collision result; (iv) open status of E(2), E(4), E₊(2), E₊(4), simple normality of E₊(8), D⁺(E₊(8);2) < 1, E(9)₃, E(25)₅, E(100)₁₀ | (i) **Paper proof**; (ii) **Paper proof** + **External input**; (iii) **Paper proof**, collision part **Conditional**; (iv) **Open** | — | Wirsing (1967) for (ii) | Track A §§5 (remark), 9, 10, 12; Track E §3.4 |
| 2.1 | Kummer's identity for many summands | **Paper proof**; two-summand case **Kernel-verified** | `digitSum_add_add_carries` W L191 | Kummer (1852), context only | Track A Lemma 1.1 |
| 2.2 | Digit inequalities (a)–(d) | **Kernel-verified** | W L196, L202, L216, L258, L338, L387, L405 | — | Track A Lemma 1.2(a)–(c); exhaustive checks in `phase24_digit_mass.py` |
| 2.3 | Signed weight: properties, recursion, and its identification with the minimal signed weight | **Kernel-verified** (upgraded from v1.0, where the identification was a paper proof + finite certificate) | W L444–L549; X L94, L137, L367, L902 | — | Track A Lemma 1.2(d); P25-I Lemma A.1; NAF agreement for \|c\| ≤ 4096 kept as an independent cross-check |
| 2.4 | Transition increments | **Kernel-verified** | W L610, L682, L738 | — | Track A Lemma 1.3; **Finite certificate**: all A ∈ [−2¹², 2¹²), m ≤ 13, and \|A\|, \|c\| ≤ 600 |
| 2.5 | Exact prefix decomposition | **Kernel-verified** (identity); **Paper proof** (tail bound) | W L756 | — | Track A Theorem 2.1 |
| 2.6 | Unsigned transfer, carry tail | **Paper proof**; prefix inequality **Kernel-verified** | W L798 | — | Track A Theorem 2.2 |
| 2.7 | Carry tail exceeds +1: E(8), N = 35 | **Finite certificate** | — | — | Track A §2; `phase24_digit_mass.py` |
| 2.8 | Asymptotic transfer | **Paper proof** | — | — | Track A Corollary 2.3 |
| 2.9 | The growth hypothesis cannot be dropped | **Paper proof** | — | — | Track A §2 example |
| 2.10 | Frequency criteria and radix descent | **Kernel-verified** for the finite inequalities in (2), (3) at b = 2, (4) at m = 2, and the descent inequality in (5); **Paper proof** otherwise | W L863, L959, L883, L2417 | — | Track A Proposition 2.4 |
| 3.1 | Dirichlet-convolution mean value | **Kernel-verified** (limit); **Paper proof** (Euler product, majorant bound) | W L1021 | — | Track A Lemma 3.1 |
| 3.2 | Independent-exponent model | **Paper proof** | — | — | Track A Lemma 3.2 |
| 3.3 | Binary divisor kernel, H, local identity | (1), (3) **Kernel-verified**; (2) **Finite certificate** | W L1142, L1283, L1308, L1313, L1517 | — | Track A Corollary 3.3 |
| 3.4 | C ≤ 29/20 and C ∈ [1.4035953, 1.4035958] | **Kernel-verified** (≤ 29/20); **Finite certificate** (enclosure) | W L1663 | — | Track A §4, §13 |
| 4.1 | Kernel-verified classification of E(2^k) | **Kernel-verified** | W L1770, L2143, L2161, L2194, L2277, L2334; definitions at U | — | Track A §13 (L15, L15′) |
| 4.2, Table 2 | Sharp constants C_true, certified E(2^k) bounds | **Paper proof** + **Finite certificate** | — | — | Track A Theorem 4.1; dynamic program over p ≤ 20000 |
| 4.3 | E(8) in base 8, E(16) in base 4; independent enclosure C_true ∈ [1.337765, 1.346123], D⁻ ≥ 0.05129 | **Paper proof** + **Finite certificate** | — | — | Track A §4; Track E Theorem 3.1(a)–(b); `phase24_classical.py` |
| 5.1 | Barrier for b not a power of 2; threshold ⌈3/j⌉ | **Paper proof** + **External input** | — | Senge–Straus (1973); Stewart (1980); Turán–Kubilius | Track A Theorem 5.1 |
| 5.2 | Multiplicative-dependence dichotomy; τ₄, τ₈, τ₁₆ thresholds | **Paper proof** + **External input** + **Finite certificate** | — | Senge–Straus (1973) | Track A Theorem 6.2 |
| 5.3 | E_odd(2^k) (k ≥ 3) and E\*(2^k) (k ≥ 3) | **Paper proof** + **Finite certificate** | — | — | Track A Theorems 6.1, 6.3 |
| 5.4, Table 3 | Base-b unitary and τ_b families | **Paper proof** + **Finite certificate** | — | — | Track A Theorem 5.2 |
| 6.1 | Non-adjacent geometric transfer (a)–(f) | **Kernel-verified** | X L85, L137, L360, L367, L376, L386, L442, L541, L579, L594, L662, L680, L716, L745, L753, L762, L847, L863, L1026 | — (NAF proved here, not imported) | P25-I Lemma A.1, Theorem A.2(1)–(3), Theorem B.1(2) mechanism |
| 6.2 | E_+(2^k): series, majorant ≤ 93694/100000, eventual bounds, 21/500 in bases 2 and 4, order and normality exclusions for k ≥ 3 | **Kernel-verified** | X L1129, L1148, L1343, L1421, L1439, L1591, L1661, L1836, L1916, L1945, L1962, L1978, L1988, L1993, L2003, L2010, L2016, L2021, L2026, L2030; T L1052 | — | P25-I Theorems B.1, B.2(1) |
| 6.3 | (1) bases 2^j via radix descent; (2) general ℓ bound from W_+ ≤ W; (3) 17431/300000 (from W_+ ≤ 0.912845) and 11477/187500 (from W_+ ≤ 0.908184) in bases 2 and 4; 11477/437500 in base 8 | **Lean-supported paper proof** + **Finite certificate** (only the two W_+ enclosures) | X L716, L745, L1026, L1988; W L2417 | — | P25-I §2–3 (I.B1); P25-D Thm 2.5; exact rationals asserted in `scripts/phase25_naf_transfer.py` (re-run below) |
| Table 4 | E_+(2^k) bounds: kernel ℓ = 2 row; best-ℓ row from W_+ ≤ 0.908184; transition-count rows | Row 1 **Kernel-verified**; row 2 **Lean-supported paper proof** + **Finite certificate**; rows 4–5 **Paper proof** + **Finite certificate** | X L1945, L1978 | — | Values recomputed in exact rational arithmetic (Python `fractions`) for this draft and rounded toward the weaker side: kernel row 0.04200, 0.19816, 0.29186, 0.35433, 0.43241, 0.54954; best-ℓ row 11477/187500, 159431/750000, 284431/937500, 284431/750000, 1478293/3000000, 1034431/1500000 |
| 7.1 | Signed transfer | **Lean-supported paper proof** | W L819, L738, L883, L2417 | — | Track A Theorem 7.1 |
| 7.2 | E₊(2^k), k ≥ 4, optimality of the transition method at k = 4 | **Paper proof** + **Finite certificate** | — | — | Track A Theorem 7.2 |
| 7.3 | Cubic characters L_±(2^k), k ≥ 4, base 2 | **Paper proof** + **Finite certificate** | — | — (the GF-31 comparison mentions Selberg–Delange, which is not used) | Track A Proposition 8.1 |
| 7.4 | Definition of σ₁ and σ_free | — | — | — | Track E §3.2 |
| 7.5 | Carry paths | **Paper proof** | — | — | Phase 23 note, Theorem 5.2(a),(d) (re-proved here) |
| 7.6 | σ₁(x;N) ≤ w_±(⌊2^N x⌋) ≤ σ₁(x;N) + C_x; equivalence of the two density inputs (new in v1.1) | **Paper proof** | uses X L367 via Theorem 6.1(a) | — | Written for this draft; short and elementary |
| 7.7 | Signed support of E₊(2^k) | **Paper proof**; NAF and its tail bound **Kernel-verified** (no External input in v1.1) | X L367, L386 | — | Track E Theorem 3.1(c); **Finite certificate**: buffer inequalities for 1 ≤ N₀ ≤ 100, 1 ≤ k ≤ 6 |
| 7.8, Table 5 | Four-state transducer and A_L | **Paper proof** + **Finite certificate** | — | — | Track E Theorem 3.2(a); A_L for L ≤ 20 and brute force for L ≤ 10 in `phase24_classical.py` |
| 7.9 | Signed-support floor | **Paper proof** | — | Maxfield (1953), alternative only | Track E Theorem 3.2(b) |
| 7.10 | The mixed inequality is false | **Paper proof** (sketch; not used elsewhere) | — | — | Track E §3.2(b) note |
| 7.11 | E₊(2^k) not normal for k ≥ 3, D⁻ ≥ 2.34 × 10⁻⁷ (transducer route) | **Paper proof** + **Finite certificate** | — | — | Track E Theorem 3.2(c); W₊ ≤ 0.912845 in `phase24_classical.py`. The paragraph after it compares with 21/500: ratio 179,224.9… with the exact `GF-40` input (179,237.5… with the rounded 0.304282), recomputed in exact rationals for this draft, so "more than 1.79 × 10⁵" holds |
| 7.12 | How far the signed-weight input can go: LP ceiling 0.059108 for limsup σ₁/N ≤ 0.912845/3; order-3 barrier 1/4 | Cites the register entry `GF-44` (**Paper proof** + **Finite certificate**, outside this paper; not used in any proof here) | — | — | P25-D Theorem 2.6 and Theorem 1.7. Arithmetic recomputed for this draft: 4887/16076 = 0.303993…, 0.912845/3 = 0.304281…, 0.908184/3 = 0.302728 < 4887/16076 (so the ceiling does not apply to the sharper input); relative gap (0.059108 − 17431/300000)/(17431/300000) = 1.729…% < 1.8% |
| 7.13 | E₊(8): simple normality and D⁺(E₊(8);2) < 1 undecided; `GF-42` B1.4 covers only k ≥ k₀ (k₀ > 3.05 × 10¹⁰) | **Open** | — | — | P25-D §2.6; `notes/phase25/generalized-lambert-and-eplus.md` Theorem B1.4 and the `GF-42` registry scope |
| 7.14 | Exact shifted identities for a₊ | **Paper proof** + **Finite certificate** | uses T L1052 | — | Track E Theorem 3.3(1)–(2); 128 pairs, 1 ≤ h ≤ 32, X ≤ 2¹⁶ |
| 7.15 | 2-adic factor via the affine divisor asymptotic | **Paper proof** + **External input** | — | Topacogullari (2017), Theorem 1.2 and §3.5 | Track E Theorem 3.3(3) |
| 8.1 | E(4) threshold | **Paper proof** | — | — | Track A Theorem 9.1 |
| 8.2 | Direct base-4 transfer fails for E(4) | **Paper proof** + **External input** | — | Wirsing (1967) | Track A §5 remark |
| 8.3 | E\*(4) threshold | **Paper proof** | — | — | Track A Theorem 10.1 |
| 8.4 | Collisions imply simple nonnormality of E\*(4) | **Conditional** | — | — | Track A Proposition 10.2 |
| Table 6 | Status map of the dyadic family | Summary of the rows' labels | — | — | — |
| Table 7 | Prefix statistics at N = 2¹⁷ | **Finite measurement only** | — | — | Track A §11 |
| 9.1–9.5 | Questions (9.5 now asks about D⁺(E₊(8);2) < 1 and cites `GF-42` B1.3/B1.4 as register results not reproduced here) | **Open** | U L229 (cited in 9.5) | — | Track A §12; Track E §6; P25-D §2.6 |

Registry correspondence: the Phase 24 results are registered as [GF-36](../../docs/results.md#gf-36) and [GF-40](../../docs/results.md#gf-40); the Phase 25 kernel-verified NAF transfer and its paper extensions as [GF-44](../../docs/results.md#gf-44) (status `lean+paper`). Related entries cited in the text but not used in any proof: [GF-31](../../docs/results.md#gf-31) (L_±(2^k) in radix 2^k), [GF-42](../../docs/results.md#gf-42) (D⁺ < 1 for E(2^k), k ≥ 3, and for E_+(2^k) only for k ≥ k₀), and [GF-28](../../docs/results.md#gf-28) (the E₊ coefficient identity). [GF-32](../../docs/results.md#gf-32) is the three-state transducer that Theorem 7.8 minimizes.

**Benchmark scope.** The fixed 50-constant roster `BC-01`…`BC-50` is unchanged by this draft; the entries `BC-37`–`BC-39` (E(2), E_odd(2), E₊(2)) remain open. No status change is derived from finite computations, conditional theorems, heuristics or cross-model reviews.

## Reproducible compilation (Track H3)

Run on 28 November 2026 on the Linux build server `hail` (`Linux Hail 7.0.0-43-generic x86_64`), never WSL, with the isolated user-local TinyTeX installation; nothing outside `~/.TinyTeX` and `/tmp/paper14-build` was touched, and no `sudo` was used.

**Toolchain.**

| Component | Version |
| --- | --- |
| TeX distribution | TinyTeX, TeX Live 2026, at `~/.TinyTeX` (`tlmgr` revision 80687, 2026-10-18) |
| Engine | pdfTeX 3.141592653-2.6-1.40.29 (TeX Live 2026), kpathsea 6.4.2 |
| LaTeX format | LaTeX2e <2026-11-01> |
| latexmk | 4.90 (John Collins, 25 November 2026) |
| BibTeX | 0.99e (TeX Live 2026), style `plainurl.bst` (package `urlbst`) |
| PDF inspection | `pdfinfo` / `pdftotext` / `pdftoppm` (poppler 26.01.0, `/usr/bin`) |

Packages added to `~/.TinyTeX` for this build with `tlmgr install` (user-local): `xurl`, `urlbst`, `grfext`. `lmodern.sty` was already provided by the `lm` package.

**Sources built** (SHA-256 of the LF-terminated files uploaded to `hail`; `paper.tex` inputs `../common/preamble.tex` and `../common/byline.tex`, so the build tree was `/tmp/paper14-build/<run>/papers/{common,14-dense-digit-mass-lambert}`):

```
c9acd8925353f7298eeced9b66816234b62be5142e3cad69ec42fd1b7e8cb591  papers/14-dense-digit-mass-lambert/paper.tex
933be9b9266e0104ac020934a10e3a3bdab96fb41498adca30a848191f82cdca  papers/14-dense-digit-mass-lambert/references.bib
c8fccceacbbc34a1038e840ae9246971cce051f5b36d9cf3ef6a9657339e21c9  papers/common/preamble.tex
a9544d1aaa6f5f5a8cc11656f882b2988004f2071b3147bd2344149721f2fb15  papers/common/byline.tex
```

**Exact reproduction command** (run in a fresh copy of `papers/14-dense-digit-mass-lambert/` next to `papers/common/`):

```sh
export PATH="$HOME/.TinyTeX/bin/x86_64-linux:$PATH"
cd papers/14-dense-digit-mass-lambert
SOURCE_DATE_EPOCH=1795547923 FORCE_SOURCE_DATE=1 TZ=UTC \
  latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
sha256sum paper.pdf
```

`latexmk` ran `pdflatex` three times and `bibtex` twice. Two independent clean builds were made in separate fresh directories (`/tmp/paper14-build/clean1`, `/tmp/paper14-build/clean2`).

**Results (identical for both clean builds).**

| Check | Result |
| --- | --- |
| `latexmk` exit status | 0 |
| TeX errors (`!` lines, file-line errors) | 0 |
| Undefined references / undefined citations | 0 / 0 |
| Multiply defined labels; "Rerun to get" warnings | 0; 0 |
| LaTeX warnings; package warnings (including `hyperref` PDF-string warnings) | 0; 0 |
| Overfull `\hbox` (any size) / overfull `\vbox` | **0** / 0 |
| Underfull `\hbox` | 12 (cosmetic loose lines in ragged identifier lists; nothing clips) |
| BibTeX warnings / errors | 0 / 0 (`warning$ -- 0`) |
| Pages | **30** (letter, 612 × 792 pt), PDF 1.7, 639,991 bytes |
| `pdfinfo` | Title "Digit-Mass Transfer and Nonnormality of Dense Arithmetic Lambert Series", Author "Christopher Anderson", Creator "LaTeX with hyperref", Producer "pdfTeX-1.40.29", CreationDate = ModDate = 2026-11-24 19:18:43 UTC (= `SOURCE_DATE_EPOCH` 1795547923; `pdfinfo` prints it in `hail` local time as 13:18:43 CST), not encrypted, no JavaScript, no forms |
| **SHA-256 of `paper.pdf`** | **`819fedf564cbed01ef4b29effdef6f79bed7eefbe6ce43305c4df9a5edf1d5f2`** (both builds; `cmp` reports the PDFs byte-identical) |

The structural statement in v1.0 ("statement numbers will be confirmed when `pdflatex` is run") is now settled: the numbering in the statement map above is read from the compiled `paper.aux`.

**`pdftotext` inspection** (`pdftotext -layout`): 30 form feeds; 0 occurrences of `??`; 0 literal TeX control words; the headings Theorem A … Theorem F appear in order, followed by Lemmas 2.1–2.4, Theorems 2.5–2.6, …, Theorems 6.1–6.2, Corollary 6.3, Theorems 7.1–7.2, Proposition 7.3, Definition 7.4, Lemmas 7.5–7.7, Theorems 7.8–7.9, Remark 7.10, Theorem 7.11, Remarks 7.12–7.13, Proposition 7.14, Remark 7.15, Theorems 8.1, 8.3, Propositions 8.2, 8.4, Questions 9.1–9.5, and Tables 1–7. The rendered statements of Theorem B and Theorem 6.2 show `21/500`, `93694/100000`, `17431/300000`, `11477/187500` and `11477/437500` as typeset fractions.

**Hyperlink targets** (`pdfinfo -url`): 214 link annotations, 103 distinct URLs (links broken across lines produce two annotations). These are 87 commit-pinned Lean line links (38 `DigitMassTransfer` at **W**, 41 `NafGeometricTransfer` at **X**, 3 `Basic` + 2 `BinaryDiscrepancy` + 1 `HigherOrderTower` + 1 `SimpleNormalityKernel` at **U**, 1 `Phase22Cores` at **T**), each landing on a declaration line at its commit; 4 commit-page links (`\commitref`), each a commit of this repository; and 12 external links (7 DOIs, the CC BY 4.0 licence, the issue tracker, the repository root, the Paper IX directory and the Captain Sude repository).

**Visual inspection.** Pages 1, 4, 5, 15, 17, 18 and 23 were rendered with `pdftoppm -r 70` and inspected: the abstract, Theorem B, Table 1 (ragged columns), Theorem 6.1, Theorem 6.2, Corollary 6.3, Table 4, Remark 7.12 and the split displays of Proposition 7.14 are within the margins with no clipped or lost symbols. An earlier development build had 7 overfull boxes (up to 118 pt) from long Lean identifiers, file paths and two wide displays; they were removed by making `\_` a break point inside `\ttt`, setting repository paths with the breakable `\tpath`/`\nolinkurl` (via `xurl`), typesetting commit hashes with `\commitref`, setting the Lean pointer paragraphs ragged right, and splitting the displays.

**Clean-up.** `/tmp/paper14-build` on `hail` was deleted after the run. No PDF was written into the repository.

## Certificate runs

- **Phase 25 (re-run for this draft):** `scripts/phase25_naf_transfer.py` at **X** (SHA-256 `81689d2da1a1fff59fa223bb669fd1b5aa3464fea6c7b6a386dbe4f04cd30829`; unchanged in the working tree) was run with `python3 -B` (Python 3.14.4) on `hail` in `/tmp/paper14-build/scripts` on 28 November 2026: exit 0, `ALL CHECKS PASSED (418091 assertions: 417978 [exact], 104 [encl], 9 [finite]) in 19.23 s`. Among its assertions are the enclosures W₊ ∈ [0.907252, 0.912845] and W₊ ∈ [0.908174, 0.908184] and the exact identities 2/3 − (2/3)·0.912845 = 17431/300000 and 2/3 − (2/3)·0.908184 = 11477/187500 (script lines 563–611).
- **Phase 24 (earlier runs, local Windows host, Python 3.13.13, 27–28 November 2026):** `python -B scripts/phase24_digit_mass.py` exited 0 with 3,095,904+ exact checks (3,095,908 in the Phase 25 re-run recorded in `notes/phase25/verification.md`). `python -B scripts/phase24_classical.py` exited 0 with `ALL CHECKS PASSED (108334 assertions) in 2.5 s`, and printed `mu_NAF(a_+)/3 <= 0.304282 < A_16 = 324039/1048576`, giving `D^-(E_+(8); 2) >= 0.000000234`.
- **Recomputed for this draft (exact rationals, Python `fractions`):** the Table 4 rows, the identities in Corollary 6.3 and Theorem 6.2(4) (2/3 − 2·93694/300000 = 1051/25000; minus 1/50000 gives 0.04202 ≥ 21/500; 93694/300000 = 0.312313… < 5/16), 11477/437500 = (3/7)·11477/187500, the ratio to the transducer bound, and the ceiling arithmetic of Remark 7.12.

## Sources and cross-provider model reviews (not human peer review)

| Material | Source note | Cross-provider model review (not human peer review) |
| --- | --- | --- |
| §§2–5, §7.1, §8 | `notes/phase24/dense-digit-mass-and-lambert.md` (Track A) | `notes/phase24/reviews/track-a-review.md`: Gemini 4 auditing Claude Opus 5.5. Initial verdict ACCEPT AFTER REVISION, 0 Critical, 4 Major, 12 Minor; post-repair verdict **ACCEPT**, all 16 findings closed. |
| §§7.2–7.3 (transducer, floor, transducer route), Remark 4.3 | `notes/phase24/classical-constants-and-joint-numerators.md` §3 (Track E, sub-track E3) | `notes/phase24/reviews/track-e-review.md`: review by Codex `gpt-6.2-astra`, repairs by Gemini 4, post-repair verification by Claude Opus 5.5. Across E1–E3: 3 Critical, 4 Major, 5 Minor, all closed; post-repair verdict **ACCEPT**. |
| Lean modules | `NormalityChecker/DigitMassTransfer.lean` (W), `NormalityChecker/NafGeometricTransfer.lean` (X) | The Lean kernel, not a model, checked both modules (builds and `leanchecker` replays on `hail`; GitHub Actions runs `46117198083` and `46129564650`). |
| §6 (Theorem B, Theorems 6.1–6.2, Corollary 6.3) | `notes/phase25/naf-geometric-transfer.md` (Phase 25 Track I; Lean blueprint) and `notes/phase25/digit-complexity-and-lp-witnesses.md` (Track D; first proof of the base-2 bounds 17431/300000 and 0.061210) | `notes/phase25/reviews/track-i-review.md`: Claude Opus 5.5 reviewing; initial verdict REVISE (0 Critical, 2 Major, attribution/novelty against Track D), post-repair verdict **ACCEPT**. `notes/phase25/reviews/track-d-review.md`: Gemini 4 Neon auditing Claude Opus 5.5; initial verdict REVISE (0 Critical, 3 Major), post-repair re-audit closed M1–M3. |
| Remark 7.12, Remark 7.13, Question 9.5 (cited register results only) | `GF-44` (Track D Theorems 1.7, 2.6) and `GF-42` (`notes/phase25/generalized-lambert-and-eplus.md`, Theorems B1.3–B1.4) | Track D review as above; `notes/phase25/reviews/track-b-review.md` (Claude Opus 5.5 reviewing; initial REVISE with 0 Critical, 4 Major; accepted after repair per `notes/phase25/README.md`). These results are not used in any proof of this draft. |
| Comparison with GF-31 (after Proposition 7.3) | `notes/phase23/dense-characters-and-nonfundamental-forms.md` | `notes/phase24/reviews/phase23-analytic-audit-gf31.md`: 0 Critical, 0 Major, 1 Minor. |

## Repository state and pending release items

- **Pinned sources.** Phase 24 (**W**): `DigitMassTransfer.lean`, `scripts/phase24_digit_mass.py`, `scripts/phase24_classical.py`, `notes/phase24/`, registry `GF-36`, `GF-40`. Phase 25 (**X**): `NafGeometricTransfer.lean`, `Audit.lean`, `scripts/phase25_naf_transfer.py`, `scripts/phase25_digit_complexity.py`, `notes/phase25/`, registry `GF-42`, `GF-44`.
- **Manuscript structural check (PASS, 28 November 2026):** 20 bibliography entries (0 duplicates, 0 uncited, 0 undefined in the compiled build); 4 valid 40-hex commit macros (`\phaseXXIIcommit`, `\phaseXXIIIcommit`, `\phaseXXIVcommit`, `\phaseXXVcommit`); 179 commit-pinned Lean citations verified mechanically (0 mismatches); the notice "Cross-model review is not independent human peer review." appears in `paper.tex` (Section 11), in this file and in `LEDGER.md`.
- **Pending before release:**
  1. Independent human specialist peer review.
  2. Owner release authorization and release steps (`metadata.toml`, `papers/manifest.toml`, `papers/SHA256SUMS`, `docs/registry/papers.toml`, and a committed `paper.pdf` built with the command above).
