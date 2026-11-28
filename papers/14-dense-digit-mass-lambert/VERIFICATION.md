# Verification map: Digit-Mass Transfer and Nonnormality of Dense Arithmetic Lambert Series (v1.0, candidate draft)

This file maps every numbered statement of the candidate draft to its evidence labels: **Kernel-verified**, **Lean-supported paper proof**, **Paper proof**, **Finite certificate**, **Conditional**, **External input**, or **Open**. Prefix digit statistics quoted in the draft (Table 6 and the base-10 example after it) are finite measurements. They are not evidence for any asymptotic statement.

**Cross-model review is not independent human peer review.** The written proofs, and the repository notes they come from, have been checked only by AI models from different providers. No human specialist has read them, and the assembled manuscript has not been reviewed as a whole.

**Status.** This is an unreleased candidate draft (Candidate Paper XIV). It has no entry in `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml`, or `docs/registry/papers.toml`, and no `paper.pdf`, `metadata.toml`, or `submission/` directory. **`pdflatex`/`bibtex` compilation is pending before release.** On 28 November 2026, `command -v pdflatex bibtex latexmk` found none of these tools on `hail` or on the local Windows host, so the draft has not been typeset. Only the structural check below has been run.

## Pinned Lean sources

- **T** = `8ca43095887858bf9697b6a8332c6a6dd0b0cda3` (Phase 22): `Phase22Cores.erdosBorweinPlusCoeff_eq` (L1052).
- **U** = `cb395159c6e343c60c1413719cdfc8429e15af2c` (Phase 23): the definitions `Basic.shift` (L15), `Basic.frequency` (L18), `BinaryDiscrepancy.radixDiscrepancy` (L11), `HigherOrderTower.OrderNormal` (L69) and `SimpleNormalityKernel.wordFreq` (L73), and the theorem `BinaryDiscrepancy.discrepancy_lt_one_iff_transitions` (L229), cited in Question 8.5.
- **W** = `04969b91f0c897ce55d21cb62c6b2c5aa3affe97` (Phase 24, committed and CI-verified): `NormalityChecker/DigitMassTransfer.lean` (2,506 lines, 62 exported theorems, 0 `sorry`, SHA-256 `103cdb48ca87fbcb3e9d01c933bce5a772c5d65d65778a58d67be8b3164d6880`). Imported by `NormalityChecker.lean` and audited in `Audit.lean` (standard axioms `propext`, `Classical.choice`, `Quot.sound` only). Built and independently replayed via `leanchecker` on `hail`, passed remote GitHub Actions `Lean verification` run `46117198083` (`success`) and `Manuscript verification` run `46117198078` (`success`), and independently re-verified in Phase 25 Stage 0.2 Audit A (`notes/phase25/reviews/phase24-analytic-audit-gf36-gf37-gf40.md`, 0 Critical, 0 Major). Every `\leanW{name}{line}` citation in `paper.tex` now expands to a commit-pinned `\leanat{04969b91f0c897ce55d21cb62c6b2c5aa3affe97}{DigitMassTransfer}{line}{name}` hyperlink.

*(Phase 25 follow-up note: Phase 25 Track B, Track D, Addendum Track I, and the new Lean 4 module `NormalityChecker/NafGeometricTransfer.lean` further strengthen the signed-digit discrepancy bound for `E_+(8)` and prove `D^+ < 1` for `E(2^k)` (`k ≥ 3`). Candidate Paper XIV v1.0 stays cleanly scoped to the pinned Phase 24 results `GF-36` and `GF-40`, with Phase 25 extensions tracked separately.)*

## Exact scope of the Lean declarations used

| Declaration | Source, line | What it states | What it does **not** state |
| --- | --- | --- | --- |
| `digitSum_add_add_carries` | W L191 | Kummer, two summands: s_b(a+c) + (b−1)·`carries b 0 a c` = s_b(a) + s_b(c) for b ≥ 2. | The many-summand carry identity (Lemma 2.1, a paper proof) or the exact transfer identity (2.6). |
| `digitSum_add_le`, `digitSum_mul_pow`, `digitSum_mul_le` | W L196, L202, L216 | s_b(a+c) ≤ s_b(a)+s_b(c), s_b(a·b^t) = s_b(a), s_b(ac) ≤ s_b(a)s_b(c). | — |
| `nonzeroDigits_add_le`, `nonzeroDigits_mul_le`, `nonzeroDigits_pred_sq` | W L258, L338, L387 | w_b(a+c) ≤ w_b(a)+w_b(c); w_b(ac) ≤ min(s_b(a)w_b(c), 2w_b(a)w_b(c)); w_b((b−1)²) = 2 and w_b(b−1) = 1 for b ≥ 3. | — |
| `digitSum_two_succ` | W L405 | s₂(m+1) + v₂(m+1) = s₂(m) + 1. | — |
| `signedWeight_two_mul`, `signedWeight_mul_two_pow`, `signedWeight_le_digitSum`, `signedWeight_add_le`, `signedWeight_sub_le`, `signedWeight_mul_le` | W L444, L459, L465, L538, L543, L549 | Shift invariance, w_± ≤ s₂, subadditivity, the difference bound and submultiplicativity for `signedWeight`, which is **defined by the recursion** of Lemma 2.3. | That the recursion equals the minimal number of signed powers of 2. That identification is a paper proof, checked against the NAF algorithm for \|c\| ≤ 4096 in `scripts/phase24_digit_mass.py`. |
| `transitions_rec`, `transitions_add_two_pow`, `transitions_add_le` | W L610, L682, L738 | The recursive characterization T(A) = [A₀ ≠ A₁] + T(⌊A/2⌋); \|T(A ± 2^m) − T(A)\| ≤ 2; T(A+c) ≤ T(A) + 2·`signedWeight` \|c\|. | — |
| `floor_pow_mul_eq_head_add_floor_tail` | W L756 | Exact prefix identity ⌊b^N x⌋ = A_N + ⌊τ_N⌋ for x = Σ a(n) b^{−kn}, a: ℕ → ℤ absolutely summable. | The tail bound \|τ_N\| ≤ b^{k−1} Θ_M in Theorem 2.5 (paper proof). |
| `digitSum_prefix_le` | W L798 | s_b(A_N + t) ≤ Σ_{n ≤ N/k} s_b(a(n)) + s_b(t) for a ≥ 0. | The exact identity (2.6) with the carry total κ(N). |
| `transitions_prefix_le` | W L819 | T(A_N + t) ≤ 2 Σ_{n ≤ N/k} w_±(a(n)) + 2 w_±(t) for base 2. | The asymptotic transition bound of Theorem 6.1 (paper proof). |
| `interval_le_radixDiscrepancy`, `radixDiscrepancy_ge_nonzero_freq`, `binaryDiscrepancy_ge_half_sub_transition`, `radixDiscrepancy_ge_zero_run`, `radixDiscrepancy_descent` | W L827, L863, L883, L959, L2417 | The finite criteria D_N ≥ (b−1)/b − F_N([1/b,1)), D_N(x;2) ≥ 1/2 − F_N([1/4,3/4)), the base-2 zero-run bound, and radix descent D_{kN}(x;b) ≤ (b^k−1)/(k(b−1))·D_N(x;b^k). | Proposition 2.10(1), the general-m window bound in (4), zero runs for b ≥ 3, and the statement that simple normality descends (all paper proofs). |
| `tendsto_average_of_summable_conv_mobius` | W L1021 | If Σ \|(G∗μ)(n)\|/n < ∞, then X⁻¹ Σ_{n ≤ X} G(n) → Σ (G∗μ)(n)/n. No multiplicativity is assumed. | The Euler-product form or the majorant bound Σ_{n ≤ Y} G ≤ HY (paper proof). |
| `local_factor_digitSum_two` | W L1142 | (1 − p⁻¹) Σ_e s₂(e+1) p^{−e} = Σ_j p/(p^{2^j}+1) for every integer p ≥ 2. | — |
| `tauDigitKernel_prime_pow`, `tauDigitMajorant_mul_moebius`, `digitSum_card_divisors_le`, `summable_abs_tauDigitKernel_div` | W L1283, L1308, L1313, L1517 | h(p^e) = s₂(e+1) − s₂(e), G∗μ = h, s₂(τ(n)) ≤ G(n), Σ \|h(n)\|/n < ∞. | The enclosure H ∈ [1.903838, 1.903848] (finite certificate). |
| `tsum_tauDigitKernel_div_le` | W L1663 | C = Σ h(n)/n ≤ 29/20, via local bounds L(p) ≤ (1−p⁻²)⁻¹ − p⁻³ − 2p⁻⁷, an exact product over p < 37 (≤ 1.3958) and Σ_{n ≥ 37} n⁻² ≤ 1/36. | The enclosure C ∈ [1.4035953, 1.4035958], or anything about C_true (finite certificates). |
| `erdosBorweinPow_eq_divisor_series` | W L1770 | E(2^k) = Σ τ(n) 2^{−kn} for k ≥ 1. | — |
| `erdosBorwein_two_pow_digitFreq_limsup_le` | W L2143 | limsup_N f₁(N; E(2^k)) ≤ 29/(20k) for every k ≥ 1. | The sharp bound C_true/k (Theorem 4.2). |
| `erdosBorwein_two_pow_radixDiscrepancy_eventually_ge`, `erdosBorwein_two_pow_lowerDiscrepancy_pos` | W L2161, L2194 | D_N(E(2^k);2) ≥ 1/2 − 29/(20k) − ε eventually; for k ≥ 3, D_N(E(2^k);2) ≥ 1/120 eventually. | The values of Table 1, D⁻ → 1, or bounds in base 2^k. |
| `erdosBorwein_two_pow_not_simplyNormal_pow`, `erdosBorwein_two_pow_not_simplyNormal` | W L2277, L2334 | For k ≥ 3 and j ≥ 1, ¬`OrderNormal (2^j) 1 (E(2^k))`. | Anything about E_odd, τ_r, unitary or base-b families. |
| private `ebTail_bounds`, `digitSum_two_le_log`, `erdosBorwein_count_le`, `popcount_word_identity` | W L1951, L1935, L2028, L2237 | 0 ≤ τ_N ≤ N + 2 for a = τ; s₂(T) ≤ ⌊log₂ T⌋ + 1; the finite count N f₁(N) ≤ Σ s₂(τ(n)) + ⌊log₂(N+2)⌋ + 1; the base-2^j popcount identity. They are kernel-checked inside the module, are not exported, and are used for Theorem A(ii) and Theorem 4.1. | — |
| `Phase22Cores.erdosBorweinPlusCoeff_eq` | T L1052 | a₊(n) = (1 − v₂(n))·τ_odd(n) for n ≥ 1. | — |
| `BinaryDiscrepancy.discrepancy_lt_one_iff_transitions` | U L229 | D⁺(x;2) < 1 if and only if the lower transition density is positive. | Cited only to motivate Question 8.5. |

## Statement map

Statement numbers come from a structural count of `paper.tex`, with one counter per section shared by all theorem-like environments and a separate counter for Theorems A–E. They will be confirmed when `pdflatex` is run. "Track A" is `notes/phase24/dense-digit-mass-and-lambert.md`; "Track E" is `notes/phase24/classical-constants-and-joint-numerators.md`.

| No. | Statement (short) | Evidence | Lean | External inputs | Source note and finite checks |
| --- | --- | --- | --- | --- | --- |
| A | (i) Kummer, s_b/w_b inequalities, failure of w_b submultiplicativity, binary successor law; (ii) prefix identity, prefix mass bound, carry tail τ_N ≤ N + 2 for E(2^k); (iii) mean-value limit, majorant, local identity, C ≤ 29/20; (iv) limsup f₁ ≤ 29/(20k), D⁻(E(2^k);2) ≥ 1/120 and not simply normal in any base 2^j for k ≥ 3; (v) discrepancy criteria and radix descent | **Kernel-verified** (all parts) | W L191–L2417 (table above) | — | Track A §13 (L1–L15); `DigitMassTransfer.lean` |
| B | (i)–(ii) C_true ∈ [1.339103, 1.339116], C ∈ [1.4035953, 1.4035958], limsup f₁ ≤ C_true/k, explicit D⁻ in bases 2, 2^j, 2^k, D⁻ → 1; (iii) E_odd, τ₄, τ₈, τ₁₆, E\* in base 2; (iv) base-b unitary and τ_b families | **Paper proof** + **Finite certificate** | — | — | Track A §§3–6; `scripts/phase24_digit_mass.py` |
| C | (i) Barrier for b not a power of 2; (ii) τ_r multiplicative-dependence dichotomy; (iii) failure of w_b(ac) ≤ w_b(a)w_b(c) for b ≥ 3 | (i)–(ii) **Paper proof** + **External input**; (iii) **Kernel-verified** | `nonzeroDigits_pred_sq` W L387, `nonzeroDigits_mul_le` W L338 | Senge–Straus (1973); Stewart (1980); Turán–Kubilius | Track A §5 (Theorem 5.1), §6 (Theorem 6.2), Lemma 1.2(c) |
| D | (i) Signed transition-count transfer; (ii) E₊(2^k) for k ≥ 4 (W₊ ∈ [0.908174, 0.908184], D⁻(E₊(16);2) ≥ 0.0459, optimality at k = 4) and L_± for k ≥ 4; (iii) four-state transducer, A_L formula, floor inequalities, E₊(2^k) not normal for k ≥ 3 with D⁻ ≥ 2.34 × 10⁻⁷ | (i) **Lean-supported paper proof**; (ii)–(iii) **Paper proof** + **Finite certificate** (Lemma 6.6 uses **External input**) | `transitions_prefix_le` W L819, `transitions_add_le` W L738, `signedWeight_*`, `binaryDiscrepancy_ge_half_sub_transition` W L883, `radixDiscrepancy_descent` W L2417 | Reitwiesner (1960) NAF minimality; Maxfield (1953) as an alternative to radix descent | Track A §§7–8; Track E §§3.1(c), 3.2; `scripts/phase24_digit_mass.py`, `scripts/phase24_classical.py` |
| E | (i) E(4) carry-density criterion; (ii) direct base-4 obstruction; (iii) E\*(4) criterion and conditional collision result; (iv) open status of E(2), E(4), E₊(2), E₊(4), E(9)₃, E(25)₅, E(100)₁₀ | (i) **Paper proof**; (ii) **Paper proof** + **External input**; (iii) **Paper proof**, collision part **Conditional**; (iv) **Open** | — | Wirsing (1967) for (ii) | Track A §§5 (remark), 9, 10, 12; Track E §3.4 |
| 2.1 | Kummer's identity for many summands | **Paper proof**; two-summand case **Kernel-verified** | `digitSum_add_add_carries` W L191 | Kummer (1852), context only | Track A Lemma 1.1 |
| 2.2 | Digit inequalities (a)–(d) | **Kernel-verified** | W L196, L202, L216, L258, L338, L387, L405 | — | Track A Lemma 1.2(a)–(c); exhaustive checks in `phase24_digit_mass.py` |
| 2.3 | Signed weight: properties and recursion | **Kernel-verified** for the recursion; **Paper proof** + **Finite certificate** for the identification with w_± | W L444–L549 | — | Track A Lemma 1.2(d); NAF agreement for \|c\| ≤ 4096 |
| 2.4 | Transition increments | **Kernel-verified** | W L610, L682, L738 | — | Track A Lemma 1.3; **Finite certificate**: all A ∈ [−2¹², 2¹²), m ≤ 13, and \|A\|, \|c\| ≤ 600 |
| 2.5 | Exact prefix decomposition | **Kernel-verified** (identity); **Paper proof** (tail bound) | W L756 | — | Track A Theorem 2.1 |
| 2.6 | Unsigned transfer, carry tail | **Paper proof**; prefix inequality **Kernel-verified** | W L798 | — | Track A Theorem 2.2 (post-repair M1 wording) |
| 2.7 | Carry tail exceeds +1: E(8), N = 35 | **Finite certificate** | — | — | Track A §2; `phase24_digit_mass.py` |
| 2.8 | Asymptotic transfer | **Paper proof** | — | — | Track A Corollary 2.3 (post-repair m3) |
| 2.9 | The growth hypothesis cannot be dropped | **Paper proof** | — | — | Track A §2 example (post-repair M2) |
| 2.10 | Frequency criteria and radix descent | **Kernel-verified** for the finite inequalities in (2), (3) at b = 2, (4) at m = 2, and the descent inequality in (5); **Paper proof** otherwise | W L863, L959, L883, L2417 | — | Track A Proposition 2.4 |
| 3.1 | Dirichlet-convolution mean value | **Kernel-verified** (limit); **Paper proof** (Euler product, majorant bound) | W L1021 | — | Track A Lemma 3.1 |
| 3.2 | Independent-exponent model | **Paper proof** | — | — | Track A Lemma 3.2 (post-repair m4) |
| 3.3 | Binary divisor kernel, H, local identity | (1), (3) **Kernel-verified**; (2) **Finite certificate** | W L1142, L1283, L1308, L1313, L1517 | — | Track A Corollary 3.3; power series through y^2047, squarefull support for n ≤ 2·10⁵ |
| 3.4 | C ≤ 29/20 and C ∈ [1.4035953, 1.4035958] | **Kernel-verified** (≤ 29/20); **Finite certificate** (enclosure) | W L1663 | — | Track A §4 certificate method, §13 |
| 4.1 | Kernel-verified classification of E(2^k) | **Kernel-verified** | W L1770, L2143, L2161, L2194, L2277, L2334; definitions at U | — | Track A §13 (L15, L15′) |
| 4.2 | Sharp constants C_true, Table 1 | **Paper proof** + **Finite certificate** | — | — | Track A Theorem 4.1; dynamic program over p ≤ 20000 |
| 4.3 | E(8) in base 8, E(16) in base 4; independent enclosure C_true ∈ [1.337765, 1.346123], D⁻ ≥ 0.05129 | **Paper proof** + **Finite certificate** | — | — | Track A §4; Track E Theorem 3.1(a)–(b); `phase24_classical.py` |
| 5.1 | Barrier for b not a power of 2; threshold ⌈3/j⌉ | **Paper proof** + **External input** | — | Senge–Straus (1973); Stewart (1980); Turán–Kubilius | Track A Theorem 5.1 |
| 5.2 | Multiplicative-dependence dichotomy; τ₄, τ₈, τ₁₆ thresholds | **Paper proof** + **External input** + **Finite certificate** | — | Senge–Straus (1973) | Track A Theorem 6.2 |
| 5.3 | E_odd(2^k) (k ≥ 3) and E\*(2^k) (k ≥ 3) | **Paper proof** + **Finite certificate** | — | — | Track A Theorems 6.1, 6.3 |
| 5.4 | Base-b unitary and τ_b families, Table 2 | **Paper proof** + **Finite certificate** | — | — | Track A Theorem 5.2 |
| 6.1 | Signed transfer | **Lean-supported paper proof** | W L819, L738, L883, L2417 | — | Track A Theorem 7.1 |
| 6.2 | E₊(2^k), k ≥ 4, Table 3, optimality | **Paper proof** + **Finite certificate** | — | — | Track A Theorem 7.2 |
| 6.3 | Cubic characters L_±(2^k), k ≥ 4, base 2 | **Paper proof** + **Finite certificate** | — | — (the GF-31 comparison mentions Selberg–Delange, which is not used) | Track A Proposition 8.1 |
| 6.4 | Definition of σ₁ and σ_free | — | — | — | Track E §3.2; `notes/phase23/binary-partition-and-carry-complexity.md` §5.2 |
| 6.5 | Carry paths | **Paper proof** | — | — | binary case of the Phase 23 note, Theorem 5.2(a),(d) (re-proved here) |
| 6.6 | Signed support of E₊(2^k) | **Paper proof** + **External input** | — | Reitwiesner (1960): NAF has minimal weight | Track E Theorem 3.1(c); **Finite certificate**: buffer inequalities for 1 ≤ N₀ ≤ 100, 1 ≤ k ≤ 6 |
| 6.7 | Four-state transducer and A_L | **Paper proof** + **Finite certificate** | — | — | Track E Theorem 3.2(a); exhaustive 7-vector closure and lumping table; A_L for L ≤ 20 and brute force for L ≤ 10 in `phase24_classical.py` |
| 6.8 | Signed-support floor (two separate limit inequalities) | **Paper proof** | — | Maxfield (1953), alternative only | Track E Theorem 3.2(b) (post-repair Critical finding) |
| 6.9 | The mixed inequality is false | **Paper proof** (sketch in a remark; not used elsewhere) | — | — | Track E §3.2(b) note; Track E review, Critical finding on Theorem 3.2(b) |
| 6.10 | E₊(2^k) not normal for k ≥ 3, D⁻ ≥ 2.34 × 10⁻⁷ | **Paper proof** + **Finite certificate** | — | — | Track E Theorem 3.2(c); W₊ ≤ 0.912845 and the D⁻ bound asserted against exact fractions in `phase24_classical.py` |
| 6.11 | Simple normality of E₊(8) undecided | **Open** | — | — | Track E §3.2, §6 Q5 |
| 6.12 | Exact shifted identities for a₊ | **Paper proof** + **Finite certificate** | uses T L1052 | — | Track E Theorem 3.3(1)–(2); 128 pairs, 1 ≤ h ≤ 32, X ≤ 2¹⁶ |
| 6.13 | 2-adic factor via the affine divisor asymptotic | **Paper proof** + **External input** | — | Topacogullari (2017), Theorem 1.2 and §3.5 | Track E Theorem 3.3(3) |
| 7.1 | E(4) threshold | **Paper proof** | — | — | Track A Theorem 9.1 (post-repair m6) |
| 7.2 | Direct base-4 transfer fails for E(4) | **Paper proof** + **External input** | — | Wirsing (1967) | Track A §5 remark (post-repair m5) |
| 7.3 | E\*(4) threshold | **Paper proof** | — | — | Track A Theorem 10.1 |
| 7.4 | Collisions imply simple nonnormality of E\*(4) | **Conditional** | — | — | Track A Proposition 10.2 |
| 8.1–8.5 | Questions | **Open** | U L229 (cited in 8.5) | — | Track A §12; Track E §6 |
| Tables 1–5 | Certified constants and status map | **Finite certificate** (Tables 1–3), **Paper proof** + **Finite certificate** (Table 4), summary (Table 5) | — | — | Track A §§4, 5, 7; Track E §3.2, §3.4 |
| Table 6 | Prefix statistics at N = 2¹⁷ | **Finite measurement only** | — | — | Track A §11 |

Registry correspondence: the Phase 24 results in this draft are registered in `docs/registry/GF.toml` as [GF-36](../../docs/results.md#gf-36) (dense digit-mass transfer, `DigitMassTransfer.lean`, `E(2^k)`, Senge–Straus barrier, signed transition-count transfer) and [GF-40](../../docs/results.md#gf-40) (4-state minimal-support transducer for `E_+(8)` and unconditional elimination of `(H2)` via Topacogullari 2017 Theorem 1.2). Both entries passed independent third-provider deep analytic audit in Phase 25 Stage 0.2 Audit A (`notes/phase25/reviews/phase24-analytic-audit-gf36-gf37-gf40.md`, 0 Critical, 0 Major). Related entries: [GF-28](../../docs/results.md#gf-28) (the E₊ coefficient identity, Phase 22), [GF-31](../../docs/results.md#gf-31) (simple nonnormality of L_±(2^k) in radix 2^k; Proposition 6.3 complements it in base 2), and [GF-32](../../docs/results.md#gf-32) (the three-state signed-support transducer that Theorem 6.7 minimizes).

## Sources and cross-provider model reviews (not human peer review)

| Material | Source note | Cross-provider model review (not human peer review) |
| --- | --- | --- |
| §§2–5, §6.1, §7 | `notes/phase24/dense-digit-mass-and-lambert.md` (Track A) | `notes/phase24/reviews/track-a-review.md`: Gemini 4 auditing Claude Opus 5.5. Initial verdict ACCEPT AFTER REVISION, with 0 Critical, 4 Major (M1 carry-tail characterization, M2 the (b,k) = (2,2) case of the growth example, M3 a rounded inequality in the closed-form C < 3/2 route, M4 the quartic remark) and 12 Minor findings. Post-repair verdict **ACCEPT**, with all 16 findings closed. The reviewer re-ran `phase24_digit_mass.py` (3,095,904 checks). The quartic-character remark of the note is not used in this draft. |
| §§6.2–6.3, Remark 4.3 | `notes/phase24/classical-constants-and-joint-numerators.md` §3 (Track E, sub-track E3) | `notes/phase24/reviews/track-e-review.md`: review by Codex `gpt-6.2-astra`, repairs by Gemini 4, post-repair verification by Claude Opus 5.5. The E3 findings were two Critical (the mixed liminf in Theorem 3.2(b); the function class in Theorem 3.1(a)), two Major (two-sided popcount in Theorem 3.1(b); the external theorem for Theorem 3.3) and several Minor. Across E1–E3 there were 3 Critical, 4 Major and 5 Minor findings, all closed. Post-repair verdict **ACCEPT** (108,334 assertions). The verifier did not re-read Topacogullari's text, which matters only for Remark 6.13. Sub-tracks E1–E2 are not used in this draft. |
| Comparison with GF-31 (after Proposition 6.3) | `notes/phase23/dense-characters-and-nonfundamental-forms.md` | `notes/phase24/reviews/phase23-analytic-audit-gf31.md`: 0 Critical, 0 Major, 1 Minor. |
| Lean module | `NormalityChecker/DigitMassTransfer.lean` | The Lean kernel, not a model, checked the module (Phase 24 build on `hail`). The statements were drafted from the Track A §13 blueprint with review items m8–m9 applied. |

## Repository state and pending release items

- **Committed and pinned Phase 24 sources (`04969b91f0c897ce55d21cb62c6b2c5aa3affe97`):** `NormalityChecker/DigitMassTransfer.lean`, `NormalityChecker.lean`, `Audit.lean`, `notes/phase24/` (including `reviews/`), `scripts/phase24_digit_mass.py`, `scripts/phase24_classical.py`, and registry entries `GF-36` and `GF-40`. All 75 `\leanW` links in `paper.tex` now point directly to commit `04969b91f0c897ce55d21cb62c6b2c5aa3affe97`, and Stage 0.2 Audit A (`notes/phase25/reviews/phase24-analytic-audit-gf36-gf37-gf40.md`) independently re-verified `GF-36` and `GF-40` (including the journal text of Topacogullari 2017, *Acta Arith.* 181, Theorem 1.2 and formula (3.20)).
- **Certificate runs (local Windows host, Python 3.13.13, 27–28 November 2026):** `python -B scripts/phase24_digit_mass.py` exited 0 with `3,095,904`+ exact checks (including explicit rational endpoint checks for `C` and `C_true` added after Audit A). `python -B scripts/phase24_classical.py` exited 0 with `ALL CHECKS PASSED (108334 assertions) in 2.5 s`, and it printed the certified line `mu_NAF(a_+)/3 <= 0.304282 < A_16 = 324039/1048576`, giving `D^-(E_+(8); 2) >= 0.000000234`.
- **Manuscript structural check (PASS, refreshed 28 November 2026):** `paper.tex` uses 20 bibliography entries (`0` duplicates, `0` uncited, `0` undefined), 3 valid 40-hex commit hashes (`8ca43095887858bf9697b6a8332c6a6dd0b0cda3`, `cb395159c6e343c60c1413719cdfc8429e15af2c`, `04969b91f0c897ce55d21cb62c6b2c5aa3affe97`), 75 commit-pinned `\leanW` citations matched byte-for-byte against `git show 04969b91f0c897ce55d21cb62c6b2c5aa3affe97:NormalityChecker/DigitMassTransfer.lean`, and retains both required notices verbatim ("Cross-model review is not independent human peer review." and "`pdflatex`/`bibtex` compilation is pending before release.").
- **Pending before release:**
  1. Three `pdflatex` passes and `bibtex`, plus visual PDF inspection for numbering, layout and overfull boxes (blocked on local Windows and `hail` because neither host has `pdflatex`/`bibtex` installed).
  2. Independent human specialist peer review and owner release steps (`metadata.toml`, `papers/manifest.toml`, `papers/SHA256SUMS`, `docs/registry/papers.toml`).
