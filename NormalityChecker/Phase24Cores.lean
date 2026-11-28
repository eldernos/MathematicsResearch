module

public import NormalityChecker.HigherOrderTower
public import NormalityChecker.Phase23Cores
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! # Phase 24 finite algebraic, combinatorial, and multi-radix cores (Tracks B1–B4, D3)

Kernel-checked theorems supporting Phase 24
(`notes/phase24/simple-normality-and-word-laws.md` and
`notes/phase24/nonlinear-boundaries-and-approximation.md`):

1. **Sub-track B2 — Higher-`m` partition reciprocals `Y_{b,m}` (Theorems 1.1 & 1.5(1)):**
   - `binToBaseM`: binary-to-base-`m` support bijection `u_m(i)`.
   - `binToBaseM_two_pow`, `binToBaseM_add_two_pow`, `binToBaseM_lt_succ`,
     `binToBaseM_strictMono`: exact power evaluation and strict monotonicity.
   - `binToBaseM_gap`: exact 2-adic gap law
     `(m - 1) * (u_m(i + 1) - u_m(i)) = (m - 2) * m^(v_2(i + 1)) + 1`.
   - `thueMorse_signed_even_gap_sum_mul`, `thueMorse_signed_even_gap_sum`: exact pairwise
     cancellation of all `1 ≤ r ≤ k - 2` layers at `N = m^k` (`m ≥ 3, k ≥ 2`).

2. **Sub-track B1 — Euler's square `E_2^2` `1/26` Selberg sieve algebraic cores
   (Lemma 2.2 & Theorem 2.3):**
   - `selberg_prime_switch_ineq`: prime-by-prime Selberg sieve switch inequality
     `(A + α B)(1 + β) ≤ (A + β B)(1 + α)`.
   - `eulerSq_local_factor_identity`: exact rational collapse of the four local Euler factors
     into `1 + 2 / ((p - 1)(p^2 + 1))`.
   - `weighted_linear_sum_le` and `weighted_linear_finset_sum_le`: exact weighted triangular
     sum inequality `2 D (K H) ≤ H^2 + D^2 K (K + 1)` and its `Finset.Icc` sum corollary.

3. **Sub-track B3 — Rational-scaling universal family and complement symmetry
   (Theorems 3.1 & 3.2):**
   - `b2_add_b_add_one_odd_and_order`, `b2_add_b_add_one_orderOf`: `b^2 + b + 1` is odd,
     divides `b^3 - 1`, and has exact multiplicative order `3` for `b ≥ 2`.
   - `coprime_rat_complement_wordAt`, `coprime_rat_complement_digitFreq`,
     `base2_complement_digit_sum`: exact digitwise `(b - 1)`-complementarity of `(d - a)/d`
     and `a/d` for coprime rationals, yielding `f_e(a/d; 2) + f_e(1 - a/d; 2) = 1`.

4. **Sub-track B4 — Multi-radix kernel intersection & cross-radix order normality
   (Theorems 4.1(1) & 4.3(1)):**
   - `gcd_pow_sub_one`: `gcd(b^{k₁} - 1, b^{k₂} - 1) = b^{gcd(k₁, k₂)} - 1`.
   - `kernel_pow_inter_eq_gcd`: `K_{b^{k₁}} ∩ K_{b^{k₂}} = K_{b^{gcd(k₁, k₂)}}`.
   - `orderNormal_of_pow_orderNormal`: `OrderNormal (b^k) L₂ x → OrderNormal b (k(L₂ - 1) + 1) x`.

5. **Sub-track D3 — Badly-approximable convergent gap for bounded partial quotients
   (`nonlinear-boundaries-and-approximation.md`, §3):**
   - `unimodular_best_approx`: unimodular basis expansion yielding `|q x - h| ≥ |q_i x - p_i|`
     for `q_i ≤ q < q_{i+1}`.
   - `cfNum`, `cfDen`, `cf_det`, `cf_approx_formula`, `cf_convergent_gap`: exact convergent
     recurrences, determinant identity, and `q_i |q_i x - p_i| = 1 / (α_i + q_{i-1} / q_i)`.
   - `cf_badly_approx_bound` and `cf_one_two_badly_approx`: for partial quotients in `{1, ..., A}`,
     every `q ≥ 1` and `h : ℤ` satisfy `q |q x - h| > 1 / (A + 2)` and `q ‖q x‖ > 1 / (A + 2)`;
     in particular, for `{1, 2}`-continued fractions, `q |q x - h| > 1 / 4` and `q ‖q x‖ > 1 / 4`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.Phase24Cores

open HigherOrderTower SimpleNormalityKernel RadixPowerTower SharpTranslation Phase23Cores

/-! ### Section 1: Sub-track B2 — Higher-`m` partition reciprocals `Y_{b,m}` -/

/-- Sub-track B2: binary-to-base-`m` support bijection `u_m(i)`, replacing each binary
digit `2^j` of `i` by `m^j`. -/
def binToBaseM (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (i + 1) % 2 + m * binToBaseM m ((i + 1) / 2)
termination_by n => n
decreasing_by omega

theorem binToBaseM_zero (m : ℕ) : binToBaseM m 0 = 0 := by
  simp [binToBaseM]

theorem binToBaseM_two_mul (m n : ℕ) : binToBaseM m (2 * n) = m * binToBaseM m n := by
  rcases n with _ | k
  · simp [binToBaseM]
  · have hstep : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [hstep, binToBaseM]
    have hmod : (2 * k + 1 + 1) % 2 = 0 := by omega
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    simp [hmod, hdiv]

theorem binToBaseM_two_mul_add_one (m n : ℕ) :
    binToBaseM m (2 * n + 1) = 1 + m * binToBaseM m n := by
  rw [binToBaseM]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [hmod, hdiv]

/-- Exact evaluation on powers of two: `u_m(2^k) = m^k`. -/
theorem binToBaseM_two_pow (m k : ℕ) : binToBaseM m (2 ^ k) = m ^ k := by
  induction k with
  | zero =>
    simpa [binToBaseM_zero] using binToBaseM_two_mul_add_one m 0
  | succ k ih =>
    rw [pow_succ', binToBaseM_two_mul, ih, pow_succ']

/-- Bit-splitting identity: for `n < 2^r`, `u_m(2^r + n) = m^r + u_m(n)`. -/
theorem binToBaseM_add_two_pow {m r n : ℕ} (hn : n < 2 ^ r) :
    binToBaseM m (2 ^ r + n) = m ^ r + binToBaseM m n := by
  induction r generalizing n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    simpa [binToBaseM_zero] using binToBaseM_two_mul_add_one m 0
  | succ k ih =>
    rcases Nat.even_or_odd n with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · have hq : q < 2 ^ k := by rw [pow_succ'] at hn; omega
      have heq1 : 2 ^ (k + 1) + (q + q) = 2 * (2 ^ k + q) := by rw [pow_succ']; omega
      have heq2 : q + q = 2 * q := by omega
      rw [heq1, binToBaseM_two_mul, ih hq, heq2, binToBaseM_two_mul, mul_add, pow_succ']
    · have hq : q < 2 ^ k := by rw [pow_succ'] at hn; omega
      have heq : 2 ^ (k + 1) + (2 * q + 1) = 2 * (2 ^ k + q) + 1 := by rw [pow_succ']; omega
      rw [heq, binToBaseM_two_mul_add_one, ih hq, binToBaseM_two_mul_add_one, pow_succ']
      ring

/-- Consecutive strict monotonicity of `binToBaseM m` for `m ≥ 2`. -/
theorem binToBaseM_lt_succ {m : ℕ} (hm : 2 ≤ m) (i : ℕ) :
    binToBaseM m i < binToBaseM m (i + 1) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rcases Nat.even_or_odd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have heq : n + n = 2 * n := by omega
      rw [heq, binToBaseM_two_mul, binToBaseM_two_mul_add_one]
      omega
    · have heq : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [heq, binToBaseM_two_mul, binToBaseM_two_mul_add_one]
      have hlt : binToBaseM m n < binToBaseM m (n + 1) := ih n (by omega)
      nlinarith

/-- Global strict monotonicity of `binToBaseM m` for `m ≥ 2`. -/
theorem binToBaseM_strictMono {m : ℕ} (hm : 2 ≤ m) : StrictMono (binToBaseM m) :=
  strictMono_nat_of_lt_succ (binToBaseM_lt_succ hm)

/-- **Sub-track B2, Theorem 1.1 (exact support-gap law):**
for `m ≥ 2` and every `i : ℕ`,
`(m - 1) * (u_m(i + 1) - u_m(i)) = (m - 2) * m^(v_2(i + 1)) + 1`. -/
theorem binToBaseM_gap {m : ℕ} (hm : 2 ≤ m) (i : ℕ) :
    (m - 1) * (binToBaseM m (i + 1) - binToBaseM m i) =
      (m - 2) * m ^ (padicValNat 2 (i + 1)) + 1 := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rcases Nat.even_or_odd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have heq : n + n = 2 * n := by omega
      rw [heq, binToBaseM_two_mul, binToBaseM_two_mul_add_one]
      have hdiff : 1 + m * binToBaseM m n - m * binToBaseM m n = 1 := by omega
      have hndvd : ¬ 2 ∣ 2 * n + 1 := by omega
      have hval : padicValNat 2 (2 * n + 1) = 0 := by
        rw [Nat.padicValNat_def]
        exact multiplicity_eq_zero_of_not_dvd hndvd
      rw [hdiff, hval, pow_zero, mul_one, mul_one]
      omega
    · have heq : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [heq, binToBaseM_two_mul, binToBaseM_two_mul_add_one]
      have hlt : binToBaseM m n < binToBaseM m (n + 1) := binToBaseM_lt_succ hm n
      have hval : padicValNat 2 (2 * (n + 1)) = 1 + padicValNat 2 (n + 1) := by
        rw [Nat.padicValNat_def, Nat.padicValNat_def,
          multiplicity_base_mul (by norm_num : 1 < 2) (Nat.succ_ne_zero n), add_comm]
      have hih := ih n (by omega)
      have hle1 : 1 + m * binToBaseM m n ≤ m * binToBaseM m (n + 1) := by nlinarith
      have hle2 : binToBaseM m n ≤ binToBaseM m (n + 1) := hlt.le
      rw [hval, pow_add, pow_one]
      zify [show 1 ≤ m by omega, show 2 ≤ m by omega, hle1, hle2] at hih ⊢
      linear_combination (m : ℤ) * hih

/-- Auxiliary evaluation of the Thue–Morse sign at powers of two: `thueMorseSign (2^r) = -1`. -/
private lemma thueMorseSign_two_pow (r : ℕ) : thueMorseSign (2 ^ r) = -1 := by
  have h0 : 0 < 2 ^ r := pow_pos (by norm_num) r
  have h := thueMorseSign_add_pow_two h0
  simpa [thueMorseSign_zero] using h

/-- **Sub-track B2, Theorem 1.5(1) (exact signed even-gap cancellation, multiplied form):**
for `m ≥ 3` and `k ≥ 2`, all `1 ≤ r ≤ k - 2` layers cancel pairwise, leaving only the two
top gaps `g_{2^k}` and `g_{2^{k-1}}`. -/
theorem thueMorse_signed_even_gap_sum_mul {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k) :
    ((m - 1 : ℕ) : ℤ) *
      (∑ j ∈ Finset.Icc 1 (2 ^ (k - 1)),
        thueMorseSign (2 * j) *
          ((binToBaseM m (2 * j) - binToBaseM m (2 * j - 1) : ℕ) : ℤ)) =
      -(((m - 2) * (m ^ k + m ^ (k - 1)) + 2 : ℕ) : ℤ) := by
  set H : ℕ := 2 ^ (k - 2)
  have hH_pos : 1 ≤ H := Nat.one_le_pow (k - 2) 2 (by norm_num)
  have h2H : 2 * H = 2 ^ (k - 1) := by
    dsimp only [H]
    rw [← pow_succ', show k - 2 + 1 = k - 1 by omega]
  have h4H : 2 * (2 * H) = 2 ^ k := by
    rw [h2H, ← pow_succ', show k - 1 + 1 = k by omega]
  let f : ℕ → ℤ := fun j =>
    thueMorseSign (2 * j) * ((binToBaseM m (2 * j) - binToBaseM m (2 * j - 1) : ℕ) : ℤ)
  -- Split `Icc 1 (2 * H)` into `{H}`, `{2 * H}`, `Icc 1 (H - 1)`, and `Icc (H + 1) (2 * H - 1)`.
  have hsplit1 : Finset.Icc 1 (2 * H) = insert (2 * H) (Finset.Icc 1 (2 * H - 1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot1 : 2 * H ∉ Finset.Icc 1 (2 * H - 1) := by
    simp only [Finset.mem_Icc]; omega
  have hsplit2 : Finset.Icc 1 (2 * H - 1) =
      Finset.Icc 1 H ∪ Finset.Icc (H + 1) (2 * H - 1) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj2 : Disjoint (Finset.Icc 1 H) (Finset.Icc (H + 1) (2 * H - 1)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_Icc] at hj1 hj2; omega
  have hsplit3 : Finset.Icc 1 H = insert H (Finset.Icc 1 (H - 1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot3 : H ∉ Finset.Icc 1 (H - 1) := by
    simp only [Finset.mem_Icc]; omega
  have himg : Finset.Icc (H + 1) (2 * H - 1) = (Finset.Icc 1 (H - 1)).image (fun t => H + t) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro hj
      exact ⟨j - H, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      omega
  -- Pairwise cancellation: `f (H + t) = - f t` for every `1 ≤ t ≤ H - 1`.
  have hpair : ∀ t ∈ Finset.Icc 1 (H - 1), f (H + t) = - f t := by
    intro t ht
    simp only [Finset.mem_Icc] at ht
    have h2t_lt : 2 * t < 2 ^ (k - 1) := by omega
    have h2t1_lt : 2 * t - 1 < 2 ^ (k - 1) := by omega
    have heq_hi : 2 * (H + t) = 2 ^ (k - 1) + 2 * t := by omega
    have heq_lo : 2 * (H + t) - 1 = 2 ^ (k - 1) + (2 * t - 1) := by omega
    dsimp only [f]
    rw [heq_lo, heq_hi, thueMorseSign_add_pow_two h2t_lt,
      binToBaseM_add_two_pow h2t_lt, binToBaseM_add_two_pow h2t1_lt,
      Nat.add_sub_add_left]
    ring
  have hsum_cancel : ∑ j ∈ Finset.Icc (H + 1) (2 * H - 1), f j =
      - ∑ t ∈ Finset.Icc 1 (H - 1), f t := by
    rw [himg, Finset.sum_image (fun a _ b _ hab => by omega), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hpair
  have hsum_eq : ∑ j ∈ Finset.Icc 1 (2 ^ (k - 1)), f j = f (2 * H) + f H := by
    rw [← h2H, hsplit1, Finset.sum_insert hnot1, hsplit2, Finset.sum_union hdisj2,
      hsplit3, Finset.sum_insert hnot3, hsum_cancel]
    ring
  change ((m - 1 : ℕ) : ℤ) * (∑ j ∈ Finset.Icc 1 (2 ^ (k - 1)), f j) = _
  rw [hsum_eq]
  -- Evaluate the two surviving gaps using `binToBaseM_gap`.
  have hg1_nat : (m - 1) * (binToBaseM m (2 ^ (k - 1)) - binToBaseM m (2 ^ (k - 1) - 1)) =
      (m - 2) * m ^ (k - 1) + 1 := by
    have hpos : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow (k - 1) 2 (by norm_num)
    have h := binToBaseM_gap (show 2 ≤ m by omega) (2 ^ (k - 1) - 1)
    rw [show 2 ^ (k - 1) - 1 + 1 = 2 ^ (k - 1) by omega] at h
    rw [h, Nat.padicValNat_def, multiplicity_base_pow (by norm_num : 1 < 2)]
  have hg2_nat : (m - 1) * (binToBaseM m (2 ^ k) - binToBaseM m (2 ^ k - 1)) =
      (m - 2) * m ^ k + 1 := by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have h := binToBaseM_gap (show 2 ≤ m by omega) (2 ^ k - 1)
    rw [show 2 ^ k - 1 + 1 = 2 ^ k by omega] at h
    rw [h, Nat.padicValNat_def, multiplicity_base_pow (by norm_num : 1 < 2)]
  have hg1 : ((m - 1 : ℕ) : ℤ) *
      ((binToBaseM m (2 ^ (k - 1)) - binToBaseM m (2 ^ (k - 1) - 1) : ℕ) : ℤ) =
      (((m - 2) * m ^ (k - 1) + 1 : ℕ) : ℤ) := by exact_mod_cast hg1_nat
  have hg2 : ((m - 1 : ℕ) : ℤ) *
      ((binToBaseM m (2 ^ k) - binToBaseM m (2 ^ k - 1) : ℕ) : ℤ) =
      (((m - 2) * m ^ k + 1 : ℕ) : ℤ) := by exact_mod_cast hg2_nat
  dsimp only [f]
  rw [h4H, h2H, thueMorseSign_two_pow k, thueMorseSign_two_pow (k - 1)]
  push_cast at hg1 hg2 ⊢
  linear_combination -hg2 - hg1

/-- **Sub-track B2, Theorem 1.5(1) (exact signed even-gap sum at `N = m^k`):**
for `m ≥ 3` and `k ≥ 2`,
`∑_{j=1}^{2^{k-1}} (-1)^{s_2(2j)} (u_m(2j) - u_m(2j - 1)) = -(((m - 2)(m^k + m^{k-1}) + 2) / (m - 1))`. -/
theorem thueMorse_signed_even_gap_sum {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k) :
    ∑ j ∈ Finset.Icc 1 (2 ^ (k - 1)),
      thueMorseSign (2 * j) *
        ((binToBaseM m (2 * j) - binToBaseM m (2 * j - 1) : ℕ) : ℤ) =
      -((((m - 2) * (m ^ k + m ^ (k - 1)) + 2) / (m - 1) : ℕ) : ℤ) := by
  have hmul := thueMorse_signed_even_gap_sum_mul hm hk
  set S : ℤ := ∑ j ∈ Finset.Icc 1 (2 ^ (k - 1)),
    thueMorseSign (2 * j) * ((binToBaseM m (2 * j) - binToBaseM m (2 * j - 1) : ℕ) : ℤ)
  set N : ℕ := (m - 2) * (m ^ k + m ^ (k - 1)) + 2
  have hm1_pos : 0 < m - 1 := by omega
  have hm1_ne : ((m - 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hm1_pos.ne'
  have hdvd_z : ((m - 1 : ℕ) : ℤ) ∣ (N : ℤ) := ⟨-S, by linarith⟩
  have hdvd : m - 1 ∣ N := Int.natCast_dvd_natCast.mp hdvd_z
  have hdiv : ((m - 1 : ℕ) : ℤ) * ((N / (m - 1) : ℕ) : ℤ) = (N : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  apply mul_left_cancel₀ hm1_ne
  linarith

/-! ### Section 2: Sub-track B1 — Euler's square `E_2^2` `1/26` Selberg sieve algebraic cores -/

/-- **Sub-track B1, Lemma 2.2 (prime-by-prime Selberg sieve switch inequality):**
for `0 ≤ B ≤ A` and `0 ≤ β ≤ α`, `(A + α B)(1 + β) ≤ (A + β B)(1 + α)`. -/
theorem selberg_prime_switch_ineq {A B α β : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) (hβ : 0 ≤ β) (hβα : β ≤ α) :
    (A + α * B) * (1 + β) ≤ (A + β * B) * (1 + α) := by
  have _ := hA
  have _ := hB
  have _ := hβ
  nlinarith

/-- **Sub-track B1, Theorem 2.3 (exact local Euler-factor collapse):**
exact rational identity collapsing the four local Euler factors into `1 + 2 / ((p - 1)(p^2 + 1))`. -/
theorem eulerSq_local_factor_identity {p : ℚ} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hp2 : p ≠ 2) (hpm1 : p ≠ -1) (hp4 : p ^ 4 - 1 ≠ 0) :
    (1 - 1 / (p - 1) ^ 2) * (1 - 1 / p ^ 2) ^ 2 * (p ^ 4 / (p ^ 4 - 1)) *
      (1 + 1 / (p * (p - 2)) + 2 * (p - 1) / ((p ^ 2 - 1) * (p - 2))) =
      1 + 2 / ((p - 1) * (p ^ 2 + 1)) := by
  have hp1' : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  have hp2' : p - 2 ≠ 0 := sub_ne_zero.mpr hp2
  have hpp1' : p + 1 ≠ 0 := by intro h; apply hpm1; linarith
  have hp2m1 : p ^ 2 - 1 ≠ 0 := by
    have hfac : p ^ 2 - 1 = (p - 1) * (p + 1) := by ring
    rw [hfac]
    exact mul_ne_zero hp1' hpp1'
  have hp2p1 : p ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg p]
  field_simp [hp0, hp1', hp2', hp2m1, hp2p1, hp4]
  ring

/-- **Sub-track B1, Theorem 2.3 (weighted triangular sum inequality, integer form):**
`2 D (K H) ≤ H^2 + D^2 K (K + 1)`, equivalently `(H - D K)^2 + D^2 K ≥ 0`. -/
theorem weighted_linear_sum_le (H D K : ℕ) :
    2 * D * (K * H) ≤ H ^ 2 + D ^ 2 * K * (K + 1) := by
  zify
  nlinarith [sq_nonneg ((H : ℤ) - (D : ℤ) * (K : ℤ))]

/-- Real `Finset.Icc` sum form of `weighted_linear_sum_le`:
`2 D ∑_{m=1}^K (H - D m) ≤ H^2`. -/
theorem weighted_linear_finset_sum_le (H D K : ℕ) :
    2 * (D : ℝ) * ∑ m ∈ Finset.Icc 1 K, ((H : ℝ) - (D : ℝ) * (m : ℝ)) ≤ (H : ℝ) ^ 2 := by
  have hsum_nat : 2 * ∑ m ∈ Finset.Icc 1 K, m = K * (K + 1) := by
    induction K with
    | zero => simp
    | succ k ih =>
      have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
      rw [hsplit, Finset.sum_insert hnot, mul_add, ih]
      ring
  have hsum_r : (2 : ℝ) * ∑ m ∈ Finset.Icc 1 K, (m : ℝ) = (K : ℝ) * ((K : ℝ) + 1) := by
    have h1 := congrArg (Nat.cast (R := ℝ)) hsum_nat
    push_cast at h1
    exact h1
  have hcard : (Finset.Icc 1 K).card = K := by simp
  have hmain : 2 * (D : ℝ) * ∑ m ∈ Finset.Icc 1 K, ((H : ℝ) - (D : ℝ) * (m : ℝ)) =
      2 * (D : ℝ) * ((K : ℝ) * (H : ℝ)) - (D : ℝ) ^ 2 * (K : ℝ) * ((K : ℝ) + 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.mul_sum]
    linear_combination -(D : ℝ) ^ 2 * hsum_r
  have hineq : (2 * (D : ℝ) * ((K : ℝ) * (H : ℝ))) ≤
      (H : ℝ) ^ 2 + (D : ℝ) ^ 2 * (K : ℝ) * ((K : ℝ) + 1) := by
    exact_mod_cast weighted_linear_sum_le H D K
  linarith

/-! ### Section 3: Sub-track B3 — Rational-scaling universal family and complement symmetry -/

/-- **Sub-track B3, Theorem 3.2:** for every `b : ℕ`, `b^2 + b + 1` is odd and divides `b^3 - 1`. -/
theorem b2_add_b_add_one_odd_and_order (b : ℕ) :
    Odd (b ^ 2 + b + 1) ∧ (b ^ 2 + b + 1) ∣ (b ^ 3 - 1) := by
  constructor
  · obtain ⟨k, hk⟩ := Nat.even_mul_succ_self b
    refine ⟨k, ?_⟩
    have hsq : b * (b + 1) = b ^ 2 + b := by ring
    omega
  · rcases b with _ | n
    · simp
    · refine ⟨n, ?_⟩
      have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (by omega)
      zify [h1]
      ring

/-- Exact multiplicative order for the universal family: for `b ≥ 2`,
`orderOf (b : ZMod (b^2 + b + 1)) = 3`. -/
theorem b2_add_b_add_one_orderOf {b : ℕ} (hb : 2 ≤ b) :
    orderOf (b : ZMod (b ^ 2 + b + 1)) = 3 := by
  set d : ℕ := b ^ 2 + b + 1
  have hdvd3 : d ∣ b ^ 3 - 1 := (b2_add_b_add_one_odd_and_order b).2
  have hord_dvd : orderOf (b : ZMod d) ∣ 3 :=
    (dvd_pow_sub_one_iff_orderOf_dvd hb).mp hdvd3
  have hord_pos : 0 < orderOf (b : ZMod d) := by
    have hpow : (b : ZMod d) ^ 3 = 1 := by
      have h1 : 1 ≤ b ^ 3 := one_le_pow₀ (by omega)
      rw [← sub_eq_zero]
      have hcast : ((b ^ 3 - 1 : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (b ^ 3 - 1) d).mpr hdvd3
      rwa [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one] at hcast
    exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hpow⟩)
  have hne1 : orderOf (b : ZMod d) ≠ 1 := by
    intro h1
    have hdvd1 : d ∣ b ^ 1 - 1 := (dvd_pow_sub_one_iff_orderOf_dvd hb).mpr (by rw [h1])
    have hpos : 0 < b ^ 1 - 1 := by rw [pow_one]; omega
    have hle : d ≤ b ^ 1 - 1 := Nat.le_of_dvd hpos hdvd1
    have hgt : b < d := by dsimp [d]; nlinarith
    rw [pow_one] at hle
    omega
  have hle3 : orderOf (b : ZMod d) ≤ 3 := Nat.le_of_dvd (by norm_num) hord_dvd
  have hnot2 : orderOf (b : ZMod d) ≠ 2 := by
    intro h2
    rw [h2] at hord_dvd
    omega
  omega

/-- Auxiliary shift formula for a general rational `a / d` (`d ≥ 1`). -/
private lemma shift_rat_general {b d a : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    shift b ((a : ℝ) / (d : ℝ)) n = ((b ^ n * a % d : ℕ) : ℝ) / (d : ℝ) := by
  have hd_pos : 0 < d := by omega
  have hd_rpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hdiv : b ^ n * a = d * (b ^ n * a / d) + b ^ n * a % d := (Nat.div_add_mod _ _).symm
  have hrew : (b : ℝ) ^ n * ((a : ℝ) / (d : ℝ)) =
      ((b ^ n * a % d : ℕ) : ℝ) / (d : ℝ) + ((b ^ n * a / d : ℕ) : ℤ) := by
    have hdiv_r : (b : ℝ) ^ n * (a : ℝ) = (d : ℝ) * ((b ^ n * a / d : ℕ) : ℝ) +
        ((b ^ n * a % d : ℕ) : ℝ) := by exact_mod_cast hdiv
    rw [Int.cast_natCast]
    field_simp [hd_rpos.ne']
    linarith
  unfold shift
  rw [hrew, Int.fract_add_intCast]
  refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
  rw [div_lt_one hd_rpos]
  exact_mod_cast Nat.mod_lt (b ^ n * a) hd_pos

/-- **Sub-track B3, Theorem 3.1 (digitwise `(b - 1)`-complement law for coprime rationals):**
if `b ≥ 2`, `d ≥ 2`, `Nat.Coprime d b`, and `1 ≤ a < d`, then at every shift `n : ℕ`,
`wordAt b 1 (1 - a/d) n = (b - 1) - wordAt b 1 (a/d) n` and `wordAt b 1 (a/d) n < b`. -/
theorem coprime_rat_complement_wordAt {b d a : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hcop : Nat.Coprime d b) (ha0 : 1 ≤ a) (had : a < d) (n : ℕ) :
    wordAt b 1 (1 - (a : ℝ) / (d : ℝ)) n = (b - 1) - wordAt b 1 ((a : ℝ) / (d : ℝ)) n ∧
      wordAt b 1 ((a : ℝ) / (d : ℝ)) n < b := by
  have hd_pos : 0 < d := by omega
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hd_rpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  set r : ℕ := b ^ n * a % d
  have hr_lt : r < d := Nat.mod_lt _ hd_pos
  have hr_ge1 : 1 ≤ r := by
    by_contra h0
    have hdvd : d ∣ b ^ n * a := Nat.dvd_of_mod_eq_zero (by omega)
    have hda : d ∣ a := (hcop.pow_right n).dvd_of_dvd_mul_left hdvd
    have := Nat.le_of_dvd (by omega) hda
    omega
  have hs_eq : shift b ((a : ℝ) / (d : ℝ)) n = (r : ℝ) / (d : ℝ) :=
    shift_rat_general (by omega) n
  have hr_pos : (0 : ℝ) < (r : ℝ) / (d : ℝ) := div_pos (by exact_mod_cast (show 0 < r by omega)) hd_rpos
  have hr_lt1 : (r : ℝ) / (d : ℝ) < 1 := (div_lt_one hd_rpos).mpr (by exact_mod_cast hr_lt)
  have hcomp_shift : shift b (1 - (a : ℝ) / (d : ℝ)) n = 1 - (r : ℝ) / (d : ℝ) := by
    have hbase : (b : ℝ) ^ n * ((a : ℝ) / (d : ℝ)) =
        (r : ℝ) / (d : ℝ) + (⌊(b : ℝ) ^ n * ((a : ℝ) / (d : ℝ))⌋ : ℝ) := by
      have hf := Int.fract_add_floor ((b : ℝ) ^ n * ((a : ℝ) / (d : ℝ)))
      have hsc : Int.fract ((b : ℝ) ^ n * ((a : ℝ) / (d : ℝ))) = (r : ℝ) / (d : ℝ) := hs_eq
      linarith
    unfold shift
    have hrew : (b : ℝ) ^ n * (1 - (a : ℝ) / (d : ℝ)) =
        (1 - (r : ℝ) / (d : ℝ)) +
          (((b : ℤ) ^ n - 1 - ⌊(b : ℝ) ^ n * ((a : ℝ) / (d : ℝ))⌋ : ℤ) : ℝ) := by
      push_cast
      conv_lhs => rw [mul_sub, mul_one, hbase]
      ring
    rw [hrew, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have ⟨he_lt, hlow, hhigh⟩ := coprime_rat_cylinder_margin hb hd hcop hr_ge1 hr_lt (le_rfl : 1 ≤ 1)
  set e : ℕ := r * b ^ 1 / d
  have hmargin_pos : (0 : ℝ) < 1 / ((d : ℝ) * (b : ℝ) ^ 1) := by positivity
  have hlow_strict : (e : ℝ) < (b : ℝ) * ((r : ℝ) / (d : ℝ)) := by
    have h1 : (e : ℝ) / (b : ℝ) < (r : ℝ) / (d : ℝ) := by
      have : (e : ℝ) / (b : ℝ) ^ 1 < (r : ℝ) / (d : ℝ) := by linarith
      simpa using this
    exact (div_lt_iff₀ hb_pos).mp h1 |> fun h => by linarith
  have hhigh_strict : (b : ℝ) * ((r : ℝ) / (d : ℝ)) < ((e + 1 : ℕ) : ℝ) := by
    have h1 : (r : ℝ) / (d : ℝ) < ((e + 1 : ℕ) : ℝ) / (b : ℝ) := by
      have : (r : ℝ) / (d : ℝ) < ((e + 1 : ℕ) : ℝ) / (b : ℝ) ^ 1 := by linarith
      simpa using this
    exact (lt_div_iff₀ hb_pos).mp h1 |> fun h => by linarith
  have hw1 : wordAt b 1 ((a : ℝ) / (d : ℝ)) n = e := by
    unfold wordAt
    rw [pow_one, hs_eq]
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast at hhigh_strict ⊢
    exact ⟨hlow_strict.le, hhigh_strict⟩
  have he_lt_b : e < b := by simpa using he_lt
  have hw2 : wordAt b 1 (1 - (a : ℝ) / (d : ℝ)) n = (b - 1) - e := by
    unfold wordAt
    rw [pow_one, hcomp_shift]
    rw [Nat.floor_eq_iff (mul_nonneg hb_pos.le (by linarith))]
    have hcast1 : (((b - 1 - e : ℕ) : ℝ)) = (b : ℝ) - 1 - (e : ℝ) := by
      rw [Nat.cast_sub (by omega : e ≤ b - 1), Nat.cast_sub (by omega : 1 ≤ b)]
      push_cast; ring
    rw [hcast1]
    push_cast at hhigh_strict
    constructor <;> linarith
  exact ⟨by rw [hw1, hw2], by rw [hw1]; exact he_lt_b⟩

/-- **Sub-track B3, Theorem 3.1 (base-`b` complement digit-frequency identity):**
for every `b ≥ 2`, `d ≥ 2`, `Nat.Coprime d b`, `1 ≤ a < d`, `e < b`, and cutoff `N`,
`digitFreq b (1 - a/d) e N = digitFreq b (a/d) (b - 1 - e) N`. -/
theorem coprime_rat_complement_digitFreq {b d a e : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hcop : Nat.Coprime d b) (ha0 : 1 ≤ a) (had : a < d) (he : e < b) (N : ℕ) :
    digitFreq b (1 - (a : ℝ) / (d : ℝ)) e N =
      digitFreq b ((a : ℝ) / (d : ℝ)) (b - 1 - e) N := by
  classical
  unfold digitFreq wordFreq wordCount
  have hfilt :
      ((range N).filter fun n => ⌊(b : ℝ) ^ 1 * shift b (1 - (a : ℝ) / (d : ℝ)) n⌋₊ = e) =
      ((range N).filter fun n => ⌊(b : ℝ) ^ 1 * shift b ((a : ℝ) / (d : ℝ)) n⌋₊ = b - 1 - e) := by
    refine Finset.filter_congr fun n _ => ?_
    have ⟨hcomp, hlt⟩ := coprime_rat_complement_wordAt hb hd hcop ha0 had n
    change wordAt b 1 (1 - (a : ℝ) / (d : ℝ)) n = e ↔
      wordAt b 1 ((a : ℝ) / (d : ℝ)) n = b - 1 - e
    rw [hcomp]
    omega
  rw [hfilt]

/-- **Sub-track B3, Theorem 3.1(1) (base-2 complement digit-frequency sum):**
for every odd `d ≥ 2` (`Nat.Coprime d 2`), `1 ≤ a < d`, binary digit `e < 2`, and `N ≥ 1`,
`digitFreq 2 (a/d) e N + digitFreq 2 (1 - a/d) e N = 1`. -/
theorem base2_complement_digit_sum {d a e N : ℕ} (hd : 2 ≤ d) (hcop : Nat.Coprime d 2)
    (ha0 : 1 ≤ a) (had : a < d) (he : e < 2) (hN : 1 ≤ N) :
    digitFreq 2 ((a : ℝ) / (d : ℝ)) e N + digitFreq 2 (1 - (a : ℝ) / (d : ℝ)) e N = 1 := by
  rw [coprime_rat_complement_digitFreq (by norm_num) hd hcop ha0 had he N]
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold digitFreq wordFreq wordCount
  rw [← add_div, ← Nat.cast_add]
  have hpart :
      ((range N).filter fun n => ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ = e).card +
      ((range N).filter fun n => ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ = 2 - 1 - e).card =
      N := by
    have hdisj : Disjoint
        ((range N).filter fun n => ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ = e)
        ((range N).filter fun n => ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ = 2 - 1 - e) := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      have e1 := (mem_filter.mp h1).2
      have e2 := (mem_filter.mp h2).2
      omega
    rw [← Finset.card_union_of_disjoint hdisj]
    have hunion :
        ((range N).filter fun n => ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ = e) ∪
        ((range N).filter fun n => ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ = 2 - 1 - e) =
        range N := by
      ext n
      simp only [mem_union, mem_filter, mem_range]
      constructor
      · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
      · intro hn
        have hlt : ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ < 2 :=
          (coprime_rat_complement_wordAt (by norm_num) hd hcop ha0 had n).2
        by_cases hcur : ⌊((2 : ℕ) : ℝ) ^ 1 * shift 2 ((a : ℝ) / (d : ℝ)) n⌋₊ = e
        · exact Or.inl ⟨hn, hcur⟩
        · exact Or.inr ⟨hn, by omega⟩
    rw [hunion, card_range]
  rw [hpart, div_self hN_ne]

/-! ### Section 4: Sub-track B4 — Multi-radix kernel intersection & cross-radix order normality -/

/-- Exact divisibility gcd identity: `gcd(b^{k₁} - 1, b^{k₂} - 1) = b^{gcd(k₁, k₂)} - 1`
for every `b ≥ 2` and `k₁, k₂ : ℕ`. -/
theorem gcd_pow_sub_one {b : ℕ} (hb : 2 ≤ b) (k₁ k₂ : ℕ) :
    Nat.gcd (b ^ k₁ - 1) (b ^ k₂ - 1) = b ^ (Nat.gcd k₁ k₂) - 1 := by
  induction hsum : k₁ + k₂ using Nat.strong_induction_on generalizing k₁ k₂ with
  | ind s ih =>
    rcases Nat.eq_zero_or_pos k₁ with rfl | hk₁
    · simp
    rcases Nat.eq_zero_or_pos k₂ with rfl | hk₂
    · simp
    rcases le_total k₁ k₂ with hle | hle
    · have hsplit : b ^ k₂ - 1 = (b ^ (k₂ - k₁) - 1) + (b ^ k₁ - 1) * b ^ (k₂ - k₁) := by
        have h1 : 1 ≤ b ^ k₁ := one_le_pow₀ (by omega)
        have h2 : 1 ≤ b ^ k₂ := one_le_pow₀ (by omega)
        have h3 : 1 ≤ b ^ (k₂ - k₁) := one_le_pow₀ (by omega)
        have hpow : b ^ k₁ * b ^ (k₂ - k₁) = b ^ k₂ := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        zify [h1, h2, h3]
        have hpow_z : (b : ℤ) ^ k₁ * (b : ℤ) ^ (k₂ - k₁) = (b : ℤ) ^ k₂ := by exact_mod_cast hpow
        linarith
      rw [hsplit, Nat.gcd_add_mul_left_right]
      rw [ih (k₁ + (k₂ - k₁)) (by omega) k₁ (k₂ - k₁) rfl, Nat.gcd_sub_self_right hle]
    · have hsplit : b ^ k₁ - 1 = (b ^ (k₁ - k₂) - 1) + (b ^ k₂ - 1) * b ^ (k₁ - k₂) := by
        have h1 : 1 ≤ b ^ k₁ := one_le_pow₀ (by omega)
        have h2 : 1 ≤ b ^ k₂ := one_le_pow₀ (by omega)
        have h3 : 1 ≤ b ^ (k₁ - k₂) := one_le_pow₀ (by omega)
        have hpow : b ^ k₂ * b ^ (k₁ - k₂) = b ^ k₁ := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        zify [h1, h2, h3]
        have hpow_z : (b : ℤ) ^ k₂ * (b : ℤ) ^ (k₁ - k₂) = (b : ℤ) ^ k₁ := by exact_mod_cast hpow
        linarith
      rw [hsplit, Nat.gcd_comm, Nat.gcd_add_mul_left_right, Nat.gcd_comm]
      rw [ih ((k₁ - k₂) + k₂) (by omega) (k₁ - k₂) k₂ rfl, Nat.gcd_sub_self_left hle]

/-- **Sub-track B4, Theorem 4.3(1) (multi-radix kernel intersection law):**
for every `b ≥ 2` and `k₁, k₂ ≥ 1`,
`Kernel (b ^ k₁) ∩ Kernel (b ^ k₂) = Kernel (b ^ (Nat.gcd k₁ k₂))`. -/
theorem kernel_pow_inter_eq_gcd {b k₁ k₂ : ℕ} (hb : 2 ≤ b) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    Kernel (b ^ k₁) ∩ Kernel (b ^ k₂) = Kernel (b ^ (Nat.gcd k₁ k₂)) := by
  set g : ℕ := Nat.gcd k₁ k₂
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left k₂ (by omega)
  have hpow_ge2 : ∀ m : ℕ, 1 ≤ m → 2 ≤ b ^ m := fun m hm =>
    (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hm)
  have hbk₁ : 2 ≤ b ^ k₁ := hpow_ge2 k₁ hk₁
  have hbk₂ : 2 ≤ b ^ k₂ := hpow_ge2 k₂ hk₂
  have hbg : 2 ≤ b ^ g := hpow_ge2 g hg_pos
  have hsub_of_dvd : ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → m ∣ n → Kernel (b ^ m) ⊆ Kernel (b ^ n) := by
    intro m n hm hn hdvd x hx
    obtain ⟨q, rfl⟩ := hdvd
    have hbm : 2 ≤ b ^ m := hpow_ge2 m hm
    have hbn : 2 ≤ b ^ (m * q) := hpow_ge2 (m * q) hn
    rw [kernel_eq_fixedPoint_add_zeroOrbit hbm] at hx
    rw [kernel_eq_fixedPoint_add_zeroOrbit hbn]
    obtain ⟨c, hc, u, hu, rfl⟩ := hx
    refine ⟨c, ?_, u, ?_, rfl⟩
    · rw [pow_mul]
      exact fixedPointSubgroup_le_pow hbm hc
    · rw [zeroOrbitSubgroup_pow_eq hb (by omega)] at hu
      rwa [zeroOrbitSubgroup_pow_eq hb (by omega)]
  ext x
  constructor
  · rintro ⟨hx₁, hx₂⟩
    rw [mem_kernel_iff_exists_fixedPoint_add_zeroOrbit hbk₁] at hx₁
    rw [mem_kernel_iff_exists_fixedPoint_add_zeroOrbit hbk₂] at hx₂
    obtain ⟨m₁, u₁, hu₁, hx₁_eq⟩ := hx₁
    obtain ⟨m₂, u₂, hu₂, hx₂_eq⟩ := hx₂
    push_cast at hx₁_eq hx₂_eq
    rw [zeroOrbitSubgroup_pow_eq hb (by omega)] at hu₁ hu₂
    set Q₁ : ℕ := b ^ k₁ - 1
    set Q₂ : ℕ := b ^ k₂ - 1
    set Qg : ℕ := b ^ g - 1
    have hQ₁_pos : 0 < Q₁ := by omega
    have hQ₂_pos : 0 < Q₂ := by omega
    have hQg_pos : 0 < Qg := by omega
    have hQ₁_r : (Q₁ : ℝ) = (b : ℝ) ^ k₁ - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hQ₂_r : (Q₂ : ℝ) = (b : ℝ) ^ k₂ - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hQg_r : (Qg : ℝ) = (b : ℝ) ^ g - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hQ₁_ne : (Q₁ : ℝ) ≠ 0 := by exact_mod_cast hQ₁_pos.ne'
    have hQ₂_ne : (Q₂ : ℝ) ≠ 0 := by exact_mod_cast hQ₂_pos.ne'
    have hQg_ne : (Qg : ℝ) ≠ 0 := by exact_mod_cast hQg_pos.ne'
    set c₁ : ℝ := (m₁ : ℝ) / ((b : ℝ) ^ k₁ - 1)
    set c₂ : ℝ := (m₂ : ℝ) / ((b : ℝ) ^ k₂ - 1)
    have hc₁_mem : c₁ ∈ fixedPointSubgroup (b ^ (k₁ * k₂)) := by
      rw [pow_mul]
      refine fixedPointSubgroup_le_pow hbk₁ ⟨m₁, ?_⟩
      dsimp only [c₁]; push_cast; rw [← hQ₁_r]; field_simp [hQ₁_ne]
    have hc₂_mem : c₂ ∈ fixedPointSubgroup (b ^ (k₁ * k₂)) := by
      rw [mul_comm, pow_mul]
      refine fixedPointSubgroup_le_pow hbk₂ ⟨m₂, ?_⟩
      dsimp only [c₂]; push_cast; rw [← hQ₂_r]; field_simp [hQ₂_ne]
    have hdiff_fp : c₁ - c₂ ∈ fixedPointSubgroup (b ^ (k₁ * k₂)) :=
      (fixedPointSubgroup (b ^ (k₁ * k₂))).sub_mem hc₁_mem hc₂_mem
    have hdiff_eq : c₁ - c₂ = u₂ - u₁ := by dsimp only [c₁, c₂]; linarith
    have hdiff_zo : c₁ - c₂ ∈ zeroOrbitSubgroup b := by
      rw [hdiff_eq]
      exact (zeroOrbitSubgroup b).sub_mem hu₂ hu₁
    obtain ⟨z, hz⟩ :=
      (fixedPointSubgroup_inter_zeroOrbitSubgroup hb (Nat.mul_pos (by omega) (by omega))
        hdiff_fp).mp hdiff_zo
    have hcross_r : (m₁ : ℝ) * (Q₂ : ℝ) = (Q₁ : ℝ) * ((m₂ : ℝ) + (z : ℝ) * (Q₂ : ℝ)) := by
      have h1 : (m₁ : ℝ) / (Q₁ : ℝ) - (m₂ : ℝ) / (Q₂ : ℝ) = (z : ℝ) := by
        dsimp [c₁, c₂] at hz
        rwa [← hQ₁_r, ← hQ₂_r] at hz
      have h2 := (div_sub_div (m₁ : ℝ) (m₂ : ℝ) hQ₁_ne hQ₂_ne)
      rw [h2] at h1
      have h3 := (div_eq_iff (mul_ne_zero hQ₁_ne hQ₂_ne)).mp h1
      linarith
    have hcross : m₁ * (Q₂ : ℤ) = (Q₁ : ℤ) * (m₂ + z * (Q₂ : ℤ)) := by exact_mod_cast hcross_r
    have hgcd_eq : Nat.gcd Q₁ Q₂ = Qg := gcd_pow_sub_one hb k₁ k₂
    have hbez : (Qg : ℤ) = (Q₁ : ℤ) * Nat.gcdA Q₁ Q₂ + (Q₂ : ℤ) * Nat.gcdB Q₁ Q₂ := by
      rw [← hgcd_eq]
      exact Nat.gcd_eq_gcd_ab Q₁ Q₂
    let m : ℤ := m₁ * Nat.gcdA Q₁ Q₂ + (m₂ + z * (Q₂ : ℤ)) * Nat.gcdB Q₁ Q₂
    have hm_rel : m * (Q₁ : ℤ) = m₁ * (Qg : ℤ) := by
      dsimp only [m]
      linear_combination -(Nat.gcdB Q₁ Q₂) * hcross + m₁ * hbez.symm
    have hm_rel_r : (m : ℝ) * (Q₁ : ℝ) = (m₁ : ℝ) * (Qg : ℝ) := by exact_mod_cast hm_rel
    have hc₁_rew : c₁ = (m : ℝ) / ((b : ℝ) ^ g - 1) := by
      dsimp only [c₁]
      rw [← hQ₁_r, ← hQg_r, div_eq_div_iff hQ₁_ne hQg_ne]
      linarith
    rw [mem_kernel_iff_exists_fixedPoint_add_zeroOrbit hbg]
    refine ⟨m, u₁, ?_, ?_⟩
    · rwa [zeroOrbitSubgroup_pow_eq hb hg_pos]
    · push_cast
      rw [hx₁_eq, ← hc₁_rew]
  · intro hxg
    exact ⟨hsub_of_dvd hg_pos hk₁ (Nat.gcd_dvd_left k₁ k₂) hxg,
      hsub_of_dvd hg_pos hk₂ (Nat.gcd_dvd_right k₁ k₂) hxg⟩

/-- Auxiliary floor-division lemma: `⌊b^(a + d) * t⌋₊ / b^d = ⌊b^a * t⌋₊` for `1 ≤ b` and `0 ≤ t`. -/
private lemma natFloor_pow_add_div' {b a d : ℕ} (hb : 1 ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    ⌊(b : ℝ) ^ (a + d) * t⌋₊ / b ^ d = ⌊(b : ℝ) ^ a * t⌋₊ := by
  have hbd_pos : 0 < b ^ d := pow_pos (by omega) d
  have hbd_r : (0 : ℝ) < (b : ℝ) ^ d := by exact_mod_cast hbd_pos
  have hba_r : (0 : ℝ) < (b : ℝ) ^ a := pow_pos (by exact_mod_cast (show 0 < b by omega)) a
  have hle : (⌊(b : ℝ) ^ a * t⌋₊ : ℝ) * (b : ℝ) ^ d ≤ (b : ℝ) ^ (a + d) * t := by
    rw [pow_add, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (mul_nonneg hba_r.le ht)) hbd_r.le
  have hlt : (b : ℝ) ^ (a + d) * t < ((⌊(b : ℝ) ^ a * t⌋₊ : ℝ) + 1) * (b : ℝ) ^ d := by
    rw [pow_add, mul_right_comm]
    exact mul_lt_mul_of_pos_right (Nat.lt_floor_add_one _) hbd_r
  have h1 : ⌊(b : ℝ) ^ a * t⌋₊ * b ^ d ≤ ⌊(b : ℝ) ^ (a + d) * t⌋₊ := by
    rw [Nat.le_floor_iff (mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) ht)]
    push_cast; exact hle
  have h2 : ⌊(b : ℝ) ^ (a + d) * t⌋₊ < (⌊(b : ℝ) ^ a * t⌋₊ + 1) * b ^ d := by
    rw [Nat.floor_lt (mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) ht)]
    push_cast; exact hlt
  have hdiv1 := (Nat.le_div_iff_mul_le hbd_pos).mpr h1
  have hdiv2 := (Nat.div_lt_iff_lt_mul hbd_pos).mpr h2
  omega

/-- Auxiliary floor-modulo lemma: for `1 ≤ b` and `0 ≤ t`,
`⌊b^L * fract(b^r * t)⌋₊ = ⌊b^(r + L) * t⌋₊ % b^L`. -/
private lemma natFloor_pow_mul_fract_pow {b r L : ℕ} (hb : 1 ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    ⌊(b : ℝ) ^ L * Int.fract ((b : ℝ) ^ r * t)⌋₊ = ⌊(b : ℝ) ^ (r + L) * t⌋₊ % b ^ L := by
  have hbL_pos : 0 < b ^ L := pow_pos (by omega) L
  have hbL_r : (0 : ℝ) < (b : ℝ) ^ L := by exact_mod_cast hbL_pos
  have hbr_nn : (0 : ℝ) ≤ (b : ℝ) ^ r * t := mul_nonneg (pow_nonneg (Nat.cast_nonneg b) r) ht
  set q : ℕ := ⌊(b : ℝ) ^ r * t⌋₊
  set w : ℕ := ⌊(b : ℝ) ^ L * Int.fract ((b : ℝ) ^ r * t)⌋₊
  have hq_cast : (q : ℝ) = (⌊(b : ℝ) ^ r * t⌋ : ℝ) := by
    have : (q : ℤ) = ⌊(b : ℝ) ^ r * t⌋ := Int.natCast_floor_eq_floor hbr_nn
    exact_mod_cast this
  have hsplit : (b : ℝ) ^ (r + L) * t =
      ((b ^ L * q : ℕ) : ℝ) + (b : ℝ) ^ L * Int.fract ((b : ℝ) ^ r * t) := by
    have hf := Int.fract_add_floor ((b : ℝ) ^ r * t)
    rw [← hq_cast] at hf
    push_cast
    rw [pow_add]
    linear_combination (b : ℝ) ^ L * hf.symm
  have hw_nn : 0 ≤ (b : ℝ) ^ L * Int.fract ((b : ℝ) ^ r * t) :=
    mul_nonneg hbL_r.le (Int.fract_nonneg _)
  have hw_le : (w : ℝ) ≤ (b : ℝ) ^ L * Int.fract ((b : ℝ) ^ r * t) := Nat.floor_le hw_nn
  have hw_lt1 : (b : ℝ) ^ L * Int.fract ((b : ℝ) ^ r * t) < (w : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hw_lt : w < b ^ L := by
    rw [Nat.floor_lt hw_nn]
    calc (b : ℝ) ^ L * Int.fract ((b : ℝ) ^ r * t)
        < (b : ℝ) ^ L * 1 := mul_lt_mul_of_pos_left (Int.fract_lt_one _) hbL_r
      _ = ((b ^ L : ℕ) : ℝ) := by push_cast; ring
  have hfl_eq : ⌊(b : ℝ) ^ (r + L) * t⌋₊ = b ^ L * q + w := by
    rw [Nat.floor_eq_iff (mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) ht), hsplit]
    push_cast
    exact ⟨by linarith, by linarith⟩
  rw [hfl_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hw_lt]

/-- Finite-sum `Tendsto` helper. -/
private lemma tendsto_finset_sum'' {ι α : Type*} {f : ι → α → ℝ} {l : Filter α}
    (s : Finset ι) {a : ι → ℝ} (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) l (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tendsto_const_nhds]
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- **Sub-track B4, Theorem 4.1(1) (exact cross-radix order implication):**
for `b ≥ 2`, `k ≥ 2`, and `L₂ ≥ 1`, every real that is `L₂`-normal in base `b^k` is
automatically `(k * (L₂ - 1) + 1)`-normal in base `b`. -/
theorem orderNormal_of_pow_orderNormal {b k L₂ : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) (hL₂ : 1 ≤ L₂)
    {x : ℝ} (hx : OrderNormal (b ^ k) L₂ x) :
    OrderNormal b (k * (L₂ - 1) + 1) x := by
  classical
  set L : ℕ := k * (L₂ - 1) + 1
  have hk_pos : 0 < k := by omega
  have hk_rpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hb_rpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hbL_pos : 0 < b ^ L := pow_pos (by omega) L
  have hbL_rpos : (0 : ℝ) < (b : ℝ) ^ L := by exact_mod_cast hbL_pos
  intro w hw
  -- Phase-`r` base-`b` word extraction from the base-`b^k` length-`L₂` word.
  have hphase_eq : ∀ r < k, ∀ m : ℕ,
      ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ =
        (⌊((b ^ k : ℕ) : ℝ) ^ L₂ * shift (b ^ k) x m⌋₊ / b ^ (k * L₂ - (r + L))) % b ^ L := by
    intro r hr m
    set s : ℕ := k * L₂ - (r + L)
    have hrLs : (r + L) + s = k * L₂ := by
      have : r + L ≤ k * L₂ := by
        have hkL : k * (L₂ - 1) + k = k * L₂ := by
          cases L₂ with
          | zero => omega
          | succ t => simp [Nat.mul_succ]
        dsimp only [L]; omega
      omega
    have hshift_km : shift (b ^ k) x m = shift b x (k * m) := by
      unfold shift; push_cast; rw [← pow_mul]
    have hshift_r : shift b x (k * m + r) = Int.fract ((b : ℝ) ^ r * shift b x (k * m)) := by
      unfold shift
      have hf := Int.fract_add_floor ((b : ℝ) ^ (k * m) * x)
      have hrew : (b : ℝ) ^ (k * m + r) * x =
          (b : ℝ) ^ r * Int.fract ((b : ℝ) ^ (k * m) * x) +
            (((b : ℤ) ^ r * ⌊(b : ℝ) ^ (k * m) * x⌋ : ℤ) : ℝ) := by
        push_cast
        rw [pow_add]
        linear_combination (b : ℝ) ^ r * hf.symm
      rw [hrew, Int.fract_add_intCast]
    have hpow_cast : ((b ^ k : ℕ) : ℝ) ^ L₂ = (b : ℝ) ^ (k * L₂) := by
      push_cast; rw [← pow_mul]
    rw [hshift_r, natFloor_pow_mul_fract_pow (by omega) (show 0 ≤ shift b x (k * m) from Int.fract_nonneg _),
      hshift_km, hpow_cast, ← hrLs, natFloor_pow_add_div' (by omega) (show 0 ≤ shift b x (k * m) from Int.fract_nonneg _)]
  -- For each phase `r < k`, the phase-`r` count splits as a disjoint union of `b^(k L₂ - L)` words.
  have hphase_count : ∀ r < k, ∀ M : ℕ,
      ((range M).filter fun m => ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ = w).card =
        ∑ pq ∈ range (b ^ r) ×ˢ range (b ^ (k * L₂ - (r + L))),
          wordCount (b ^ k) L₂ x ((pq.1 * b ^ L + w) * b ^ (k * L₂ - (r + L)) + pq.2) M := by
    intro r hr M
    set s : ℕ := k * L₂ - (r + L)
    have hrLs : (r + L) + s = k * L₂ := by
      have : r + L ≤ k * L₂ := by
        have hkL : k * (L₂ - 1) + k = k * L₂ := by
          cases L₂ with
          | zero => omega
          | succ t => simp [Nat.mul_succ]
        dsimp only [L]; omega
      omega
    have hbs_pos : 0 < b ^ s := pow_pos (by omega) s
    unfold wordCount
    rw [← Finset.card_biUnion]
    · congr 1
      ext m
      simp only [mem_biUnion, mem_product, mem_filter, mem_range]
      constructor
      · rintro ⟨hm, heq⟩
        rw [hphase_eq r hr m] at heq
        set V : ℕ := ⌊((b ^ k : ℕ) : ℝ) ^ L₂ * shift (b ^ k) x m⌋₊
        have hV_lt : V < b ^ (k * L₂) := by
          dsimp only [V]
          have hnn : 0 ≤ ((b ^ k : ℕ) : ℝ) ^ L₂ * shift (b ^ k) x m :=
            mul_nonneg (by positivity) (show 0 ≤ shift (b ^ k) x m from Int.fract_nonneg _)
          rw [Nat.floor_lt hnn]
          have hpow_r : ((b ^ k : ℕ) : ℝ) ^ L₂ = ((b ^ (k * L₂) : ℕ) : ℝ) := by
            push_cast; rw [← pow_mul]
          rw [hpow_r]
          calc ((b ^ (k * L₂) : ℕ) : ℝ) * shift (b ^ k) x m
              < ((b ^ (k * L₂) : ℕ) : ℝ) * 1 :=
                mul_lt_mul_of_pos_left (show shift (b ^ k) x m < 1 from Int.fract_lt_one _)
                  (by exact_mod_cast pow_pos (show 0 < b by omega) (k * L₂))
            _ = ((b ^ (k * L₂) : ℕ) : ℝ) := mul_one _
        have hVdiv_lt : V / b ^ s < b ^ (r + L) := by
          rw [Nat.div_lt_iff_lt_mul hbs_pos, ← pow_add, hrLs]
          exact hV_lt
        set p : ℕ := (V / b ^ s) / b ^ L
        set q : ℕ := V % b ^ s
        have hp_lt : p < b ^ r := by
          dsimp only [p]
          rw [Nat.div_lt_iff_lt_mul hbL_pos, ← pow_add]
          exact hVdiv_lt
        have hq_lt : q < b ^ s := Nat.mod_lt V hbs_pos
        refine ⟨(p, q), ⟨hp_lt, hq_lt⟩, hm, ?_⟩
        have h1 : p * b ^ L + w = V / b ^ s := by
          dsimp only [p]
          rw [← heq, mul_comm (V / b ^ s / b ^ L) (b ^ L)]
          exact Nat.div_add_mod (V / b ^ s) (b ^ L)
        rw [h1, mul_comm (V / b ^ s) (b ^ s)]
        exact (Nat.div_add_mod V (b ^ s)).symm
      · rintro ⟨⟨p, q⟩, ⟨_, hq_lt⟩, hm, hV_eq⟩
        refine ⟨hm, ?_⟩
        rw [hphase_eq r hr m, hV_eq]
        rw [mul_comm (p * b ^ L + w) (b ^ s), Nat.mul_add_div hbs_pos,
          Nat.div_eq_of_lt hq_lt, add_zero, mul_comm p (b ^ L), Nat.mul_add_mod,
          Nat.mod_eq_of_lt hw]
    · intro pq₁ hpq₁ pq₂ hpq₂ hne
      simp only [Finset.mem_coe, mem_product, mem_range] at hpq₁ hpq₂
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro m h1 h2
      have e1 := (mem_filter.mp h1).2
      have e2 := (mem_filter.mp h2).2
      have heq : (pq₁.1 * b ^ L + w) * b ^ s + pq₁.2 = (pq₂.1 * b ^ L + w) * b ^ s + pq₂.2 :=
        e1.symm.trans e2
      have hq_eq : pq₁.2 = pq₂.2 := by
        have h1' := congrArg (· % b ^ s) heq
        rw [mul_comm _ (b ^ s), Nat.mul_add_mod, Nat.mod_eq_of_lt hpq₁.2,
          mul_comm _ (b ^ s), Nat.mul_add_mod, Nat.mod_eq_of_lt hpq₂.2] at h1'
        exact h1'
      have hp_eq : pq₁.1 = pq₂.1 := by
        have h1' : (pq₁.1 * b ^ L + w) * b ^ s = (pq₂.1 * b ^ L + w) * b ^ s := by omega
        have h2' : pq₁.1 * b ^ L + w = pq₂.1 * b ^ L + w := Nat.eq_of_mul_eq_mul_right hbs_pos h1'
        have h3' : pq₁.1 * b ^ L = pq₂.1 * b ^ L := by omega
        exact Nat.eq_of_mul_eq_mul_right hbL_pos h3'
      exact hne (Prod.ext hp_eq hq_eq)
  -- Each phase frequency converges to `1 / b^L`.
  have hphase_tend : ∀ r < k,
      Tendsto (fun M =>
        (((range M).filter fun m => ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ = w).card : ℝ) / (M : ℝ))
        atTop (𝓝 (1 / (b : ℝ) ^ L)) := by
    intro r hr
    set s : ℕ := k * L₂ - (r + L)
    have hrLs : (r + L) + s = k * L₂ := by
      have : r + L ≤ k * L₂ := by
        have hkL : k * (L₂ - 1) + k = k * L₂ := by
          cases L₂ with
          | zero => omega
          | succ t => simp [Nat.mul_succ]
        dsimp only [L]; omega
      omega
    have hfun_eq : (fun M =>
        (((range M).filter fun m => ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ = w).card : ℝ) / (M : ℝ)) =
        fun M => ∑ pq ∈ range (b ^ r) ×ˢ range (b ^ s),
          wordFreq (b ^ k) L₂ x ((pq.1 * b ^ L + w) * b ^ s + pq.2) M := by
      funext M
      rw [hphase_count r hr M, Nat.cast_sum, Finset.sum_div]
      rfl
    rw [hfun_eq]
    have hsum_tend : Tendsto (fun M => ∑ pq ∈ range (b ^ r) ×ˢ range (b ^ s),
        wordFreq (b ^ k) L₂ x ((pq.1 * b ^ L + w) * b ^ s + pq.2) M)
        atTop (𝓝 (∑ _pq ∈ range (b ^ r) ×ˢ range (b ^ s), (1 / ((b ^ k : ℕ) : ℝ) ^ L₂))) := by
      refine tendsto_finset_sum'' _ fun pq hpq => ?_
      simp only [mem_product, mem_range] at hpq
      have hval_lt : (pq.1 * b ^ L + w) * b ^ s + pq.2 < (b ^ k) ^ L₂ := by
        have h1 : pq.1 * b ^ L + w < b ^ (r + L) := by
          have hle : (pq.1 + 1) * b ^ L ≤ b ^ r * b ^ L := Nat.mul_le_mul_right (b ^ L) hpq.1
          rw [← pow_add] at hle
          nlinarith
        have h2 : (pq.1 * b ^ L + w + 1) * b ^ s ≤ b ^ (r + L) * b ^ s :=
          Nat.mul_le_mul_right (b ^ s) h1
        rw [← pow_add, hrLs, pow_mul] at h2
        nlinarith [hpq.2]
      exact hx _ hval_lt
    have hlim_eq : ∑ _pq ∈ range (b ^ r) ×ˢ range (b ^ s), (1 / ((b ^ k : ℕ) : ℝ) ^ L₂) =
        1 / (b : ℝ) ^ L := by
      rw [Finset.sum_const, Finset.card_product, card_range, card_range, nsmul_eq_mul]
      push_cast
      rw [← pow_mul, ← hrLs, pow_add, pow_add]
      have hbr_ne : (b : ℝ) ^ r ≠ 0 := (pow_pos hb_rpos r).ne'
      have hbs_ne : (b : ℝ) ^ s ≠ 0 := (pow_pos hb_rpos s).ne'
      field_simp [hbr_ne, hbs_ne, hbL_rpos.ne']
    rwa [hlim_eq] at hsum_tend
  -- Combine all `k` phases at multiples `k * M`.
  have hcount_mul : ∀ M : ℕ,
      wordCount b L x w (k * M) =
        ∑ r ∈ range k, ((range M).filter fun m => ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ = w).card := by
    intro M
    unfold wordCount
    have hbiu : (range (k * M)).filter (fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = w) =
        (range k).biUnion fun r =>
          ((range M).filter fun m => ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ = w).image
            (fun m => k * m + r) := by
      ext n
      simp only [mem_filter, mem_range, mem_biUnion, mem_image]
      constructor
      · rintro ⟨hn, hw'⟩
        refine ⟨n % k, Nat.mod_lt n hk_pos, n / k, ⟨?_, ?_⟩, Nat.div_add_mod n k⟩
        · exact (Nat.div_lt_iff_lt_mul hk_pos).mpr (by rw [mul_comm]; exact hn)
        · rwa [Nat.div_add_mod n k]
      · rintro ⟨r, hr, m, ⟨hm, hw'⟩, rfl⟩
        refine ⟨?_, hw'⟩
        calc k * m + r < k * m + k := by omega
          _ = k * (m + 1) := by ring
          _ ≤ k * M := Nat.mul_le_mul_left k hm
    rw [hbiu, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun r _ => ?_
      exact Finset.card_image_of_injective _ (fun m₁ m₂ heq =>
        Nat.eq_of_mul_eq_mul_left hk_pos (by omega))
    · intro r₁ hr₁ r₂ hr₂ hne
      have hr₁' : r₁ < k := mem_range.mp hr₁
      have hr₂' : r₂ < k := mem_range.mp hr₂
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n h1 h2
      obtain ⟨m₁, _, rfl⟩ := mem_image.mp h1
      obtain ⟨m₂, _, heq⟩ := mem_image.mp h2
      have hmod := congrArg (· % k) heq
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr₂', Nat.mul_add_mod, Nat.mod_eq_of_lt hr₁'] at hmod
      exact hne hmod.symm
  have hfreq_mul_tend : Tendsto (fun M => wordFreq b L x w (k * M)) atTop (𝓝 (1 / (b : ℝ) ^ L)) := by
    have hrew : (fun M => wordFreq b L x w (k * M)) =
        fun M => (1 / (k : ℝ)) * ∑ r ∈ range k,
          (((range M).filter fun m => ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ = w).card : ℝ) / (M : ℝ) := by
      funext M
      unfold wordFreq
      rw [hcount_mul M, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [hrew]
    have hsum : Tendsto (fun M => ∑ r ∈ range k,
        (((range M).filter fun m => ⌊(b : ℝ) ^ L * shift b x (k * m + r)⌋₊ = w).card : ℝ) / (M : ℝ))
        atTop (𝓝 (∑ _r ∈ range k, (1 / (b : ℝ) ^ L))) :=
      tendsto_finset_sum'' (range k) fun r hr => hphase_tend r (mem_range.mp hr)
    have hscaled := hsum.const_mul (1 / (k : ℝ))
    have hlim : (1 / (k : ℝ)) * (∑ _r ∈ range k, (1 / (b : ℝ) ^ L)) = 1 / (b : ℝ) ^ L := by
      rw [Finset.sum_const, card_range, nsmul_eq_mul]
      field_simp [hk_rpos.ne']
    rwa [hlim] at hscaled
  -- Pass from multiples `k * (N / k)` to arbitrary `N`.
  have hdiv_top : Tendsto (fun N : ℕ => N / k) atTop atTop :=
    tendsto_atTop_atTop.mpr fun B => ⟨k * B, fun N hN =>
      (Nat.le_div_iff_mul_le hk_pos).mpr (by rw [mul_comm]; exact hN)⟩
  have hmain_tend : Tendsto (fun N => wordFreq b L x w (k * (N / k))) atTop (𝓝 (1 / (b : ℝ) ^ L)) :=
    hfreq_mul_tend.comp hdiv_top
  have hinv_tend : Tendsto (fun N : ℕ => (k : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (k : ℝ))).div_atTop tendsto_natCast_atTop_atTop
  have hratio_tend : Tendsto (fun N : ℕ => ((k * (N / k) : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have hsub_tend : Tendsto (fun N : ℕ => 1 - ((k * (N / k) : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hinv_tend
      · filter_upwards [eventually_ge_atTop 1] with N hN
        have hle : k * (N / k) ≤ N := Nat.mul_div_le N k
        have hle_r : ((k * (N / k) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
        have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        have : ((k * (N / k) : ℕ) : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN_pos).mpr hle_r
        linarith
      · filter_upwards [eventually_ge_atTop 1] with N hN
        have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        have hmod : N - k * (N / k) = N % k := by
          have := Nat.div_add_mod N k; omega
        have hrem_le : N - k * (N / k) ≤ k := by
          rw [hmod]; exact (Nat.mod_lt N hk_pos).le
        have hrem_r : (N : ℝ) - ((k * (N / k) : ℕ) : ℝ) ≤ (k : ℝ) := by
          have h1 : ((N - k * (N / k) : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrem_le
          rwa [Nat.cast_sub (Nat.mul_div_le N k)] at h1
        have hrew : 1 - ((k * (N / k) : ℕ) : ℝ) / (N : ℝ) =
            ((N : ℝ) - ((k * (N / k) : ℕ) : ℝ)) / (N : ℝ) := by
          field_simp [hN_pos.ne']
        rw [hrew]
        exact div_le_div_of_nonneg_right hrem_r hN_pos.le
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hsub_tend
    simpa using h1
  have htail_tend : Tendsto (fun N : ℕ =>
      ((wordCount b L x w N - wordCount b L x w (k * (N / k)) : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hinv_tend
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hle_mul : k * (N / k) ≤ N := Nat.mul_div_le N k
    have hdiff_le : wordCount b L x w N - wordCount b L x w (k * (N / k)) ≤ k := by
      unfold wordCount
      set A := (range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = w
      set B := (range (k * (N / k))).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = w
      have hBA : B ⊆ A := filter_subset_filter _ (range_mono hle_mul)
      have hsdiff : (A \ B).card = A.card - B.card := Finset.card_sdiff_of_subset hBA
      have hsub_rng : A \ B ⊆ Finset.Ico (k * (N / k)) N := by
        intro n hn
        have hnA := (mem_sdiff.mp hn).1
        have hnB := (mem_sdiff.mp hn).2
        have hnr := mem_range.mp (mem_filter.mp hnA).1
        have hnw := (mem_filter.mp hnA).2
        refine Finset.mem_Ico.mpr ⟨?_, hnr⟩
        by_contra hlt
        exact hnB (mem_filter.mpr ⟨mem_range.mpr (by omega), hnw⟩)
      have hcard_le : (A \ B).card ≤ N - k * (N / k) := by
        calc (A \ B).card ≤ (Finset.Ico (k * (N / k)) N).card := card_le_card hsub_rng
          _ = N - k * (N / k) := Nat.card_Ico _ _
      have hmod : N - k * (N / k) = N % k := by have := Nat.div_add_mod N k; omega
      have hmod_le : N % k ≤ k := (Nat.mod_lt N hk_pos).le
      omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hdiff_le) hN_pos.le
  have hcomb : Tendsto (fun N : ℕ =>
      wordFreq b L x w (k * (N / k)) * (((k * (N / k) : ℕ) : ℝ) / (N : ℝ)) +
        ((wordCount b L x w N - wordCount b L x w (k * (N / k)) : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 (1 / (b : ℝ) ^ L)) := by
    have h := (hmain_tend.mul hratio_tend).add htail_tend
    simpa using h
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  have hM_pos : 0 < N / k := Nat.div_pos hN hk_pos
  have hkM_ne : ((k * (N / k) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hk_pos hM_pos).ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hle_cnt : wordCount b L x w (k * (N / k)) ≤ wordCount b L x w N :=
    card_le_card (filter_subset_filter _ (range_mono (Nat.mul_div_le N k)))
  unfold wordFreq
  rw [Nat.cast_sub hle_cnt]
  field_simp [hkM_ne, hN_ne]
  ring

/-! ### Section 5: Sub-track D3 — Badly-approximable convergent gap for bounded partial quotients -/

/-- **Sub-track D3 (§3 unimodular best-approximation inequality):**
if `(p_i, q_i)` and `(p_{i+1}, q_{i+1})` form a unimodular pair (`p_{i+1} q_i - p_i q_{i+1} = ±1`)
whose approximation errors `q_i x - p_i` and `q_{i+1} x - p_{i+1}` have opposite signs, then every
integer pair `(h, q)` with `1 ≤ q_i ≤ q < q_{i+1}` satisfies `|q x - h| ≥ |q_i x - p_i|`. -/
theorem unimodular_best_approx {p₁ p₂ : ℤ} {q₁ q₂ q : ℕ} {x : ℝ}
    (hq₁ : 1 ≤ q₁) (hq_lo : q₁ ≤ q) (hq_hi : q < q₂)
    (hdet : p₂ * (q₁ : ℤ) - p₁ * (q₂ : ℤ) = 1 ∨ p₂ * (q₁ : ℤ) - p₁ * (q₂ : ℤ) = -1)
    (hopp : ((q₁ : ℝ) * x - (p₁ : ℝ)) * ((q₂ : ℝ) * x - (p₂ : ℝ)) ≤ 0) (h : ℤ) :
    |(q₁ : ℝ) * x - (p₁ : ℝ)| ≤ |(q : ℝ) * x - (h : ℝ)| := by
  set s : ℤ := p₂ * (q₁ : ℤ) - p₁ * (q₂ : ℤ)
  have hs2 : s * s = 1 := by rcases hdet with h1 | h1 <;> rw [h1] <;> norm_num
  set u : ℤ := s * (p₂ * (q : ℤ) - (q₂ : ℤ) * h)
  set v : ℤ := s * ((q₁ : ℤ) * h - p₁ * (q : ℤ))
  have hlin_h : u * p₁ + v * p₂ = h := by
    have hrew : u * p₁ + v * p₂ = (s * s) * h := by dsimp only [u, v, s]; ring
    rw [hrew, hs2, one_mul]
  have hlin_q : u * (q₁ : ℤ) + v * (q₂ : ℤ) = (q : ℤ) := by
    have hrew : u * (q₁ : ℤ) + v * (q₂ : ℤ) = (s * s) * (q : ℤ) := by dsimp only [u, v, s]; ring
    rw [hrew, hs2, one_mul]
  set e₁ : ℝ := (q₁ : ℝ) * x - (p₁ : ℝ)
  set e₂ : ℝ := (q₂ : ℝ) * x - (p₂ : ℝ)
  have herr : (q : ℝ) * x - (h : ℝ) = (u : ℝ) * e₁ + (v : ℝ) * e₂ := by
    have hh_r : (u : ℝ) * (p₁ : ℝ) + (v : ℝ) * (p₂ : ℝ) = (h : ℝ) := by exact_mod_cast hlin_h
    have hq_r : (u : ℝ) * (q₁ : ℝ) + (v : ℝ) * (q₂ : ℝ) = (q : ℝ) := by exact_mod_cast hlin_q
    dsimp only [e₁, e₂]
    linear_combination hq_r.symm * x - hh_r.symm
  rw [herr]
  by_cases hv : v = 0
  · rw [hv, Int.cast_zero, zero_mul, add_zero, abs_mul]
    have hu_pos : 1 ≤ u := by
      have : u * (q₁ : ℤ) = (q : ℤ) := by simpa [hv] using hlin_q
      have hq1_z : (1 : ℤ) ≤ (q₁ : ℤ) := by exact_mod_cast hq₁
      have hq_z : (q₁ : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq_lo
      nlinarith
    have hu_r : (1 : ℝ) ≤ |(u : ℝ)| := by
      have : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu_pos
      exact this.trans (le_abs_self _)
    calc |e₁| = 1 * |e₁| := (one_mul _).symm
      _ ≤ |(u : ℝ)| * |e₁| := mul_le_mul_of_nonneg_right hu_r (abs_nonneg e₁)
  · have hu_ne : u ≠ 0 := by
      intro hu0
      have hqv : v * (q₂ : ℤ) = (q : ℤ) := by simpa [hu0] using hlin_q
      have hq_pos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (show 0 < q by omega)
      have hq_lt : (q : ℤ) < (q₂ : ℤ) := by exact_mod_cast hq_hi
      have hv_pos : 1 ≤ v := by nlinarith
      nlinarith
    have huv_neg : u * v ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have hq1_z : (1 : ℤ) ≤ (q₁ : ℤ) := by exact_mod_cast hq₁
      have hq_pos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (show 0 < q by omega)
      have hq_lt : (q : ℤ) < (q₂ : ℤ) := by exact_mod_cast hq_hi
      rcases lt_or_gt_of_ne hu_ne with hu_lt | hu_gt
      · have hv_lt : v ≤ -1 := by nlinarith
        have hu_le : u ≤ -1 := by omega
        nlinarith
      · have hv_ge : 1 ≤ v := by nlinarith
        have hu_ge : 1 ≤ u := by omega
        nlinarith
    have hprod_nn : 0 ≤ ((u : ℝ) * e₁) * ((v : ℝ) * e₂) := by
      have huv_r : (u : ℝ) * (v : ℝ) ≤ 0 := by exact_mod_cast huv_neg
      have hrew : ((u : ℝ) * e₁) * ((v : ℝ) * e₂) = ((u : ℝ) * (v : ℝ)) * (e₁ * e₂) := by ring
      rw [hrew]
      exact mul_nonneg_of_nonpos_of_nonpos huv_r hopp
    have habs_add : |(u : ℝ) * e₁| ≤ |(u : ℝ) * e₁ + (v : ℝ) * e₂| := by
      have hsq : |(u : ℝ) * e₁| ^ 2 ≤ |(u : ℝ) * e₁ + (v : ℝ) * e₂| ^ 2 := by
        rw [sq_abs, sq_abs]
        nlinarith [sq_nonneg ((v : ℝ) * e₂)]
      nlinarith [abs_nonneg ((u : ℝ) * e₁), abs_nonneg ((u : ℝ) * e₁ + (v : ℝ) * e₂)]
    have hu_r : (1 : ℝ) ≤ |(u : ℝ)| := by exact_mod_cast Int.one_le_abs hu_ne
    calc |e₁| = 1 * |e₁| := (one_mul _).symm
      _ ≤ |(u : ℝ)| * |e₁| := mul_le_mul_of_nonneg_right hu_r (abs_nonneg e₁)
      _ = |(u : ℝ) * e₁| := (abs_mul _ _).symm
      _ ≤ |(u : ℝ) * e₁ + (v : ℝ) * e₂| := habs_add

/-- Continued-fraction convergent numerators for `[0; a 0, a 1, ...]` indexed with
`cfNum a 0 = 1` (`p_{-1}`), `cfNum a 1 = 0` (`p_0`), `cfNum a (n + 2) = a n * cfNum a (n + 1) + cfNum a n`. -/
def cfNum (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => a n * cfNum a (n + 1) + cfNum a n

/-- Continued-fraction convergent denominators for `[0; a 0, a 1, ...]` indexed with
`cfDen a 0 = 0` (`q_{-1}`), `cfDen a 1 = 1` (`q_0`), `cfDen a (n + 2) = a n * cfDen a (n + 1) + cfDen a n`. -/
def cfDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a n * cfDen a (n + 1) + cfDen a n

/-- Exact continued-fraction unimodular determinant identity:
`p_{n+1} q_n - p_n q_{n+1} = (-1)^(n + 1)`. -/
theorem cf_det (a : ℕ → ℕ) (n : ℕ) :
    (cfNum a (n + 1) : ℤ) * (cfDen a n : ℤ) - (cfNum a n : ℤ) * (cfDen a (n + 1) : ℤ) =
      (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero => simp [cfNum, cfDen]
  | succ k ih =>
    simp only [cfNum, cfDen]
    push_cast
    rw [pow_succ]
    linear_combination -ih

theorem cfDen_pos {a : ℕ → ℕ} (ha : ∀ n, 1 ≤ a n) : ∀ n, 1 ≤ cfDen a (n + 1)
  | 0 => by simp [cfDen]
  | n + 1 => by
    simp only [cfDen]
    have h1 := cfDen_pos ha n
    have h2 := ha n
    nlinarith

theorem cfDen_le_succ {a : ℕ → ℕ} (ha : ∀ n, 1 ≤ a n) : ∀ n, cfDen a n ≤ cfDen a (n + 1)
  | 0 => by simp [cfDen]
  | 1 => by simp [cfDen]; exact ha 0
  | n + 2 => by
    change cfDen a (n + 2) ≤ a (n + 1) * cfDen a (n + 2) + cfDen a (n + 1)
    have h1 := ha (n + 1)
    nlinarith

theorem cfDen_ge_index {a : ℕ → ℕ} (ha : ∀ n, 1 ≤ a n) : ∀ n, n ≤ cfDen a (n + 1)
  | 0 => by simp [cfDen]
  | 1 => by simp [cfDen]; exact ha 0
  | n + 2 => by
    change n + 2 ≤ a (n + 1) * cfDen a (n + 2) + cfDen a (n + 1)
    have h1 := cfDen_ge_index ha (n + 1)
    have h2 := cfDen_pos ha n
    have h3 := ha (n + 1)
    nlinarith

/-- Complete-quotient representation: if `x = 1 / α 0` and `α n = a n + 1 / α (n + 1)`
with `1 ≤ a n` and `α n > 0` for all `n`, then
`x = (α n * p_{n+1} + p_n) / (α n * q_{n+1} + q_n)`. -/
theorem cf_complete_quotient_eq {a : ℕ → ℕ} {α : ℕ → ℝ} {x : ℝ}
    (ha : ∀ n, 1 ≤ a n) (hα_pos : ∀ n, 0 < α n)
    (hα_rec : ∀ n, α n = (a n : ℝ) + 1 / α (n + 1)) (hx : x = 1 / α 0) (n : ℕ) :
    x = (α n * (cfNum a (n + 1) : ℝ) + (cfNum a n : ℝ)) /
        (α n * (cfDen a (n + 1) : ℝ) + (cfDen a n : ℝ)) := by
  induction n with
  | zero =>
    simp [cfNum, cfDen, hx]
  | succ k ih =>
    rw [ih, hα_rec k]
    have hαk1_ne : α (k + 1) ≠ 0 := (hα_pos (k + 1)).ne'
    have hden1 : (((a k : ℝ) + 1 / α (k + 1)) * (cfDen a (k + 1) : ℝ) + (cfDen a k : ℝ)) ≠ 0 := by
      have hpos : 0 < α k := hα_pos k
      rw [hα_rec k] at hpos
      have hq_nn : 0 ≤ (cfDen a k : ℝ) := Nat.cast_nonneg _
      have hq1_pos : (0 : ℝ) < (cfDen a (k + 1) : ℝ) := by exact_mod_cast cfDen_pos ha k
      nlinarith
    change (((a k : ℝ) + 1 / α (k + 1)) * (cfNum a (k + 1) : ℝ) + (cfNum a k : ℝ)) /
        (((a k : ℝ) + 1 / α (k + 1)) * (cfDen a (k + 1) : ℝ) + (cfDen a k : ℝ)) =
      (α (k + 1) * ((a k * cfNum a (k + 1) + cfNum a k : ℕ) : ℝ) + (cfNum a (k + 1) : ℝ)) /
        (α (k + 1) * ((a k * cfDen a (k + 1) + cfDen a k : ℕ) : ℝ) + (cfDen a (k + 1) : ℝ))
    push_cast
    have hden2 : (α (k + 1) * ((a k : ℝ) * (cfDen a (k + 1) : ℝ) + (cfDen a k : ℝ)) +
        (cfDen a (k + 1) : ℝ)) ≠ 0 := by
      have hmul : α (k + 1) * (((a k : ℝ) + 1 / α (k + 1)) * (cfDen a (k + 1) : ℝ) +
          (cfDen a k : ℝ)) =
          α (k + 1) * ((a k : ℝ) * (cfDen a (k + 1) : ℝ) + (cfDen a k : ℝ)) +
          (cfDen a (k + 1) : ℝ) := by
        field_simp [hαk1_ne]; ring
      rw [← hmul]
      exact mul_ne_zero hαk1_ne hden1
    rw [div_eq_div_iff hden1 hden2]
    field_simp [hαk1_ne]
    ring

/-- Exact signed convergent error identity:
`q_{n+1} * x - p_{n+1} = (-1)^n / (α n * q_{n+1} + q_n)`. -/
theorem cf_approx_error {a : ℕ → ℕ} {α : ℕ → ℝ} {x : ℝ}
    (ha : ∀ n, 1 ≤ a n) (hα_pos : ∀ n, 0 < α n)
    (hα_rec : ∀ n, α n = (a n : ℝ) + 1 / α (n + 1)) (hx : x = 1 / α 0) (n : ℕ) :
    (cfDen a (n + 1) : ℝ) * x - (cfNum a (n + 1) : ℝ) =
      (-1 : ℝ) ^ n / (α n * (cfDen a (n + 1) : ℝ) + (cfDen a n : ℝ)) := by
  have hq1_pos : (0 : ℝ) < (cfDen a (n + 1) : ℝ) := by exact_mod_cast cfDen_pos ha n
  have hden_pos : 0 < α n * (cfDen a (n + 1) : ℝ) + (cfDen a n : ℝ) := by
    have : 0 ≤ (cfDen a n : ℝ) := Nat.cast_nonneg _
    nlinarith [hα_pos n]
  have hden_ne : α n * (cfDen a (n + 1) : ℝ) + (cfDen a n : ℝ) ≠ 0 := hden_pos.ne'
  have hdet_r : (cfNum a (n + 1) : ℝ) * (cfDen a n : ℝ) -
      (cfNum a n : ℝ) * (cfDen a (n + 1) : ℝ) = (-1 : ℝ) ^ (n + 1) := by
    exact_mod_cast cf_det a n
  rw [cf_complete_quotient_eq ha hα_pos hα_rec hx n, eq_div_iff hden_ne, sub_mul, mul_assoc,
    div_mul_cancel₀ _ hden_ne]
  rw [pow_succ] at hdet_r
  linear_combination -hdet_r

/-- Exact convergent gap identity (`nonlinear-boundaries-and-approximation.md`, §3):
`q_{n+1} |q_{n+1} x - p_{n+1}| = 1 / (α n + q_n / q_{n+1})`. -/
theorem cf_convergent_gap {a : ℕ → ℕ} {α : ℕ → ℝ} {x : ℝ}
    (ha : ∀ n, 1 ≤ a n) (hα_pos : ∀ n, 0 < α n)
    (hα_rec : ∀ n, α n = (a n : ℝ) + 1 / α (n + 1)) (hx : x = 1 / α 0) (n : ℕ) :
    (cfDen a (n + 1) : ℝ) * |(cfDen a (n + 1) : ℝ) * x - (cfNum a (n + 1) : ℝ)| =
      1 / (α n + (cfDen a n : ℝ) / (cfDen a (n + 1) : ℝ)) := by
  have hq1_pos : (0 : ℝ) < (cfDen a (n + 1) : ℝ) := by exact_mod_cast cfDen_pos ha n
  have hden_pos : 0 < α n * (cfDen a (n + 1) : ℝ) + (cfDen a n : ℝ) := by
    have : 0 ≤ (cfDen a n : ℝ) := Nat.cast_nonneg _
    nlinarith [hα_pos n]
  have hden2_pos : 0 < α n + (cfDen a n : ℝ) / (cfDen a (n + 1) : ℝ) := by
    have : 0 ≤ (cfDen a n : ℝ) / (cfDen a (n + 1) : ℝ) := by positivity
    linarith [hα_pos n]
  rw [cf_approx_error ha hα_pos hα_rec hx n, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos hden_pos]
  field_simp [hq1_pos.ne', hden_pos.ne', hden2_pos.ne']

/-- **Sub-track D3 (§3 general bounded-partial-quotient gap):**
if `x = [0; a 0, a 1, ...]` has partial quotients `1 ≤ a n ≤ A`, then for every integer `q ≥ 1`
and every `h : ℤ`, `1 / (A + 2) < q * |q * x - h|` and `1 / (A + 2) < q * circDist (q * x)`. -/
theorem cf_badly_approx_bound {a : ℕ → ℕ} {α : ℕ → ℝ} {x : ℝ} {A : ℕ}
    (ha_lo : ∀ n, 1 ≤ a n) (ha_hi : ∀ n, a n ≤ A)
    (hα_pos : ∀ n, 0 < α n) (hα_rec : ∀ n, α n = (a n : ℝ) + 1 / α (n + 1))
    (hx : x = 1 / α 0) {q : ℕ} (hq : 1 ≤ q) :
    (∀ h : ℤ, 1 / ((A : ℝ) + 2) < (q : ℝ) * |(q : ℝ) * x - (h : ℝ)|) ∧
      1 / ((A : ℝ) + 2) < (q : ℝ) * circDist ((q : ℝ) * x) := by
  -- Select the largest index `n₀` with `cfDen a (n₀ + 1) ≤ q`.
  let S : Finset ℕ := (range (q + 2)).filter fun n => cfDen a (n + 1) ≤ q
  have h0_mem : 0 ∈ S := by
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
    simpa [cfDen] using hq
  have hS_ne : S.Nonempty := ⟨0, h0_mem⟩
  set n₀ : ℕ := S.max' hS_ne
  have hn₀_mem : n₀ ∈ S := Finset.max'_mem S hS_ne
  have hq_lo : cfDen a (n₀ + 1) ≤ q := (mem_filter.mp hn₀_mem).2
  have hn₀_lt : n₀ < q + 1 := by
    have hle_q1 : n₀ ≤ q := (cfDen_ge_index ha_lo n₀).trans hq_lo
    omega
  have hq_hi : q < cfDen a (n₀ + 2) := by
    by_contra hle
    push Not at hle
    have hmem : n₀ + 1 ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), hle⟩
    have := Finset.le_max' S (n₀ + 1) hmem
    omega
  -- Verify unimodularity and opposite signs for `(p_{n₀+1}, q_{n₀+1})` and `(p_{n₀+2}, q_{n₀+2})`.
  have hdet : (cfNum a (n₀ + 2) : ℤ) * (cfDen a (n₀ + 1) : ℤ) -
      (cfNum a (n₀ + 1) : ℤ) * (cfDen a (n₀ + 2) : ℤ) = 1 ∨
      (cfNum a (n₀ + 2) : ℤ) * (cfDen a (n₀ + 1) : ℤ) -
      (cfNum a (n₀ + 1) : ℤ) * (cfDen a (n₀ + 2) : ℤ) = -1 := by
    rw [cf_det a (n₀ + 1)]
    rcases Nat.even_or_odd (n₀ + 2) with ⟨k, hk⟩ | ⟨k, hk⟩
    · left; rw [hk, ← two_mul, pow_mul]; norm_num
    · right; rw [hk, pow_succ, pow_mul]; norm_num
  have hden0_pos : 0 < α n₀ * (cfDen a (n₀ + 1) : ℝ) + (cfDen a n₀ : ℝ) := by
    have : 0 ≤ (cfDen a n₀ : ℝ) := Nat.cast_nonneg _
    have hq1 : (0 : ℝ) < (cfDen a (n₀ + 1) : ℝ) := by exact_mod_cast cfDen_pos ha_lo n₀
    nlinarith [hα_pos n₀]
  have hden1_pos : 0 < α (n₀ + 1) * (cfDen a (n₀ + 2) : ℝ) + (cfDen a (n₀ + 1) : ℝ) := by
    have : 0 ≤ (cfDen a (n₀ + 1) : ℝ) := Nat.cast_nonneg _
    have hq2 : (0 : ℝ) < (cfDen a (n₀ + 2) : ℝ) := by exact_mod_cast cfDen_pos ha_lo (n₀ + 1)
    nlinarith [hα_pos (n₀ + 1)]
  have hopp : ((cfDen a (n₀ + 1) : ℝ) * x - (cfNum a (n₀ + 1) : ℝ)) *
      ((cfDen a (n₀ + 2) : ℝ) * x - (cfNum a (n₀ + 2) : ℝ)) ≤ 0 := by
    rw [cf_approx_error ha_lo hα_pos hα_rec hx n₀,
      cf_approx_error ha_lo hα_pos hα_rec hx (n₀ + 1), div_mul_div_comm]
    have hnum : (-1 : ℝ) ^ n₀ * (-1 : ℝ) ^ (n₀ + 1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hnum]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_pos hden0_pos hden1_pos).le
  -- Bound the convergent gap from below by `1 / (A + 2)`.
  have hα_lt : α n₀ < (A : ℝ) + 1 := by
    have hα_next_gt : 1 < α (n₀ + 1) := by
      have ha1 : (1 : ℝ) ≤ (a (n₀ + 1) : ℝ) := by exact_mod_cast ha_lo (n₀ + 1)
      have hinv_pos : 0 < 1 / α (n₀ + 2) := div_pos one_pos (hα_pos (n₀ + 2))
      rw [hα_rec (n₀ + 1)]
      linarith
    have hinv_lt1 : 1 / α (n₀ + 1) < 1 := (div_lt_one (hα_pos (n₀ + 1))).mpr hα_next_gt
    have ha_le : (a n₀ : ℝ) ≤ (A : ℝ) := by exact_mod_cast ha_hi n₀
    rw [hα_rec n₀]
    linarith
  have hratio_le : (cfDen a n₀ : ℝ) / (cfDen a (n₀ + 1) : ℝ) ≤ 1 := by
    have hq1_pos : (0 : ℝ) < (cfDen a (n₀ + 1) : ℝ) := by exact_mod_cast cfDen_pos ha_lo n₀
    exact (div_le_one hq1_pos).mpr (by exact_mod_cast cfDen_le_succ ha_lo n₀)
  have hgap_gt : 1 / ((A : ℝ) + 2) <
      (cfDen a (n₀ + 1) : ℝ) * |(cfDen a (n₀ + 1) : ℝ) * x - (cfNum a (n₀ + 1) : ℝ)| := by
    rw [cf_convergent_gap ha_lo hα_pos hα_rec hx n₀]
    have hsum_pos : 0 < α n₀ + (cfDen a n₀ : ℝ) / (cfDen a (n₀ + 1) : ℝ) := by
      have : 0 ≤ (cfDen a n₀ : ℝ) / (cfDen a (n₀ + 1) : ℝ) := by positivity
      linarith [hα_pos n₀]
    exact one_div_lt_one_div_of_lt hsum_pos (by linarith)
  have hfor_all : ∀ h : ℤ, 1 / ((A : ℝ) + 2) < (q : ℝ) * |(q : ℝ) * x - (h : ℝ)| := by
    intro h
    have hbest := unimodular_best_approx (cfDen_pos ha_lo n₀) hq_lo hq_hi hdet hopp h
    have hq_le_r : (cfDen a (n₀ + 1) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_lo
    have hmul_le :
        (cfDen a (n₀ + 1) : ℝ) * |(cfDen a (n₀ + 1) : ℝ) * x - (cfNum a (n₀ + 1) : ℝ)| ≤
        (q : ℝ) * |(q : ℝ) * x - (h : ℝ)| :=
      mul_le_mul hq_le_r hbest (abs_nonneg _) (Nat.cast_nonneg q)
    exact hgap_gt.trans_le hmul_le
  refine ⟨hfor_all, ?_⟩
  obtain ⟨z, hz⟩ := exists_int_abs_sub_eq_circDist ((q : ℝ) * x)
  rw [← hz]
  exact hfor_all z

/-- **Sub-track D3 (§3 `{1, 2}`-continued-fraction bad-approximation bound):**
every continued fraction `x = [0; a 0, a 1, ...]` with partial quotients `a n ∈ {1, 2}`
satisfies `q * |q * x - h| > 1 / 4` and `q * ‖q * x‖ > 1 / 4` for every `q ≥ 1` and `h : ℤ`. -/
theorem cf_one_two_badly_approx {a : ℕ → ℕ} {α : ℕ → ℝ} {x : ℝ}
    (ha : ∀ n, a n = 1 ∨ a n = 2)
    (hα_pos : ∀ n, 0 < α n) (hα_rec : ∀ n, α n = (a n : ℝ) + 1 / α (n + 1))
    (hx : x = 1 / α 0) {q : ℕ} (hq : 1 ≤ q) :
    (∀ h : ℤ, (1 : ℝ) / 4 < (q : ℝ) * |(q : ℝ) * x - (h : ℝ)|) ∧
      (1 : ℝ) / 4 < (q : ℝ) * circDist ((q : ℝ) * x) := by
  have ha_lo : ∀ n, 1 ≤ a n := fun n => by rcases ha n with h | h <;> omega
  have ha_hi : ∀ n, a n ≤ 2 := fun n => by rcases ha n with h | h <;> omega
  have h := cf_badly_approx_bound ha_lo ha_hi hα_pos hα_rec hx hq
  norm_num at h
  exact h

end NormalityChecker.Phase24Cores
