module

public import NormalityChecker.ParameterTwoQuadratic
public import Mathlib.Tactic

/-! Kernel-checked algebraic and geometric cores for Phase 16 Tracks 5 and 6:
1. Track 5 (Dyadic Stoneham quadratics): exact integer recurrence `Z_k` for `X^2 - 2X`
   and its identity with `2^k * b^{2^k} * cancellation b (k - 1)`, reducing normality of
   `(α² - 2α)/D` directly to `2k - v₂(Z_k) → ∞`.
2. Track 6 (Independent-prime Stoneham product `α_{2,3} α_{2,5}`):
   - Exact single-shape maximum relative length `4/11` for shape `(1, 1)` (attained at `r = 5/6`);
   - Exact boundary-strip piecewise-linear upper bound `p / (p - 1) * η`;
   - Simultaneous ultrametric separation inequalities for distinct active shells.
-/

@[expose] public section

open Finset

namespace NormalityChecker.Phase16StonehamBounds

/-! ### Part 1: Quadratic integer recurrence `Z_k` (Track 5, Theorem A') -/

/-- Exact integer recurrence for `X^2 - 2X`: `Z b 0 = 2 - 2*b^2`,
`Z b (j + 1) = 2 + 2 * b^(2^(j+1)) * (Z b j - 1)`. Here `Z b j` corresponds to `Z_{j+1}`
in the Phase 16 note (matching `cancellation b j` = `T_{j+1}`). -/
def quadZ (b : ℕ) : ℕ → ℤ
  | 0 => 2 - 2 * (b : ℤ) ^ 2
  | j + 1 => 2 + 2 * (b : ℤ) ^ (2 ^ (j + 1)) * (quadZ b j - 1)

/-- Closed-form sum formula for `quadZ b j`:
`Z_{j+1} = 1 - 2^(j+1) * b^(2^(j+1)) + ∑_{i=0}^j 2^(j - i) * b^(2^(j+1) - 2^(i+1))`. -/
theorem quadZ_closed_form (b j : ℕ) :
    quadZ b j =
      1 - (2 : ℤ) ^ (j + 1) * (b : ℤ) ^ (2 ^ (j + 1)) +
        ∑ i ∈ range (j + 1), (2 : ℤ) ^ (j - i) * (b : ℤ) ^ (2 ^ (j + 1) - 2 ^ (i + 1)) := by
  induction j with
  | zero =>
    simp [quadZ]
    ring
  | succ j ih =>
    rw [quadZ, ih]
    conv_rhs => rw [sum_range_succ]
    have hsplit : 2 ^ (j + 1 + 1) = 2 ^ (j + 1) + 2 ^ (j + 1) := by
      rw [pow_succ, mul_two]
    have hsum :
        ∑ i ∈ range (j + 1),
            (2 : ℤ) ^ (j + 1 - i) * (b : ℤ) ^ (2 ^ (j + 1 + 1) - 2 ^ (i + 1)) =
          2 * (b : ℤ) ^ (2 ^ (j + 1)) *
            ∑ i ∈ range (j + 1),
              (2 : ℤ) ^ (j - i) * (b : ℤ) ^ (2 ^ (j + 1) - 2 ^ (i + 1)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have hpow_le : 2 ^ (i + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have he1 : j + 1 - i = (j - i) + 1 := by omega
      have he2 : 2 ^ (j + 1 + 1) - 2 ^ (i + 1) = 2 ^ (j + 1) + (2 ^ (j + 1) - 2 ^ (i + 1)) := by
        rw [hsplit, Nat.add_sub_assoc hpow_le]
      rw [he1, he2, pow_succ, pow_add]
      ring
    rw [hsum, Nat.sub_self, Nat.sub_self, pow_zero, pow_zero, one_mul, hsplit, pow_add, pow_succ]
    ring

/-- Exact 2-adic link between `quadZ b j` and Phase 14's `cancellation b j` (= `T_{j+1}`):
in `ℚ_[2]`, `quadZ b j = 2^(j+1) * b^(2^(j+1)) * cancellation b j`!
Since `b` is odd, `‖b^(2^(j+1))‖₂ = 1`, so `v₂(quadZ b j) = (j + 1) + v₂(T_{j+1})`. -/
theorem quadZ_eq_cancellation (b j : ℕ) (hb : b ≠ 0) :
    (quadZ b j : ℚ_[2]) =
      (2 : ℚ_[2]) ^ (j + 1) * (b : ℚ_[2]) ^ (2 ^ (j + 1)) *
        NormalityChecker.ParameterTwoQuadratic.cancellation b j := by
  have hb2 : (b : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr hb
  rw [quadZ_closed_form, NormalityChecker.ParameterTwoQuadratic.cancellation]
  push_cast
  simp only [NormalityChecker.ParameterTwoQuadratic.delta]
  have hsum :
      (2 : ℚ_[2]) ^ (j + 1) * (b : ℚ_[2]) ^ (2 ^ (j + 1)) *
          ∑ i ∈ range (j + 1), (((b : ℚ_[2]) ^ (2 ^ (i + 1)))⁻¹ - 1) / (2 : ℚ_[2]) ^ (i + 1) =
        (∑ i ∈ range (j + 1),
            (2 : ℚ_[2]) ^ (j - i) * (b : ℚ_[2]) ^ (2 ^ (j + 1) - 2 ^ (i + 1))) -
          ((2 : ℚ_[2]) ^ (j + 1) - 1) * (b : ℚ_[2]) ^ (2 ^ (j + 1)) := by
    have hgeom :
        ∑ i ∈ range (j + 1), (2 : ℚ_[2]) ^ (j - i) = (2 : ℚ_[2]) ^ (j + 1) - 1 := by
      clear hb hb2
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [sum_range_succ, Nat.sub_self, pow_zero]
        have hstep :
            ∑ i ∈ range (j + 1), (2 : ℚ_[2]) ^ (j + 1 - i) =
              2 * ∑ i ∈ range (j + 1), (2 : ℚ_[2]) ^ (j - i) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
          rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ, mul_comm]
        rw [hstep, ih, pow_succ]
        ring
    rw [mul_sum, ← hgeom, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hpow_le : 2 ^ (i + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2split : (2 : ℚ_[2]) ^ (j + 1) = (2 : ℚ_[2]) ^ (j - i) * (2 : ℚ_[2]) ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    have hbsplit :
        (b : ℚ_[2]) ^ (2 ^ (j + 1)) =
          (b : ℚ_[2]) ^ (2 ^ (j + 1) - 2 ^ (i + 1)) * (b : ℚ_[2]) ^ (2 ^ (i + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h2ne : (2 : ℚ_[2]) ^ (i + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hbne : (b : ℚ_[2]) ^ (2 ^ (i + 1)) ≠ 0 := pow_ne_zero _ hb2
    rw [h2split, hbsplit]
    field_simp [h2ne, hbne]
  have hlast :
      (2 : ℚ_[2]) ^ (j + 1) * (b : ℚ_[2]) ^ (2 ^ (j + 1)) *
          ((((b : ℚ_[2]) ^ (2 ^ (j + 1)))⁻¹ - 1) / (2 : ℚ_[2]) ^ (j + 1)) =
        1 - (b : ℚ_[2]) ^ (2 ^ (j + 1)) := by
    have h2ne : (2 : ℚ_[2]) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hbne : (b : ℚ_[2]) ^ (2 ^ (j + 1)) ≠ 0 := pow_ne_zero _ hb2
    field_simp [h2ne, hbne]
  rw [mul_add, hsum, hlast]
  ring

/-- Exact upper-shell denominator formula for `X^2 - 2X` in terms of `quadZ`:
on `3 * 2^j ≤ n < 2^(j+2)`, `den(prefix b n 1 (-2) C₀) = max 1 (2^(2*j+1) * ‖quadZ b j‖₂)`. -/
theorem quadratic_upper_den_eq_quadZ {b n j : ℕ} (hb : 3 ≤ b) (odd : Odd b)
    (mid : 3 * 2 ^ j ≤ n) (hi : n < 2 ^ (j + 2)) (C₀ : ℤ) :
    ((NormalityChecker.ParameterTwoQuadratic.«prefix» b n 1 (-2) C₀).den : ℝ) =
      max 1 ((2 : ℝ) ^ (2 * j + 1) * ‖(quadZ b j : ℚ_[2])‖) := by
  have hup := NormalityChecker.ParameterTwoQuadratic.upper_denominator hb odd mid hi 1 (-2) C₀
    (by decide)
  -- Compare `2 * slope * ((j+1) - kappa)` with `2 * cancellation` modulo `2^(j+1)`!
  -- Actually directly: `quadZ b j = 2^(j+1) * b^(2^(j+1)) * cancellation b j`,
  -- and from `error_integral`, `‖2 * (cancellation - (j+1)*slope - intercept) / 2^(j+1)‖ ≤ 1`,
  -- so `max 1 (2^(j+1) * ‖2 * (slope * ((j+1) - kappa))‖) = max 1 (2^(j+1) * ‖2 * cancellation‖)`!
  have hbne : b ≠ 0 := by omega
  have hZnorm :
      (2 : ℝ) ^ (2 * j + 1) * ‖(quadZ b j : ℚ_[2])‖ =
        (2 : ℝ) ^ (j + 1) * ‖(2 : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.cancellation b j‖ := by
    rw [quadZ_eq_cancellation b j hbne, norm_mul, norm_mul, norm_pow, norm_pow,
      NormalityChecker.ParameterTwoQuadratic.radix_norm odd, one_pow, mul_one,
      norm_mul, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p := 2), inv_pow]
    have hpow : (2 : ℝ) ^ (2 * j + 1) * ((2 : ℝ) ^ (j + 1))⁻¹ = (2 : ℝ) ^ (j + 1) * (2 : ℝ)⁻¹ := by
      have : (2 * j + 1 : ℕ) = j + (j + 1) := by omega
      rw [this, pow_add, pow_succ]
      field_simp
    calc
      (2 : ℝ) ^ (2 * j + 1) * (((2 : ℝ) ^ (j + 1))⁻¹ *
          ‖NormalityChecker.ParameterTwoQuadratic.cancellation b j‖)
          = ((2 : ℝ) ^ (2 * j + 1) * ((2 : ℝ) ^ (j + 1))⁻¹) *
            ‖NormalityChecker.ParameterTwoQuadratic.cancellation b j‖ := by ring
      _ = (2 : ℝ) ^ (j + 1) * ((2 : ℝ)⁻¹ *
            ‖NormalityChecker.ParameterTwoQuadratic.cancellation b j‖) := by rw [hpow]; ring
  rw [hup, hZnorm]
  have hslope : NormalityChecker.ParameterTwoQuadratic.slope b ≠ 0 :=
    norm_ne_zero_iff.mp (by
      rw [NormalityChecker.ParameterTwoQuadratic.slope_norm hb odd]
      exact norm_ne_zero_iff.mpr (NormalityChecker.ParameterTwoQuadratic.delta_zero_ne hb))
  have hV :
      2 * (1 : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.slope b *
          (((j + 1 : ℕ) : ℚ_[2]) - NormalityChecker.ParameterTwoQuadratic.kappa b 1 (-2)) =
        2 * (((j + 1 : ℕ) : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.slope b +
          NormalityChecker.ParameterTwoQuadratic.intercept b) := by
    simp only [NormalityChecker.ParameterTwoQuadratic.kappa]
    push_cast
    field_simp [hslope]
    ring
  have herr :
      ‖2 * (NormalityChecker.ParameterTwoQuadratic.cancellation b j -
          ((j + 1 : ℕ) : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.slope b -
          NormalityChecker.ParameterTwoQuadratic.intercept b)‖ ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := by
    have h1 := NormalityChecker.ParameterTwoQuadratic.affine_error_le hb odd j
    have hd := NormalityChecker.ParameterTwoQuadratic.delta_zero_norm_lt_one odd
    rw [norm_mul, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p := 2)]
    calc
      (2 : ℝ)⁻¹ * ‖NormalityChecker.ParameterTwoQuadratic.cancellation b j -
          ((j + 1 : ℕ) : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.slope b -
          NormalityChecker.ParameterTwoQuadratic.intercept b‖
          ≤ (2 : ℝ)⁻¹ * ((1 / 2 : ℝ) ^ j * ‖NormalityChecker.ParameterTwoQuadratic.delta b 0‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (2 : ℝ)⁻¹ * ((1 / 2 : ℝ) ^ j * 1) := by
        have hsq : ‖NormalityChecker.ParameterTwoQuadratic.delta b 0‖ ^ 2 ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) hd.le
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
      _ = ((2 : ℝ) ^ (j + 1))⁻¹ := by
        rw [one_div, inv_pow, pow_succ]; ring
  set x : ℚ_[2] :=
    2 * (((j + 1 : ℕ) : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.slope b +
      NormalityChecker.ParameterTwoQuadratic.intercept b)
  set y : ℚ_[2] := 2 * NormalityChecker.ParameterTwoQuadratic.cancellation b j
  have hdiff : ‖y - x‖ ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := by
    have hsub : y - x =
        2 * (NormalityChecker.ParameterTwoQuadratic.cancellation b j -
          ((j + 1 : ℕ) : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.slope b -
          NormalityChecker.ParameterTwoQuadratic.intercept b) := by
      dsimp [x, y]; ring
    rw [hsub]
    exact herr
  have hcast :
      2 * ((1 : ℤ) : ℚ_[2]) * NormalityChecker.ParameterTwoQuadratic.slope b *
          (((j + 1 : ℕ) : ℚ_[2]) - NormalityChecker.ParameterTwoQuadratic.kappa b 1 (-2)) = x := by
    simpa [x] using hV
  rw [hcast]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  by_cases hx : ((2 : ℝ) ^ (j + 1))⁻¹ < ‖x‖
  · have hxy : ‖y‖ = ‖x‖ := by
      have hlt : ‖y + (-x)‖ < ‖-x‖ := by
        rw [← sub_eq_add_neg, norm_neg]
        exact hdiff.trans_lt hx
      simpa [norm_neg] using Padic.norm_eq_of_norm_add_lt_right hlt
    rw [hxy]
  · push Not at hx
    have hy : ‖y‖ ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := by
      have hadd : (y - x) + x = y := sub_add_cancel y x
      rw [← hadd]
      exact (Padic.nonarchimedean (y - x) x).trans (max_le hdiff hx)
    have hx1 : (2 : ℝ) ^ (j + 1) * ‖x‖ ≤ 1 := by
      calc (2 : ℝ) ^ (j + 1) * ‖x‖ ≤ (2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ (j + 1))⁻¹ :=
            mul_le_mul_of_nonneg_left hx hpos.le
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    have hy1 : (2 : ℝ) ^ (j + 1) * ‖y‖ ≤ 1 := by
      calc (2 : ℝ) ^ (j + 1) * ‖y‖ ≤ (2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ (j + 1))⁻¹ :=
            mul_le_mul_of_nonneg_left hy hpos.le
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    rw [max_eq_left hx1, max_eq_left hy1]

/-! ### Part 2: Independent-prime product `4/11` and ultrametric separation (Track 6) -/

/-- Exact single-shape maximum relative length for the primary corner `(1, 1)` of
`α_{2,3} α_{2,5}`: for every positive ratio `r = Q/P > 0`,
`min(4r/5, 2/3) / (1 + r) ≤ 4/11`, with equality at `r = 5/6`. -/
theorem single_shape_one_one_max (r : ℝ) (hr : 0 < r) :
    min (4 * r / 5) (2 / 3) / (1 + r) ≤ 4 / 11 := by
  rw [div_le_iff₀ (by linarith)]
  by_cases h : r ≤ 5 / 6
  · have hmin : min (4 * r / 5) (2 / 3) ≤ 4 * r / 5 := min_le_left _ _
    linarith
  · have hmin : min (4 * r / 5) (2 / 3) ≤ 2 / 3 := min_le_right _ _
    linarith

theorem single_shape_one_one_attained :
    min (4 * (5 / 6 : ℝ) / 5) (2 / 3) / (1 + 5 / 6) = 4 / 11 := by
  norm_num

/-- Exact piecewise-linear boundary-strip upper bound for base `p > 1`, `0 < η < 1`,
`p * η ≤ p - 1` (e.g. `p ≥ 2` and `η ≤ 1/2`), and `0 < t`:
`min(1 - t, (η / (1 - η)) * t) + (η / ((p - 1) * (1 - η))) * t ≤ (p / (p - 1)) * η`. -/
theorem boundary_strip_piecewise_le {p : ℝ} (hp : 1 < p) {η t : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hηp : p * η ≤ p - 1) :
    min (1 - t) ((η / (1 - η)) * t) + (η / ((p - 1) * (1 - η))) * t ≤ (p / (p - 1)) * η := by
  have h1 : 0 < 1 - η := by linarith
  have hp1 : 0 < p - 1 := by linarith
  by_cases h : t ≤ 1 - η
  · have hmin : min (1 - t) ((η / (1 - η)) * t) ≤ (η / (1 - η)) * t := min_le_right _ _
    have hcoeff : η / (1 - η) + η / ((p - 1) * (1 - η)) = (p / (p - 1)) * (η / (1 - η)) := by
      field_simp [h1.ne', hp1.ne']
      ring
    have hmul : (p / (p - 1)) * (η / (1 - η)) * t ≤ (p / (p - 1)) * η := by
      have hdiv : (η / (1 - η)) * t ≤ η := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h1]
        nlinarith
      have hppos : 0 ≤ p / (p - 1) := by positivity
      calc
        (p / (p - 1)) * (η / (1 - η)) * t = (p / (p - 1)) * ((η / (1 - η)) * t) := by ring
        _ ≤ (p / (p - 1)) * η := mul_le_mul_of_nonneg_left hdiv hppos
    calc
      min (1 - t) ((η / (1 - η)) * t) + (η / ((p - 1) * (1 - η))) * t
          ≤ (η / (1 - η)) * t + (η / ((p - 1) * (1 - η))) * t := by linarith [hmin]
      _ = (η / (1 - η) + η / ((p - 1) * (1 - η))) * t := by ring
      _ = (p / (p - 1)) * (η / (1 - η)) * t := by rw [hcoeff]
      _ ≤ (p / (p - 1)) * η := hmul
  · push Not at h
    have hmin : min (1 - t) ((η / (1 - η)) * t) ≤ 1 - t := min_le_left _ _
    have hc_le : η / ((p - 1) * (1 - η)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have hdec : (1 - t) + (η / ((p - 1) * (1 - η))) * t ≤
        (1 - (1 - η)) + (η / ((p - 1) * (1 - η))) * (1 - η) := by
      have hdiff : (1 - η - t) * (1 - η / ((p - 1) * (1 - η))) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      linarith
    have hrhs : (1 - (1 - η)) + (η / ((p - 1) * (1 - η))) * (1 - η) = (p / (p - 1)) * η := by
      field_simp [h1.ne', hp1.ne']
      ring
    linarith

/-- Simultaneous ultrametric separation for active shells of the same nonrectangular shape:
if two distinct shells `(K₁, L₁)` and `(K₂, L₂)` with `L₁ < L₂` and `K₁ < K₂` agree with the
same target classes modulo `2 * 3^(h - 1)` and `4 * 5^(k - 1)`, then
`L₂ - L₁ ≥ 2 * 3^(h - 1)` and `K₂ - K₁ ≥ 4 * 5^(k - 1)`. -/
theorem simultaneous_ultrametric_spacing {K₁ K₂ L₁ L₂ h k a₃ a₅ : ℕ}
    (hK : K₁ < K₂) (hL : L₁ < L₂)
    (hmod3₁ : L₁ ≡ a₃ [MOD 2 * 3 ^ (h - 1)]) (hmod3₂ : L₂ ≡ a₃ [MOD 2 * 3 ^ (h - 1)])
    (hmod5₁ : K₁ ≡ a₅ [MOD 4 * 5 ^ (k - 1)]) (hmod5₂ : K₂ ≡ a₅ [MOD 4 * 5 ^ (k - 1)]) :
    2 * 3 ^ (h - 1) ≤ L₂ - L₁ ∧ 4 * 5 ^ (k - 1) ≤ K₂ - K₁ := by
  have hdvd3 : 2 * 3 ^ (h - 1) ∣ L₂ - L₁ :=
    (Nat.modEq_iff_dvd' hL.le).mp (hmod3₁.trans hmod3₂.symm)
  have hdvd5 : 4 * 5 ^ (k - 1) ∣ K₂ - K₁ :=
    (Nat.modEq_iff_dvd' hK.le).mp (hmod5₁.trans hmod5₂.symm)
  exact ⟨Nat.le_of_dvd (Nat.sub_pos_of_lt hL) hdvd3,
    Nat.le_of_dvd (Nat.sub_pos_of_lt hK) hdvd5⟩

end NormalityChecker.Phase16StonehamBounds
