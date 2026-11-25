module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic

/-! Kernel-checked core bounds for the Phase 16 rounded Chebyshev-pole approximants to `ln 2`:
1. Exact integral denominator divisibility: for any integer polynomial `Q` of degree `< D`,
   `∑_{k < D} Q_k / (k + 1)` has reduced denominator dividing `lcm(1, ..., D)`.
2. Exact error bound for rounded pole-quotient polynomials: if `|T(x)| ≤ 1` on `[0, 1]`,
   `T(x) - T(-1) = (x + 1) P(x)`, and `Q_D` rounds `2^e P(x) / T(-1)` coefficientwise within `1/2`,
   then `|2^e ln 2 + ∫_0^1 Q_D(x) dx| ≤ (2^e / |T(-1)|) ln 2 + (1/2) ∑_{k=1}^D 1/k`.
-/

@[expose] public section

open Finset

namespace NormalityChecker.ChebyshevPoleApproximation

/-- Least common multiple of `1, 2, ..., D`. -/
def lcmRange (D : ℕ) : ℕ :=
  (range D).lcm (fun k => k + 1)

theorem lcmRange_pos (D : ℕ) : 0 < lcmRange D := by
  unfold lcmRange
  refine Nat.pos_of_ne_zero ?_
  intro h
  have h0 : ∃ k ∈ range D, k + 1 = 0 := by
    by_contra hall
    push Not at hall
    have hne : (range D).lcm (fun k => k + 1) ≠ 0 := by
      rw [Finset.lcm_ne_zero_iff]
      intro k hk
      exact hall k hk
    exact hne h
  obtain ⟨k, _, hk⟩ := h0
  omega

/-- Every `k + 1` with `k < D` divides `lcmRange D`. -/
theorem succ_dvd_lcmRange {D k : ℕ} (hk : k < D) : k + 1 ∣ lcmRange D :=
  Finset.dvd_lcm (mem_range.mpr hk)

/-- The integral `∑_{k < D} Q k / (k + 1)` of an integer polynomial of degree `< D`
has reduced denominator dividing `lcmRange D`. -/
theorem poly_integral_den_dvd_lcmRange (Q : ℕ → ℤ) (D : ℕ) :
    (∑ k ∈ range D, (Q k : ℚ) / (k + 1 : ℚ)).den ∣ lcmRange D := by
  let L := lcmRange D
  have hLpos : 0 < L := lcmRange_pos D
  let num : ℤ := ∑ k ∈ range D, Q k * ((L / (k + 1) : ℕ) : ℤ)
  have heq : (∑ k ∈ range D, (Q k : ℚ) / (k + 1 : ℚ)) = (num : ℚ) / (L : ℚ) := by
    have hLq : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hLpos.ne'
    rw [eq_div_iff hLq, sum_mul]
    simp only [num, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply sum_congr rfl
    intro k hk
    have hdvd : k + 1 ∣ L := succ_dvd_lcmRange (mem_range.mp hk)
    have hkq : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hmul : ((L / (k + 1) : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ) = (L : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    push_cast at hkq hmul ⊢
    field_simp [hkq]
    linarith [congrArg (fun t : ℚ => (Q k : ℚ) * t) hmul]
  rw [heq]
  have hd : (((num : ℚ) / ((L : ℤ) : ℚ)).den : ℤ) ∣ (L : ℤ) := by
    rw [Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd num (L : ℤ)
  exact_mod_cast hd

/-- After dividing by `2^w`, the shifted rational `Y_N = -2^{-w} ∫_0^1 Q_D(x) dx`
has reduced denominator dividing `2^w * lcmRange D`. -/
theorem shifted_poly_integral_den_dvd (Q : ℕ → ℤ) (D w : ℕ) :
    (-(∑ k ∈ range D, (Q k : ℚ) / (k + 1 : ℚ)) / (2 : ℚ) ^ w).den ∣ 2 ^ w * lcmRange D := by
  let S : ℚ := ∑ k ∈ range D, (Q k : ℚ) / (k + 1 : ℚ)
  have hS : S.den ∣ lcmRange D := poly_integral_den_dvd_lcmRange Q D
  have hneg : (-S / (2 : ℚ) ^ w) = (-S) * (1 / (2 : ℚ) ^ w) := by ring
  rw [hneg]
  have h1 : ((-S) * (1 / (2 : ℚ) ^ w)).den ∣ (-S).den * (1 / (2 : ℚ) ^ w).den :=
    Rat.mul_den_dvd _ _
  have h2 : (-S).den = S.den := Rat.neg_den S
  have h3 : (1 / (2 : ℚ) ^ w).den ∣ 2 ^ w := by
    have : (1 / (2 : ℚ) ^ w) = (((1 : ℤ) : ℚ) / ((2 ^ w : ℤ) : ℚ)) := by push_cast; rfl
    rw [this]
    have hd : ((((1 : ℤ) : ℚ) / ((2 ^ w : ℤ) : ℚ)).den : ℤ) ∣ (2 ^ w : ℤ) := by
      rw [Rat.intCast_div_eq_divInt]
      exact Rat.den_dvd 1 (2 ^ w : ℤ)
    exact_mod_cast hd
  rw [h2] at h1
  exact h1.trans (by rw [mul_comm]; exact Nat.mul_dvd_mul h3 hS)

/-- Rounding error bound on `[0, 1]`: if `|Q k - R k| ≤ 1/2` for all `k < D`, then
`|∑_{k < D} Q k / (k + 1) - ∑_{k < D} R k / (k + 1)| ≤ (1/2) ∑_{k < D} 1 / (k + 1)`. -/
theorem rounding_integral_error (Q R : ℕ → ℝ) (D : ℕ)
    (hround : ∀ k < D, |Q k - R k| ≤ (1 / 2 : ℝ)) :
    |∑ k ∈ range D, Q k / (k + 1 : ℝ) - ∑ k ∈ range D, R k / (k + 1 : ℝ)| ≤
      (1 / 2 : ℝ) * ∑ k ∈ range D, (1 : ℝ) / (k + 1 : ℝ) := by
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  apply sum_le_sum
  intro k hk
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k + 1 : ℝ))]
  have hr := hround k (mem_range.mp hk)
  have hpos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
  calc
    |Q k - R k| / (k + 1 : ℝ) ≤ (1 / 2 : ℝ) / (k + 1 : ℝ) :=
      div_le_div_of_nonneg_right hr hpos.le
    _ = (1 / 2 : ℝ) * ((1 : ℝ) / (k + 1 : ℝ)) := by ring

/-- Master error bound for the single-pole (`1/(1+x)`) rounded Chebyshev-pole approximant:
given the exact pole identity `2^e ln 2 + ∫_0^1 R_D = (2^e / T(-1)) ∫_0^1 T(x)/(1+x) dx`,
`|∫_0^1 T(x)/(1+x) dx| ≤ ln 2`, and `|Q_k - R_k| ≤ 1/2` for all `k < D`, the integer-polynomial
integral `∫_0^1 Q_D(x) dx = ∑_{k < D} Q_k / (k + 1)` approximates `-2^e ln 2` within
`(2^e / |T(-1)|) ln 2 + (1/2) H_D`. -/
theorem chebyshev_pole_master_error (e D : ℕ) (Tneg1 I_rem : ℝ) (Q R : ℕ → ℝ)
    (hT : Tneg1 ≠ 0)
    (hI : |I_rem| ≤ Real.log 2)
    (hdecomp : (2 : ℝ) ^ e * Real.log 2 + ∑ k ∈ range D, R k / (k + 1 : ℝ) =
      ((2 : ℝ) ^ e / Tneg1) * I_rem)
    (hround : ∀ k < D, |Q k - R k| ≤ (1 / 2 : ℝ)) :
    |(2 : ℝ) ^ e * Real.log 2 + ∑ k ∈ range D, Q k / (k + 1 : ℝ)| ≤
      ((2 : ℝ) ^ e / |Tneg1|) * Real.log 2 +
        (1 / 2 : ℝ) * ∑ k ∈ range D, (1 : ℝ) / (k + 1 : ℝ) := by
  have split :
      (2 : ℝ) ^ e * Real.log 2 + ∑ k ∈ range D, Q k / (k + 1 : ℝ) =
        ((2 : ℝ) ^ e * Real.log 2 + ∑ k ∈ range D, R k / (k + 1 : ℝ)) +
          (∑ k ∈ range D, Q k / (k + 1 : ℝ) - ∑ k ∈ range D, R k / (k + 1 : ℝ)) := by
    ring
  rw [split, hdecomp]
  refine (abs_add_le _ _).trans ?_
  have h1 : |((2 : ℝ) ^ e / Tneg1) * I_rem| ≤ ((2 : ℝ) ^ e / |Tneg1|) * Real.log 2 := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ e)]
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  exact add_le_add h1 (rounding_integral_error Q R D hround)

/-- Exact integral of `1/(1+x)` over `[0, 1]` equals `Real.log 2`. -/
theorem integral_inv_one_add_eq_log_two :
    ∫ x in (0 : ℝ)..1, (1 + x)⁻¹ = Real.log 2 := by
  have hcont : ContinuousOn (fun x : ℝ => (1 + x)⁻¹) (Set.uIcc 0 1) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 + x)⁻¹ x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hpos : (1 + x) ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    simpa [div_eq_mul_inv] using h1.log hpos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  norm_num

end NormalityChecker.ChebyshevPoleApproximation
