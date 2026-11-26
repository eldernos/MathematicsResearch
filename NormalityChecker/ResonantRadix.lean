module

public import NormalityChecker.ResonantRadixSeries
public import NormalityChecker.ParameterTwoQuadratic
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

/-! Identification of the Taylor series with the slope, intercept and actual
quadratic phase. The identity `exp(2x)-1-2x = 2x(F(2x)-F(x))` makes the
series defining the intercept telescope. -/
@[expose] public noncomputable section
open NormedSpace Filter Finset
open scoped NNReal ENNReal Topology
open NormalityChecker.ParameterTwoQuadratic
namespace NormalityChecker.ResonantRadix

private lemma mem_quarter {x : ℚ_[2]} : x ∈ quarterBall ↔ ‖x‖ ≤ 1/4 := by
  simp [Metric.mem_closedBall, dist_zero_right]

private lemma factorial_bound (n : ℕ) :
    ‖((n.factorial : ℚ_[2]))⁻¹‖ = (2 : ℝ)^(multiplicity 2 n.factorial) := by
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), Padic.valuation_natCast]
  simp

private lemma exp_coeff_bound (n : ℕ) : ‖(((n+2).factorial : ℚ_[2]))⁻¹‖ ≤ (2 : ℝ)^(n+1) := by
  rw [factorial_bound]
  have h := multiplicity_factorial_lt_of_ne_zero 2 (n := n+2) (by omega)
  exact pow_le_pow_right₀ (by norm_num) (by omega)

private lemma within_radius {x : ℚ_[2]} (hx : x ∈ quarterBall) :
    x ∈ Metric.eball 0 (expSeries ℚ_[2] ℚ_[2]).radius := by
  have hr : ((1/2 : ℝ≥0) : ℝ≥0∞) ≤ (expSeries ℚ_[2] ℚ_[2]).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ 1
    intro n
    simp only [expSeries, norm_smul, ContinuousMultilinearMap.norm_mkPiAlgebraFin,
      mul_one, factorial_bound, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    calc
      _ ≤ (2 : ℝ)^n * (1/2 : ℝ)^n := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num)
          (multiplicity_factorial_le 2 n)) (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  apply lt_of_lt_of_le _ hr
  rw [edist_dist, dist_zero_right, ENNReal.ofReal_lt_coe_iff (norm_nonneg _)]
  exact (mem_quarter.mp hx).trans_lt (by norm_num)

private lemma exp_tail {x : ℚ_[2]} (hx : x ∈ quarterBall) :
    HasSum (fun n : ℕ => x^(n+2) / (n+2).factorial) (exp x - 1 - x) := by
  have h := (hasSum_nat_add_iff' 2).mpr (expSeries_div_hasSum_exp_of_mem_ball ℚ_[2] x
    (within_radius hx))
  simpa [sum_range_succ, sub_sub] using h

private lemma exp_sub_one {x : ℚ_[2]} (hx : x ∈ quarterBall) :
    exp x - 1 = tangentSeries (fun n => ((n+2).factorial : ℚ_[2])⁻¹) x := by
  have h := (exp_tail hx).tsum_eq
  simp only [div_eq_mul_inv, mul_comm (x^_) _] at h
  unfold tangentSeries
  rw [h]
  abel

theorem exp_isometry {x y : ℚ_[2]} (hx : x ∈ quarterBall) (hy : y ∈ quarterBall) :
    ‖exp x - exp y‖ = ‖x-y‖ := by
  simpa only [← exp_sub_one hx, ← exp_sub_one hy, sub_sub_sub_cancel_right] using
    tangent_isometry exp_coeff_bound hx hy

theorem exp_sub_one_bijOn : Set.BijOn (fun x : ℚ_[2] => exp x - 1) quarterBall quarterBall :=
  (tangent_bijOn exp_coeff_bound).congr fun _ hx => (exp_sub_one hx).symm

theorem phase_hasSum {x : ℚ_[2]} (hx : x ∈ quarterBall) :
    HasSum (fun n : ℕ => (coeff (n+1) : ℚ_[2]) * x^(n+1)) (phaseSeries x) := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa [phaseSeries, tangentSeries, add_comm x, add_assoc] using
    (tangent_summable (c := fun n => (coeff (n+2) : ℚ_[2]))
      (fun n => (coeff_norm_le_one (by omega)).trans (one_le_pow₀ (by norm_num))) hx).hasSum

private lemma scaled_mem {x : ℚ_[2]} (hx : x ∈ quarterBall) (n : ℕ) :
    (2 : ℚ_[2])^n * x ∈ quarterBall := by
  apply mem_quarter.mpr
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
    (by rw [show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p:=2)]; norm_num))).trans
    (mem_quarter.mp hx)

/-- A Taylor identity whose sum over dyadic scales telescopes. -/
theorem phase_doubling {x : ℚ_[2]} (hx : x ∈ quarterBall) :
    exp (2*x) - 1 - 2*x = 2*x*(phaseSeries (2*x) - phaseSeries x) := by
  have h2 : 2*x ∈ quarterBall := by simpa using scaled_mem hx 1
  apply (exp_tail h2).unique
  apply (((phase_hasSum h2).sub (phase_hasSum hx)).mul_left (2*x)).congr_fun
  intro n
  have hn : 1 < (2 : ℕ)^(n+1) := Nat.one_lt_pow (by omega) (by decide)
  have ne : (2 : ℚ_[2])^(n+1) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr; exact_mod_cast hn.ne'
  simp only [coeff, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_sub, Rat.cast_one,
    Nat.cast_sub (by omega : 1 ≤ 2^(n+1)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_pow]
  field_simp [ne]
  ring

private lemma exp_dyadic {x : ℚ_[2]} (hx : x ∈ quarterBall) (n : ℕ) :
    exp (2^n*x) = (exp x)^(2^n : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have same := exp_add_of_mem_ball (within_radius (scaled_mem hx n))
      (within_radius (scaled_mem hx n))
    rw [show (2 : ℚ_[2])^(n+1)*x = 2^n*x+2^n*x by ring, same, ih, ← pow_add]
    congr 1; ring

private lemma phase_dyadic_tendsto {x : ℚ_[2]} (hx : x ∈ quarterBall) :
    Tendsto (fun j : ℕ => phaseSeries (2^j*x)) atTop (𝓝 0) := by
  have hz : (0 : ℚ_[2]) ∈ quarterBall := mem_quarter.mpr (by norm_num)
  have eqn (j : ℕ) : ‖phaseSeries (2^j*x)‖ = ‖(2 : ℚ_[2])^j*x‖ := by
    simpa [phaseSeries, tangent_zero] using phase_isometry (scaled_mem hx j) hz
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [eqn]
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (show ‖(2 : ℚ_[2])‖ < 1 by
    rw [show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p:=2)]; norm_num)).mul_const x

/-- The exponential of the parameter may be either sign of the inverse radix.
The square formulation eliminates this sign from every positive Stoneham index. -/
theorem slope_and_kappa {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) {x : ℚ_[2]} (hx : x ∈ quarterBall)
    (hexp : (exp x)^2 = ((b : ℚ_[2])⁻¹)^2) :
    slope b = x ∧ kappa b 1 (-2) + 1 = phaseSeries x := by
  let f (j : ℕ) := phaseSeries (2^j*x)
  have difference (j : ℕ) : delta b j - x = x*(f (j+1) - f j) := by
    have invpow : exp (2^(j+1)*x) = ((b : ℚ_[2])^(2^(j+1) : ℕ))⁻¹ := by
      rw [exp_dyadic hx, pow_succ' (2 : ℕ), pow_mul, hexp, ← pow_mul, inv_pow]
    have h := phase_doubling (scaled_mem hx j)
    rw [show (2 : ℚ_[2])*(2^j*x) = 2^(j+1)*x by ring, invpow] at h
    unfold delta
    dsimp [f]
    apply (sub_eq_iff_eq_add).mpr
    apply (div_eq_iff (pow_ne_zero (j+1) (by norm_num : (2 : ℚ_[2]) ≠ 0))).mpr
    linear_combination h
  have lim := phase_dyadic_tendsto hx
  have shifted := lim.comp (tendsto_add_atTop_nat 1)
  have dl : Tendsto (fun j => delta b j - x) atTop (𝓝 0) := by
    simp_rw [difference]
    simpa [f] using (shifted.sub lim).const_mul x
  have sl := tendsto_nhds_unique (delta_tendsto hb odd) (tendsto_sub_nhds_zero_iff.mp dl)
  have summ : Summable fun j => delta b j - x := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num)).mul_right (‖delta b 0‖^2)) fun j => ?_
    simpa [← sl] using delta_error_le hb odd j
  have correction : HasSum (fun j => delta b j - x) (-(x * phaseSeries x)) := by
    apply summ.hasSum_iff_tendsto_nat.mpr
    simp_rw [difference, ← mul_sum, sum_range_sub]
    simpa [f] using (lim.sub_const (f 0)).const_mul x
  have nz : x ≠ 0 := by
    rw [← sl, ← norm_ne_zero_iff, slope_norm hb odd, norm_ne_zero_iff]
    exact delta_zero_ne hb
  refine ⟨sl, ?_⟩
  rw [kappa, intercept, sl, correction.tsum_eq]
  push_cast
  field_simp
  ring

/-- The sign representative of an odd integer radix that is 1 modulo 4. -/
def signedRadix (b : ℕ) : ℚ_[2] := if b % 4 = 1 then (b : ℚ_[2]) else -b

private lemma signedRadix_mem {b : ℕ} (odd : Odd b) : signedRadix b - 1 ∈ quarterBall := by
  have h4 : ‖(4 : ℚ_[2])‖ = 1/4 := by
    rw [show (4 : ℚ_[2]) = 2^2 by norm_num, norm_pow,
      show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p:=2)]; norm_num
  have bound (a : ℤ) : ‖(4 : ℚ_[2])*a‖ ≤ 1/4 := by
    rw [norm_mul, h4]
    simpa using mul_le_mul_of_nonneg_left (Padic.norm_int_le_one (p:=2) a)
      (show 0 ≤ (1/4 : ℝ) by norm_num)
  apply mem_quarter.mpr
  obtain ⟨d, hd⟩ := odd
  have multiple : ∃ a : ℤ, (if b % 4 = 1 then (b : ℤ) else -b) - 1 = 4*a := by
    split_ifs
    · exact ⟨(b/4 : ℕ), by omega⟩
    · exact ⟨-((b/4 : ℕ) : ℤ)-1, by omega⟩
  obtain ⟨a, ha⟩ := multiple
  have hcast := congrArg (fun z : ℤ => (z : ℚ_[2])) ha
  have eqn : signedRadix b - 1 = 4 * (a : ℚ_[2]) := by
    unfold signedRadix
    split_ifs at hcast ⊢ <;> push_cast at hcast <;> exact hcast
  rw [eqn]
  exact bound a

private lemma neg_mem {x : ℚ_[2]} (hx : x ∈ quarterBall) : -x ∈ quarterBall :=
  mem_quarter.mpr (by simpa using mem_quarter.mp hx)

/-- The actual arithmetic slope is the logarithm of the inverse signed radix. -/
theorem radix_parameter {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    slope b ∈ quarterBall ∧ exp (-slope b) = signedRadix b ∧
    kappa b 1 (-2) + 1 = phaseSeries (slope b) := by
  obtain ⟨y, hy, h⟩ := exp_sub_one_bijOn.surjOn (signedRadix_mem odd)
  have ey : exp y = signedRadix b := by linear_combination h
  have sqr : (exp (-y))^2 = ((b : ℚ_[2])⁻¹)^2 := by
    rw [exp_neg_of_mem_ball ℚ_[2] (within_radius hy), ey, signedRadix]
    split_ifs <;> simp
  obtain ⟨hs, hk⟩ := slope_and_kappa hb odd (neg_mem hy) sqr
  exact ⟨hs ▸ neg_mem hy, by simpa [hs] using ey, hs.symm ▸ hk⟩

/-- Distances of the actual phases equal distances of the sign-normalized radices. -/
theorem radix_isometry {b d : ℕ} (hb : 3 ≤ b) (ob : Odd b) (hd : 3 ≤ d) (od : Odd d) :
    ‖kappa b 1 (-2) - kappa d 1 (-2)‖ = ‖signedRadix b - signedRadix d‖ := by
  obtain ⟨mb, eb, kb⟩ := radix_parameter hb ob
  obtain ⟨md, ed, kd⟩ := radix_parameter hd od
  rw [← eb, ← ed, exp_isometry (neg_mem mb) (neg_mem md)]
  calc
    _ = ‖phaseSeries (slope b) - phaseSeries (slope d)‖ := by rw [← kb, ← kd]; abel_nf
    _ = _ := by rw [phase_isometry mb md, neg_sub_neg, norm_sub_rev]

/-- For any integral target in the logarithmic ball, one normalized centre
represents all distances of that target from the shifted arithmetic phases. -/
theorem radix_center {z : ℚ_[2]} (hz : z ∈ quarterBall) :
    ∃ u : ℚ_[2], u - 1 ∈ quarterBall ∧ ‖u - 1‖ = ‖z‖ ∧
      ∀ {b : ℕ}, 3 ≤ b → Odd b → ‖kappa b 1 (-2) + 1 - z‖ = ‖signedRadix b - u‖ := by
  obtain ⟨x, hx, rfl⟩ := phase_bijOn.surjOn hz
  have h0 : (0 : ℚ_[2]) ∈ quarterBall := mem_quarter.mpr (by norm_num)
  refine ⟨exp (-x), exp_sub_one_bijOn.mapsTo (neg_mem hx), ?_, ?_⟩
  · have he := exp_isometry (neg_mem hx) h0
    have hf := phase_isometry hx h0
    simpa [phaseSeries] using he.trans (by simpa [phaseSeries] using hf.symm)
  · intro b hb odd
    obtain ⟨mb, eb, kb⟩ := radix_parameter hb odd
    rw [kb, phase_isometry mb hx, ← eb, exp_isometry (neg_mem mb) (neg_mem hx),
      neg_sub_neg, norm_sub_rev]

/-- If `k+1` lies in 4ℤ₂, one normalized centre controls the denominator
at every integer radix throughout the upper half of shell `k=j+1`. -/
theorem upper_denominator_radix_center (j : ℕ) (hz : ((j+1 : ℕ) : ℚ_[2]) + 1 ∈ quarterBall) :
    ∃ u : ℚ_[2], u - 1 ∈ quarterBall ∧ ‖u - 1‖ = ‖((j+1 : ℕ) : ℚ_[2]) + 1‖ ∧
      ∀ {b n : ℕ}, 3 ≤ b → Odd b → 3*2^j ≤ n → n < 2^(j+2) →
        ((«prefix» b n 1 (-2) 0).den : ℝ) =
          max 1 ((2 : ℝ)^(j+1) * ‖2 * slope b‖ * ‖signedRadix b - u‖) := by
  obtain ⟨u, hu, hn, dist⟩ := radix_center hz
  refine ⟨u, hu, hn, fun hb odd mid hi => ?_⟩
  rw [upper_denominator hb odd mid hi 1 (-2) 0 (by decide), ← dist hb odd]
  simp only [Int.cast_one, mul_one, norm_mul, add_sub_add_right_eq_sub]
  rw [norm_sub_rev (kappa _ _ _)]
  ring_nf

end NormalityChecker.ResonantRadix
