module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-! The dyadic Taylor series for the shifted phase of the Stoneham polynomial
`X² − 2X`. The closed ball of radius one quarter in ℚ₂ is 4ℤ₂. -/
@[expose] public noncomputable section
open scoped NNReal
namespace NormalityChecker.ResonantRadix

/-- Coefficient of degree `m ≥ 1` in the shifted phase. -/
def coeff (m : ℕ) : ℚ :=
  2^m / (((2^m - 1 : ℕ) : ℚ) * (m+1).factorial)

@[simp] theorem coeff_one : coeff 1 = 1 := by norm_num [coeff, Nat.factorial]

private theorem coeff_val_aux {m : ℕ} (hm : 0 < m) :
    padicValRat 2 (coeff m) = (m : ℤ) - multiplicity 2 (m+1).factorial := by
  have hpow : 1 < 2^m := Nat.one_lt_pow hm.ne' (by decide)
  have hodd : ¬ 2 ∣ 2^m - 1 := by
    have h := dvd_pow_self 2 hm.ne'
    omega
  have hn : (((2^m-1 : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (by omega : 2^m-1 ≠ 0)
  rw [coeff, padicValRat.div (by positivity) (mul_ne_zero hn (by positivity)),
    padicValRat.mul hn (by positivity), padicValRat.pow, padicValRat.of_nat,
    padicValRat.of_nat, multiplicity_eq_zero_of_not_dvd hodd]
  norm_num [show padicValRat 2 2 = 1 from padicValRat.self (by decide)]

/-- Legendre's formula gives the binary digit sum of `m+1`, less one. -/
theorem coeff_valuation {m : ℕ} (hm : 0 < m) :
    padicValRat 2 (coeff m) = (((2 : ℕ).digits (m+1)).sum : ℤ) - 1 := by
  rw [coeff_val_aux hm]
  have h := Nat.prime_two.sub_one_mul_multiplicity_factorial (n := m+1)
  simp only [Nat.reduceSub, one_mul] at h
  have := Nat.digit_sum_le 2 (m+1)
  omega

theorem coeff_norm_le_one {m : ℕ} (hm : 0 < m) : ‖(coeff m : ℚ_[2])‖ ≤ 1 := by
  rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast, coeff_val_aux hm]
  have := multiplicity_factorial_lt_of_ne_zero 2 (n := m+1) (by omega)
  omega

/-- Write `x + ∑ cₙ xⁿ⁺²` with the linear term exposed. -/
def tangentSeries (c : ℕ → ℚ_[2]) (x : ℚ_[2]) : ℚ_[2] :=
  x + ∑' n, c n * x^(n+2)

abbrev quarterBall := Metric.closedBall (0 : ℚ_[2]) (1/4)

private lemma small {x : ℚ_[2]} : x ∈ quarterBall ↔ ‖x‖ ≤ 1/4 := by
  simp [Metric.mem_closedBall, dist_zero_right]

private lemma geometric_factor (n : ℕ) :
    (2 : ℝ)^(n+1) * (1/4 : ℝ)^(n+1) = (1/2 : ℝ)^(n+1) := by
  rw [← mul_pow]; norm_num

theorem tangent_summable {c : ℕ → ℚ_[2]} (hc : ∀ n, ‖c n‖ ≤ (2 : ℝ)^(n+1))
    {x : ℚ_[2]} (hx : x ∈ quarterBall) : Summable fun n => c n * x^(n+2) := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num)) fun n => ?_
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 : ℝ)^(n+1) * (1/4 : ℝ)^(n+2) := by gcongr; exacts [hc _, small.mp hx]
    _ = (1/2 : ℝ)^(n+1) * (1/4) := by rw [pow_succ (1/4 : ℝ) (n+1), ← mul_assoc, geometric_factor]
    _ ≤ (1/2 : ℝ)^n := by rw [pow_succ]; nlinarith [show 0 ≤ (1/2 : ℝ)^n by positivity]

private lemma pow_diff {x y : ℚ_[2]} (hx : x ∈ quarterBall) (hy : y ∈ quarterBall) (n : ℕ) :
    ‖x^(n+1) - y^(n+1)‖ ≤ (1/4 : ℝ)^n * ‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x^(n+2) - y^(n+2) = (x^(n+1) - y^(n+1))*x + y^(n+1)*(x-y) := by ring
    rw [e]
    apply (Padic.nonarchimedean _ _).trans
    rw [norm_mul, norm_mul, norm_pow]
    apply max_le
    · calc
        _ ≤ ((1/4 : ℝ)^n * ‖x-y‖) * (1/4) := by exact mul_le_mul ih (small.mp hx) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · gcongr; exact small.mp hy

private lemma tail_diff {c : ℕ → ℚ_[2]} (hc : ∀ n, ‖c n‖ ≤ (2 : ℝ)^(n+1))
    {x y : ℚ_[2]} (hx : x ∈ quarterBall) (hy : y ∈ quarterBall) :
    ‖(∑' n, c n * x^(n+2)) - ∑' n, c n * y^(n+2)‖ ≤ (1/2) * ‖x-y‖ := by
  rw [← (tangent_summable hc hx).tsum_sub (tangent_summable hc hy)]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ (2 : ℝ)^(n+1) * ((1/4 : ℝ)^(n+1) * ‖x-y‖) := by
      gcongr; exacts [hc _, pow_diff hx hy (n+1)]
    _ ≤ (1/2) * ‖x-y‖ := by
      rw [← mul_assoc, geometric_factor, pow_succ]
      gcongr
      simpa using (pow_le_one₀ (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num) (n := n))

@[simp] theorem tangent_zero (c : ℕ → ℚ_[2]) : tangentSeries c 0 = 0 := by simp [tangentSeries]

theorem tangent_isometry {c : ℕ → ℚ_[2]} (hc : ∀ n, ‖c n‖ ≤ (2 : ℝ)^(n+1))
    {x y : ℚ_[2]} (hx : x ∈ quarterBall) (hy : y ∈ quarterBall) :
    ‖tangentSeries c x - tangentSeries c y‖ = ‖x-y‖ := by
  rcases eq_or_ne x y with rfl | h
  · simp
  apply Padic.norm_eq_of_norm_sub_lt_right
  have id : tangentSeries c x - tangentSeries c y - (x-y) =
      (∑' n, c n * x^(n+2)) - ∑' n, c n * y^(n+2) := by unfold tangentSeries; abel
  rw [id]
  exact (tail_diff hc hx hy).trans_lt (by nlinarith [norm_pos_iff.mpr (sub_ne_zero.mpr h)])

theorem tangent_bijOn {c : ℕ → ℚ_[2]} (hc : ∀ n, ‖c n‖ ≤ (2 : ℝ)^(n+1)) :
    Set.BijOn (tangentSeries c) quarterBall quarterBall := by
  have zero_mem : (0 : ℚ_[2]) ∈ quarterBall := small.mpr (by norm_num)
  refine ⟨fun x hx => small.mpr ?_, fun x hx y hy h => ?_, fun z hz => ?_⟩
  · simpa using (tangent_isometry hc hx zero_mem).trans_le (by simpa using small.mp hx)
  · have := tangent_isometry hc hx hy
    rwa [h, sub_self, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at this
  · let r (x : ℚ_[2]) := ∑' n, c n * x^(n+2)
    let f (x : ℚ_[2]) := z - r x
    have maps : Set.MapsTo f quarterBall quarterBall := by
      intro x hx
      have hr := tail_diff hc hx zero_mem
      simp at hr
      apply small.mpr
      change ‖z - r x‖ ≤ 1/4
      rw [sub_eq_add_neg]
      exact (Padic.nonarchimedean z (-(r x))).trans (max_le (small.mp hz) (by
        rw [norm_neg]; exact hr.trans (show 2⁻¹ * ‖x‖ ≤ 1/4 by linarith [small.mp hx])))
    have contract : ContractingWith (1/2 : ℝ≥0) (maps.restrict f quarterBall quarterBall) := by
      refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
      change dist (z - r x) (z - r y) ≤ _ * dist (x : ℚ_[2]) y
      simpa [dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev (r y) (r x), r] using
        tail_diff hc x.property y.property
    obtain ⟨y, hy, hfix, _⟩ := ContractingWith.exists_fixedPoint'
      Metric.isClosed_closedBall.isComplete maps contract zero_mem (edist_ne_top _ _)
    exact ⟨y, hy, by change z - r y = y at hfix; change y + r y = z; linear_combination -hfix⟩

/-- The analytic extension of κ+1 in the logarithmic parameter. -/
def phaseSeries := tangentSeries (fun n => (coeff (n+2) : ℚ_[2]))

private lemma coeff_bound (n : ℕ) : ‖(coeff (n+2) : ℚ_[2])‖ ≤ (2 : ℝ)^(n+1) :=
  (coeff_norm_le_one (by omega)).trans (one_le_pow₀ (by norm_num))

theorem phase_isometry {x y : ℚ_[2]} (hx : x ∈ quarterBall) (hy : y ∈ quarterBall) :
    ‖phaseSeries x - phaseSeries y‖ = ‖x-y‖ := tangent_isometry coeff_bound hx hy

theorem phase_bijOn : Set.BijOn phaseSeries quarterBall quarterBall := tangent_bijOn coeff_bound

end NormalityChecker.ResonantRadix
