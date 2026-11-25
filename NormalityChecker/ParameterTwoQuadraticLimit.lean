module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-! The 2-adic affine approximation to the actual quadratic cancellation term.
Index `j` in `delta b j` denotes the positive Stoneham index `j+1`. -/
@[expose] public noncomputable section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ParameterTwoQuadratic

private lemma norm_two : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p (p := 2)

def delta (b j : ℕ) : ℚ_[2] :=
  (((b : ℚ_[2]) ^ (2^(j+1) : ℕ))⁻¹ - 1) / 2^(j+1)

def step (b j : ℕ) : ℚ_[2] := 2^j * delta b j ^ 2

theorem delta_succ (b j : ℕ) :
    delta b (j+1) = delta b j + 2^j * delta b j ^ 2 := by
  simp only [delta, pow_succ (2 : ℕ) (j+1), pow_mul, ← inv_pow]
  rw [pow_succ (2 : ℚ_[2]) (j+1), pow_succ (2 : ℚ_[2]) j]
  field_simp
  ring

theorem radix_norm {b : ℕ} (odd : Odd b) : ‖(b : ℚ_[2])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr odd.coprime_two_left

theorem delta_zero_norm {b : ℕ} (odd : Odd b) :
    ‖delta b 0‖ = 2 * ‖(b : ℚ_[2])^2 - 1‖ := by
  have hb : (b : ℚ_[2]) ≠ 0 := norm_ne_zero_iff.mp (by rw [radix_norm odd]; norm_num)
  have h : delta b 0 = -((b : ℚ_[2])^2 - 1) / ((b : ℚ_[2])^2 * 2) := by
    simp only [delta, zero_add, pow_one]
    field_simp
    ring
  rw [h, norm_div, norm_neg, norm_mul, norm_pow, radix_norm odd, norm_two]
  norm_num
  ring

theorem delta_zero_norm_lt_one {b : ℕ} (odd : Odd b) : ‖delta b 0‖ < 1 := by
  rw [delta_zero_norm odd]
  obtain ⟨r, hr⟩ := odd
  have h : (b : ℚ_[2])^2 - 1 = (2 : ℚ_[2])^2 * ((r*(r+1) : ℕ) : ℚ_[2]) := by
    rw [hr]; push_cast; ring
  have hu := Padic.norm_int_le_one (p := 2) (r*(r+1) : ℕ)
  rw [h, norm_mul, norm_pow, norm_two]
  push_cast at hu ⊢
  norm_num at *
  linarith

theorem delta_zero_ne {b : ℕ} (hb : 3 ≤ b) : delta b 0 ≠ 0 := by
  have q : 1 < b^2 := by nlinarith
  have ne : (b : ℚ_[2])^2 ≠ 1 := by exact_mod_cast q.ne'
  simpa [delta, sub_ne_zero, inv_eq_one] using ne

private lemma norm_two_pow (j : ℕ) : ‖(2 : ℚ_[2])^j‖ = (1/2 : ℝ)^j := by
  rw [norm_pow, norm_two]; norm_num

theorem delta_norm {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (j : ℕ) :
    ‖delta b j‖ = ‖delta b 0‖ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [delta_succ]
    have small : ‖(2 : ℚ_[2])^j * delta b j ^ 2‖ < ‖delta b j‖ := by
      rw [norm_mul, norm_two_pow, norm_pow, ih]
      have hp : (1 / 2 : ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hd := delta_zero_norm_lt_one odd
      have pos := norm_pos_iff.mpr (delta_zero_ne hb)
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg ‖delta b 0‖),
        mul_pos pos (sub_pos.mpr hd)]
    rw [Padic.add_eq_max_of_ne small.ne', max_eq_left small.le, ih]

private lemma step_norm {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (j : ℕ) :
    ‖step b j‖ = (1/2 : ℝ)^j * ‖delta b 0‖^2 := by
  rw [step, norm_mul, norm_two_pow, norm_pow, delta_norm hb odd]

private lemma step_summable {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) : Summable (step b) := by
  apply Summable.of_norm
  simpa only [step_norm hb odd] using
    (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)).mul_right
      (‖delta b 0‖^2)

def slope (b : ℕ) : ℚ_[2] := delta b 0 + ∑' j, step b j

private lemma slope_sub (b k : ℕ) (hb : 3 ≤ b) (odd : Odd b) :
    slope b - delta b k = ∑' j, step b (j+k) := by
  have h : delta b 0 + ∑ i ∈ range k, step b i = delta b k := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ← add_assoc, ih, delta_succ]; rfl
  rw [slope, ← (step_summable hb odd).sum_add_tsum_nat_add k, ← add_assoc, h, add_sub_cancel_left]

private lemma tail_bound {f : ℕ → ℚ_[2]} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ j, ‖f j‖ ≤ (1/2 : ℝ)^j * r) (k : ℕ) :
    ‖∑' j, f (j+k)‖ ≤ (1/2 : ℝ)^k * r := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro j
  refine (hf _).trans ?_
  rw [pow_add]
  gcongr
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

theorem delta_error_le {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (j : ℕ) :
    ‖delta b j - slope b‖ ≤ (1/2 : ℝ)^j * ‖delta b 0‖^2 := by
  rw [norm_sub_rev, slope_sub b j hb odd]
  exact tail_bound (sq_nonneg _) (fun i => (step_norm hb odd i).le) j

private lemma correction_summable {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    Summable fun j => delta b j - slope b :=
  Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)).mul_right _)
    (delta_error_le hb odd)

theorem delta_tendsto {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    Tendsto (delta b) atTop (𝓝 (slope b)) :=
  tendsto_sub_nhds_zero_iff.mp (correction_summable hb odd).tendsto_atTop_zero

theorem slope_norm {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    ‖slope b‖ = ‖delta b 0‖ := by
  apply Padic.norm_eq_of_norm_sub_lt_right
  rw [norm_sub_rev]
  have h := delta_error_le hb odd 0
  simp only [pow_zero, one_mul] at h
  nlinarith [delta_zero_norm_lt_one odd, norm_pos_iff.mpr (delta_zero_ne hb),
    mul_pos (norm_pos_iff.mpr (delta_zero_ne hb)) (sub_pos.mpr (delta_zero_norm_lt_one odd))]

theorem slope_valuation {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    (slope b).valuation = (padicValInt 2 ((b : ℤ)^2-1) : ℤ) - 1 := by
  have hn : slope b ≠ 0 := norm_ne_zero_iff.mp (by rw [slope_norm hb odd]; exact norm_ne_zero_iff.mpr (delta_zero_ne hb))
  have hz : (b : ℤ)^2-1 ≠ 0 := by
    have h : (3 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have e := (slope_norm hb odd).trans (delta_zero_norm odd)
  have cast : (b : ℚ_[2])^2-1 = (((b : ℤ)^2-1 : ℤ) : ℚ_[2]) := by push_cast; rfl
  rw [cast, Padic.norm_eq_zpow_neg_valuation hn,
    Padic.norm_eq_zpow_neg_valuation (Int.cast_ne_zero.mpr hz), Padic.valuation_intCast] at e
  have pow : (2 : ℝ)^(-(slope b).valuation) = 2^((1 : ℤ)-padicValInt 2 ((b : ℤ)^2-1)) := by
    rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_one]; exact e
  rw [zpow_right_inj₀ (by norm_num) (by norm_num)] at pow
  omega

private lemma bound_strict {b : ℕ} (hb : 3 ≤ b) (j : ℕ) :
    (1/2 : ℝ)^(j+1) * ‖delta b 0‖^2 < (1/2 : ℝ)^j * ‖delta b 0‖^2 := by
  rw [pow_succ]
  have pos : 0 < (1/2 : ℝ)^j * ‖delta b 0‖^2 :=
    mul_pos (by positivity) (sq_pos_of_pos (norm_pos_iff.mpr (delta_zero_ne hb)))
  linarith

theorem delta_error_norm {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (j : ℕ) :
    ‖delta b j - slope b‖ = (1/2 : ℝ)^j * ‖delta b 0‖^2 := by
  have e : delta b j - slope b = -step b j + (delta b (j+1)-slope b) := by
    rw [delta_succ, step]; ring
  have lt : ‖delta b (j+1)-slope b‖ < ‖-step b j‖ := by
    rw [norm_neg, step_norm hb odd]
    exact (delta_error_le hb odd _).trans_lt (bound_strict hb j)
  rw [e, Padic.add_eq_max_of_ne lt.ne', max_eq_left lt.le, norm_neg, step_norm hb odd]

def intercept (b : ℕ) : ℚ_[2] := slope b + ∑' j, (delta b j - slope b)

/-- The paper's `T_(j+1)`. -/
def cancellation (b j : ℕ) : ℚ_[2] := (∑ i ∈ range (j+1), delta b i) + delta b j

theorem affine_error_norm {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (j : ℕ) :
    ‖cancellation b j - ((j+1 : ℕ) : ℚ_[2]) * slope b - intercept b‖ =
      (1/2 : ℝ)^j * ‖delta b 0‖^2 := by
  have h := (correction_summable hb odd).sum_add_tsum_nat_add (j+1)
  have eqn : cancellation b j - ((j+1 : ℕ) : ℚ_[2]) * slope b - intercept b =
      (delta b j - slope b) - ∑' i : ℕ, (delta b (i+(j+1)) - slope b) := by
    rw [intercept, ← h, sum_sub_distrib]
    simp only [sum_const, card_range, nsmul_eq_mul, cancellation]
    ring
  have lt : ‖-(∑' i : ℕ, (delta b (i+(j+1)) - slope b))‖ < ‖delta b j - slope b‖ := by
    rw [norm_neg, delta_error_norm hb odd]
    exact (tail_bound (sq_nonneg _) (delta_error_le hb odd) (j+1)).trans_lt (bound_strict hb j)
  rw [eqn, sub_eq_add_neg (delta b j - slope b), Padic.add_eq_max_of_ne lt.ne', max_eq_left lt.le,
    delta_error_norm hb odd]

theorem affine_error_le {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (j : ℕ) :
    ‖cancellation b j - ((j+1 : ℕ) : ℚ_[2]) * slope b - intercept b‖ ≤
      (1/2 : ℝ)^j * ‖delta b 0‖^2 := (affine_error_norm hb odd j).le

end NormalityChecker.ParameterTwoQuadratic
