module

public import NormalityChecker.DiagonalStep
public import NormalityChecker.FirstFrequency

/-! A concrete obstruction to estimates uniform over the reduced numerators of
corrected logarithm models. Numerator one always gives a reduced model. -/
@[expose] public section
open Finset
namespace NormalityChecker

/-- On a block of length `n`, the total first-frequency deficit at numerator
one is at most `2π (2^n-1)/Q`. -/
theorem unit_numerator_escape {Q : ℕ} (hQ : 0<Q) (n : ℕ) :
    escapeAverage (fun i => (2:ℝ)^i/Q) n ≤ 2*Real.pi*((2:ℝ)^n-1)/Q/n := by
  have qr : (0:ℝ)<Q := by exact_mod_cast hQ
  have each (i : ℕ) : cosineEscape ((2:ℝ)^i/Q) ≤ (2*Real.pi/Q)*2^i := by
    let z : ℝ := 2*Real.pi*(2^i/Q)
    have hz : 0≤z := by dsimp [z]; positivity
    have lip := Real.abs_cos_sub_cos_le 0 z
    simp only [Real.cos_zero,zero_sub,abs_neg,abs_of_nonneg hz] at lip
    change 1-Real.cos z≤_
    exact (le_abs_self _).trans (lip.trans_eq (by dsimp [z]; ring))
  have geom : ∑ i∈range n,(2:ℝ)^i=2^n-1 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih,pow_succ]; ring
  have sum := sum_le_sum (s:=range n) (fun i _ => each i)
  rw [← mul_sum,geom] at sum
  unfold escapeAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact sum.trans_eq (by ring)

/-- At every positive index at least one of the two consecutive actual
model denominators admits a reduced numerator with total deficit at most `4π`. -/
theorem adjacent_small_escape {n : ℕ} (hn : 0<n) :
    ∃ j∈({n,n+1}:Finset ℕ), escapeAverage (fun i => (2:ℝ)^i/(logShadow j j).den) j ≤ 4*Real.pi/n := by
  obtain ⟨j,hj,big⟩ : ∃ j∈({n,n+1}:Finset ℕ),2^n≤(logShadow j j).den := by
    rcases le_max_iff.mp (logShadow_diagonal_max n) with h|h
    · exact ⟨n,by simp,h⟩
    · exact ⟨n+1,by simp,h⟩
  refine ⟨j,hj,(unit_numerator_escape (logShadow j j).pos j).trans ?_⟩
  have cases := mem_insert.mp hj
  have lo : n≤j := by rcases cases with rfl|h <;> simp_all
  have hi : j≤n+1 := by rcases cases with rfl|h <;> simp_all
  have major : (2:ℝ)^j ≤ 2*(logShadow j j).den := by
    have b : (2:ℝ)^n ≤ (logShadow j j).den := by exact_mod_cast big
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hi; rw [pow_succ] at h; linarith
  have qpos : (0:ℝ)<(logShadow j j).den := by exact_mod_cast (logShadow j j).pos
  have total : 2*Real.pi*(2^j-1)/(logShadow j j).den ≤ 4*Real.pi := by
    rw [div_le_iff₀ qpos]; nlinarith only [mul_le_mul_of_nonneg_left major Real.pi_pos.le,Real.pi_pos]
  exact (div_le_div_of_nonneg_right total (Nat.cast_nonneg j)).trans
    (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hn) (by exact_mod_cast lo))

end NormalityChecker
