module

public import NormalityChecker.DensePolynomial

/-! A finite test for periodic weights when all power boundaries visit class one. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker

/-- One radix-discounted period, starting at residue `x`. -/
def periodWeight (b d : ℕ) (A : ZMod d → ℚ) (x : ZMod d) : ℚ :=
  ∑ i ∈ range d, A (x+i)*((b:ℚ)⁻¹)^i

/-- On subtracting the shifted period, all interior coefficients cancel. -/
private theorem period_step {b d : ℕ} (A : ZMod d → ℚ) (x : ZMod d) :
    periodWeight b d A x - (b:ℚ)⁻¹*periodWeight b d A (x+1) =
      (1-((b:ℚ)⁻¹)^d)*A x := by
  let term (i : ℕ) := A (x+i)*((b:ℚ)⁻¹)^i
  have next (i : ℕ) : (b:ℚ)⁻¹*(A (x+1+i)*((b:ℚ)⁻¹)^i) = term (i+1) := by
    simp only [term,Nat.cast_add,Nat.cast_one,pow_succ]
    rw [add_right_comm x 1,add_assoc]; ring
  simp only [periodWeight,mul_sum,next,← sum_sub_distrib]
  change ∑ i ∈ range d, (term i-term (i+1)) = _
  rw [sum_range_sub']; simp [term]; ring

/-- For a period dividing `c-1`, the rational sum of one discounted period
starting at class one decides between exact zero and base-`b` normality. -/
theorem periodic_plateau_test {b c d s : ℕ} [NeZero d] (hb : 2≤b) (hc : 2≤c)
    (cop : b.Coprime c) (order : 0<s) (residue : (c:ZMod d)=1) (A : ZMod d → ℚ) :
    let value := ∑' i : ℕ, (A ((i:ZMod d)+1):ℝ) / (c:ℝ)^(s*Nat.log c (i+1)) / (b:ℝ)^(i+1)
    if periodWeight b d A 1=0 then value=0 else NormalIn b value := by
  let denom := 1-((b:ℚ)⁻¹)^d
  have bq : (1:ℚ)<b := by exact_mod_cast (show 1<b by omega)
  have den : denom≠0 := (sub_pos.mpr (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ bq) (NeZero.ne d))).ne'
  let F (x : ZMod d) := periodWeight b d A x / denom
  have step (n : ℕ) : A (n:ZMod d)=F n-F (n+1:ℕ)/b := by
    have h := period_step (b:=b) A n
    dsimp only [F]; push_cast
    rw [show periodWeight b d A (n:ZMod d)/denom - periodWeight b d A ((n:ZMod d)+1)/denom/b =
      (periodWeight b d A n-(b:ℚ)⁻¹*periodWeight b d A ((n:ZMod d)+1))/denom by ring,h]
    exact (mul_div_cancel_left₀ _ den).symm
  have summ : Summable (fun n : ℕ => (F (n:ZMod d):ℝ)/(b:ℝ)^n) := by
    let bound := ∑ z : ZMod d, |(F z:ℝ)|
    have br : (1:ℝ)<b := by exact_mod_cast bq
    apply Summable.of_norm_bounded ((summable_geometric_of_lt_one (r:=(b:ℝ)⁻¹) (by positivity) (inv_lt_one_of_one_lt₀ br)).mul_left bound)
    intro n
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : (0:ℝ)<(b:ℝ)^n),inv_pow,← div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact single_le_sum (fun i _ => abs_nonneg (F i:ℝ)) (mem_univ (n:ZMod d))
  have bd (j : ℕ) : F ((c^j:ℕ):ZMod d)=F 1 := by simp [residue]
  dsimp only
  split_ifs with test
  · have h := dense_boundary_identity (b:=b) (c:=c) (s:=s) hc (fun n => A n) (fun n => F n) step summ
    have zero : F 1=0 := by simp [F,test]
    simp_rw [bd] at h
    simpa [zero] using h
  · have nz : F 1≠0 := div_ne_zero test den
    have h := normal_of_polynomial_boundaries (b:=b) (c:=c) (s:=s) hb hc cop (fun n => A n) (fun n => F n)
      (C (F 1)) (by simpa using nz) (by simpa using order) step summ (by simpa using bd)
    simpa using h

end NormalityChecker
