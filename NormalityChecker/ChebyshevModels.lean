module

public import NormalityChecker.LogPolynomialKernel
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! Normalized Chebyshev models in each degree. -/
@[expose] public section
open Polynomial MeasureTheory intervalIntegral
namespace NormalityChecker

/-- The normalizing value for logarithmic shifts at radix b. -/
noncomputable def chebScale (b d : ℕ) : ℚ := (Chebyshev.T ℚ d).eval (2*b-1)

private lemma cast_scale (b d : ℕ) :
    (chebScale b d:ℝ)=(Chebyshev.T ℝ d).eval (2*(b:ℝ)-1) := by
  unfold chebScale
  have h := eval_map_apply (p:=Chebyshev.T ℚ (d:ℤ)) (Rat.castHom ℝ) (2*(b:ℚ)-1)
  simpa using h.symm

theorem chebScale_pos {b : ℕ} (hb : 1≤b) (d : ℕ) : 0<chebScale b d := by
  apply Rat.cast_pos (K:=ℝ) |>.mp
  rw [cast_scale]
  have hr : 1≤2*(b:ℝ)-1 := by exact_mod_cast (by omega : (1:ℤ)≤2*(b:ℤ)-1)
  rw [← Real.cosh_arcosh hr,Chebyshev.T_real_cosh]
  exact Real.cosh_pos _

noncomputable def normalizedChebyshev (b d : ℕ) : ℚ[X] :=
  Polynomial.C (chebScale b d)⁻¹ * (Chebyshev.T ℚ d).comp (2*X-1)

theorem normalizedChebyshev_eval {b : ℕ} (hb : 1≤b) (d : ℕ) :
    (normalizedChebyshev b d).eval (b:ℚ)=1 := by
  simpa [normalizedChebyshev, eval_comp, chebScale] using inv_mul_cancel₀ (chebScale_pos hb d).ne'

theorem normalizedChebyshev_bound {b : ℕ} (hb : 1≤b) (d : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    |(normalizedChebyshev b d).eval₂ (Rat.castHom ℝ) t|≤1/(chebScale b d:ℝ) := by
  have pos : (0:ℝ)<chebScale b d := by exact_mod_cast chebScale_pos hb d
  have eval : (normalizedChebyshev b d).eval₂ (Rat.castHom ℝ) t =
      (chebScale b d:ℝ)⁻¹*(Chebyshev.T ℝ d).eval (2*t-1) := by
    simp [normalizedChebyshev, eval₂_eq_eval_map, Polynomial.map_comp, eval_comp]
  rw [eval,abs_mul,abs_inv,abs_of_pos pos,one_div]
  apply mul_le_of_le_one_right (inv_nonneg.mpr pos.le)
  rw [← Real.cos_arccos (by linarith [ht.1] : -1≤2*t-1) (by linarith [ht.2] : 2*t-1≤1),
    Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- Uniform error for the actual logarithm, using one polynomial of exact degree d. -/
theorem full_degree_log_error (n d : ℕ) :
    |(2:ℝ)^n*Real.log 2-polynomialLogModel (normalizedChebyshev 2 d) n| ≤
      (1/(chebScale 2 d:ℝ))/((n:ℝ)+1) := by
  let F := normalizedChebyshev 2 d
  change |(2:ℝ)^n*Real.log 2-(polynomialLogModel F n:ℝ)|≤_
  rw [polynomial_log_error F (normalizedChebyshev_eval (by decide) d)]
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans
  have cont : Continuous (fun t : ℝ => F.eval₂ (Rat.castHom ℝ) t) := by
    simp only [eval₂_eq_eval_map]; exact Polynomial.continuous _
  have den (t : ℝ) (ht : t∈Set.Icc 0 1) : 1≤2-t := by linarith [ht.2]
  have intg : ContinuousOn (fun t : ℝ => t^n * F.eval₂ (Rat.castHom ℝ) t/(2-t)) (Set.Icc 0 1) :=
    ((continuous_pow n).mul cont).continuousOn.div
      (g:=fun t : ℝ => 2-t) (by fun_prop) (fun t ht => by linarith [den t ht])
  calc
    _ ≤ ∫ t : ℝ in 0..1, (1/(chebScale 2 d:ℝ))*t^n := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (intg.abs.intervalIntegrable_of_Icc (by norm_num)) (Continuous.intervalIntegrable (by fun_prop) ..)
      intro t ht
      rw [abs_div,abs_mul,abs_pow,abs_of_nonneg ht.1,abs_of_pos (by linarith [den t ht] : 0<2-t)]
      apply (div_le_self (mul_nonneg (pow_nonneg ht.1 n) (abs_nonneg _)) (den t ht)).trans
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (normalizedChebyshev_bound (b:=2) (by decide) d ht) (pow_nonneg ht.1 n)
    _ = _ := by rw [intervalIntegral.integral_const_mul,integral_pow]; simp; ring

end NormalityChecker
