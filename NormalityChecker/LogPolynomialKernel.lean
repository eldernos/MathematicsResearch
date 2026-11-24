module

public import NormalityChecker.LogShadowIntegral
public import NormalityChecker.BBPShadow
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Rational polynomial kernels for shifted logarithms. -/
@[expose] public section
open Finset Polynomial MeasureTheory intervalIntegral
namespace NormalityChecker

/-- Rational linear combination of shifted logarithmic prefixes. -/
def polynomialLogModel (F : ℚ[X]) (n : ℕ) : ℚ :=
  ∑ j∈F.support, F.coeff j * logPrefix (n+j)

private theorem integrable_moment (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => t^k/(2-t)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (by fun_prop : Continuous (fun t : ℝ => t^k)).continuousOn.div (by fun_prop)
    (fun t ht => by linarith [ht.2])

/-- A normalized polynomial combines shifted models for any radix moment identity. -/
theorem polynomial_moment_error {b : ℕ} (R : ℕ → ℚ) (x : ℝ) (g w : ℝ → ℝ)
    (integrable : ∀ k : ℕ, IntervalIntegrable (fun t => g t^k*w t) volume 0 1)
    (moment : ∀ k : ℕ, (∫ t : ℝ in 0..1, g t^k*w t)=(b:ℝ)^k*x-R k)
    (F : ℚ[X]) (normalized : F.eval (b:ℚ)=1) (n : ℕ) :
    (b:ℝ)^n*x-((∑ j∈F.support, F.coeff j*R (n+j):ℚ):ℝ) =
      ∫ t : ℝ in 0..1, g t^n*F.eval₂ (Rat.castHom ℝ) (g t)*w t := by
  have expand (t : ℝ) : g t^n*F.eval₂ (Rat.castHom ℝ) (g t)*w t =
      ∑ j∈F.support, (F.coeff j:ℝ)*(g t^(n+j)*w t) := by
    rw [eval₂_eq_sum]; unfold Polynomial.sum; rw [Finset.mul_sum,Finset.sum_mul]
    apply sum_congr rfl; intro j _; simp only [Rat.coe_castHom,pow_add]; ring
  have factor : (∑ j∈F.support,(F.coeff j:ℝ)*(b:ℝ)^j)=1 := by
    rw [eval_eq_sum] at normalized
    exact_mod_cast (show (∑ j∈F.support,F.coeff j*(b:ℚ)^j)=1 from normalized)
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun j _ => (integrable (n+j)).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul,moment,mul_sub,Finset.sum_sub_distrib]
  simp only [Rat.cast_sum,Rat.cast_mul]
  congr 1
  rw [← one_mul ((b:ℝ)^n*x),← factor,Finset.sum_mul]
  apply sum_congr rfl; intro j _; rw [pow_add]; ring

/-- Exact error for every digit position and every normalized rational polynomial.
The rational model is executable directly from the coefficients. -/
theorem polynomial_log_error (F : ℚ[X]) (normalized : F.eval 2=1) (n : ℕ) :
    (2:ℝ)^n*Real.log 2-polynomialLogModel F n =
      ∫ t : ℝ in 0..1, t^n*F.eval₂ (Rat.castHom ℝ) t/(2-t) := by
  simpa [polynomialLogModel,div_eq_mul_inv] using
    polynomial_moment_error (b:=2) logPrefix (Real.log 2) id (fun t => (2-t)⁻¹)
      (fun k => by simpa [div_eq_mul_inv] using integrable_moment k)
      (fun k => by simpa [logShadow,div_eq_mul_inv] using (logShadow_integral 0 k).symm)
      F normalized n

/-- The same construction on the BBP integral, normalized at sixteen. -/
theorem polynomial_bbp_error (F : ℚ[X]) (normalized : F.eval 16=1) (n : ℕ) :
    (16:ℝ)^n*Real.pi-((∑ j∈F.support,F.coeff j*BBP.radixPrefix (n+j):ℚ):ℝ) =
    ∫ t : ℝ in 0..1, (t^8)^n*F.eval₂ (Rat.castHom ℝ) (t^8)*(t^8*BBP.weight t/(16-t^8)) := by
  have eq (k : ℕ) (t : ℝ) : (t^8)^k*(t^8*BBP.weight t/(16-t^8))=BBP.kernel (k+1) 0 t := by
    simp only [BBP.kernel,BBP.integrand,pow_zero,mul_one,pow_succ]; ring
  apply polynomial_moment_error (b:=16) BBP.radixPrefix Real.pi (fun t => t^8)
    (fun t => t^8*BBP.weight t/(16-t^8)) _ _ F normalized n
  · intro k; apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.mul (by fun_prop)
    exact (by unfold BBP.weight; fun_prop : Continuous (fun t : ℝ => t^8*BBP.weight t)).continuousOn.div
      (by fun_prop) (fun t ht => by linarith [pow_le_one₀ ht.1 ht.2 (n:=8)])
  · intro k; simp_rw [eq]; simpa [BBP.shadow] using (BBP.shadow_integral k 0).symm

/-- At position zero the quotient integral itself is the rational model. -/
theorem polynomial_log_rational_integral (F : ℚ[X]) (normalized : F.eval 2=1) :
    (∫ t : ℝ in 0..1, (1-F.eval₂ (Rat.castHom ℝ) t)/(2-t)) =
      (polynomialLogModel F 0:ℝ) := by
  have err := polynomial_log_error F normalized 0
  simp only [pow_zero,one_mul] at err
  have one : (∫ t : ℝ in 0..1,1/(2-t))=Real.log 2 := by
    simpa [logShadow,logPrefix] using (logShadow_integral 0 0).symm
  have continuous : Continuous (fun t : ℝ => F.eval₂ (Rat.castHom ℝ) t) := by
    simp only [eval₂_eq_sum,Polynomial.sum]; fun_prop
  have intF : IntervalIntegrable (fun t : ℝ => F.eval₂ (Rat.castHom ℝ) t/(2-t)) volume 0 1 :=
    (continuous.continuousOn.div (by fun_prop) (fun t ht => by linarith [ht.2])).intervalIntegrable_of_Icc (by norm_num)
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub (by simpa using integrable_moment 0) intF,one]
  linarith

/-- Adjusting the linear coefficient and compensating at degree zero preserves
the normalization at two and changes the model by exactly h/(n+1). -/
noncomputable def adjustKernel (F : ℚ[X]) (h : ℚ) := F + monomial 1 h + C (-2*h)

theorem adjustKernel_eval (F : ℚ[X]) (h : ℚ) : (adjustKernel F h).eval 2=F.eval 2 := by
  simp [adjustKernel]; ring

theorem adjustKernel_model (F : ℚ[X]) (n : ℕ) (h : ℚ) :
    polynomialLogModel (adjustKernel F h) n = polynomialLogModel F n+h/(n+1:ℚ) := by
  let f (j : ℕ) (a : ℚ) := a*logPrefix (n+j)
  have add (U V : ℚ[X]) : (U+V).sum f=U.sum f+V.sum f :=
    sum_add_index U V f (by simp [f]) (by simp [f,add_mul])
  change ((F+monomial 1 h)+C (-2*h)).sum f = F.sum f + _
  rw [add,add,sum_monomial_index _ _ (by simp [f]),sum_C_index (by simp [f])]
  dsimp [f]; rw [logPrefix]; ring

/-- Unrestricted rational coefficients attain every rational target at any one
start. The arithmetic content of a search lies in its independent error bound. -/
theorem normalized_kernel_for_target (n : ℕ) (y : ℚ) :
    ∃ F : ℚ[X], F.eval 2=1 ∧ polynomialLogModel F n=y := by
  let h := ((n:ℚ)+1)*(y-polynomialLogModel 1 n)
  refine ⟨adjustKernel 1 h,by simp [adjustKernel_eval],?_⟩
  rw [adjustKernel_model]; dsimp [h]; field_simp; ring

/-- Powers of the shifted degree-two Chebyshev polynomial, normalized at two. -/
noncomputable def chebyshevKernel (d : ℕ) : ℚ[X] :=
  (C (1/17) * (C 8*X^2-C 8*X+1))^d

theorem chebyshevKernel_normalized (d : ℕ) : (chebyshevKernel d).eval 2=1 := by
  norm_num [chebyshevKernel]

/-- An explicit rational enclosure, uniform in the shift n and in the power d. -/
theorem chebyshev_log_error (n d : ℕ) :
    |(2:ℝ)^n*Real.log 2-polynomialLogModel (chebyshevKernel d) n| ≤
      (1/17:ℝ)^d/((n:ℝ)+1) := by
  rw [polynomial_log_error _ (chebyshevKernel_normalized _) n]
  let v (t : ℝ) := (1/17:ℝ)*(8*t^2-8*t+1)
  have eval (t : ℝ) : (chebyshevKernel d).eval₂ (Rat.castHom ℝ) t=v t^d := by
    simp [chebyshevKernel,v,eval₂_pow,eval₂_mul,eval₂_sub]
  simp_rw [eval]
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans
  have cont : ContinuousOn (fun t : ℝ => t^n*v t^d/(2-t)) (Set.Icc 0 1) :=
    (by dsimp [v]; fun_prop : Continuous (fun t : ℝ => t^n*v t^d)).continuousOn.div
      (by fun_prop) (fun t ht => by linarith [ht.2])
  calc
    _ ≤ ∫ t : ℝ in 0..1, (1/17:ℝ)^d*t^n := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (cont.abs.intervalIntegrable_of_Icc (by norm_num)) (Continuous.intervalIntegrable (by fun_prop) ..)
      intro t ht
      have den : 1≤2-t := by linarith [ht.2]
      have small : |v t|≤(1/17:ℝ) := by
        dsimp [v]; apply abs_le.mpr
        constructor <;> nlinarith [sq_nonneg (2*t-1),mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
      rw [abs_div,abs_mul,abs_pow,abs_pow,abs_of_nonneg ht.1,abs_of_pos (by linarith : 0<2-t)]
      apply (div_le_self (mul_nonneg (pow_nonneg ht.1 n) (pow_nonneg (abs_nonneg _) d)) den).trans
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) small d) (pow_nonneg ht.1 n)
    _ = _ := by rw [intervalIntegral.integral_const_mul,integral_pow]; simp; ring

end NormalityChecker
