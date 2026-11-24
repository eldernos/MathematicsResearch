module

public import NormalityChecker.LogShadow
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact integral remainder and an endpoint-uniform corrected logarithmic orbit. -/
@[expose] public section
open Real Set intervalIntegral MeasureTheory
namespace NormalityChecker

private noncomputable def kernel (n r : ℕ) (t : ℝ) := t^n*(1-t)^r/(2-t)

private lemma integrable_kernel (n r : ℕ) : IntervalIntegrable (kernel n r) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num); unfold kernel
  exact (by fun_prop : Continuous (fun t : ℝ => t^n*(1-t)^r)).continuousOn.div (by fun_prop) (fun t ht => by have := ht.2; linarith)

lemma beta_difference (r n : ℕ) : (∫ t : ℝ in 0..1,t^n*(1-t)^r) = (logDifference r n:ℝ) := by
  induction r generalizing n with
  | zero => simp [difference_zero]
  | succ r ih =>
    rw [← difference_step,Rat.cast_sub,← ih n,← ih (n+1),← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) ..) (Continuous.intervalIntegrable (by fun_prop) ..)]
    exact integral_congr fun t _ => by rw [pow_succ,pow_succ]; ring

private lemma base_integral (n : ℕ) : (2:ℝ)^n*log 2-logPrefix n = ∫ t in 0..1,kernel n 0 t := by
  induction n with
  | zero =>
    simp only [pow_zero,one_mul,logPrefix,Rat.cast_zero,sub_zero,kernel,mul_one]
    rw [integral_comp_sub_left (fun t : ℝ => 1/t) 2]; norm_num [integral_one_div_of_pos]
  | succ n ih =>
    have recurrence : (∫ t in 0..1,kernel (n+1) 0 t) = 2*(∫ t in 0..1,kernel n 0 t)-(∫ t : ℝ in 0..1,t^n) := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub ((integrable_kernel n 0).const_mul _) (Continuous.intervalIntegrable (by fun_prop) ..)]
      apply integral_congr; intro t ht; rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
      dsimp [kernel]; have nz : 2-t≠0 := by have := ht.2; linarith
      rw [pow_succ]; field_simp; ring
    rw [recurrence,← ih,logPrefix,pow_succ,integral_pow]; push_cast; simp; ring

/-- The factorial corrections are moments of the error of a finite geometric series. -/
theorem logShadow_integral (r n : ℕ) :
    (2:ℝ)^n*log 2-logShadow r n = (-1:ℝ)^r*(∫ t : ℝ in 0..1,t^n*(1-t)^r/(2-t)) := by
  change _ = (-1:ℝ)^r*(∫ t in 0..1,kernel n r t)
  induction r with
  | zero => simpa [logShadow] using base_integral n
  | succ r ih =>
    have step : (∫ t in 0..1,kernel n (r+1) t) = (logDifference r n:ℝ)-(∫ t in 0..1,kernel n r t) := by
      rw [← beta_difference,← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) ..) (integrable_kernel ..)]
      apply integral_congr; intro t ht; rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
      have nz : 2-t≠0 := by have := ht.2; linarith
      dsimp [kernel]; rw [pow_succ]; field_simp; ring
    rw [step,logShadow]; push_cast; rw [pow_succ]; linear_combination ih

/-- The diagonal error is bounded by a beta integral, retaining the factor
that tends to zero even after `2*n` further shifts. -/
theorem logShadow_beta_bound (n : ℕ) : |(2:ℝ)^n*log 2-logShadow n n| ≤ (logDifference n n:ℝ) := by
  rw [logShadow_integral,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,← beta_difference]
  have pos (t : ℝ) (ht : t∈Icc 0 1) : 0≤kernel n n t := by dsimp [kernel]; exact div_nonneg (mul_nonneg (pow_nonneg ht.1 _) (pow_nonneg (sub_nonneg.mpr ht.2) _)) (by have := ht.2; linarith)
  change |∫ t in 0..1,kernel n n t|≤_
  rw [abs_of_nonneg (integral_nonneg (by norm_num) pos)]
  apply integral_mono_on (by norm_num) (integrable_kernel ..) (Continuous.intervalIntegrable (by fun_prop) ..)
  intro t ht; dsimp [kernel]; apply div_le_self (mul_nonneg (pow_nonneg ht.1 _) (pow_nonneg (sub_nonneg.mpr ht.2) _)); linarith [ht.2]

private lemma beta_diagonal_step (n : ℕ) : logDifference (n+1) (n+1)=logDifference n n*((n+1:ℚ)/(2*(2*n+3))) := by
  unfold logDifference
  rw [show n+1+(n+1)+1=(n+n+1+1)+1 by omega,Nat.factorial_succ (n+n+1+1),Nat.factorial_succ (n+n+1),Nat.factorial_succ n]; push_cast; field_simp; ring

private lemma beta_diagonal (n : ℕ) : ((4:ℚ)^n*logDifference n n)^2*(n+1)≤1 := by
  induction n with
  | zero => norm_num [logDifference]
  | succ n ih =>
    rw [beta_diagonal_step,pow_succ]; push_cast
    let u := (4:ℚ)^n*logDifference n n
    change u^2*(n+1)≤1 at ih
    have scale : (2*((n:ℚ)+1))^2*((n:ℚ)+2)≤((n:ℚ)+1)*(2*n+3)^2 := by nlinarith [Nat.cast_nonneg (α:=ℚ) n]
    have h := (mul_le_mul_of_nonneg_left scale (sq_nonneg u)).trans (by simpa [mul_assoc] using (mul_le_mul_of_nonneg_right ih (sq_nonneg (2*(n:ℚ)+3))))
    dsimp [u] at h; field_simp; simp only [pow_succ (4:ℚ) n]; nlinarith only [h]

/-- The same rational model shadows the inclusive endpoint at `2*n` further
shifts. The squared unwrapped error is at most `1/(n+1)`. -/
theorem logShadow_double_length {n i : ℕ} (hi : i≤2*n) :
    ((2:ℝ)^(n+i)*log 2-(2:ℝ)^i*logShadow n n)^2*(n+1)≤1 := by
  have absBound := logShadow_beta_bound n
  have tw : (2:ℝ)^i≤4^n := by
    calc _ ≤ (2:ℝ)^(2*n) := pow_le_pow_right₀ (by norm_num) hi
         _ = _ := by rw [pow_mul]; norm_num
  have bnd := mul_le_mul tw absBound (abs_nonneg _) (by positivity)
  have sqb := pow_le_pow_left₀ (mul_nonneg (by positivity) (abs_nonneg _)) bnd 2
  have rd : ((4:ℝ)^n*(logDifference n n:ℝ))^2*(n+1)≤1 := by exact_mod_cast beta_diagonal n
  rw [← abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) i),← abs_mul,sq_abs] at sqb
  apply le_trans _ rd; convert mul_le_mul_of_nonneg_right sqb (show 0≤(n:ℝ)+1 by positivity) using 2; rw [pow_add]; ring

end NormalityChecker
