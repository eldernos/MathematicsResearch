module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Rational hexadecimal models for π, obtained by integrating the BBP kernel. -/
@[expose] public section
open Real Set MeasureTheory intervalIntegral Filter
open scoped Topology
namespace NormalityChecker.BBP

def coefficient (k : ℕ) : ℚ := 4/(8*k+1:ℚ)-2/(8*k+4:ℚ)-1/(8*k+5:ℚ)-1/(8*k+6:ℚ)
noncomputable def weight (t : ℝ) := 4-2*t^3-t^4-t^5
noncomputable def integrand (k r : ℕ) (t : ℝ) := (t^8)^k*(t^8-1)^r*weight t
noncomputable def kernel (k r : ℕ) (t : ℝ) := integrand k r t/(16-t^8)

private lemma unit_pow {t : ℝ} (h : t∈Icc 0 1) (a : ℕ) : 0≤t^a ∧ t^a≤1 :=
  ⟨pow_nonneg h.1 _,pow_le_one₀ h.1 h.2⟩
private lemma no_pole {t : ℝ} (h : t∈Icc 0 1) : 0<16-t^8 := by linarith [(unit_pow h 8).2]
private lemma continuous_moment (k r : ℕ) : Continuous (integrand k r) := by unfold integrand weight; fun_prop
private lemma integrable_kernel (k r : ℕ) : IntervalIntegrable (kernel k r) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) ((continuous_moment ..).continuousOn.div (by fun_prop) (fun _ h => (no_pole h).ne'))

/-- This integral evaluates the BBP sum without an external axiom for its value. -/
theorem integral_pi : (∫ t in 0..1,16*kernel 0 0 t)=π := by
  let F (t : ℝ) := 2*log (2-t^2)-2*log ((t-1)^2+1)+4*arctan (t-1)
  have D (t : ℝ) (h : t∈uIcc 0 1) : HasDerivAt F (16*kernel 0 0 t) t := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at h
    have a : 2-t^2≠0 := by linarith [(unit_pow h 2).2]
    have b : (t-1)^2+1≠0 := by positivity
    have c : 1+(t-1)^2≠0 := by positivity
    have d := no_pole h
    have t1 := (hasDerivAt_id t).sub_const 1
    have h1 := (((hasDerivAt_id t).pow 2).const_sub 2).log a
    have h2 := (((t1.pow 2).add_const 1).log b)
    apply (((h1.const_mul 2).sub (h2.const_mul 2)).add (t1.arctan.const_mul 4)).congr_deriv
    dsimp [kernel,integrand,weight]; field_simp [a,b,c,d.ne']; ring
  rw [integral_eq_sub_of_hasDerivAt D ((integrable_kernel 0 0).const_mul _)]
  norm_num [F,arctan_one]; ring

private lemma monomial (m : ℕ) : (∫ t : ℝ in 0..1,t^m)=1/(m+1:ℝ) := by simp [one_div]

theorem coefficient_integral (k : ℕ) : (∫ t in 0..1,integrand k 0 t)=(coefficient k:ℝ) := by
  have e : integrand k 0 = fun t : ℝ => 4*t^(8*k)-2*t^(8*k+3)-t^(8*k+4)-t^(8*k+5) := by
    funext t; dsimp [integrand,weight]; simp only [pow_zero,mul_one,pow_add,pow_mul]; ring
  rw [e,intervalIntegral.integral_sub,intervalIntegral.integral_sub,intervalIntegral.integral_sub] <;> try (apply Continuous.intervalIntegrable; fun_prop)
  simp only [intervalIntegral.integral_const_mul,monomial]
  dsimp [coefficient]; push_cast; ring_nf

/-- Signed differences of the rational BBP coefficients are polynomial moments. -/
def moment : ℕ → ℕ → ℚ
  | 0,k => coefficient k
  | r+1,k => moment r (k+1)-moment r k

private lemma moment_integral (k r : ℕ) : (∫ t in 0..1,integrand k r t)=(moment r k:ℝ) := by
  induction r generalizing k with
  | zero => exact coefficient_integral k
  | succ r ih =>
    rw [moment,Rat.cast_sub,← ih,← ih,← intervalIntegral.integral_sub ((continuous_moment ..).intervalIntegrable ..) ((continuous_moment ..).intervalIntegrable ..)]
    apply integral_congr; intro t _; dsimp [integrand]; rw [pow_succ,pow_succ]; ring

/-- The scaled rational prefix includes the coefficient at hexadecimal position `n`. -/
def radixPrefix : ℕ → ℚ
  | 0 => coefficient 0
  | n+1 => 16*radixPrefix n+coefficient (n+1)

private lemma uncorrected (n : ℕ) : (16:ℝ)^n*π-radixPrefix n=∫ t in 0..1,kernel (n+1) 0 t := by
  have diff (k : ℕ) : (∫ t in 0..1,kernel (k+1) 0 t)=16*(∫ t in 0..1,kernel k 0 t)-(coefficient k:ℝ) := by
    rw [← coefficient_integral,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub ((integrable_kernel ..).const_mul _) ((continuous_moment ..).intervalIntegrable ..)]
    apply integral_congr; intro t h; rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at h
    dsimp [kernel,integrand]; rw [pow_succ]; field_simp [(no_pole h).ne']; ring
  induction n with
  | zero => rw [diff,← intervalIntegral.integral_const_mul,integral_pi]; simp [radixPrefix]
  | succ n ih => rw [diff,← ih,radixPrefix,pow_succ]; push_cast; ring

def shadow : ℕ → ℕ → ℚ
  | 0,n => radixPrefix n
  | r+1,n => shadow r n+moment r (n+1)/(15:ℚ)^(r+1)

/-- The exact integral error after any number of rational corrections. -/
theorem shadow_integral (n r : ℕ) : (16:ℝ)^n*π-shadow r n=(∫ t in 0..1,kernel (n+1) r t)/(15:ℝ)^r := by
  induction r with
  | zero => simpa [shadow] using uncorrected n
  | succ r ih =>
    have e : (∫ t in 0..1,kernel (n+1) (r+1) t)=15*(∫ t in 0..1,kernel (n+1) r t)-(moment r (n+1):ℝ) := by
      rw [← moment_integral,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub ((integrable_kernel ..).const_mul _) ((continuous_moment ..).intervalIntegrable ..)]
      apply integral_congr; intro t h; rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at h
      dsimp [kernel,integrand]; rw [pow_succ (t^8-1)]; field_simp [(no_pole h).ne']; ring
    rw [e,shadow]; push_cast; rw [pow_succ]; field_simp at ih ⊢; linear_combination 15*ih

/-- Diagonal correction gives an exponentially accurate model of a hexadecimal shift of π. -/
theorem shadow_error (n : ℕ) : |(16:ℝ)^n*π-shadow n n| ≤ 4/(15*60^n) := by
  rw [shadow_integral,abs_div,abs_of_pos (by positivity : (0:ℝ)<15^n)]
  have point (t : ℝ) (h : t∈Icc 0 1) : |kernel (n+1) n t| ≤ 4/(15*4^n) := by
    let u := t^8
    obtain ⟨ul,ur⟩ := unit_pow h 8; change 0≤u at ul; change u≤1 at ur
    have quad : u*(1-u)≤1/4 := by nlinarith [sq_nonneg (u-1/2)]
    have w : |weight t|≤4 := by dsimp [weight]; exact abs_le.mpr ⟨by linarith [(unit_pow h 3).2,(unit_pow h 4).2,(unit_pow h 5).2],by linarith [(unit_pow h 3).1,(unit_pow h 4).1,(unit_pow h 5).1]⟩
    have eqn : |kernel (n+1) n t|=u*(u*(1-u))^n*|weight t|/(16-u) := by
      dsimp [kernel,integrand]; change |u^(n+1)*(u-1)^n*weight t/(16-u)|=_
      rw [abs_div,abs_mul,abs_mul,abs_pow u (n+1),abs_pow (u-1) n,abs_of_nonneg ul,abs_of_nonpos (sub_nonpos.mpr ur),abs_of_pos (show 0<16-u by linarith),mul_pow,pow_succ,neg_sub]; ring
    rw [eqn]; calc _ ≤ 1*(1/4:ℝ)^n*4/15 := by
                         apply div_le_div₀ (by positivity) _ (by norm_num) (by linarith); gcongr
                   _ = _ := by rw [div_pow]; ring
  have obs := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1) (f:=kernel (n+1) n) (C:=4/(15*4^n)) (by
    intro t ht; apply point; rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at ht; exact ⟨ht.1.le,ht.2⟩)
  simp only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] at obs
  apply (div_le_div_of_nonneg_right obs (by positivity : (0:ℝ)≤15^n)).trans_eq
  rw [show (60:ℝ)=4*15 by norm_num,mul_pow]; ring

/-- The same rational suffices for every position of a hexadecimal block. -/
theorem shadow_error_after_shifts (n i : ℕ) :
    |(16:ℝ)^(n+i)*π-(16:ℝ)^i*shadow n n| ≤ (16:ℝ)^i*4/(15*60^n) := by
  rw [show (16:ℝ)^(n+i)*π-(16:ℝ)^i*shadow n n = (16:ℝ)^i*((16:ℝ)^n*π-shadow n n) by rw [pow_add]; ring,
    abs_mul,abs_of_pos (by positivity : (0:ℝ)<16^i),mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (shadow_error n) (by positivity)

end NormalityChecker.BBP
