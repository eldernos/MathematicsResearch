module

public import NormalityChecker.StridedLogarithm
public import NormalityChecker.LogShadowIntegral

/-! Finite beta corrections on signed logarithmic strides. -/
@[expose] public section
open MeasureTheory Set intervalIntegral
namespace NormalityChecker.CorrectedStrides

def raw (a : ℤ) : ℕ → ℚ
  | 0 => 0
  | m+1 => a*raw a m+1/(m+1:ℚ)

def corrected (a : ℤ) (m : ℕ) : ℕ → ℚ
  | 0 => raw a m
  | r+1 => corrected a m r+((-1:ℚ)^r/(a-1:ℚ)^(r+1))*logDifference r m

noncomputable def moment (a : ℤ) (m r : ℕ) :=
  ∫ t : ℝ in 0..1, t^m*(1-t)^r/(a-t)

private lemma continuous_kernel {a : ℤ} (away : ∀ t∈Icc (0:ℝ) 1, (a:ℝ)≠t) (m r : ℕ) :
    IntervalIntegrable (fun t : ℝ => t^m*(1-t)^r/(a-t)) volume 0 1 :=
  ((by fun_prop : Continuous (fun t : ℝ => t^m*(1-t)^r)).continuousOn.div
    (by fun_prop) (fun t ht => sub_ne_zero.mpr (away t ht))).intervalIntegrable_of_Icc (by norm_num)

private lemma raw_integral {a : ℤ} (away : ∀ t∈Icc (0:ℝ) 1, (a:ℝ)≠t) (m : ℕ) :
    (a:ℝ)^m*moment a 0 0-raw a m = moment a m 0 := by
  induction m with
  | zero => simp [raw]
  | succ m ih =>
    have step : moment a (m+1) 0=(a:ℝ)*moment a m 0-1/((m:ℝ)+1) := by
      have ip : (∫ t : ℝ in 0..1,t^m)=1/((m:ℝ)+1) := by rw [integral_pow]; simp
      rw [←ip,moment,moment,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub
        ((continuous_kernel away m 0).const_mul _) (Continuous.intervalIntegrable (by fun_prop) ..)]
      apply integral_congr; intro t ht; rw [uIcc_of_le (by norm_num)] at ht
      simp only [pow_zero,mul_one,pow_succ]; field_simp [sub_ne_zero.mpr (away t ht)]; ring
    rw [step,←ih,raw,pow_succ]; push_cast; ring

/-- Exact rational correction and signed residual in every degree, including zero. -/
theorem corrected_integral {a : ℤ} (away : ∀ t∈Icc (0:ℝ) 1, (a:ℝ)≠t) (m r : ℕ) :
    (a:ℝ)^m*moment a 0 0-corrected a m r =
      ((-1:ℝ)^r/(a-1:ℝ)^r)*moment a m r := by
  have nz : (a:ℝ)-1≠0 := sub_ne_zero.mpr (away 1 ⟨by norm_num,le_rfl⟩)
  induction r with
  | zero => simpa [corrected] using raw_integral away m
  | succ r ih =>
    have step : moment a m (r+1)=(logDifference r m:ℝ)-((a:ℝ)-1)*moment a m r := by
      rw [← beta_difference,moment,moment,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) ..) ((continuous_kernel away m r).const_mul _)]
      apply integral_congr; intro t ht; rw [uIcc_of_le (by norm_num)] at ht
      dsimp only; rw [pow_succ]; field_simp [sub_ne_zero.mpr (away t ht)]; ring
    rw [corrected, Rat.cast_add,sub_add_eq_sub_sub,ih,step]; push_cast; simp only [pow_succ]
    field_simp; ring

theorem corrected_error {a : ℤ} (gap : ∀ t∈Icc (0:ℝ) 1, 1≤|(a:ℝ)-t|) (m r : ℕ) :
    |(a:ℝ)^m*moment a 0 0-corrected a m r|≤(logDifference r m:ℝ)/|(a:ℝ)-1|^r := by
  have away : ∀ t∈Icc (0:ℝ) 1,(a:ℝ)≠t := by
    intro t ht eqn; have h := gap t ht; rw [eqn,sub_self,abs_zero] at h; linarith
  have bnd : |moment a m r| ≤ (logDifference r m:ℝ) := by
    unfold moment; apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans
    rw [←beta_difference]
    apply intervalIntegral.integral_mono_on (by norm_num) (continuous_kernel away m r).abs
      (Continuous.intervalIntegrable (by fun_prop) ..)
    intro t ht
    rw [abs_div,abs_of_nonneg (mul_nonneg (pow_nonneg ht.1 _) (pow_nonneg (sub_nonneg.mpr ht.2) _))]
    exact div_le_self (by positivity [sub_nonneg.mpr ht.2,ht.1]) (gap t ht)
  rw [corrected_integral away,abs_mul,abs_div,abs_pow,abs_pow,abs_neg,abs_one,one_pow,one_div]
  simpa [div_eq_inv_mul] using mul_le_mul_of_nonneg_left bnd (by positivity : 0≤(|(a:ℝ)-1|^r)⁻¹)

private lemma inv_den {j M : ℕ} (pos : 0<j) (h : j≤M) : ((1:ℚ)/j).den ∣ Nat.lcmUpto M := by
  simpa [one_div,Rat.inv_natCast_den_of_pos pos] using index_dvd_lcm pos h

theorem beta_den {m r M : ℕ} (h : m+r+1≤M) : (logDifference r m).den ∣ Nat.lcmUpto M := by
  induction r generalizing m with
  | zero => rw [difference_zero]; simpa using inv_den (j:=m+1) (by omega) (by omega : m+1≤M)
  | succ r ih =>
    rw [←difference_step]
    exact (Rat.sub_den_dvd_lcm ..).trans (Nat.lcm_dvd (ih (by omega)) (ih (by omega)))

private lemma raw_den (a : ℤ) {m M : ℕ} (h : m≤M) : (raw a m).den∣Nat.lcmUpto M := by
  induction m with
  | zero => simp [raw]
  | succ m ih =>
    rw [raw]
    apply (Rat.add_den_dvd_lcm ..).trans (Nat.lcm_dvd ?_ ?_)
    · exact (Rat.mul_den_dvd ..).trans (by simpa using ih (by omega))
    · simpa using inv_den (j:=m+1) (by omega) h

private lemma coeff_den (a : ℤ) (r : ℕ) :
    (((-1:ℚ)^r/(a-1:ℚ)^(r+1))).den ∣ (a-1).natAbs^(r+1) := by
  have hd := Rat.den_dvd ((-1:ℤ)^r) ((a-1)^(r+1))
  rw [Rat.divInt_eq_div] at hd
  have d := Int.natCast_dvd.mp hd
  simpa using d

theorem corrected_den (a : ℤ) {m r M : ℕ} (h : m+r≤M) :
    (corrected a m r).den ∣ (a-1).natAbs^r * Nat.lcmUpto M := by
  induction r with
  | zero => simpa [corrected] using raw_den a (by omega : m≤M)
  | succ r ih =>
    rw [corrected]; apply (Rat.add_den_dvd_lcm ..).trans (Nat.lcm_dvd ?_ ?_)
    · exact (ih (by omega)).trans (mul_dvd_mul_right (pow_dvd_pow _ (by omega)) _)
    · exact (Rat.mul_den_dvd ..).trans (Nat.mul_dvd_mul (coeff_den ..) (beta_den (by omega)))

def mulTwo (N : ℕ) : ℤ := 2*2^(N%2)
def mulThree (N : ℕ) : ℤ := (-1)^(N/3)*2^(N%3)

/-- Rational model of the actual binary shift at N, at independent orders. -/
def model (N r s : ℕ) : ℚ :=
  mulTwo N * corrected 4 (N/2) r - mulThree N * corrected (-8) (N/3) s

theorem model_den (N r s : ℕ) :
    (model N r s).den ∣ 3^(max r (2*s))*Nat.lcmUpto (max (N/2+r) (N/3+s)) := by
  let M := max (N/2+r) (N/3+s)
  have d := corrected_den 4 (le_max_left (N/2+r) (N/3+s))
  have e := corrected_den (-8) (le_max_right (N/2+r) (N/3+s))
  change (corrected 4 (N/2) r).den ∣ 3^r*Nat.lcmUpto M at d
  change (corrected (-8) (N/3) s).den ∣ 9^s*Nat.lcmUpto M at e
  rw [show 9^s=(3:ℕ)^(2*s) by rw [pow_mul]; norm_num] at e
  unfold model; apply (Rat.sub_den_dvd_lcm ..).trans (Nat.lcm_dvd ?_ ?_)
  · exact (Rat.mul_den_dvd ..).trans (by simpa using d.trans (mul_dvd_mul_right (pow_dvd_pow 3 (le_max_left r (2*s))) (Nat.lcmUpto M)))
  · exact (Rat.mul_den_dvd ..).trans (by simpa using e.trans (mul_dvd_mul_right (pow_dvd_pow 3 (le_max_right r (2*s))) (Nat.lcmUpto M)))

private theorem values : 2*moment 4 0 0-moment (-8) 0 0=Real.log 2 := by
  have pos : moment 4 0 0=Real.log (4/3) := by
    unfold moment; norm_num only [pow_zero,mul_one,Int.cast_ofNat]
    rw [integral_comp_sub_left (fun t : ℝ => 1/t) 4,integral_one_div_of_pos (by norm_num) (by norm_num)]
    norm_num
  have neg : moment (-8) 0 0=Real.log (8/9) := by
    unfold moment; norm_num only [pow_zero,mul_one,Int.cast_neg,Int.cast_ofNat]
    rw [integral_comp_sub_left (fun t : ℝ => 1/t) (-8),integral_one_div_of_neg (by norm_num) (by norm_num)]
    norm_num
  rw [pos,neg]
  have id : (4/3:ℝ)^2/(8/9)=2 := by norm_num
  have logid := congrArg Real.log id
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow] at logid; exact_mod_cast logid

theorem model_error (N r s : ℕ) :
    |(2:ℝ)^N*Real.log 2-model N r s| ≤
      (2*2^(N%2):ℝ)*logDifference r (N/2)/3^r + (2^(N%3):ℝ)*logDifference s (N/3)/9^s := by
  have four : (2:ℝ)^(N%2)*4^(N/2)=2^N := by
    rw [show (4:ℝ)=2^2 by norm_num,←pow_mul,←pow_add,Nat.mod_add_div]
  have eight : ((-1:ℝ)^(N/3)*2^(N%3))*(-8)^(N/3)=2^N := by
    rw [mul_right_comm,←mul_pow]; norm_num; rw [mul_comm,show (8:ℝ)=2^3 by norm_num,←pow_mul,←pow_add,Nat.mod_add_div]
  have decomp : (2:ℝ)^N*Real.log 2-model N r s =
      (mulTwo N:ℝ)*(4^(N/2)*moment 4 0 0-corrected 4 (N/2) r) -
      (mulThree N:ℝ)*((-8)^(N/3)*moment (-8) 0 0-corrected (-8) (N/3) s) := by
    rw [←values]; simp [model,mulTwo,mulThree]; linear_combination
      -(2*moment 4 0 0)*four + moment (-8) 0 0*eight
  rw [decomp]
  apply (abs_sub ..).trans
  rw [abs_mul,abs_mul]
  have d := corrected_error (a:=4) (by intro t ht; rw [abs_of_nonneg] <;> norm_num <;> linarith [ht.2]) (N/2) r
  have e := corrected_error (a:=-8) (by intro t ht; rw [abs_of_nonpos] <;> norm_num <;> linarith [ht.1]) (N/3) s
  norm_num at d e
  have am : |(mulThree N:ℝ)|=2^(N%3) := by simp [mulThree,abs_mul,abs_pow]
  have bm : |(mulTwo N:ℝ)|=2*2^(N%2) := by simp [mulTwo,abs_mul,abs_pow]
  rw [am,bm]; simpa [mul_div_assoc] using add_le_add
    (mul_le_mul_of_nonneg_left d (by positivity : (0:ℝ)≤2*2^(N%2)))
    (mul_le_mul_of_nonneg_left e (by positivity : (0:ℝ)≤2^(N%3)))

end NormalityChecker.CorrectedStrides
