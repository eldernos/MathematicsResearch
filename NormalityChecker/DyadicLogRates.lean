module

public import NormalityChecker.StrideDenominatorRate
public import NormalityChecker.PolylogGrowth

/-! Exact denominator rates for ordinary binary shifts of dyadic logarithms. -/
@[expose] public section
open Filter
open scoped Topology
namespace NormalityChecker

/-- The all-radix order-one polylogarithm denominator rate, from the finite loss bound. -/
theorem polylog_first_den_rate {b : ℕ} (hb : 2≤b) :
    Tendsto (fun n : ℕ => Real.log (Polylog.denominator b 1 n)/n) atTop (𝓝 1) := by
  have little : (fun n : ℕ => (n:ℝ)^(2/3:ℝ)) =o[atTop] (fun n : ℕ => (n:ℝ)) := by
    apply Asymptotics.isLittleO_of_tendsto (fun n hn => by simp [hn])
    apply ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    change (n:ℝ)^(-(1/3):ℝ)=_/_
    rw [show -(1/3:ℝ)=2/3-1 by norm_num,Real.rpow_sub (by positivity),Real.rpow_one]
  have loss := ((Polylog.loss_isBigO hb 1).trans_isLittleO little).tendsto_div_nhds_zero
  have orig := Nat.tendsto_log_lcmUpto_div_atTop.sub loss
  rw [sub_zero] at orig
  apply orig.congr; intro n
  have den_pos := (Polylog.shifted b 1 n).pos
  simp only [Polylog.loss,pow_one]
  rw [Real.log_div (by exact_mod_cast Nat.lcmUpto_ne_zero n) (by exact_mod_cast den_pos.ne')]
  ring

/-- Model 2^N times the truncation of −log(1−2⁻ᵏ), allowing every residue of N mod k. -/
def dyadicLogPrefix (k N : ℕ) : ℚ :=
  (2:ℚ)^(N%k)*Polylog.shifted (2^k) 1 (N/k)

theorem dyadicLogPrefix_eq (k N : ℕ) :
    dyadicLogPrefix k N = 2^N*Polylog.partialSum (2^k) 1 (N/k) := by
  unfold dyadicLogPrefix; rw [←Polylog.shifted_eq (pow_pos (by decide) k),←mul_assoc]
  push_cast; rw [←pow_mul,←pow_add,Nat.mod_add_div]

/-- The loss from an incomplete stride is bounded by the fixed multiplier 2^k. -/
theorem dyadicLogPrefix_rate {k : ℕ} (hk : 0<k) :
    Tendsto (fun N : ℕ => Real.log (dyadicLogPrefix k N).den/N) atTop (𝓝 (1/(k:ℝ))) := by
  let f (N : ℕ) := Polylog.denominator (2^k) 1 (N/k)
  have b : 2≤2^k := (Nat.pow_le_pow_right (by decide : 0<2) (show 1≤k by omega))
  have grow := Nat.tendsto_div_const_atTop hk.ne'
  have t := ((polylog_first_den_rate b).comp grow).mul (StrideDenominatorRate.floor_ratio k hk)
  rw [one_mul] at t
  have lim : Tendsto (fun n : ℕ => Real.log (f n)/n) atTop (𝓝 (1/(k:ℝ))) := by
    apply t.congr'; filter_upwards [grow.eventually_gt_atTop 0] with n hn
    change Real.log (f n)/(n/k:ℕ)*(((n/k:ℕ):ℝ)/n)=_
    rw [div_mul_div_cancel₀ (by exact_mod_cast hn.ne' : ((n/k:ℕ):ℝ)≠0)]
  have low := lim.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log ((2:ℝ)^k)))
  rw [sub_zero] at low
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le low lim <;> intro n
  · let c := (2:ℕ)^(n%k)
    let y := dyadicLogPrefix k n
    have pos := (Polylog.shifted (2^k) 1 (n/k)).pos
    have id : Polylog.shifted (2^k) 1 (n/k)=y*(1/(c:ℚ)) := by
      dsimp [y,dyadicLogPrefix,c]; push_cast; field_simp
    have dv := Rat.mul_den_dvd y (1/(c:ℚ))
    rw [←id,one_div,Rat.inv_natCast_den_of_pos (by dsimp [c]; positivity)] at dv
    have l := Real.log_le_log (show (0:ℝ)<f n by exact_mod_cast pos)
      (Nat.cast_le.mpr ((Nat.le_of_dvd (Nat.mul_pos y.pos (by dsimp [c]; positivity)) dv).trans
        (Nat.mul_le_mul_left y.den (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mod_lt n hk).le))))
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast y.pos.ne') (by positivity)] at l
    change Real.log (f n)/n-Real.log ((2:ℝ)^k)/n≤Real.log y.den/n
    norm_cast at l ⊢; push_cast at l ⊢
    rw [←sub_div]; apply div_le_div_of_nonneg_right _ (by positivity); linarith
  · have hd := Rat.mul_den_dvd ((2:ℚ)^(n%k)) (Polylog.shifted (2^k) 1 (n/k))
    have small : (dyadicLogPrefix k n).den∣f n := by simpa [dyadicLogPrefix,f,Polylog.denominator] using hd
    exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast (dyadicLogPrefix k n).pos)
      (Nat.cast_le.mpr (Nat.le_of_dvd (Polylog.shifted ..).pos small))) (by positivity)

end NormalityChecker
