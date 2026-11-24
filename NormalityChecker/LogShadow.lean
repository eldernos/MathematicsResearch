module

public import NormalityChecker.Correlations

/-! Rational block models for the logarithm with iterated finite-difference corrections. -/
@[expose] public section
open Finset
namespace NormalityChecker

/-- Magnitude of the order-`r` forward difference of `1/(n+1)`. -/
def logDifference (r n : ℕ) : ℚ := (r.factorial:ℚ)*n.factorial/(n+r+1).factorial

lemma difference_zero (n : ℕ) : logDifference 0 n=1/(n+1:ℚ) := by
  simp only [logDifference,Nat.add_zero,Nat.factorial_zero,Nat.cast_one,one_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add]
  field_simp [Nat.factorial_ne_zero]

lemma difference_step (r n : ℕ) : logDifference r n - logDifference r (n+1) = logDifference (r+1) n := by
  dsimp [logDifference]; rw [show n+1+r+1=(n+r+1)+1 by omega,show n+(r+1)+1=(n+r+1)+1 by omega]
  rw [Nat.factorial_succ (n+r+1),Nat.factorial_succ r,Nat.factorial_succ n]; push_cast
  field_simp; ring

private lemma difference_next (r n : ℕ) : logDifference (r+1) n = logDifference r n*((r+1:ℚ)/(n+r+2)) := by
  dsimp [logDifference]; rw [show n+(r+1)+1=(n+r+1)+1 by omega,Nat.factorial_succ (n+r+1),Nat.factorial_succ r]; push_cast; field_simp; ring

/-- Fix the correction order for the duration of a block. -/
def logShadow : ℕ → ℕ → ℚ
  | 0, n => logPrefix n
  | r+1, n => logShadow r n + (-1)^r*logDifference r n

/-- The remaining one-step error has an explicit sign and factorial quotient. -/
theorem logShadow_step (r n : ℕ) : logShadow r (n+1)-2*logShadow r n=(-1)^r*logDifference r n := by
  induction r with
  | zero => simp [logShadow,logPrefix,difference_zero]
  | succ r ih =>
    simp only [logShadow,pow_succ]; rw [← difference_step]; linarith only [ih]

private lemma difference_bound {m n r : ℕ} (hr : r≤n) (hm : n≤m) :
    logDifference r m ≤ (1/2:ℚ)^r/(n+1) := by
  induction r with
  | zero => rw [difference_zero,pow_zero]; gcongr
  | succ r ih =>
    have small : ((r:ℚ)+1)/(m+r+2)≤1/2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; have h : (r:ℚ)≤m := by exact_mod_cast (show r≤m by omega)
      linarith only [h]
    rw [difference_next,pow_succ,mul_div_right_comm]
    exact mul_le_mul (ih (by omega)) small (by positivity) (by positivity)

private lemma shadow_prefix {n r : ℕ} (hr : r≤n) :
    |logShadow r n-logPrefix n|≤(2-2*(1/2:ℚ)^r)/(n+1) := by
  induction r with
  | zero => simp [logShadow]
  | succ r ih =>
    rw [logShadow,add_sub_right_comm]; apply (abs_add_le ..).trans
    rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul, abs_of_nonneg (show 0≤logDifference r n by dsimp [logDifference]; positivity)]
    apply (add_le_add (ih (by omega)) (difference_bound (by omega : r≤n) le_rfl)).trans_eq
    rw [pow_succ]; ring

/-- Uniform local error on a block. Its constants are explicit even when `r`
is chosen as a function of the starting position. -/
theorem logShadow_orbit_bound {r n : ℕ} (hr : r≤n) (i : ℕ) :
    |logShadow r (n+i)-(2:ℚ)^i*logShadow r n| ≤ (2^i-1)*((1/2:ℚ)^r/(n+1)) := by
  let e := (1/2:ℚ)^r/(n+1)
  induction i with
  | zero => simp
  | succ i ih =>
    have step := logShadow_step r (n+i)
    rw [Nat.add_succ,pow_succ']
    rw [show logShadow r (n+i+1)-2*2^i*logShadow r n =
      2*(logShadow r (n+i)-2^i*logShadow r n)+(-1)^r*logDifference r (n+i) by linarith only [step]]
    apply (abs_add_le ..).trans
    simp only [abs_mul, abs_of_nonneg (by norm_num : 0≤(2:ℚ)),abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_nonneg (show 0≤logDifference r (n+i) by dsimp [logDifference]; positivity)]
    apply (add_le_add (mul_le_mul_of_nonneg_left ih (by norm_num : 0≤(2:ℚ))) (difference_bound hr (Nat.le_add_right n i))).trans_eq
    ring

/-- A rational model shadows all actual rational prefixes on `[n,2n]` with
unwrapped error at most `3/(n+1)`. No smoothness assumption on its denominator. -/
theorem logPrefix_linear_shadow {i n : ℕ} (hi : i≤n) :
    |logPrefix (n+i)-(2:ℚ)^i*logShadow n n| ≤ 3/(n+1) := by
  have orbit := logShadow_orbit_bound (r:=n) le_rfl i
  have near := shadow_prefix (n:=n+i) (Nat.le_add_right n i)
  rw [abs_sub_comm] at near
  have a : (2-(2:ℚ)*(1/2)^(n:ℕ))/(↑(n+i)+1) ≤ 2/(n+1) := by
    apply div_le_div₀ (by norm_num) (by linarith [show 0≤(1/2:ℚ)^n by positivity]) (by positivity); push_cast; linarith [Nat.cast_nonneg (α:=ℚ) i]
  have b : ((2:ℚ)^i-1)*((1/2:ℚ)^n/(n+1))≤1/(n+1) := by
    rw [one_div_pow,← mul_div_assoc,mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_one₀ (by positivity)]; linarith only [pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) hi]
  apply (abs_sub_le _ (logShadow n (n+i)) _).trans
  apply (add_le_add (near.trans a) (orbit.trans b)).trans_eq; ring

/-- Divide the block error by `2^i` and let the block grow. The endpoint error
in the actual logarithm stays bounded, yielding exponential accuracy at the start. -/
theorem logTwo_corrected_tail {r n : ℕ} (hr : r≤n) :
    |(2:ℝ)^n*Real.log 2-(logShadow r n:ℝ)| ≤ (1/2:ℝ)^r/(n+1) := by
  let e := (1/2:ℝ)^r/(n+1)
  let A := |(2:ℝ)^n*Real.log 2-(logShadow r n:ℝ)|
  change A≤e; by_contra! bad
  obtain ⟨i,hi⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually_gt_atTop (3/(A-e))).exists
  have big := (div_lt_iff₀ (sub_pos.mpr bad)).mp hi
  let m := n+i
  have H := logTwo_tail_bounds m
  have hx : |(2:ℝ)^m*Real.log 2-(logPrefix m:ℝ)|≤1 := by
    rw [abs_of_nonneg H.1]; exact H.2.trans ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m]))
  have rle : r≤m := hr.trans (Nat.le_add_right ..)
  have near : |(logShadow r m:ℝ)-(logPrefix m:ℝ)| ≤ (2-2*(1/2:ℝ)^r)/(m+1) := by
    simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_natCast,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr (shadow_prefix rle)
  have cap : |(logPrefix m:ℝ)-(logShadow r m:ℝ)|≤2 := by
    rw [abs_sub_comm]; apply near.trans; rw [div_le_iff₀ (by positivity)]; linarith [show 0≤(1/2:ℝ)^r by positivity,Nat.cast_nonneg (α:=ℝ) m]
  have orbit : |(logShadow r m:ℝ)-2^i*(logShadow r n:ℝ)|≤(2^i-1)*e := by
    simpa only [e,m,Rat.cast_abs,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_natCast,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr (logShadow_orbit_bound hr i)
  have bound := (abs_sub_le ((2:ℝ)^m*Real.log 2) (logPrefix m:ℝ) ((2:ℝ)^i*(logShadow r n:ℝ))).trans
    (add_le_add hx ((abs_sub_le _ (logShadow r m:ℝ) _).trans (add_le_add cap orbit)))
  have id : |(2:ℝ)^m*Real.log 2-2^i*(logShadow r n:ℝ)|=2^i*A := by
    rw [show (2:ℝ)^m*Real.log 2-2^i*logShadow r n = 2^i*(2^n*Real.log 2-logShadow r n) by dsimp [m]; rw [pow_add]; ring,
      abs_mul,abs_of_nonneg (pow_nonneg (by norm_num : 0≤(2:ℝ)) i)]
  rw [id] at bound; nlinarith only [big,bound,show 0≤e by dsimp [e]; positivity]

end NormalityChecker
