module

public import NormalityChecker.BinomialShadow
public import NormalityChecker.DiagonalStep
public import Mathlib.Data.Nat.Choose.Dvd
public import NormalityChecker.ShadowGrowth

/-! Every large upper-half prime survives in at least one of two adjacent diagonal models. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

def binomialPrefix (p n d : ℕ) : ZMod p := ∑ j∈range (d+1),(n.choose j:ZMod p)

lemma pascal_prefix (p n d : ℕ) : binomialPrefix p (n+1) (d+1)=
    2*binomialPrefix p n d+(n.choose (d+1):ZMod p) := by
  induction d with
  | zero => simp [binomialPrefix,sum_range_succ,Nat.choose_succ_succ]; ring
  | succ d ih =>
    have step (m k : ℕ) : binomialPrefix p m (k+1)=binomialPrefix p m k+(m.choose (k+1):ZMod p) := sum_range_succ ..
    rw [step (n+1),ih,step n,Nat.choose_succ_succ]; push_cast; ring

/-- All primes greater than three in `(n,2*n+1]` occur in at least one neighbor. -/
theorem logShadow_adjacent_prime {p n : ℕ} (pr : p.Prime) (big : 3<p) (lo : n<p) (hi : p≤2*n+1) :
    p∣(logShadow n n).den ∨ p∣(logShadow (n+1) (n+1)).den := by
  have factor : p ∣ 2*(2*n+1)*n.centralBinom := by
    by_cases endpt : p=2*n+1
    · rw [endpt]; exact (dvd_mul_left ..).trans (dvd_mul_right ..)
    · have h := pr.dvd_choose_add lo lo (by omega : p≤n+n)
      exact (by simpa [Nat.centralBinom_eq_two_mul_choose,two_mul] using h : p∣n.centralBinom).trans (dvd_mul_left ..)
  have divides := (pr.dvd_mul.mp (factor.trans (logShadow_diagonal_lcm n))).resolve_left (Nat.not_dvd_of_pos_of_lt (by decide) big)
  exact pr.dvd_mul.mp (divides.trans (Nat.lcm_dvd (dvd_mul_right ..) (dvd_mul_left ..)))

/-- Joint logarithmic denominator growth, including all primes in the open overlap. -/
theorem logShadow_adjacent_theta {n : ℕ} (hn : 3≤n) :
    Chebyshev.theta (2*n:ℕ)-Chebyshev.theta (n+1:ℕ) ≤ Real.log (logShadow n n).den+Real.log (logShadow (n+1) (n+1)).den := by
  let P := (2*n).primesLE \ (n+1).primesLE
  have sub := Nat.primesLE_mono (show n+1≤2*n by omega)
  have mem (p : ℕ) (h : p∈P) : p.Prime ∧ p≤2*n ∧ n+1<p := by
    obtain ⟨a,c⟩ := mem_sdiff.mp h; obtain ⟨u,pr⟩ := Nat.mem_primesLE.mp a
    exact ⟨pr,u,lt_of_not_ge (fun l => c (Nat.mem_primesLE.mpr ⟨l,pr⟩))⟩
  have dvd : (∏ p∈P,p)∣(logShadow n n).den*(logShadow (n+1) (n+1)).den := prod_primes_dvd _ (fun p h => (mem p h).1.prime) (by
    intro p h; obtain ⟨pr,hi,lo⟩ := mem p h; exact pr.dvd_mul.mpr (logShadow_adjacent_prime pr (by omega) (by omega) (by omega)))
  have le := Nat.le_of_dvd (Nat.mul_pos (logShadow n n).pos (logShadow (n+1) (n+1)).pos) dvd
  have pos := prod_pos (fun p h => (mem p h).1.pos)
  have bound := Real.log_le_log (show (0:ℝ)<(∏ p∈P,p:ℕ) by exact_mod_cast pos) ((Nat.cast_le (α:=ℝ)).mpr le)
  rw [Nat.cast_prod,Real.log_prod (fun p h => by exact_mod_cast (mem p h).1.ne_zero),Nat.cast_mul,Real.log_mul (by exact_mod_cast (logShadow n n).pos.ne') (by exact_mod_cast (logShadow (n+1) (n+1)).pos.ne')] at bound
  rwa [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log,← sum_sdiff sub,add_sub_cancel_right]

/-- At least one model in every sufficiently large adjacent pair has an exponential denominator. -/
theorem logShadow_adjacent_growth {ε : ℝ} (pos : 0<ε) : ∀ᶠ n : ℕ in atTop,
    (1/2-ε)*n ≤ max (Real.log (logShadow n n).den) (Real.log (logShadow (n+1) (n+1)).den) := by
  have top := tendsto_natCast_atTop_atTop (R:=ℝ)
  have grow := top.const_mul_atTop (by norm_num : (0:ℝ)<2)
  have f := ((Chebyshev.tendsto_theta_div_atTop.comp grow).mul_const 2).eventually_const_lt (by linarith : 2-ε<1*2)
  have g := (Chebyshev.tendsto_theta_div_atTop.comp (tendsto_atTop_add_const_right _ 1 top)).eventually_lt_const (by linarith : 1<1+ε/2)
  filter_upwards [f,g,top.eventually_gt_atTop (2/ε+2),eventually_ge_atTop 3] with n h₁ h₂ big hn
  have nn : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  change 2-ε<Chebyshev.theta (2*n)/(2*n)*2 at h₁
  change Chebyshev.theta ((n:ℝ)+1)/(n+1)<1+ε/2 at h₂
  have b1 : (2-ε)*n<Chebyshev.theta (2*n) := by field_simp [nn.ne'] at h₁; linarith
  rw [div_lt_iff₀ (by linarith)] at h₂
  have budget : 2<((n:ℝ)-2)*ε := (div_lt_iff₀ pos).mp (by linarith : 2/ε<(n:ℝ)-2)
  have obs := logShadow_adjacent_theta hn; push_cast at obs
  have l := le_max_left (Real.log (logShadow n n).den) (Real.log (logShadow (n+1) (n+1)).den)
  have r := le_max_right (Real.log (logShadow n n).den) (Real.log (logShadow (n+1) (n+1)).den)
  nlinarith only [budget,obs,b1,h₂,l,r,pos]

end NormalityChecker
