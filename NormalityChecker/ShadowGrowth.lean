module

public import NormalityChecker.ShadowDenominator
public import Mathlib.NumberTheory.LSeries.WeakPNT

/-! A uniform exponential obstruction below the diagonal correction order. -/
@[expose] public section
open Finset Filter Real Nat
open scoped Topology
namespace NormalityChecker

/-- A whole interval of surviving primes gives a finite logarithmic lower bound. -/
theorem logShadow_theta_lower {n r : ℕ} {x : ℝ} (hx : 2≤x) (hn : x≤n) (hr : (n+r:ℝ)≤2*x) :
    Chebyshev.theta n-Chebyshev.theta x ≤ Real.log (logShadow r n).den := by
  let S := n.primesLE \ (⌊x⌋₊).primesLE
  have sub := Nat.primesLE_mono (show ⌊x⌋₊ ≤ n by exact_mod_cast (Nat.floor_le (by linarith : 0≤x)).trans hn)
  have mem (p : ℕ) (h : p∈S) : p.Prime ∧ p≤n ∧ x<(p:ℝ) := by
    obtain ⟨a,c⟩ := mem_sdiff.mp h; obtain ⟨u,pr⟩ := Nat.mem_primesLE.mp a
    refine ⟨pr,u,?_⟩; by_contra! e; exact c (Nat.mem_primesLE.mpr ⟨Nat.le_floor e,pr⟩)
  have dvd : (∏ p∈S,p)∣(logShadow r n).den := prod_primes_dvd _ (fun p h => (mem p h).1.prime) (by
    intro p h; obtain ⟨pr,u,v⟩ := mem p h
    have two : (2:ℝ)<p := hx.trans_lt v
    exact logShadow_upper_prime pr (by rintro rfl; norm_num at two) u (by exact_mod_cast (show (n:ℝ)+r<2*p by linarith)))
  have positive := prod_pos (fun p h => (mem p h).1.pos)
  have bound := Real.log_le_log (show (0:ℝ)<(∏ p∈S,p:ℕ) by exact_mod_cast positive)
    ((Nat.cast_le (α:=ℝ)).mpr (Nat.le_of_dvd (logShadow r n).pos dvd))
  rw [Nat.cast_prod,Real.log_prod (fun p h => by exact_mod_cast (mem p h).1.ne_zero)] at bound
  rwa [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE,← sum_sdiff sub,add_sub_cancel_right]

/-- All `r ≤ θ n` satisfy the exponential denominator lower bound simultaneously,
for any fixed fraction below one and any positive slack in the exponent. -/
theorem logShadow_subcritical_growth {θ ε : ℝ} (nonneg : 0≤θ) (lt : θ<1) (pos : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, (r:ℝ)≤θ*n → ((1-θ)/2-ε)*n ≤ Real.log (logShadow r n).den := by
  let a := (1+θ)/2
  have ap : 0<a := by dsimp [a]; linarith
  have al : a≤1 := by dsimp [a]; linarith
  have grow : Tendsto (fun n : ℕ => a*(n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.const_mul_atTop ap
  have f := Chebyshev.tendsto_theta_div_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have g := (Chebyshev.tendsto_theta_div_atTop.comp grow).mul_const a
  have diff : Tendsto (fun n : ℕ => (Chebyshev.theta n-Chebyshev.theta (a*n))/(n:ℝ)) atTop (𝓝 (1-a)) := by
    convert (f.sub g).congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn; dsimp; field_simp [ap.ne',show (n:ℝ)≠0 by exact_mod_cast hn.ne']
  have ev := diff.eventually_const_lt (show 1-a-ε<1-a by linarith)
  filter_upwards [ev,grow.eventually_ge_atTop 2,eventually_gt_atTop 0] with n h big hn r hr
  have nr : (0:ℝ)<n := by exact_mod_cast hn
  have u := (lt_div_iff₀ nr).mp h
  have v := logShadow_theta_lower (n:=n) (r:=r) big ((mul_le_mul_of_nonneg_right al nr.le).trans_eq (one_mul _)) (by dsimp [a]; linarith)
  apply le_trans _ v; dsimp [a] at u; linarith

end NormalityChecker
