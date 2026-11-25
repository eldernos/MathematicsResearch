module

public import NormalityChecker.ParameterTwoQuadratic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Algebra.Polynomial.Roots

/-! Height and separation estimates for the shell index. -/
@[expose] public noncomputable section
open Polynomial Finset Filter
open scoped Topology
namespace NormalityChecker.ParameterTwoQuadratic

/-- A nonzero integer cannot simultaneously be small at the real and 2-adic places. -/
theorem integer_height {z : ℤ} (hz : z ≠ 0) : 1 ≤ (z.natAbs : ℝ) * ‖(z : ℚ_[2])‖ := by
  have h := Int.natAbs_le_of_dvd_ne_zero (padicValInt_dvd (p:=2) z) hz
  simp only [Int.natAbs_pow] at h
  rw [Padic.norm_eq_zpow_neg_valuation (Int.cast_ne_zero.mpr hz), Padic.valuation_intCast,
    zpow_neg, zpow_natCast, ← div_eq_mul_inv, one_le_div (by positivity)]
  exact_mod_cast h

/-- Integral polynomials are 1-Lipschitz on the 2-adic unit ball. At a
root this gives a direct estimate for its distance to any ordinary integer. -/
theorem polynomial_root_distance {x : ℚ_[2]} (P : ℤ[X]) (hx : ‖x‖ ≤ 1)
    (root : aeval x P = 0) (k : ℕ) :
    ‖((P.eval (k : ℤ) : ℤ) : ℚ_[2])‖ ≤ ‖(k : ℚ_[2]) - x‖ := by
  let u : ℤ_[2] := ⟨x, hx⟩
  let Q := P.map (Int.castRingHom ℤ_[2])
  obtain ⟨v,hv⟩ := sub_dvd_eval_sub (k : ℤ_[2]) u Q
  have castEval (z : ℤ_[2]) : ((Q.eval z : ℤ_[2]) : ℚ_[2]) = aeval (z : ℚ_[2]) P := by
    rw [show Q = P.map (Int.castRingHom ℤ_[2]) from rfl, eval_map, aeval_def]
    exact P.hom_eval₂ (Int.castRingHom ℤ_[2]) PadicInt.Coe.ringHom z
  have h := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hv
  simp only [PadicInt.coe_sub, PadicInt.coe_mul, castEval, PadicInt.coe_natCast,
    show (u : ℚ_[2]) = x from rfl, root, sub_zero] at h
  have zk : aeval (k : ℚ_[2]) P = ((P.eval (k : ℤ) : ℤ) : ℚ_[2]) :=
    P.eval₂_at_natCast (Int.castRingHom ℚ_[2]) k
  rw [← zk, h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) v.2

private lemma eval_bound (P : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) :
    (P.eval (k : ℤ)).natAbs ≤ (∑ i ∈ range (P.natDegree+1), (P.coeff i).natAbs) * k^P.natDegree := by
  rw [eval_eq_sum_range, sum_mul]
  refine (Int.natAbs_sum_le ..).trans (sum_le_sum fun i hi => ?_)
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hk (by simpa [Nat.lt_succ_iff] using hi))

private lemma late_eval_ne_zero {P : ℤ[X]} (hP : P ≠ 0) : ∀ᶠ k : ℕ in atTop, P.eval (k : ℤ) ≠ 0 := by
  let M := P.roots.toFinset.sup Int.natAbs
  filter_upwards [eventually_ge_atTop (M+1)] with k hk he
  have hin : (k : ℤ) ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hP).mpr he)
  have le : (k : ℤ).natAbs ≤ M := Finset.le_sup (f:=Int.natAbs) hin
  simp at le
  omega

/-- For any algebraic 2-adic number, the geometric denominator scale times
the distance to the integer index grows without bound. -/
theorem algebraic_growth {x : ℚ_[2]} (hx : IsAlgebraic ℚ x) :
    Tendsto (fun k : ℕ => (2 : ℝ)^k * ‖(k : ℚ_[2]) - x‖) atTop atTop := by
  by_cases hu : ‖x‖ ≤ 1
  · obtain ⟨P, hP, root⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℚ_[2]).mpr hx
    let H := 1 + ∑ i ∈ range (P.natDegree+1), (P.coeff i).natAbs
    have hH : 0 < (H : ℝ) := by dsimp [H]; positivity
    have bound : ∀ᶠ k : ℕ in atTop, 1 ≤ (H : ℝ) * (k : ℝ)^P.natDegree * ‖(k : ℚ_[2])-x‖ := by
      filter_upwards [late_eval_ne_zero hP, eventually_ge_atTop 1] with k hk kpos
      refine (integer_height hk).trans (mul_le_mul ?_ (polynomial_root_distance P hu root k)
        (norm_nonneg _) (by positivity))
      exact_mod_cast (eval_bound P kpos).trans (Nat.mul_le_mul_right _ (show _ ≤ H by dsimp [H]; omega))
    have small := (tendsto_pow_const_div_const_pow_of_one_lt P.natDegree (by norm_num : 1 < (2 : ℝ))).const_mul (H : ℝ)
    rw [mul_zero] at small
    have positive : ∀ᶠ k : ℕ in atTop, 0 < (H : ℝ)*((k : ℝ)^P.natDegree / 2^k) := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      have : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      positivity
    apply tendsto_atTop_mono' atTop _ ((tendsto_nhdsWithin_iff.mpr ⟨small, positive⟩).inv_tendsto_nhdsGT_zero)
    filter_upwards [bound, positive] with k hk hp
    change ((H : ℝ) * ((k : ℝ)^P.natDegree / 2^k))⁻¹ ≤ _
    rw [inv_le_iff_one_le_mul₀ hp]
    convert hk using 1
    field_simp
  · have hn (k : ℕ) : ‖(k : ℚ_[2])-x‖ = ‖x‖ := by
      have hlt : ‖(k : ℚ_[2])‖ < ‖x‖ :=
        (by simpa using Padic.norm_int_le_one (p:=2) (k : ℤ) : ‖(k : ℚ_[2])‖ ≤ 1).trans_lt (lt_of_not_ge hu)
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by simpa using hlt.ne), norm_neg, max_eq_right hlt.le]
    simp only [hn, mul_comm _ ‖x‖]
    exact Tendsto.const_mul_atTop (by linarith) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- The positive reduced denominators at the actual upper midpoints grow for
algebraic `kappa`; the exact profile transfers this to every upper cutoff. -/
theorem algebraic_upper_growth {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (A B C₀ : ℤ) (hA : A ≠ 0)
    (alg : IsAlgebraic ℚ (kappa b A B)) :
    Tendsto (fun j : ℕ => ((«prefix» b (3*2^j) A B C₀).den : ℝ)) atTop atTop := by
  have hp : 0 < ‖2*(A : ℚ_[2])*slope b‖ := by
    rw [norm_mul, norm_mul, slope_norm hb odd]
    exact mul_pos (mul_pos (norm_pos_iff.mpr (by norm_num)) (norm_pos_iff.mpr (Int.cast_ne_zero.mpr hA)))
      (norm_pos_iff.mpr (delta_zero_ne hb))
  have h := (algebraic_growth alg).comp (tendsto_add_atTop_nat 1)
  refine tendsto_atTop_mono' atTop (.of_forall fun j => ?_) (h.const_mul_atTop hp)
  have hi : 3*2^j < 2^(j+2) := by rw [pow_add]; have := Nat.two_pow_pos j; omega
  dsimp only [Function.comp_apply]
  rw [upper_denominator hb odd le_rfl hi A B C₀ hA]
  refine le_trans ?_ (le_max_right ..)
  simp only [norm_mul]
  ring_nf
  rfl

private theorem gap_norm (x : ℚ_[2]) {i j : ℕ} (hij : i ≤ j) :
    ‖((j-i : ℕ) : ℚ_[2])‖ ≤ max ‖(i : ℚ_[2])-x‖ ‖(j : ℚ_[2])-x‖ := by
  have h := Padic.nonarchimedean (-((i : ℚ_[2])-x)) ((j : ℚ_[2])-x)
  rw [norm_neg, show -((i : ℚ_[2])-x)+((j : ℚ_[2])-x) = (j : ℚ_[2])-i by ring] at h
  rwa [Nat.cast_sub hij]

/-- Two ordinary indices approximating one 2-adic target to precision `m`
are congruent, including when one is the target itself. -/
theorem two_power_dvd_gap (x : ℚ_[2]) {i j m : ℕ} (hij : i ≤ j)
    (hi : ‖(i : ℚ_[2])-x‖ ≤ (2 : ℝ)^(-(m : ℤ))) (hj : ‖(j : ℚ_[2])-x‖ ≤ (2 : ℝ)^(-(m : ℤ))) :
    2^m ∣ j-i := by
  have h := (gap_norm x hij).trans (max_le hi hj)
  have hd := (Padic.norm_int_le_pow_iff_dvd (p:=2) ((j-i : ℕ) : ℤ) m).mp (by simpa using h)
  exact_mod_cast hd

/-- If two actual upper-shell denominators are at most `Q`, the distance
between their shell indices is at least `2^(i+1) * ‖2*A*slope b‖ / Q`. -/
theorem bounded_upper_separation {b i j n m : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hij : i < j)
    (ni : 3*2^i ≤ n) (ni' : n < 2^(i+2)) (mj : 3*2^j ≤ m) (mj' : m < 2^(j+2))
    (A B C₀ : ℤ) (hA : A ≠ 0) {Q : ℝ}
    (hn : ((«prefix» b n A B C₀).den : ℝ) ≤ Q) (hm : ((«prefix» b m A B C₀).den : ℝ) ≤ Q) :
    (2 : ℝ)^(i+1) * ‖2*(A : ℚ_[2])*slope b‖ ≤ ((j-i : ℕ) : ℝ)*Q := by
  let x := kappa b A B
  let c := ‖2*(A : ℚ_[2])*slope b‖
  let R := (2 : ℝ)^(i+1)*c
  have hR : 0 ≤ R := by dsimp [R, c]; positivity
  rw [upper_denominator hb odd ni ni' A B C₀ hA, max_le_iff, norm_mul, ← mul_assoc] at hn
  rw [upper_denominator hb odd mj mj' A B C₀ hA, max_le_iff, norm_mul, ← mul_assoc] at hm
  have hi : R*‖((i+1 : ℕ) : ℚ_[2])-x‖ ≤ Q := hn.2
  have hj : R*‖((j+1 : ℕ) : ℚ_[2])-x‖ ≤ Q := by
    apply le_trans _ hm.2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega)) (norm_nonneg _)) (norm_nonneg _)
  have d := gap_norm x (show i+1 ≤ j+1 by omega)
  rw [Nat.add_sub_add_right] at d
  have small : R*‖((j-i : ℕ) : ℚ_[2])‖ ≤ Q :=
    (mul_le_mul_of_nonneg_left d hR).trans (by rw [mul_max_of_nonneg _ _ hR]; exact max_le hi hj)
  have hz := integer_height (z:=((j-i : ℕ) : ℤ)) (by exact_mod_cast Nat.sub_ne_zero_of_lt hij)
  simp only [Int.natAbs_natCast, Int.cast_natCast] at hz
  calc
    R ≤ R * (((j-i : ℕ) : ℝ)*‖((j-i : ℕ) : ℚ_[2])‖) := le_mul_of_one_le_right hR hz
    _ = ((j-i : ℕ) : ℝ)*(R*‖((j-i : ℕ) : ℚ_[2])‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left small (by positivity)

/-- At most one upper midpoint in any sufficiently late window of `H`
successive shell indices has denominator strictly smaller than `M`. -/
theorem midpoint_window_unique {b : ℕ} (hb : 3 ≤ b) (odd : Odd b)
    (A B C₀ : ℤ) (hA : A ≠ 0) (M H : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ i ∈ Finset.Ico t (t+H), ∀ j ∈ Finset.Ico t (t+H),
      («prefix» b (3*2^i) A B C₀).den < M → («prefix» b (3*2^j) A B C₀).den < M → i = j := by
  let c := ‖2*(A : ℚ_[2])*slope b‖
  have hc : 0 < c := by
    dsimp [c]
    rw [norm_mul, norm_mul, slope_norm hb odd]
    exact mul_pos (mul_pos (norm_pos_iff.mpr (by norm_num)) (norm_pos_iff.mpr (Int.cast_ne_zero.mpr hA)))
      (norm_pos_iff.mpr (delta_zero_ne hb))
  have tend := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℝ))).const_mul_atTop hc
  filter_upwards [tend.eventually_gt_atTop ((H : ℝ)*M)] with t ht i hi j hj di dj
  have impossible {a d : ℕ} (had : a < d) (ha : a ∈ Finset.Ico t (t+H)) (hd : d ∈ Finset.Ico t (t+H))
      (da : («prefix» b (3*2^a) A B C₀).den < M) (dd : («prefix» b (3*2^d) A B C₀).den < M) : False := by
    have endpt (u : ℕ) : 3*2^u < 2^(u+2) := by rw [pow_add]; have := Nat.two_pow_pos u; omega
    have gap := bounded_upper_separation hb odd had le_rfl (endpt a) le_rfl (endpt d) A B C₀ hA
      (Q := (M : ℝ)) (by exact_mod_cast da.le) (by exact_mod_cast dd.le)
    obtain ⟨ta, ah⟩ := mem_Ico.mp ha
    obtain ⟨td, dh⟩ := mem_Ico.mp hd
    have lo : c * (2 : ℝ)^t ≤ (2 : ℝ)^(a+1) * c := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hc.le
    have up : ((d-a : ℕ) : ℝ)*M ≤ (H : ℝ)*M := by exact_mod_cast Nat.mul_le_mul_right M (by omega : d-a ≤ H)
    exact (not_lt_of_ge (lo.trans (gap.trans up))) ht
  exact le_antisymm (le_of_not_gt fun h => impossible h hj hi dj di)
    (le_of_not_gt fun h => impossible h hi hj di dj)

end NormalityChecker.ParameterTwoQuadratic
