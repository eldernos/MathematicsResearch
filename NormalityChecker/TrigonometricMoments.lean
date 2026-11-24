module

public import NormalityChecker.FirstFrequency
public import Mathlib.NumberTheory.Real.Irrational

/-! An aggregate spike criterion for binary discrepancy. -/
@[expose] public section
open Finset Filter Real
open scoped Topology
namespace NormalityChecker

noncomputable def cosineSpike (x : ℝ) (n : ℕ) := -log |cos (π * (2^n*x))|

private lemma sine_ne_zero {x : ℝ} (hx : Irrational x) (n : ℕ) : sin (π*(2^n*x))≠0 := by
  intro hz; obtain ⟨z,hz⟩ := sin_eq_zero_iff.mp hz
  apply hx.ne_rational z ((2:ℤ)^n)
  push_cast; apply (eq_div_iff (pow_ne_zero n (by norm_num : (2:ℝ)≠0))).mpr
  apply mul_left_cancel₀ Real.pi_ne_zero; linear_combination -hz

/-- Exact finite conservation law, including both endpoint terms. -/
theorem cosineSpike_sum {x : ℝ} (hx : Irrational x) (N : ℕ) :
    ∑ n∈range N, cosineSpike x n = N*log 2 + log |sin (π*x)|-log |sin (π*(2^N*x))| := by
  induction N with
  | zero => simp
  | succ N ih =>
    let u := π*(2^N*x)
    have double : π*(2^(N+1)*x)=2*u := by dsimp [u]; rw [pow_succ]; ring
    have hz := sine_ne_zero hx (N+1); rw [double,sin_two_mul] at hz
    have hc : cos u≠0 := right_ne_zero_of_mul hz
    have hs := sine_ne_zero hx N
    rw [sum_range_succ,ih,double,sin_two_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
      log_mul (mul_ne_zero two_ne_zero (abs_ne_zero.mpr hs)) (abs_ne_zero.mpr hc),log_mul two_ne_zero (abs_ne_zero.mpr hs)]
    dsimp only [cosineSpike,u]; push_cast; ring

private lemma spike_outside {x : ℝ} (n : ℕ) (miss : ¬(1/4≤shift 2 x n ∧ shift 2 x n<3/4)) :
    cosineSpike x n ≤ log 2/2 := by
  let y := shift 2 x n
  let u := π*(2^n*x)
  have h0 : 0≤y := Int.fract_nonneg _
  have h1 : y<1 := Int.fract_lt_one _
  have sign : 0≤cos (2*π*y) := by
    by_cases h : y<1/4
    · apply cos_nonneg_of_mem_Icc; constructor <;> nlinarith [mul_nonneg pi_pos.le h0,mul_nonneg pi_pos.le (sub_nonneg.mpr h.le),pi_pos]
    · have H : 3/4≤y := le_of_not_gt (fun l => miss ⟨le_of_not_gt h,l⟩)
      rw [← cos_sub_two_pi]; apply cos_nonneg_of_mem_Icc; constructor <;> nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr H),mul_nonneg pi_pos.le (sub_nonneg.mpr h1.le),pi_pos]
  have eqn : cos (2*π*y)=cos (2*u) := by
    dsimp only [y,shift,Int.fract]; simp only [Nat.cast_two,mul_sub,mul_comm (2*π) (⌊_⌋:ℝ),cos_sub_int_mul_two_pi]; congr 1; dsimp [u]; ring
  rw [eqn,cos_two_mul] at sign
  have hsq : (2:ℝ)⁻¹≤|cos u|^2 := by rw [sq_abs]; linarith
  have H := log_le_log (by norm_num : (0:ℝ)<2⁻¹) hsq
  rw [log_inv,log_pow] at H; norm_num at H; change -log |cos u|≤_; rw [log_abs]; linarith

noncomputable def spikeSecondMoment (x : ℝ) (N : ℕ) := (∑ n∈range N, (cosineSpike x n)^2)/(N:ℝ)

/-- A finite transition inequality. The free positive parameter trades the
second-moment allowance against the mass of the transition interval. -/
theorem spike_transition_bound {x : ℝ} (hx : Irrational x) {N : ℕ} (hN : 0<N) {a : ℝ} (ha : 0<a) :
    log 2/2 + log |sin (π*x)|/N ≤ a*spikeSecondMoment x N + transitionFrequency x N/(4*a) := by
  classical
  let hit (n : ℕ) := 1/4≤shift 2 x n ∧ shift 2 x n<3/4
  let flag (n : ℕ) : ℝ := if hit n then 1 else 0
  have pt (n : ℕ) : cosineSpike x n ≤ log 2/2 + a*(cosineSpike x n)^2 + flag n/(4*a) := by
    by_cases h : hit n
    · simp only [flag,ite_eq_left h]; have H : 0≤(2*a*cosineSpike x n-1)^2 := sq_nonneg _
      have q : cosineSpike x n ≤ a*(cosineSpike x n)^2+1/(4*a) := by
        apply (le_of_sub_nonneg ?_); field_simp [ha.ne']; nlinarith only [H]
      linarith [log_pos (by norm_num : (1:ℝ)<2)]
    · simp only [flag,ite_eq_right h,zero_div,add_zero]; exact (spike_outside n h).trans (le_add_of_nonneg_right (mul_nonneg ha.le (sq_nonneg _)))
  have total := sum_le_sum (s:=range N) (fun n _ => pt n)
  rw [cosineSpike_sum hx,sum_add_distrib,sum_add_distrib,← mul_sum,← sum_div (f:=flag)] at total
  have count : ∑ n∈range N, flag n = transitionFrequency x N*N := by
    simp [flag,hit,transitionFrequency,frequency,sum_boole,hN.ne']
  rw [count] at total; simp only [sum_const,card_range,nsmul_eq_mul] at total
  have endTerm := log_nonpos (abs_nonneg _) (abs_sin_le_one (π*(2^N*x)))
  have np : (0:ℝ)<N := by exact_mod_cast hN
  rw [show π*(2^N*x)=π*x*2^N by ring] at endTerm
  unfold spikeSecondMoment; field_simp [np.ne',ha.ne'] at total ⊢; nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le endTerm]

/-- An eventual upper bound on the second moment with arbitrary positive slack
is the usual finite limsup hypothesis, including eventual boundedness. -/
theorem transition_of_spike_moment {x C : ℝ} (hx : Irrational x) (hC : 0<C)
    (mom : ∀ e : ℝ, 0<e → ∀ᶠ N in atTop, spikeSecondMoment x N≤C+e) :
    (log 2)^2/(4*C) ≤ transitionDensity x := by
  let a := log 2/(4*C)
  have lp := log_pos (by norm_num : (1:ℝ)<2)
  have ha : 0<a := by dsimp [a]; positivity
  apply le_of_forall_lt_imp_le_of_dense
  intro u hu
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun N => (frequency_bounds (shift 2 x) (1/4) (3/4) N).2))
  let gap := (log 2)^2/(4*C)-u
  have hg : 0<gap := sub_pos.mpr hu
  let e := gap/(16*a*a)
  have he : 0<e := by dsimp [e]; positivity
  have decay := (tendsto_const_div_atTop_nhds_zero_nat (log |sin (π*x)|)).eventually_const_lt (show -(gap/(16*a))<0 from neg_lt_zero.mpr (by positivity))
  filter_upwards [mom e he,decay,eventually_gt_atTop 0] with N hm hend hN
  have t := spike_transition_bound hx hN ha
  have ce : a*e=gap/(16*a) := by dsimp [e]; field_simp
  have v := mul_le_mul_of_nonneg_left hm ha.le; rw [mul_add,ce] at v
  have H : log 2/2-a*C-2*(gap/(16*a)) ≤ transitionFrequency x N/(4*a) := by linarith
  have T := (le_div_iff₀ (show 0<4*a by positivity)).mp H
  have identity : (log 2/2-a*C-2*(gap/(16*a)))*(4*a) = u+gap/2 := by
    dsimp [gap,a]; field_simp; ring
  rw [identity] at T; change u≤transitionFrequency x N; linarith

theorem discrepancy_of_spike_moment {x C : ℝ} (hx : Irrational x) (hC : 0<C)
    (mom : ∀ e : ℝ, 0<e → ∀ᶠ N in atTop, spikeSecondMoment x N≤C+e) :
    asymptoticDiscrepancy x ≤ max (2/3) (1-(log 2)^2/(4*C)) :=
  (sharp_asymptotic_discrepancy x).trans (max_le_max_left _ (sub_le_sub_left (transition_of_spike_moment hx hC mom) _))

/-- Mean contribution above a fixed truncation height. -/
noncomputable def spikeExcess (x M : ℝ) (N : ℕ) : ℝ := (∑ n∈range N,max (cosineSpike x n-M) 0)/(N:ℝ)

/-- A first-moment tail allowance suffices. It can be tested at a single finite cutoff. -/
theorem transition_of_spike_excess {x M L : ℝ} (hx : Irrational x) (cut : log 2/2<M)
    (tail : ∀ e : ℝ, 0<e → ∀ᶠ N in atTop,spikeExcess x M N≤L+e) :
    (log 2/2-L)/(M-log 2/2) ≤ transitionDensity x := by
  classical
  let w := M-log 2/2
  have wp : 0<w := sub_pos.mpr cut
  let hit (n : ℕ) := 1/4≤shift 2 x n ∧ shift 2 x n<3/4
  have pt (n : ℕ) : cosineSpike x n ≤ log 2/2 + (if hit n then w else 0) + max (cosineSpike x n-M) 0 := by
    split_ifs with h
    · dsimp [w]; linarith only [le_max_left (cosineSpike x n-M) 0]
    · linarith only [spike_outside n h,le_max_right (cosineSpike x n-M) 0]
  apply le_of_forall_lt_imp_le_of_dense; intro u hu
  have gap : 0<log 2/2-L-u*w := sub_pos.mpr ((lt_div_iff₀ wp).mp hu)
  let e := (log 2/2-L-u*w)/3
  have ep : 0<e := div_pos gap (by norm_num)
  have floor := (tendsto_const_div_atTop_nhds_zero_nat (log |sin (π*x)|)).eventually_const_lt (neg_lt_zero.mpr ep)
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun N => (frequency_bounds (shift 2 x) (1/4) (3/4) N).2))
  filter_upwards [tail e ep,floor,eventually_gt_atTop 0] with N allow mend hn
  have np : (0:ℝ)<N := by exact_mod_cast hn
  have flags : (∑ n∈range N,if hit n then w else 0)=w*(transitionFrequency x N*N) := by
    simp [hit,transitionFrequency,frequency,← sum_filter,mul_comm]; left; field_simp
  have total := sum_le_sum (s:=range N) (fun i _ => pt i)
  rw [cosineSpike_sum hx,sum_add_distrib,sum_add_distrib,flags,sum_const,card_range,nsmul_eq_mul] at total
  unfold spikeExcess at allow; rw [div_le_iff₀ np] at allow; rw [lt_div_iff₀ np] at mend
  have endTerm := log_nonpos (abs_nonneg _) (abs_sin_le_one (π*(2^N*x)))
  change u≤transitionFrequency x N
  by_contra! bad; have short := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right bad wp) np
  dsimp [e] at allow mend; nlinarith only [total,endTerm,short,mend,allow,mul_pos gap np]

end NormalityChecker
