module

public import NormalityChecker.LogTwoTransitions
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Number of successive misses immediately before position `n`. -/
def gapAge (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n+1 => if P n then 0 else gapAge P n + 1

/-- The last, possibly incomplete gap ends at the prefix boundary for this count. -/
private lemma gap_moments (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    let hits := (range N).filter P
    (∑ i ∈ hits, (gapAge P i + 1)) + (gapAge P N+1) = N+1 ∧
    (∑ i ∈ hits, (gapAge P i + 1)^2) + (gapAge P N+1)^2 =
      (N+1) + 2*(∑ i ∈ range (N+1), gapAge P i) := by
  induction N with
  | zero => simp [gapAge]
  | succ N ih =>
    dsimp only at ih ⊢
    rw [range_add_one,filter_insert, sum_range_succ (fun i => gapAge P i) (N+1)]
    have fresh : N ∉ (range N).filter P := fun h => (mem_range.mp (mem_filter.mp h).1).false
    by_cases hp : P N
    · simp only [hp,ite_true,sum_insert fresh,gapAge,zero_add,one_pow,add_zero]
      constructor <;> omega
    · simp only [hp,ite_false,gapAge]
      exact ⟨by omega,by nlinarith [ih.2]⟩

/-- If a prefix contains few hits, its aggregate waiting time must be large.
This holds at every cutoff, including one in the middle of a long gap. -/
theorem gap_age_count_bound (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    (N+1)^2 ≤ (((range N).filter P).card+1) *
      (N+1 + 2*(∑ i ∈ range (N+1), gapAge P i)) := by
  let hits := (range N).filter P
  have fresh : N ∉ hits := fun h => (mem_range.mp (mem_filter.mp h).1).false
  obtain ⟨h₁,h₂⟩ := gap_moments P N
  have h := sq_sum_le_card_mul_sum_sq (s:=insert N hits) (f:=fun i => gapAge P i+1)
  simp only [sum_insert fresh,card_insert_of_notMem fresh,Nat.cast_id] at h
  rw [add_comm (gapAge P N+1),add_comm ((gapAge P N+1)^2),h₁,h₂] at h
  exact h

/-- An upper bound on average age across all prefixes gives an explicit lower density. -/
theorem hit_density_of_mean_age (P : ℕ → Prop) [DecidablePred P] {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ N : ℕ in atTop, (∑ i ∈ range (N+1), (gapAge P i:ℝ)) ≤ C*(N+1)) :
    1/(1+2*C) ≤ liminf (fun N : ℕ => (((range N).filter P).card:ℝ)/N) atTop := by
  let f := fun N : ℕ => (((range N).filter P).card:ℝ)/N
  have hub (N : ℕ) : f N ≤ 1 := by
    obtain rfl | hn := Nat.eq_zero_or_pos N
    · simp [f]
    · apply (div_le_one (by positivity : (0:ℝ)<N)).mpr
      exact_mod_cast (card_filter_le (range N) P).trans_eq (card_range _)
  have hc : 0 < 1+2*C := by linarith
  have bound : ∀ᶠ N : ℕ in atTop, 1/(1+2*C)-1/(N:ℝ) ≤ f N := by
    filter_upwards [h,eventually_gt_atTop 0] with N hN hn
    have hn' : (0:ℝ) < N := by exact_mod_cast hn
    let k : ℝ := ((range N).filter P).card
    have e : ((N:ℝ)+1)^2 ≤ (k+1)*(N+1+2*(∑ i ∈ range (N+1), (gapAge P i:ℝ))) := by
      dsimp [k]; exact_mod_cast gap_age_count_bound P N
    have e' : ((N:ℝ)+1)^2 ≤ (k+1)*((N+1)*(1+2*C)) := e.trans
      (mul_le_mul_of_nonneg_left (by nlinarith) (by dsimp [k]; positivity))
    have cancel : (N:ℝ)+1 ≤ (k+1)*(1+2*C) := by
      apply le_of_mul_le_mul_left (a:=(N:ℝ)+1) _ (by positivity)
      nlinarith only [e']
    change 1/(1+2*C)-1/(N:ℝ) ≤ k/N
    field_simp; linarith
  have hlim : Tendsto (fun N : ℕ => 1/(1+2*C) - 1/(N:ℝ)) atTop (𝓝 (1/(1+2*C))) := by
    simpa using (tendsto_const_nhds (x:=1/(1+2*C))).sub (tendsto_const_div_atTop_nhds_zero_nat 1)
  exact hlim.liminf_eq ▸ liminf_le_liminf bound hlim.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_le _ hub)

open Classical in
/-- A sufficient aggregate-gap estimate on the logarithmic recurrence. -/
theorem logTwo_discrepancy_of_mean_age {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ N : ℕ in atTop, (∑ i ∈ range (N+1), (gapAge MiddleHit i:ℝ)) ≤ C*(N+1)) :
    asymptoticDiscrepancy (Real.log 2) ≤ max (2/3) (1-1/(1+2*C)) :=
  logTwo_discrepancy_le_middle.trans (max_le_max_left _
    (sub_le_sub_left (hit_density_of_mean_age MiddleHit hC h) 1))

end NormalityChecker
