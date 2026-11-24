module

public import NormalityChecker.BinaryDiscrepancy

@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker

private lemma direction_balance (x : ℝ) (N : ℕ) :
    |frequency (shift 2 x) (1/4) (1/2) N - frequency (shift 2 x) (1/2) (3/4) N| ≤ 1/(N:ℝ) := by
  let b (n : ℕ) : ℝ := if shift 2 x n<1/2 then 0 else 1
  have step (n : ℕ) : b (n+1)-b n =
      (if 1/4≤shift 2 x n ∧ shift 2 x n<1/2 then (1:ℝ) else 0) -
      (if 1/2≤shift 2 x n ∧ shift 2 x n<3/4 then 1 else 0) := by
    dsimp only [b]; rw [binary_shift_step]
    by_cases h : shift 2 x n<1/2
    · have cmp : 2*shift 2 x n<1/2 ↔ shift 2 x n<1/4 := by constructor <;> intro H <;> linarith
      by_cases low : shift 2 x n<1/4
      · simp only [h,cmp,low,not_le.mpr low,not_le.mpr h,ite_true,ite_false,false_and]
      · simp only [h,cmp,low,le_of_not_gt low,not_le.mpr h,ite_true,ite_false,true_and,false_and]
    · have cmp : 2*shift 2 x n-1<1/2 ↔ shift 2 x n<3/4 := by constructor <;> intro H <;> linarith
      by_cases low : shift 2 x n<3/4 <;> simp only [h,cmp,low,le_of_not_gt h,ite_true,ite_false,and_false,true_and]; norm_num
  have h := sum_range_sub b N
  simp only [step,sum_sub_distrib,sum_boole] at h
  unfold frequency
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) N),h]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  dsimp only [b]; split_ifs <;> norm_num

private lemma intervals_mono (v : ℕ → ℝ) (N : ℕ) {a b c d : ℝ}
    (ha : c≤a) (hb : b≤d) : frequency v a b N≤frequency v c d N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro n hn; obtain ⟨hz,h₁,h₂⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hz,ha.trans h₁,h₂.trans_le hb⟩

private lemma intervals_disjoint (v : ℕ → ℝ) {N : ℕ} (hN : 0<N) {a b c d : ℝ}
    (H : b≤c ∨ d≤a) : frequency v a b N+frequency v c d N≤1 := by
  classical
  let I := (range N).filter (fun n => a≤v n ∧ v n<b)
  let J := (range N).filter (fun n => c≤v n ∧ v n<d)
  have dis : Disjoint I J := by
    apply disjoint_left.mpr; intro n hi hj
    obtain ⟨_,h₁,h₂⟩ := mem_filter.mp hi; obtain ⟨_,h₃,h₄⟩ := mem_filter.mp hj
    rcases H with h|h <;> linarith
  have hs : I∪J ⊆ range N := union_subset (filter_subset _ _) (filter_subset _ _)
  have h := card_le_card hs; rw [card_union_of_disjoint dis,card_range] at h
  change I.card/(N:ℝ)+J.card/N≤_
  rw [← add_div,div_le_one (by exact_mod_cast hN)]; exact_mod_cast h

/-- An interval containing the half point of width below 1/3 cannot contain
three consecutive shifts. The same holds for width below 1/6 if the interval
meets the middle half. -/
private lemma no_three (x : ℝ) (n : ℕ) {a c : ℝ} (hlen : c-a<1/3)
    (hmeet : 1/4<c ∧ a<3/4) (h : a≤1/2 ∧ 1/2≤c ∨ c-a<1/6) :
    ¬ (a≤shift 2 x n ∧ shift 2 x n<c) ∨
    ¬ (a≤shift 2 x (n+1) ∧ shift 2 x (n+1)<c) ∨
    ¬ (a≤shift 2 x (n+2) ∧ shift 2 x (n+2)<c) := by
  by_contra! bad
  obtain ⟨⟨a₁,a₂⟩,⟨b₁,b₂⟩,⟨c₁,c₂⟩⟩ := bad
  have e := binary_shift_step x n; have e' := binary_shift_step x (n+1)
  obtain ⟨hl,hr⟩ := hmeet
  rcases h with ⟨h₁,h₂⟩|h <;> split_ifs at e e' <;> linarith

/-- A sharp universal constant in the asymptotic bound, with explicit
finite-prefix boundary allowance. -/
theorem sharp_finite_discrepancy (x : ℝ) {N : ℕ} (hN : 0<N) :
    binaryDiscrepancy x N≤max (2/3) (1-transitionFrequency x N)+1/N := by
  classical
  let v := shift 2 x
  let τ := transitionFrequency x N
  let U := frequency v (1/4) (1/2) N
  let V := frequency v (1/2) (3/4) N
  let e := 1/(N:ℝ)
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have he : 0≤e := by dsimp [e]; positivity
  have sum : τ=U+V := by
    dsimp only [τ,U,V,transitionFrequency,v]
    rw [anchored_difference _ (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤3/4),
      anchored_difference _ (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1/2),
      anchored_difference _ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤3/4)]
    ring
  obtain ⟨bl,bu⟩ := abs_le.mp (show |U-V|≤e from direction_balance x N)
  let D := max (2/3) (1-τ)
  have d₀ : 2/3≤D := le_max_left ..
  have d₁ : 1-τ≤D := le_max_right ..
  have mix : 1-τ/2-1/6≤D := by linarith
  apply discrepancy_le; intro a c ha hac hc
  let f := frequency v a c N
  obtain ⟨hf₀,hf₁⟩ := (show 0≤f ∧ f≤1 from frequency_bounds v _ _ N)
  change |f-(c-a)|≤D+e
  apply abs_le.mpr
  constructor
  · by_cases h : c-a≤2/3
    · linarith
    by_cases mid : a≤1/4 ∧ 3/4≤c
    · have ht : τ≤f := intervals_mono v N mid.1 mid.2
      linarith
    by_cases low : a≤1/4
    · have ht : U≤f := intervals_mono v N low (by linarith)
      have hr : c<3/4 := lt_of_not_ge (fun z => mid ⟨low,z⟩)
      linarith
    · have ht : V≤f := intervals_mono v N (by linarith) (by linarith)
      linarith
  · by_cases h : 1/3≤c-a
    · linarith
    by_cases dis : c≤1/4 ∨ 3/4≤a
    · have hh : f+τ≤1 := intervals_disjoint v hN dis
      linarith
    push Not at dis
    by_cases H : a≤1/2 ∧ 1/2≤c ∨ c-a<1/6
    · let P (n : ℕ) := a≤v n ∧ v n<c
      have miss (n : ℕ) : ∃ j≤2, ¬P (n+j) := by
        rcases no_three x n (lt_of_not_ge h) dis H with h|h|h
        · exact ⟨0,by decide,by simpa [P,v] using h⟩
        · exact ⟨1,by decide,h⟩
        · exact ⟨2,le_rfl,h⟩
      have cnt := count_within_steps (P:=fun _ => True) (Q:=fun n => ¬P n) N 2 (fun n _ => miss n)
      simp at cnt
      have hc := card_filter_add_card_filter_not (s:=range N) P
      rw [card_range] at hc
      have Hnat : 3*((range N).filter P).card ≤ 2*N+2 := by omega
      have Hreal : 3*(((range N).filter P).card:ℝ) ≤ 2*N+2 := by exact_mod_cast Hnat
      have Hf : f≤2/3+e := by
        change (((range N).filter P).card:ℝ)/N≤2/3+1/N
        rw [div_le_iff₀ hN',add_mul,one_div_mul_cancel hN'.ne']; linarith
      linarith
    · have hl : 1/6≤c-a := le_of_not_gt (fun hh => H (Or.inr hh))
      by_cases half : c≤1/2
      · have ht : f+V≤1 := intervals_disjoint v hN (Or.inl half)
        linarith
      · have r : 1/2≤a := le_of_not_gt (fun l => H (Or.inl ⟨l.le,le_of_not_ge half⟩))
        have ht : f+U≤1 := intervals_disjoint v hN (Or.inr r)
        linarith

theorem sharp_asymptotic_discrepancy (x : ℝ) :
    asymptoticDiscrepancy x ≤ max (2/3) (1-transitionDensity x) := by
  apply (limsup_le_iff (isCoboundedUnder_le_of_le _ (fun N => (discrepancy_bounds x N).1))
    (isBoundedUnder_of_eventually_le (.of_forall fun N => (discrepancy_bounds x N).2))).mpr
  intro y hy
  let D := max (2/3:ℝ) (1-transitionDensity x)
  let e := (y-D)/3
  have he : 0<e := by dsimp [e]; linarith
  have lower := eventually_lt_of_lt_liminf (show transitionDensity x-e<transitionDensity x by linarith)
    (isBoundedUnder_of_eventually_ge (.of_forall (fun n => (frequency_bounds (shift 2 x) (1/4) (3/4) n).1)))
  have small := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).eventually_lt_const he
  filter_upwards [lower,small,eventually_gt_atTop 0] with N hN hsmall hn
  apply (sharp_finite_discrepancy x hn).trans_lt
  change transitionDensity x-e < transitionFrequency x N at hN
  have hmax : max (2/3:ℝ) (1-transitionFrequency x N)≤D+e := max_le
    ((le_max_left ..).trans (by linarith : D≤D+e))
    (by linarith [show 1-transitionDensity x≤D from le_max_right ..])
  dsimp [e] at *; linarith

/-- The period-two orbit attains the universal plateau in the bound. -/
theorem third_discrepancy_sharp :
    transitionDensity (1/3)=1 ∧ asymptoticDiscrepancy (1/3)=2/3 := by
  have orbit (n : ℕ) : shift 2 (1/3) n=1/3 ∨ shift 2 (1/3) n=2/3 := by
    induction n with
    | zero =>
      left; simp only [shift,pow_zero,one_mul]; exact Int.fract_eq_self.mpr ⟨by norm_num,by norm_num⟩
    | succ n ih =>
      rw [binary_shift_step]; rcases ih with h|h <;> rw [h] <;> norm_num
  have allIn (a c : ℝ) (a₁ : a≤1/3) (c₂ : 2/3<c) {N : ℕ} (hN : 0<N) :
      frequency (shift 2 (1/3)) a c N=1 := by
    unfold frequency
    have H : (range N).filter (fun n => a≤shift 2 (1/3) n ∧ shift 2 (1/3) n<c)=range N := by
      apply filter_true_of_mem; intro n _; rcases orbit n with h|h <;> rw [h] <;> constructor <;> linarith
    rw [H,card_range,div_self (by exact_mod_cast hN.ne')]
  have t : transitionDensity (1/3)=1 := by
    apply Filter.Tendsto.liminf_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (allIn _ _ (by norm_num) (by norm_num) hn).symm
  have upper := sharp_asymptotic_discrepancy (1/3)
  rw [t,sub_self,max_eq_left (by norm_num)] at upper
  refine ⟨t,le_antisymm upper ?_⟩
  apply le_limsup_of_frequently_le _ (isBoundedUnder_of_eventually_le (.of_forall (fun n => (discrepancy_bounds _ n).2)))
  apply Eventually.frequently
  filter_upwards [eventually_gt_atTop 0] with n hn
  by_contra! bad
  let D := binaryDiscrepancy (1/3) n
  let ε := min (1/6) ((2/3-D)/2)
  have hp : 0<ε := lt_min (by norm_num) (by change 0<(2/3-binaryDiscrepancy (1/3) n)/2; linarith)
  have he : ε≤1/6 := min_le_left ..
  have H := interval_le_discrepancy (1/3) n (by norm_num : (0:ℝ)≤1/3)
    (show (1/3:ℝ)<2/3+ε by linarith) (by linarith)
  rw [allIn _ _ le_rfl (by linarith) hn] at H
  have := (le_abs_self _).trans H
  have hsmall : ε≤(2/3-D)/2 := min_le_right ..
  change D<2/3 at bad
  change _≤D at this
  linarith

end NormalityChecker
