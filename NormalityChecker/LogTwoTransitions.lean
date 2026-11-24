module

public import NormalityChecker.SharpDiscrepancy
public import NormalityChecker.LogTwo
public import NormalityChecker.LogTwoLinearForms

@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker

noncomputable def prefixResidue (n : ℕ) := Int.fract (logPrefix n : ℝ)
def MiddleHit (n : ℕ) : Prop := 1/3≤prefixResidue n ∧ prefixResidue n≤2/3

open Classical in
noncomputable def middleFrequency (N : ℕ) : ℝ := ((range N).filter MiddleHit).card/(N:ℝ)

private lemma prefix_step (n : ℕ) : prefixResidue (n+1) =
    Int.fract (2*prefixResidue n+1/((n:ℝ)+1)) := by
  let v := (logPrefix n:ℝ)
  have e : 2*v+1/((n:ℝ)+1) = ((2*⌊v⌋:ℤ):ℝ)+(2*Int.fract v+1/((n:ℝ)+1)) := by
    push_cast; linarith [Int.fract_add_floor v]
  unfold prefixResidue; rw [logPrefix]; push_cast; exact e ▸ Int.fract_intCast_add _ _

private lemma actual_step (n : ℕ) :
    ∃ e : ℝ, 0≤e ∧ e≤1/((n:ℝ)+1) ∧ shift 2 (Real.log 2) n = Int.fract (prefixResidue n+e) := by
  let e := (2:ℝ)^n*Real.log 2-logPrefix n
  obtain ⟨hl,hu⟩ := logTwo_tail_bounds n
  refine ⟨e,hl,hu,?_⟩
  have h : (2:ℝ)^n*Real.log 2 = (prefixResidue n+e)+⌊(logPrefix n:ℝ)⌋ := by
    dsimp [prefixResidue,e]; linarith [Int.fract_add_floor (logPrefix n:ℝ)]
  unfold shift; change Int.fract ((2:ℝ)^n*Real.log 2)=_; rw [h,Int.fract_add_intCast]

private lemma small_step {n : ℕ} (hn : 12≤n) : 1/((n:ℝ)+1)<1/12 := by
  have h : (12:ℝ)≤n := by exact_mod_cast hn
  exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

theorem transition_of_middle_hit {n : ℕ} (hn : 12≤n) (h : MiddleHit n) :
    1/4≤shift 2 (Real.log 2) n ∧ shift 2 (Real.log 2) n<3/4 := by
  obtain ⟨e,h₀,h₁,he⟩ := actual_step n
  obtain ⟨hl,hr⟩ := h
  rw [he, Int.fract_eq_self.mpr ⟨by linarith,by linarith [small_step hn]⟩]
  constructor <;> linarith [small_step hn]

private lemma fract_of_one_le {y : ℝ} (hl : 1≤y) (hu : y<2) : Int.fract y=y-1 := by
  rw [← Int.fract_sub_one]; exact Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩

/-- The one-sided recurrence forces a middle-third visit within two steps
of every sufficiently late digit transition, even near the period-two endpoints. -/
theorem middle_hit_near_transition {n : ℕ} (hn : 12≤n)
    (ht : 1/4≤shift 2 (Real.log 2) n ∧ shift 2 (Real.log 2) n<3/4) :
    ∃ j≤2, MiddleHit (n+j) := by
  obtain ⟨e,h₀,h₁,he⟩ := actual_step n
  have hr₀ : 0≤prefixResidue n := Int.fract_nonneg _
  have hr₁ : prefixResidue n<1 := Int.fract_lt_one _
  have hs := small_step hn
  have hs' := small_step (n:=n+1) (by omega)
  have hn₀ : 0<1/((n:ℝ)+1) := by positivity
  have hn₁ : 0<1/(((n+1:ℕ):ℝ)+1) := by positivity
  rw [he] at ht
  have nowrap : prefixResidue n+e<1 := by
    by_contra! h
    rw [fract_of_one_le h (by linarith)] at ht
    linarith [ht.1]
  rw [Int.fract_eq_self.mpr ⟨by linarith,nowrap⟩] at ht
  by_cases h : MiddleHit n
  · exact ⟨0,by decide,by simpa using h⟩
  by_cases low : prefixResidue n<1/3
  · have step := prefix_step n
    rw [Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩] at step
    by_cases hright : prefixResidue (n+1)≤2/3
    · exact ⟨1,by decide,by exact ⟨by linarith [ht.1],hright⟩⟩
    · have step' := prefix_step (n+1)
      rw [fract_of_one_le (by linarith) (by linarith)] at step'
      exact ⟨2,le_rfl,by exact ⟨by linarith,by linarith⟩⟩
  · have hr : 2/3<prefixResidue n := lt_of_not_ge (fun hr => h ⟨le_of_not_gt low,hr⟩)
    have step := prefix_step n
    rw [fract_of_one_le (by linarith) (by linarith [ht.2])] at step
    exact ⟨1,by decide,by exact ⟨by linarith,by linarith [ht.2]⟩⟩

private lemma initial_count (P : ℕ → Prop) [DecidablePred P] (K N : ℕ) :
    ((range N).filter P).card ≤ K+((range N).filter (fun n => K≤n ∧ P n)).card := by
  have hs : (range N).filter P ⊆ range K ∪ (range N).filter (fun n => K≤n ∧ P n) := by
    intro n hn; by_cases h : n<K
    · exact mem_union_left _ (mem_range.mpr h)
    · obtain ⟨hn,hp⟩ := mem_filter.mp hn
      exact mem_union_right _ (mem_filter.mpr ⟨hn,by omega,hp⟩)
  simpa using (card_le_card hs).trans (card_union_le ..)

theorem middle_transition_bounds (N : ℕ) :
    middleFrequency N ≤ 12/(N:ℝ)+transitionFrequency (Real.log 2) N ∧
    transitionFrequency (Real.log 2) N ≤ 14/(N:ℝ)+3*middleFrequency N := by
  classical
  let T (n : ℕ) := 1/4≤shift 2 (Real.log 2) n ∧ shift 2 (Real.log 2) n<3/4
  have H₁ := initial_count MiddleHit 12 N
  have hs : (range N).filter (fun n => 12≤n ∧ MiddleHit n) ⊆ (range N).filter T := by
    intro n h; obtain ⟨h₁,h₂,h₃⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨h₁,transition_of_middle_hit h₂ h₃⟩
  have H₂ := card_le_card hs
  have H₃ := initial_count T 12 N
  have H₄ := count_within_steps (P:=fun n => 12≤n ∧ T n) (Q:=MiddleHit) N 2 (fun n h => middle_hit_near_transition h.1 h.2)
  change _/(_ : ℝ)≤_/(_ : ℝ)+_/(_ : ℝ) ∧ _/(_ : ℝ)≤_/(_ : ℝ)+3*(_/(_ : ℝ))
  rw [← add_div,← mul_div_assoc,← add_div]
  constructor
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (show ((range N).filter MiddleHit).card≤12+((range N).filter T).card by omega)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (show ((range N).filter T).card≤14+3*((range N).filter MiddleHit).card by omega)

private lemma liminf_comparison {f g : ℕ → ℝ} (hf : ∀ n, 0≤f n ∧ f n≤1) (hg : ∀ n, 0≤g n)
    (C A : ℝ) (H : ∀ N, g N≤C/(N:ℝ)+A*f N) : liminf g atTop ≤ A*liminf f atTop := by
  obtain ⟨t,ht,hgrow⟩ := exists_seq_tendsto_liminf
    (isCoboundedUnder_ge_of_le atTop fun n => (hf n).2)
    (isBoundedUnder_of_eventually_ge (.of_forall fun n => (hf n).1))
  have h := ((tendsto_const_div_atTop_nhds_zero_nat C).comp hgrow).add (ht.const_mul A)
  rw [zero_add] at h
  by_contra! bad
  obtain ⟨y,hlo,hhi⟩ := exists_between bad
  have lower := hgrow.eventually (eventually_lt_of_lt_liminf hhi
    (isBoundedUnder_of_eventually_ge (.of_forall hg)))
  obtain ⟨k,h₁,h₂⟩ := (lower.and (h.eventually_lt_const hlo)).exists
  exact h₂.not_ge ((H (t k)).trans' h₁.le)

theorem logTwo_density_comparison :
    liminf middleFrequency atTop ≤ transitionDensity (Real.log 2) ∧
      transitionDensity (Real.log 2) ≤ 3*liminf middleFrequency atTop := by
  classical
  have hi (n : ℕ) : 0≤middleFrequency n ∧ middleFrequency n≤1 := by
    constructor
    · unfold middleFrequency; positivity
    · cases n with
      | zero => simp [middleFrequency]
      | succ n =>
        apply (div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
        exact_mod_cast (card_filter_le (range (n+1)) MiddleHit).trans_eq (card_range _)
  have ht (n : ℕ) : 0≤transitionFrequency (Real.log 2) n ∧ transitionFrequency (Real.log 2) n≤1 :=
    frequency_bounds _ _ _ _
  constructor
  · simpa only [one_mul,transitionDensity] using liminf_comparison ht (fun n => (hi n).1) 12 1
      (fun n => by simpa using (middle_transition_bounds n).1)
  · exact liminf_comparison hi (fun n => (ht n).1) 14 3 (fun n => (middle_transition_bounds n).2)

theorem logTwo_discrepancy_lt_one_iff_middle :
    asymptoticDiscrepancy (Real.log 2)<1 ↔ 0<liminf middleFrequency atTop := by
  rw [discrepancy_lt_one_iff_transitions]
  obtain ⟨h₁,h₂⟩ := logTwo_density_comparison
  constructor <;> intro h <;> linarith

theorem logTwo_discrepancy_le_middle :
    asymptoticDiscrepancy (Real.log 2) ≤ max (2/3) (1-liminf middleFrequency atTop) :=
  (sharp_asymptotic_discrepancy _).trans (max_le_max_left _ (sub_le_sub_left logTwo_density_comparison.1 1))

/-- Every sufficiently late multiplicative window contains a visit of the
rational recurrence to the closed middle third and a true binary transition. -/
theorem logTwo_window_hit :
    ∀ᶠ n : ℕ in atTop, ∃ t, n≤t ∧ t<34*n ∧ MiddleHit t ∧
      binaryBit (Real.log 2) t ≠ binaryBit (Real.log 2) (t+1) := by
  filter_upwards [LogTwoForm.dyadic_separation,eventually_ge_atTop 12] with n H hn
  let v := (2:ℝ)^n*Real.log 2
  let B := (1/2:ℝ)^(32*n)
  have hlo : B≤Int.fract v := by
    have h := H ⌊v⌋
    change B≤|Int.fract v| at h
    rwa [abs_of_nonneg (Int.fract_nonneg v)] at h
  have hhi : B≤1-Int.fract v := by
    have h := H (⌊v⌋+1)
    change B≤|v-((⌊v⌋+1:ℤ):ℝ)| at h
    push_cast at h; rw [abs_of_neg (sub_neg.mpr (Int.lt_floor_add_one v))] at h
    unfold Int.fract; linarith
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨j,hj,hT⟩ := transition_near_interior (Real.log 2) (32*n) n
    (show B/4≤Int.fract v by linarith) (show Int.fract v<1-B/4 by linarith)
  obtain ⟨i,hi,hI⟩ := middle_hit_near_transition (by omega : 12≤n+j) hT
  exact ⟨n+j+i,by omega,by omega,hI,(transition_iff_bits ..).mp (transition_of_middle_hit (by omega) hI)⟩

private theorem count_geometric {P : ℕ → Prop} [DecidablePred P] {b : ℕ} (hb : 1<b)
    (H : ∀ᶠ n : ℕ in atTop, ∃ t, n≤t ∧ t<b*n ∧ P t) :
    ∃ K : ℕ, ∀ N, Nat.log b N-K ≤ ((range N).filter P).card := by
  have grow := tendsto_pow_atTop_atTop_of_one_lt hb
  obtain ⟨K,hK⟩ := eventually_atTop.mp (grow.eventually H)
  let S (N : ℕ) := (range N).filter P
  have mono : Monotone S := fun _ _ h => filter_subset_filter _ (range_mono h)
  have shells (k : ℕ) (hk : K≤k) : k-K≤(S (b^k)).card := by
    induction k,hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      obtain ⟨t,hl,hu,hp⟩ := hK k hk
      have strict : S (b^k) ⊂ S (b^(k+1)) := by
        apply Finset.ssubset_iff_of_subset (mono (Nat.pow_le_pow_right (by omega) k.le_succ)) |>.mpr
        refine ⟨t,mem_filter.mpr ⟨mem_range.mpr (by simpa [pow_succ'] using hu),hp⟩,?_⟩
        intro h; exact hl.not_gt (mem_range.mp (mem_filter.mp h).1)
      have := card_lt_card strict; omega
  refine ⟨K,fun N => ?_⟩
  by_cases hz : N=0
  · simp [hz]
  by_cases hk : K≤Nat.log b N
  · exact (shells _ hk).trans (card_le_card (mono (Nat.pow_log_le_self b hz)))
  · omega

open Classical in
/-- An unconditional logarithmic lower bound for both counts, with a fixed
additive offset. This gives infinitely many hits but leaves their lower density open. -/
theorem logTwo_logarithmic_count :
    ∃ K : ℕ, ∀ N, Nat.log 34 N-K ≤ ((range N).filter MiddleHit).card ∧
      Nat.log 34 N-K ≤ ((range N).filter (fun t =>
        binaryBit (Real.log 2) t ≠ binaryBit (Real.log 2) (t+1))).card := by
  classical
  obtain ⟨K,hK⟩ := count_geometric (P:=fun t => MiddleHit t ∧
    binaryBit (Real.log 2) t ≠ binaryBit (Real.log 2) (t+1)) (by decide : 1<34) logTwo_window_hit
  refine ⟨K,fun N => ⟨(hK N).trans (card_le_card ?_),(hK N).trans (card_le_card ?_)⟩⟩
  · intro t ht; obtain ⟨h₁,h₂,_⟩ := mem_filter.mp ht; exact mem_filter.mpr ⟨h₁,h₂⟩
  · intro t ht; obtain ⟨h₁,_,h₂⟩ := mem_filter.mp ht; exact mem_filter.mpr ⟨h₁,h₂⟩

/-- The unconditional finite-prefix discrepancy gap obtained from the count. -/
theorem logTwo_finite_discrepancy_gap :
    ∃ K : ℕ, ∀ N≥2, binaryDiscrepancy (Real.log 2) N ≤
      max (7/8) (1-((Nat.log 34 N-K:ℕ):ℝ)/N) := by
  classical
  obtain ⟨K,hK⟩ := logTwo_logarithmic_count
  refine ⟨K,fun N hN => (discrepancy_le_transitions _ hN).trans (max_le_max_left _ (sub_le_sub_left ?_ 1))⟩
  unfold transitionFrequency frequency
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have H := (hK N).2
  simpa only [← transition_iff_bits] using Nat.cast_le (α:=ℝ).mpr H

end NormalityChecker
