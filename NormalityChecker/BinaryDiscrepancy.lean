module

public import NormalityChecker.Distribution

@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker

/-- Extreme interval discrepancy of the first N radix shifts, counting overlapping starts. -/
noncomputable def radixDiscrepancy (b : ℕ) (x : ℝ) (N : ℕ) : ℝ :=
  sSup {d | ∃ a c : ℝ, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧
    d = |frequency (shift b x) a c N - (c-a)|}

noncomputable abbrev binaryDiscrepancy := radixDiscrepancy 2

noncomputable def asymptoticDiscrepancy (x : ℝ) := limsup (binaryDiscrepancy x) atTop

/-- The first binary digit after position n, with the terminating convention. -/
noncomputable def binaryBit (x : ℝ) (n : ℕ) : Bool := decide (1/2 ≤ shift 2 x n)

/-- The union of the two adjacent cylinders 01 and 10. -/
noncomputable def transitionFrequency (x : ℝ) := frequency (shift 2 x) (1/4) (3/4)

noncomputable def transitionDensity (x : ℝ) := liminf (transitionFrequency x) atTop

theorem frequency_bounds (u : ℕ → ℝ) (a c : ℝ) (N : ℕ) :
    0 ≤ frequency u a c N ∧ frequency u a c N ≤ 1 := by
  constructor
  · unfold frequency; positivity
  · cases N with
    | zero => simp [frequency]
    | succ n =>
      apply (div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
      exact_mod_cast (card_filter_le (range (n+1)) _).trans_eq (card_range _)

private lemma discrepancy_bounded (x : ℝ) (N : ℕ) :
    ∀ d ∈ {d | ∃ a c : ℝ, 0 ≤ a ∧ a<c ∧ c≤1 ∧ d=|frequency (shift 2 x) a c N-(c-a)|}, d ≤ 1 := by
  rintro d ⟨a,c,ha,hac,hc,rfl⟩
  obtain ⟨h1,h2⟩ := frequency_bounds (shift 2 x) a c N
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem interval_le_discrepancy (x : ℝ) (N : ℕ) {a c : ℝ} (ha : 0≤a) (hac : a<c) (hc : c≤1) :
    |frequency (shift 2 x) a c N-(c-a)| ≤ binaryDiscrepancy x N :=
  le_csSup ⟨1,discrepancy_bounded x N⟩ ⟨a,c,ha,hac,hc,rfl⟩

lemma discrepancy_le {x : ℝ} {N : ℕ} {D : ℝ}
    (H : ∀ a c : ℝ, 0≤a → a<c → c≤1 → |frequency (shift 2 x) a c N-(c-a)|≤D) :
    binaryDiscrepancy x N ≤ D := by
  unfold binaryDiscrepancy radixDiscrepancy
  refine csSup_le ?_ ?_
  · exact ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩
  rintro _ ⟨a,c,ha,hac,hc,rfl⟩
  exact H a c ha hac hc

theorem discrepancy_bounds (x : ℝ) (N : ℕ) :
    0≤binaryDiscrepancy x N ∧ binaryDiscrepancy x N≤1 :=
  ⟨(abs_nonneg _).trans (interval_le_discrepancy x N le_rfl zero_lt_one le_rfl),
    csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ (discrepancy_bounded x N)⟩

theorem binary_shift_step (x : ℝ) (n : ℕ) :
    shift 2 x (n+1) = if shift 2 x n < 1/2 then 2*shift 2 x n else 2*shift 2 x n-1 := by
  let v := (2:ℝ)^n*x
  have hv := Int.fract_add_floor v
  have he : (2:ℝ)^(n+1)*x = ((2*⌊v⌋:ℤ):ℝ)+2*Int.fract v := by
    rw [pow_succ]; dsimp [v] at *; push_cast; linarith
  change Int.fract ((2:ℝ)^(n+1)*x)=if Int.fract v<1/2 then _ else _
  rw [he,Int.fract_intCast_add]
  have h0 := Int.fract_nonneg v
  have h1 := Int.fract_lt_one v
  split_ifs with h
  · exact Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩
  · have eqn : Int.fract (2*Int.fract v)=Int.fract (2*Int.fract v-1) := by simp
    rw [eqn]; exact Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩

theorem transition_iff_bits (x : ℝ) (n : ℕ) :
    1/4≤shift 2 x n ∧ shift 2 x n<3/4 ↔ binaryBit x n ≠ binaryBit x (n+1) := by
  unfold binaryBit; rw [binary_shift_step]
  rw [ne_eq, decide_eq_decide]
  split_ifs with h
  · have a : ¬1/2≤shift 2 x n := not_le.mpr h
    simp only [a,false_iff,not_not]
    constructor <;> intro H
    · linarith [H.1]
    · exact ⟨by linarith,by linarith⟩
  · have a := le_of_not_gt h
    simp only [a,true_iff,not_le]
    constructor <;> intro H
    · linarith [H.2]
    · exact ⟨by linarith,by linarith⟩

private lemma half_sep (s : Finset ℕ) (N : ℕ) (hs : s⊆range N)
    (sep : ∀ n∈s, n+1∉s) : 2*s.card ≤ N+1 := by
  let t := s.image (fun n => n+1)
  have hd : Disjoint s t := by
    apply disjoint_left.mpr
    rintro n hn hn'; obtain ⟨j,hj,rfl⟩ := mem_image.mp hn'
    exact sep j hj hn
  have hu : s ∪ t ⊆ range (N+1) := by
    intro n hn; rcases mem_union.mp hn with h|h
    · exact mem_range.mpr ((mem_range.mp (hs h)).trans (Nat.lt_succ_self N))
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      exact mem_range.mpr (Nat.succ_lt_succ (mem_range.mp (hs hj)))
  have hc := card_le_card hu
  rw [card_union_of_disjoint hd,card_range] at hc
  have hcard : t.card=s.card := card_image_of_injective _ (by intro x y h; exact Nat.add_right_cancel h)
  omega

/-- A finite-sample bound for arbitrary half-open intervals, valid from N=2. -/
theorem discrepancy_le_transitions (x : ℝ) {N : ℕ} (hN : 2≤N) :
    binaryDiscrepancy x N ≤ max (7/8) (1-transitionFrequency x N) := by
  classical
  apply discrepancy_le
  intro a c ha hac hc
  let f := frequency (shift 2 x) a c N
  let τ := transitionFrequency x N
  obtain ⟨hf₀,hf₁⟩ := frequency_bounds (shift 2 x) a c N
  change 0≤f at hf₀
  change f≤1 at hf₁
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  let I := (range N).filter (fun n => a≤shift 2 x n ∧ shift 2 x n<c)
  let T := (range N).filter (fun n => 1/4≤shift 2 x n ∧ shift 2 x n<3/4)
  have disj (H : c≤1/4 ∨ 3/4≤a) : f+τ ≤ 1 := by
    have hd : Disjoint I T := by
      apply disjoint_left.mpr; intro n hi ht
      obtain ⟨_,hl,hr⟩ := mem_filter.mp hi; obtain ⟨_,hl',hr'⟩ := mem_filter.mp ht
      rcases H with H|H <;> linarith
    have card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _) : I ∪ T ⊆ range N)
    rw [card_union_of_disjoint hd,card_range] at card
    change I.card/(N:ℝ)+T.card/N≤1
    rw [← add_div, div_le_one hn]; exact_mod_cast card
  apply abs_le.mpr
  constructor
  · change -max _ _≤f-(c-a)
    by_cases h : c-a≤7/8
    · linarith [le_max_left (7/8:ℝ) (1-τ)]
    · have hs : T⊆I := by
        intro n hT; obtain ⟨h₁,h₂,h₃⟩ := mem_filter.mp hT
        exact mem_filter.mpr ⟨h₁,by linarith,by linarith⟩
      have hτ : τ≤f := div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hs)) hn.le
      linarith [le_max_right (7/8:ℝ) (1-τ)]
  · change f-(c-a)≤max _ _
    by_cases h : 1/8≤c-a
    · linarith [le_max_left (7/8:ℝ) (1-τ)]
    by_cases H : c≤1/4 ∨ 3/4≤a
    · linarith [disj H,le_max_right (7/8:ℝ) (1-τ)]
    have sep (n : ℕ) (hn : n∈I) : n+1∉I := by
      intro hsucc
      obtain ⟨_,h1,h2⟩ := mem_filter.mp hn
      obtain ⟨_,h3,h4⟩ := mem_filter.mp hsucc
      rw [binary_shift_step] at h3 h4
      push Not at H
      split_ifs at h3 h4 <;> linarith
    have hcard := half_sep I N (filter_subset _ _) sep
    have hf : f≤3/4 := by
      change (I.card:ℝ)/N≤3/4; rw [div_le_iff₀ hn]
      have hc' : 2*(I.card:ℝ)≤N+1 := by exact_mod_cast hcard
      have hn' : (2:ℝ)≤N := by exact_mod_cast hN
      linarith
    linarith [le_max_left (7/8:ℝ) (1-τ)]

theorem asymptoticDiscrepancy_le_transitions (x : ℝ) :
    asymptoticDiscrepancy x ≤ max (7/8) (1-transitionDensity x) := by
  apply (limsup_le_iff (isCoboundedUnder_le_of_le _ (fun N => (discrepancy_bounds x N).1))
    (isBoundedUnder_of_eventually_le (.of_forall fun N => (discrepancy_bounds x N).2))).mpr
  intro y hy
  have h := eventually_lt_of_lt_liminf (show 1-y < transitionDensity x by
    linarith [le_max_right (7/8:ℝ) (1-transitionDensity x)])
    (isBoundedUnder_of_eventually_ge (.of_forall (fun N => (frequency_bounds (shift 2 x) (1/4) (3/4) N).1)))
  filter_upwards [h,eventually_ge_atTop 2] with N hτ hN
  apply (discrepancy_le_transitions x hN).trans_lt (max_lt ?_ ?_)
  · exact (le_max_left ..).trans_lt hy
  · change 1-y<transitionFrequency x N at hτ; linarith

/-- If a shift is outside the two constant-word cylinders of length k+2,
one of its next k+1 positions is a transition. -/
theorem transition_near_interior (x : ℝ) (k n : ℕ)
    (hl : (1/2:ℝ)^k/4 ≤ shift 2 x n) (hu : shift 2 x n < 1-(1/2:ℝ)^k/4) :
    ∃ j≤k, 1/4≤shift 2 x (n+j) ∧ shift 2 x (n+j)<3/4 := by
  induction k generalizing n with
  | zero => exact ⟨0,le_rfl,by simpa using hl,by norm_num at hu ⊢; linarith⟩
  | succ k ih =>
    by_cases h : 1/4≤shift 2 x n ∧ shift 2 x n<3/4
    · exact ⟨0,Nat.zero_le _,by simpa using h⟩
    have hδ : (1/2:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [pow_succ] at hl hu
    have hnext : (1/2:ℝ)^k/4≤shift 2 x (n+1) ∧ shift 2 x (n+1)<1-(1/2:ℝ)^k/4 := by
      rw [binary_shift_step]; split_ifs with v <;> push Not at h <;> constructor <;>
        first | linarith | (have := h (by linarith); linarith) | (by_contra! z; have := h (by linarith); linarith)
    obtain ⟨j,hj,H⟩ := ih (n+1) hnext.1 hnext.2
    exact ⟨j+1,by omega,by rwa [show n+(j+1)=(n+1)+j by omega]⟩

/-- Counting positions that can reach a marked position within k further
steps. The last k starts account for the finite-prefix boundary. -/
theorem count_within_steps {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] (N k : ℕ)
    (H : ∀ n, P n → ∃ j≤k, Q (n+j)) :
    ((range N).filter P).card ≤ k+(k+1)*((range N).filter Q).card := by
  classical
  let T := (range N).filter Q
  let B (j : ℕ) := T.image (fun t => t-j)
  have hs : (range N).filter P ⊆ Ico (N-k) N ∪ (range (k+1)).biUnion B := by
    intro n hn
    obtain ⟨hnN,hP⟩ := mem_filter.mp hn
    by_cases he : N-k≤n
    · exact mem_union_left _ (mem_Ico.mpr ⟨he,mem_range.mp hnN⟩)
    · obtain ⟨j,hj,hQ⟩ := H n hP
      apply mem_union_right _ (mem_biUnion.mpr ⟨j,mem_range.mpr (by omega),?_⟩)
      exact mem_image.mpr ⟨n+j,mem_filter.mpr ⟨mem_range.mpr (by omega),hQ⟩,by omega⟩
  have hB := card_biUnion_le (s:=range (k+1)) (t:=B)
  have hc : (∑ j ∈ range (k+1), (B j).card) ≤ (k+1)*T.card := by
    simpa [B] using
      sum_le_sum (s:=range (k+1)) (fun j _ => (card_image_le : (B j).card≤T.card))
  have ht := (card_le_card hs).trans (card_union_le ..)
  rw [Nat.card_Ico] at ht
  change _ ≤ _+_*T.card
  omega

theorem interior_frequency_le_transitions (x : ℝ) (N k : ℕ) :
    frequency (shift 2 x) ((1/2)^k/4) (1-(1/2)^k/4) N ≤
      k/(N:ℝ)+(k+1:ℝ)*transitionFrequency x N := by
  classical
  have H := count_within_steps (P:=fun n => (1/2:ℝ)^k/4≤shift 2 x n ∧ shift 2 x n<1-(1/2:ℝ)^k/4) (Q:=fun n => 1/4≤shift 2 x n ∧ shift 2 x n<3/4) N k (fun n h => transition_near_interior x k n h.1 h.2)
  unfold transitionFrequency frequency
  rw [← mul_div_assoc, ← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast H) (Nat.cast_nonneg _)

/-- Positive lower transition density is exactly the condition that the upper
limiting discrepancy is strictly below one. -/
theorem discrepancy_lt_one_iff_transitions (x : ℝ) :
    asymptoticDiscrepancy x<1 ↔ 0<transitionDensity x := by
  constructor
  · intro H
    let D := (1+asymptoticDiscrepancy x)/2
    have hd : D<1 := by dsimp [D]; linarith
    have small := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)<1))
    obtain ⟨k,hk⟩ := (small.eventually_lt_const (sub_pos.mpr hd)).exists
    let δ := (1/2:ℝ)^k/4
    have gap : 0<1-2*δ-D := by dsimp [δ]; linarith
    let η := (1-2*δ-D)/(2*((k:ℝ)+1))
    have hη : 0<η := div_pos gap (by positivity)
    apply hη.trans_le
    apply le_liminf_of_le (isCoboundedUnder_ge_of_le _ (fun N => (frequency_bounds (shift 2 x) (1/4) (3/4) N).2))
    have ED := eventually_lt_of_limsup_lt (show asymptoticDiscrepancy x<D by dsimp [D]; linarith)
      (isBoundedUnder_of_eventually_le (.of_forall fun N => (discrepancy_bounds x N).2))
    have boundary := (tendsto_const_div_atTop_nhds_zero_nat (k:ℝ)).eventually_lt_const (half_pos gap)
    filter_upwards [ED,boundary] with N hD hsmall
    have hδ : 0<δ := by dsimp [δ]; positivity
    have hlt : δ<1-δ := by dsimp [δ]; linarith [pow_le_one₀ (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)≤1) (n:=k)]
    have lower := (abs_le.mp (interval_le_discrepancy x N hδ.le hlt (by linarith))).1
    have upper := interior_frequency_le_transitions x N k
    change frequency _ δ (1-δ) N≤_ at upper
    dsimp only [η]; rw [div_le_iff₀ (by positivity)]
    change binaryDiscrepancy x N<D at hD
    change _ ≤ transitionFrequency x N * _
    linarith
  · intro h
    exact (asymptoticDiscrepancy_le_transitions x).trans_lt (max_lt (by norm_num) (by linarith))

private lemma anchored_mono (u : ℕ → ℝ) {a b : ℝ} (h : a≤b) (N : ℕ) :
    frequency u 0 a N ≤ frequency u 0 b N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro i hi; obtain ⟨hN,h₁,h₂⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨hN,h₁,h₂.trans_le h⟩

lemma anchored_difference (u : ℕ → ℝ) {a c : ℝ} (ha : 0≤a) (hac : a≤c) (N : ℕ) :
    frequency u a c N = frequency u 0 c N - frequency u 0 a N := by
  classical
  let A := (range N).filter (fun n => 0≤u n ∧ u n<a)
  let B := (range N).filter (fun n => a≤u n ∧ u n<c)
  have hd : Disjoint A B := by
    apply disjoint_left.mpr; intro n hA hB
    exact (mem_filter.mp hA).2.2.not_ge (mem_filter.mp hB).2.1
  have eqn : (range N).filter (fun n => 0≤u n ∧ u n<c)=A∪B := by
    ext n; simp only [A,B,mem_union,mem_filter]
    by_cases h : u n<a <;> grind
  unfold frequency
  rw [eqn,card_union_of_disjoint hd,Nat.cast_add,add_div]; ring

theorem normal_iff_discrepancy_zero (x : ℝ) :
    NormalIn 2 x ↔ asymptoticDiscrepancy x=0 := by
  constructor
  · intro hn
    suffices H : Tendsto (binaryDiscrepancy x) atTop (𝓝 0) from H.limsup_eq
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨q,hq⟩ := exists_nat_gt (8/ε)
    have hq' : (0:ℝ)<q := (div_pos (by norm_num) hε).trans hq
    have hδ : 1/(q:ℝ)<ε/8 := by
      rw [div_lt_iff₀ hq']; have h := (div_lt_iff₀ hε).mp hq; linarith
    let G (j : ℕ) := (j:ℝ)/q
    let F (t : ℝ) := frequency (shift 2 x) 0 t
    have points : ∀ j∈range (q+1), ∀ᶠ N : ℕ in atTop, |F (G j) N-G j| < ε/8 := by
      intro j hj
      have le : j≤q := by have := mem_range.mp hj; omega
      have ht := anchored_frequency_of_normal hn (t:=G j) (by dsimp [G]; positivity)
        ((div_le_one hq').mpr (by exact_mod_cast le))
      exact (Metric.tendsto_nhds.mp ht (ε/8) (by positivity)).mono (fun n h => by simpa only [Real.dist_eq] using h)
    obtain ⟨K,hK⟩ := eventually_atTop.mp ((eventually_all_finset _).mpr points)
    refine ⟨K,fun N hN => ?_⟩
    have anch (t : ℝ) (hl : 0≤t) (hu : t≤1) : |F t N-t|≤ε/4 := by
      by_cases e : t=1
      · have h := hK N hN q (mem_range.mpr (Nat.lt_succ_self _))
        simpa [e,G,hq'.ne'] using (h.le.trans (show ε/8≤ε/4 by linarith))
      let j := ⌊t*q⌋₊
      have hj : j<q := (Nat.floor_lt (mul_nonneg hl hq'.le)).mpr
        (by simpa using mul_lt_mul_of_pos_right (lt_of_le_of_ne hu e) hq')
      have left : G j≤t := (div_le_iff₀ hq').mpr (Nat.floor_le (mul_nonneg hl hq'.le))
      have right : t<G (j+1) := (lt_div_iff₀ hq').mpr (by simpa [j] using Nat.lt_floor_add_one (t*q))
      have step : G (j+1)=G j+1/q := by dsimp [G]; push_cast; ring
      have h₁ := abs_lt.mp (hK N hN j (mem_range.mpr (by omega)))
      have h₂ := abs_lt.mp (hK N hN (j+1) (mem_range.mpr (by omega)))
      have lo : F (G j) N≤F t N := anchored_mono _ left _
      have hi : F t N≤F (G (j+1)) N := anchored_mono _ right.le _
      apply abs_le.mpr; constructor <;> linarith
    have hD : binaryDiscrepancy x N≤ε/2 := by
      apply discrepancy_le; intro a c ha hac hc
      have h₁ := abs_le.mp (anch a ha (hac.le.trans hc))
      have h₂ := abs_le.mp (anch c (ha.trans hac.le) hc)
      rw [anchored_difference _ ha hac.le]
      change |F c N-F a N-(c-a)|≤_
      apply abs_le.mpr; constructor <;> linarith
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (discrepancy_bounds x N).1]; linarith
  · intro hz
    refine ⟨by decide,fun k m _ hm => ?_⟩
    let q := (2:ℝ)^k
    have hq : 0<q := by dsimp [q]; positivity
    have grid (N : ℕ) := interval_le_discrepancy x N (a:=m/q) (c:=(m+1)/q) (by positivity)
      ((div_lt_div_iff_of_pos_right hq).mpr (by linarith)) ((div_le_one hq).mpr (by dsimp [q]; exact_mod_cast (show m+1≤2^k from hm)))
    rw [Metric.tendsto_atTop]; intro ε hε
    obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt (show asymptoticDiscrepancy x<ε by rwa [hz])
      (isBoundedUnder_of_eventually_le (.of_forall (fun n => (discrepancy_bounds x n).2))))
    refine ⟨K,fun N hn => ?_⟩
    have H := (grid N).trans_lt (hK N hn)
    simpa only [Real.dist_eq,show ((m:ℝ)+1)/q-m/q=1/q by ring,q,Nat.cast_ofNat] using H

end NormalityChecker
