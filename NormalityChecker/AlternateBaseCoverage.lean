module

public import NormalityChecker.Basic

/-! Counting all complete geometric windows and the unfinished last window. -/
@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker.AlternateBase

private theorem count_increment (p : ℕ → Prop) [DecidablePred p] {L N : ℕ} (le : L≤N)
    (hit : ∀ i : ℕ, L ≤ i → i < N → p i) :
    ((range N).filter p).card = ((range L).filter p).card + (N-L) := by
  have disj : Disjoint ((range L).filter p) (Ico L N) := by
    apply disjoint_left.mpr
    intro i hi hj
    exact (mem_range.mp (mem_filter.mp hi).1).not_ge (mem_Ico.mp hj).1
  have eqn : (range N).filter p = (range L).filter p ∪ Ico L N := by
    ext i; simp only [mem_filter,mem_range,mem_union,mem_Ico]
    constructor
    · rintro ⟨hi,hp⟩
      by_cases e : i<L
      · exact Or.inl ⟨e,hp⟩
      · exact Or.inr ⟨by omega,hi⟩
    · rintro (⟨lo,good⟩|⟨lo,up⟩)
      · exact ⟨lo.trans_le le,good⟩
      · exact ⟨up,hit i lo up⟩
  rw [eqn,card_union_of_disjoint disj,Nat.card_Ico]

/-- For disjoint windows the two densities are attained by the windows themselves
at their left and right endpoints respectively. Extra observations can only help. -/
theorem geometric_window_shares {c : ℕ} (hc : 1<c) {l h : ℝ}
    (hl : 0<l) (lh : l<h) (sep : h≤c*l) (p : ℕ → Prop) [DecidablePred p]
    (hit : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, l*(c:ℝ)^k ≤ n → (n:ℝ)<h*c^k → p n) :
    (∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, (h-l)/((c-1:ℝ)*l)-ε ≤
      (((range N).filter p).card:ℝ)/N) ∧
    (∀ ε : ℝ, 0<ε → ∃ᶠ N : ℕ in atTop, (c:ℝ)*(h-l)/((c-1:ℝ)*h)-ε ≤
      (((range N).filter p).card:ℝ)/N) := by
  let count (N : ℕ) : ℝ := ((range N).filter p).card
  let L (k : ℕ) := ⌈l*(c:ℝ)^k⌉₊
  let H (k : ℕ) := ⌈h*(c:ℝ)^k⌉₊
  let A := (h-l)/((c:ℝ)-1)
  let low := A/l
  let high := ((c:ℝ)*A)/h
  have cp : (1:ℝ)<c := by exact_mod_cast hc
  have hp := hl.trans lh
  have den : 0<(c:ℝ)-1 := by linarith
  have Apos : 0<A := div_pos (sub_pos.mpr lh) den
  have delta : A*((c:ℝ)-1)=h-l := div_mul_cancel₀ _ den.ne'
  have lowpos : 0<low := div_pos Apos hl
  have lowle : low≤1 := by rw [div_le_one hl,div_le_iff₀ den]; linarith
  have loweq : low*l = A := div_mul_cancel₀ _ hl.ne'
  have higheq : high*h = c*A := div_mul_cancel₀ _ hp.ne'
  have highle : high≤1 := by
    rw [div_le_one hp]
    nlinarith only [delta,(div_le_one hl).mp lowle]
  have highpos : 0<high := div_pos (mul_pos (by positivity) Apos) hp
  have mono {i j : ℕ} (ij : i≤j) : count i ≤ count j := by
    dsimp [count]; exact_mod_cast card_le_card (filter_subset_filter p (range_mono ij))
  have left (k) : l*(c:ℝ)^k ≤ L k := Nat.le_ceil _
  have left' (k) : (L k:ℝ) < l*(c:ℝ)^k+1 := Nat.ceil_lt_add_one (by positivity)
  have right (k) : h*(c:ℝ)^k ≤ H k := Nat.le_ceil _
  have right' (k) : (H k:ℝ) < h*(c:ℝ)^k+1 := Nat.ceil_lt_add_one (by positivity)
  have order (k) : L k ≤ H k := Nat.ceil_mono (by gcongr)
  have disjoint (k) : H k ≤ L (k+1) := Nat.ceil_mono (by
    rw [pow_succ]; simpa [mul_left_comm,mul_comm,mul_assoc] using
      mul_le_mul_of_nonneg_right sep (pow_nonneg (by positivity : (0:ℝ)≤c) k))
  obtain ⟨K,good⟩ := eventually_atTop.mp hit
  have inc {k n : ℕ} (hk : K≤k) (lo : L k≤n) (up : n≤H k) :
      count n = count (L k)+(n:ℝ)-L k := by
    have res := count_increment p lo (fun i a b => good k hk i (Nat.ceil_le.mp a)
      (Nat.lt_ceil.mp (b.trans_le up)))
    have e : count n = count (L k)+((n-L k:ℕ):ℝ) := by dsimp only [count]; exact_mod_cast res
    rw [e,Nat.cast_sub lo]; ring
  let C := A*(c:ℝ)^K
  have base {k : ℕ} (hk : K≤k) : A*(c:ℝ)^k ≤ count (L k)+k+C := by
    induction k, hk using Nat.le_induction with
    | base => have : 0≤count (L K) := by dsimp [count]; positivity
              dsimp [C]; linarith [Nat.cast_nonneg (α:=ℝ) K]
    | succ k hk ih =>
      have x := inc hk (order k) le_rfl
      have y := mono (disjoint k)
      have e := congrArg (· * (c:ℝ)^k) delta
      rw [pow_succ,Nat.cast_add_one]
      nlinarith only [x,y,ih,e,left' k,right k]
  have loss (ε : ℝ) (ep : 0<ε) : ∀ᶠ k : ℕ in atTop, (k:ℝ)+C+2 ≤ ε*(l*c^k) := by
    have f := tendsto_pow_const_div_const_pow_of_one_lt 1 cp
    have g := (tendsto_const_nhds (x:=C+2)).div_atTop (tendsto_pow_atTop_atTop_of_one_lt cp)
    have t := f.add g
    simp only [pow_one,add_zero] at t
    filter_upwards [t.eventually_le_const (mul_pos ep hl)] with k bound
    change (k:ℝ)/((c:ℝ)^k)+(C+2)/((c:ℝ)^k) ≤ ε*l at bound
    rw [← add_div,div_le_iff₀ (by positivity)] at bound
    linarith only [bound,show ε*l*(c:ℝ)^k=ε*(l*c^k) by ring]
  constructor
  · intro ε ep
    obtain ⟨T,small⟩ := eventually_atTop.mp (loss ε ep)
    filter_upwards [eventually_ge_atTop (L (max T K)),eventually_gt_atTop 0] with N enough np
    let m := ⌊(N:ℝ)/l⌋₊
    let k := Nat.log c m
    have powle : c^(max T K) ≤ m := Nat.le_floor ((le_div_iff₀ hl).mpr (by
      simpa [mul_comm] using (left _).trans (show (L (max T K):ℝ)≤N by exact_mod_cast enough)))
    have late := Nat.le_log_of_pow_le hc powle
    have kt : T≤k := (le_max_left ..).trans late
    have kk : K≤k := (le_max_right ..).trans late
    have mpos := (pow_pos (by omega : 0<c) _).trans_le powle
    have loq : l*(c:ℝ)^k ≤ N := by
      rw [mul_comm,← le_div_iff₀ hl]
      exact (show (c:ℝ)^k≤m by exact_mod_cast Nat.pow_log_le_self c mpos.ne').trans (Nat.floor_le (by positivity))
    have upq : (N:ℝ) < l*(c:ℝ)^(k+1) := by
      rw [mul_comm,← div_lt_iff₀ hl]
      exact (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast Nat.lt_pow_succ_log_self hc m)
    have bnd := base kk
    have price := (small k kt).trans (mul_le_mul_of_nonneg_left loq ep.le)
    change (h-l)/(((c:ℝ)-1)*l)-ε ≤ count N/N
    rw [← div_div,le_div_iff₀ (by exact_mod_cast np : (0:ℝ)<N)]
    change (low-ε)*N ≤ _
    by_cases inside : N≤H k
    · have add := inc kk (Nat.ceil_le.mpr loq) inside
      have slope := mul_nonneg (sub_nonneg.mpr lowle) (sub_nonneg.mpr loq)
      have atL := congrArg (· * (c:ℝ)^k) loweq
      nlinarith only [add,bnd,price,slope,atL,left' k]
    · have add := inc kk (order k) le_rfl
      have more := mono (le_of_not_ge inside)
      rw [pow_succ] at upq
      have slope := mul_le_mul_of_nonneg_left upq.le lowpos.le
      have atL := congrArg (· * ((c:ℝ)^k*c)) loweq
      have e := congrArg (· * (c:ℝ)^k) delta
      nlinarith only [add,more,bnd,price,slope,atL,e,left' k,right k]
  · intro ε ep
    obtain ⟨T,small⟩ := eventually_atTop.mp (loss ε ep)
    rw [frequently_atTop]
    intro M
    obtain ⟨k,late,big⟩ := ((eventually_ge_atTop (max K T)).and
      ((tendsto_pow_atTop_atTop_of_one_lt cp).eventually_ge_atTop ((M:ℝ)/h))).exists
    have hM : M≤H k := by
      have bound : (M:ℝ) ≤ H k := ((div_le_iff₀ hp).mp big).trans (by simpa [mul_comm] using right k)
      exact_mod_cast bound
    refine ⟨H k,hM,?_⟩
    have kk : K≤k := le_trans (le_max_left ..) late
    have kt : T≤k := le_trans (le_max_right ..) late
    have hpos : (0:ℝ)<H k := (mul_pos hp (by positivity)).trans_le (right k)
    have add := inc kk (order k) le_rfl
    have bnd := base kk
    have loq : l*(c:ℝ)^k ≤ H k := (mul_le_mul_of_nonneg_right lh.le (by positivity)).trans (right k)
    have price := (small k kt).trans (mul_le_mul_of_nonneg_left loq ep.le)
    have atH := congrArg (· * (c:ℝ)^k) higheq
    have e := congrArg (· * (c:ℝ)^k) delta
    have rounded := mul_le_mul_of_nonneg_left (right' k).le highpos.le
    rw [← div_div,mul_div_assoc,le_div_iff₀ hpos]
    change (high-ε)*H k ≤ count (H k)
    nlinarith only [price,bnd,e,atH,add,rounded,highle,left' k,right k]

end NormalityChecker.AlternateBase
