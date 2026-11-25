module

public import NormalityChecker.QuadraticOrbitShells

/-! Density of exceptional upper half-shells through arbitrary cutoffs.
The hypotheses concern actual partial-shell counts and separation in shell
index, whereas the conclusion concerns ordinary prefixes in digit position. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.QuadraticOrbit

def Separated (q : ℕ → ℕ) : Prop :=
  ∀ M H : ℕ, ∀ᶠ t : ℕ in atTop, ∀ i ∈ Ico t (t+H), ∀ j ∈ Ico t (t+H),
    q i < M → q j < M → i = j

private def Bad (q : ℕ → ℕ) (M n : ℕ) : Prop :=
  ∃ r, q r < M ∧ 3*2^r ≤ n ∧ n < 4*2^r

private noncomputable def badSet (q : ℕ → ℕ) (M N : ℕ) : Finset ℕ := by
  classical exact (range N).filter (Bad q M)

private theorem index_unique {r j n : ℕ} (lo : 2*2^r ≤ n) (hi : n < 4*2^r)
    (low : 3*2^j ≤ n) (high : n < 4*2^j) : j = r := by
  have next (k : ℕ) : 2^(k+2) = 4*2^k := by rw [pow_add]; ring
  apply Nat.succ.inj
  calc j+1 = Nat.log 2 n := (Nat.log_eq_of_pow_le_of_lt_pow (by rw [pow_succ']; omega) (by rwa [next])).symm
       _ = r+1 := Nat.log_eq_of_pow_le_of_lt_pow (by rwa [pow_succ']) (by rwa [next])

private theorem unit_sum (f : ℕ → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) (s T : ℕ) :
    ‖∑ i ∈ range T, f (s+i)‖ ≤ T :=
  (norm_sum_le ..).trans ((sum_le_sum (fun i _ => hf (s+i))).trans_eq (by simp))

/-- At a fixed accuracy the unexceptional positions contribute a uniformly
small centered count, even with an unfinished half-shell. -/
private theorem discrepancy_le_count {b : ℕ} {x : ℝ} {q : ℕ → ℕ} (good : GoodHalves b x q)
    {ε : ℝ} (ep : 0 < ε) : ∃ M : ℕ, ∀ᶠ N : ℕ in atTop,
      radixDiscrepancy b x N ≤ ε + ((badSet q M N).card : ℝ)/N := by
  classical
  obtain ⟨M,late⟩ := good (ε/12) (by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp late
  let L := 2*2^K
  have small := (tendsto_const_div_atTop_nhds_zero_nat (L:ℝ)).eventually_le_const (half_pos ep)
  refine ⟨M,?_⟩
  filter_upwards [eventually_ge_atTop L,small,eventually_gt_atTop 0] with N hn init pos
  have nr : (0:ℝ)<N := by exact_mod_cast pos
  unfold radixDiscrepancy
  refine csSup_le ?_ ?_
  · exact ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩
  rintro _ ⟨a,c,ha,hac,hc,rfl⟩
  let f := Localized.centered (shift b x) a c
  let g (n : ℕ) := if Bad q M n then 0 else f n
  have gu (n : ℕ) : ‖g n‖ ≤ 1 := by
    dsimp [g]; split_ifs <;> first | simp | exact Localized.centered_norm _ ha hac.le hc n
  have bulk := prefix_of_radix_cells (c:=2) (S:=2) (f:=g) (by decide) (by decide)
    (show 0 < ε/12 by positivity) hn (fun r hr u hu T ht => by
      obtain ⟨ul,ur⟩ := mem_Ico.mp hu
      have cases : u=2 ∨ u=3 := by omega
      have bad (i : ℕ) (hi : i < T) : Bad q M (u*2^r+i) ↔ u=3 ∧ q r < M := by
        constructor
        · rintro ⟨j,low,left,right⟩
          have id := index_unique (r:=r) (j:=j)
            (by rcases cases with h|h <;> rw [h] <;> omega)
            (by rcases cases with h|h <;> rw [h] <;> omega) left right
          subst j
          exact ⟨by rcases cases with h|h <;> subst u <;> omega, low⟩
        · rintro ⟨rfl,low⟩
          exact ⟨r,low,by omega,by omega⟩
      by_cases pay : u=3 ∧ q r<M
      · have eqn : (∑ i ∈ range T, g (u*2^r+i)) = 0 :=
          sum_eq_zero (fun i hi => by simp [g,(bad i (mem_range.mp hi)).mpr pay])
        rw [eqn]
        rw [norm_zero]; positivity
      · have eqn : (∑ i ∈ range T, g (u*2^r+i)) = ∑ i ∈ range T, f (u*2^r+i) :=
          sum_congr rfl (fun i hi => by simp [g,show ¬ Bad q M (u*2^r+i) from fun h => pay ((bad i (mem_range.mp hi)).mp h)])
        rw [eqn]
        exact hK r hr u (by rcases cases with h|h; exact Or.inl h; exact Or.inr ⟨h,by grind⟩)
          T ht a c ha hac.le hc)
  have start : ‖∑ i ∈ range L, g i‖ ≤ L := by simpa using unit_sum g gu 0 L
  have gsmall : ‖∑ i ∈ range N, g i‖ ≤ ε*N := by
    change ‖_‖ ≤ ‖∑ i ∈ range L,g i‖+_ at bulk
    push_cast at bulk
    linarith only [bulk,start,(div_le_iff₀ nr).mp init]
  have residual : ‖(∑ i ∈ range N, f i) - ∑ i ∈ range N, g i‖ ≤ (badSet q M N).card := by
    rw [← sum_sub_distrib]
    have each (i : ℕ) : ‖f i-g i‖ ≤ (if Bad q M i then (1:ℝ) else 0) := by
      by_cases h : Bad q M i
      · simpa [g,h] using Localized.centered_norm (shift b x) ha hac.le hc i
      · simp [g,h]
    apply (norm_sum_le ..).trans ((sum_le_sum (fun i _ => each i)).trans_eq _)
    simp [badSet]
  have bound := (norm_le_norm_add_norm_sub' (∑ i ∈ range N, f i) (∑ i ∈ range N, g i)).trans (add_le_add gsmall residual)
  have id := Localized.centered_sum (shift b x) a c 0 N
  simp only [zero_add] at id
  change ‖∑ i ∈ range N, f i‖ = _ at id
  rw [id] at bound
  change |(IntervalFourier.count (shift b x) a c N : ℝ)/N-(c-a)| ≤ _
  rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_iff₀ nr,add_mul,div_mul_cancel₀ _ nr.ne']
  simpa only [mul_comm (c-a)] using bound

private theorem recent_index {t H N n r : ℕ} (up : N ≤ 2^(t+H+1))
    (near : 2^(t+1) ≤ n) (hn : n < N) (lo : 3*2^r ≤ n) (hi : n < 4*2^r) :
    r ∈ Ico t (t+H) := by
  have h₁ : 2^(t+1) < 2^(r+2) := by rw [pow_add (2:ℕ) r 2]; omega
  have h₂ : 2^(r+1) < 2^(t+H+1) := by rw [pow_succ']; omega
  have i := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h₁
  have j := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h₂
  exact mem_Ico.mpr ⟨by omega,by omega⟩

private theorem no_recent (q : ℕ → ℕ) (M t H N : ℕ) (up : N ≤ 2^(t+H+1))
    (clear : ∀ r ∈ Ico t (t+H), M ≤ q r) : (badSet q M N).card ≤ 2^(t+1) := by
  classical
  apply (card_le_card (t:=range (2^(t+1))) _).trans_eq (card_range _)
  intro n hn
  obtain ⟨hn, r,small,lo,hi⟩ := mem_filter.mp (show n ∈ (range N).filter (Bad q M) from hn)
  apply mem_range.mpr
  by_contra! near
  exact small.not_ge (clear r (recent_index up near (mem_range.mp hn) lo hi))

/-- Any single exceptional upper half, even when the prefix ends inside it,
accounts for at most one quarter of all positions before the cutoff. -/
theorem clipped_upper_quarter (r N : ℕ) :
    4*(Ico (3*2^r) (min N (4*2^r))).card ≤ N := by
  rw [Nat.card_Ico]; omega

private theorem one_recent (q : ℕ → ℕ) (M t H N : ℕ) (up : N ≤ 2^(t+H+1))
    (uniq : ∀ i ∈ Ico t (t+H), ∀ j ∈ Ico t (t+H), q i < M → q j < M → i=j) :
    4*(badSet q M N).card ≤ 4*2^(t+1)+N := by
  classical
  by_cases ex : ∃ r ∈ Ico t (t+H), q r < M
  · obtain ⟨r,hr,small⟩ := ex
    let S := Ico (3*2^r) (min N (4*2^r))
    have sub : badSet q M N ⊆ range (2^(t+1)) ∪ S := by
      intro n hn
      obtain ⟨hn,j,jb,lo,hi⟩ := mem_filter.mp (show n ∈ (range N).filter (Bad q M) from hn)
      by_cases old : n < 2^(t+1)
      · exact mem_union_left _ (mem_range.mpr old)
      · obtain rfl := uniq j (recent_index up (by omega) (mem_range.mp hn) lo hi) r hr jb small
        exact mem_union_right _ (mem_Ico.mpr ⟨lo,lt_min (mem_range.mp hn) hi⟩)
    have count := (card_le_card sub).trans (card_union_le ..)
    rw [card_range] at count
    have cost : 4*S.card ≤ N := clipped_upper_quarter r N
    omega
  · push Not at ex
    have := no_recent q M t H N up ex
    omega

/-- The half-shell geometry gives both the worst ordinary upper discrepancy
and arbitrarily late ordinary prefixes with vanishing discrepancy. -/
theorem ordinary_limits {b : ℕ} {x : ℝ} {q : ℕ → ℕ}
    (good : GoodHalves b x q) (sep : Separated q) :
    limsup (radixDiscrepancy b x) atTop ≤ 1/4 ∧ liminf (radixDiscrepancy b x) atTop = 0 := by
  have bd := radix_discrepancy_bounds b x
  have lower := isBoundedUnder_of_eventually_ge (f:=atTop) (.of_forall (fun n => (bd n).1))
  have upper := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall (fun n => (bd n).2))
  have choose (e : ℝ) (he : 0 < e) : ∃ H : ℕ, 2 ≤ e*(2:ℝ)^H := by
    obtain ⟨H,h⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually_ge_atTop (2/e)).exists
    exact ⟨H,by linarith only [(div_le_iff₀ he).mp h]⟩
  have old {t H N : ℕ} {e : ℝ} (he : 0 ≤ e) (h : 2 ≤ e*(2:ℝ)^H)
      (low : 2^(t+H) ≤ N) : ((2^(t+1):ℕ):ℝ) ≤ e*N := by
    have l : (2:ℝ)^t*2^H ≤ N := by exact_mod_cast (show 2^t*2^H ≤ N by rwa [←pow_add])
    push_cast; rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2:ℝ)^t),mul_le_mul_of_nonneg_left l he]
  constructor
  · apply (limsup_le_iff (isCoboundedUnder_le_of_le _ (fun n => (bd n).1)) upper).mpr
    intro v hv
    let e := (v-1/4)/3
    have ep : 0 < e := by dsimp [e]; linarith
    obtain ⟨H,hH⟩ := choose e ep
    obtain ⟨M,cmp⟩ := discrepancy_le_count good ep
    obtain ⟨K,hK⟩ := eventually_atTop.mp (sep M H)
    filter_upwards [cmp,eventually_ge_atTop (2^(K+H))] with N hN large
    have np := (pow_pos (by decide : 0<2) _).trans_le large
    let t := Nat.log 2 N-H
    have late := Nat.le_log_of_pow_le (by decide : 1<2) large
    have eqn : t+H=Nat.log 2 N := by dsimp [t]; omega
    have space := one_recent q M t H N (by rw [eqn]; exact (Nat.lt_pow_succ_log_self (by decide) N).le)
      (hK t (by dsimp [t]; omega))
    have d : 4*((badSet q M N).card:ℝ) ≤ 4*((2^(t+1):ℕ):ℝ)+N := by exact_mod_cast space
    have os := old ep.le hH (N:=N) (t:=t) (by rw [eqn]; exact Nat.pow_log_le_self _ np.ne')
    have nr : (0:ℝ)<N := by exact_mod_cast np
    have frac : ((badSet q M N).card:ℝ)/N ≤ e+1/4 := by rw [div_le_iff₀ nr]; linarith
    dsimp only [e] at *; linarith
  · apply le_antisymm _ (le_liminf_of_le (isCoboundedUnder_ge_of_le _ (fun n => (bd n).2)) (.of_forall fun n => (bd n).1))
    refine le_of_forall_gt_imp_ge_of_dense (fun v hv => ?_)
    let e := v/3
    have ep : 0 < e := by dsimp [e]; positivity
    obtain ⟨H,hH⟩ := choose e ep
    obtain ⟨M,cmp⟩ := discrepancy_le_count good ep
    obtain ⟨K,late⟩ := eventually_atTop.mp ((sep M (2*H)).and cmp)
    refine liminf_le_of_frequently_le ?_ lower
    rw [frequently_atTop]
    intro L
    let t := max K L
    have unique := (late t (le_max_left ..)).1
    have clear : ∃ s, t ≤ s ∧ ∀ i ∈ Ico s (s+H), M ≤ q i := by
      by_cases e₁ : ∀ i ∈ Ico t (t+H), M ≤ q i
      · exact ⟨t,le_rfl,e₁⟩
      · push Not at e₁; obtain ⟨i,hi,bi⟩ := e₁
        refine ⟨t+H,Nat.le_add_right ..,fun j hj => ?_⟩
        by_contra! bj
        simp only [mem_Ico] at hi hj
        have id := unique i (mem_Ico.mpr ⟨hi.1,by omega⟩) j (mem_Ico.mpr ⟨by omega,by omega⟩) bi bj
        omega
    obtain ⟨s,ts,clear⟩ := clear
    let N := 2^(s+H+1)
    have sn : s ≤ N := (Nat.lt_two_pow_self (n:=s)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have ns : 0 < N := pow_pos (by decide) _
    have nr : (0:ℝ)<N := by exact_mod_cast ns
    have comp := (late N ((le_max_left ..).trans (ts.trans sn))).2
    have cost := no_recent q M s H N le_rfl clear
    have bd' : ((badSet q M N).card:ℝ)/N ≤ e := (div_le_iff₀ nr).mpr
      ((by exact_mod_cast cost : ((badSet q M N).card:ℝ) ≤ ((2^(s+1):ℕ):ℝ)).trans
        (old ep.le hH (by exact Nat.pow_le_pow_right (by decide) (Nat.le_succ (s+H)))))
    refine ⟨N,(le_max_right ..).trans (ts.trans sn),?_⟩
    dsimp [e] at *; linarith

/-- In the absence of repeated bounded upper denominators all late halves
have the same estimate; only finitely many positions can be exceptional. -/
theorem normal_of_good_halves {b : ℕ} {x : ℝ} {q : ℕ → ℕ} (hb : 2 ≤ b)
    (good : GoodHalves b x q) (grow : Tendsto q atTop atTop) : NormalIn b x := by
  classical
  apply normal_of_radix_limsup_zero hb
  apply (limsup_le_iff (isCoboundedUnder_le_of_le _ (fun n => (radix_discrepancy_bounds b x n).1))
    (isBoundedUnder_of_eventually_le (.of_forall fun n => (radix_discrepancy_bounds b x n).2))).mpr
  intro v hv
  obtain ⟨M,cmp⟩ := discrepancy_le_count good (show 0<v/3 by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (grow.eventually_ge_atTop M)
  have card (N : ℕ) : (badSet q M N).card ≤ 4*2^K := by
    apply (card_le_card (t:=range (4*2^K)) _).trans_eq (card_range _)
    intro n hn
    obtain ⟨_,j,small,_,hi⟩ := mem_filter.mp (show n ∈ (range N).filter (Bad q M) from hn)
    have le : j ≤ K := by by_contra! gt; exact small.not_ge (hK _ gt.le)
    exact mem_range.mpr (hi.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) le)))
  have lim := (tendsto_const_div_atTop_nhds_zero_nat ((4*2^K:ℕ):ℝ)).eventually_le_const (show 0<v/3 by positivity)
  filter_upwards [cmp,lim] with n h small
  have cost := (div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr (card n)) (Nat.cast_nonneg n)).trans small
  linarith

theorem normal_iff_upper_growth {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) :
    NormalIn b (value b A B C / D) ↔ Tendsto (upperDen b A B C) atTop atTop := by
  constructor
  · intro h
    apply upper_den_tendsto_of_normal hb odd A B C nz
    have scaled := (normal_mul_nat_iff (by omega : 2≤b) hd _).mpr h
    rwa [show (D:ℝ)*(value b A B C / D) = value b A B C by field_simp] at scaled
  · exact normal_of_good_halves (by omega) (rational_good_halves hb odd hd A B C nz)

end NormalityChecker.QuadraticOrbit
