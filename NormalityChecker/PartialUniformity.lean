module

public import NormalityChecker.SupportDiscrepancy

/-! Finite resolution and positive-coverage discrepancy bounds for arbitrary radix orbits. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- An anchored empirical distribution with slope `g ≤ 1` can be tested on a finite mesh. -/
private theorem anchored_mesh {F : ℝ → ℝ} (mono : Monotone F) {g e : ℝ} (lo : 0≤g) (hi : g≤1)
    {q : ℕ} (hq : 0<q) (mesh : ∀ j≤q, |F (j/q:ℝ)-g*(j/q:ℝ)|≤e) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    |F t-g*t|≤e+1/q := by
  have qr : (0:ℝ)<q := by exact_mod_cast hq
  by_cases endpt : t=1
  · simpa [endpt,qr.ne'] using (mesh q le_rfl).trans (show e≤e+1/(q:ℝ) by linarith [one_div_pos.mpr qr])
  let j := ⌊t*q⌋₊
  have h := (Nat.floor_lt (mul_nonneg ht.1 qr.le)).mpr (by simpa using mul_lt_mul_of_pos_right (lt_of_le_of_ne ht.2 endpt) qr : t*q<(q:ℝ))
  change j<q at h
  have left : (j:ℝ)/q≤t := (div_le_iff₀ qr).mpr (Nat.floor_le (mul_nonneg ht.1 qr.le))
  have right : t<((j+1:ℕ):ℝ)/q := (lt_div_iff₀ qr).mpr (by simpa using Nat.lt_floor_add_one (t*q))
  have l := (abs_le.mp (mesh j h.le)).1; have r := (abs_le.mp (mesh (j+1) h)).2
  have width : ((j+1:ℕ):ℝ)/q=(j:ℝ)/q+1/q := by push_cast; ring
  have bot := mono left; have top := mono right.le; rw [width] at r right top
  have cost := mul_le_mul_of_nonneg_right hi (one_div_pos.mpr qr).le
  apply abs_le.mpr; constructor <;> nlinarith only [bot,top,l,r,cost,mul_le_mul_of_nonneg_left left lo,mul_le_mul_of_nonneg_left right.le lo]

private theorem radix_le {b N : ℕ} {x D : ℝ}
    (H : ∀ a c : ℝ, 0≤a → a<c → c≤1 → |frequency (shift b x) a c N-(c-a)|≤D) :
    radixDiscrepancy b x N ≤ D := by
  unfold radixDiscrepancy
  refine csSup_le ?_ ?_
  · exact ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩
  rintro _ ⟨a,c,ha,hac,hc,rfl⟩
  exact H a c ha hac hc

/-- Any positive integer mesh size can be used, including `q=b^k` for a digit test. -/
theorem discrepancy_of_fixed_cells {b q : ℕ} {x : ℝ} (hq : 0<q)
    (cells : ∀ j<q,Tendsto (frequency (shift b x) (j/q:ℝ) (((j:ℝ)+1)/q)) atTop (𝓝 (1/(q:ℝ)))) :
    limsup (radixDiscrepancy b x) atTop ≤ 2/(q:ℝ) := by
  let f := shift b x
  have qr : (0:ℝ)<q := by exact_mod_cast hq
  have anchors (j : ℕ) (hj : j≤q) : Tendsto (frequency f 0 (j/q:ℝ)) atTop (𝓝 (j/q:ℝ)) := by
    induction j with
    | zero =>
      simp only [Nat.cast_zero,zero_div]; convert (tendsto_const_nhds (x:=(0:ℝ)) (f:=atTop (α:=ℕ))) using 1
      funext N; simp [frequency,show ∀ i : ℕ, ¬(0≤f i ∧ f i<0) from fun i h => h.2.not_ge h.1]
    | succ j ih =>
      have p := (cells j (by omega)).add (ih (by omega))
      push_cast; rw [show ((j:ℝ)+1)/q=1/q+j/q by ring] at *
      apply p.congr; intro N
      rw [anchored_difference _ (by positivity : 0≤(j:ℝ)/q) (by linarith [one_div_pos.mpr qr] : (j:ℝ)/q≤1/q+j/q)]
      change _-frequency f 0 _ N+frequency f 0 _ N=_; ring
  apply (limsup_le_iff (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds b x N).1)) (isBoundedUnder_of_eventually_le (.of_forall (fun N => (radix_discrepancy_bounds b x N).2)))).mpr
  intro z hz; let e := (z-2/q)/4
  have ep : 0<e := div_pos (sub_pos.mpr hz) (by norm_num)
  have each (j : ℕ) (hj : j∈range (q+1)) := (Metric.tendsto_nhds.mp (anchors j (by have := mem_range.mp hj; omega)) e ep).mono (fun _ h => (show |_ - _|<e by simpa only [Real.dist_eq] using h).le)
  filter_upwards [(eventually_all_finset _).mpr each] with N grid
  have mono : Monotone (fun t => frequency f 0 t N) := by
    intro a c ac; apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _); apply Nat.cast_le.mpr; apply card_le_card
    intro i h; obtain ⟨hi,lo,up⟩ := mem_filter.mp h; exact mem_filter.mpr ⟨hi,lo,up.trans_le ac⟩
  have anchor {t : ℝ} (h : t∈Set.Icc 0 1) : |frequency f 0 t N-t|≤e+1/q := by
    simpa using anchored_mesh mono (g:=1) zero_le_one le_rfl hq (fun j hj => by simpa using grid j (mem_range.mpr (by omega))) h
  suffices h : radixDiscrepancy b x N≤2*(e+1/q) by
    dsimp [e] at h
    linarith [show (2:ℝ)/q=2*(1/q) by ring]
  apply radix_le
  intro a c ha ac hc
  have l := abs_le.mp (anchor ⟨ha,ac.le.trans hc⟩); have r := abs_le.mp (anchor ⟨ha.trans ac.le,hc⟩)
  rw [anchored_difference _ ha ac.le]; apply abs_le.mpr; constructor <;> dsimp [f] at l r <;> linarith [l.1,l.2,r.1,r.2]

/-- `G N` may vary with the prefix. A uniformly distributed selected part covering
at least `g` in lower density bounds the full asymptotic discrepancy by `1-g`. -/
theorem discrepancy_of_uniform_share {b : ℕ} {x g : ℝ} (G : ℕ → Finset ℕ) (sub : ∀ N,G N⊆range N)
    (cover : ∀ e : ℝ,0<e → ∀ᶠ N : ℕ in atTop,g-e≤((G N).card:ℝ)/N)
    (uniform : ∀ e : ℝ,0<e → ∀ᶠ N : ℕ in atTop,∀ a c : ℝ,0≤a → a<c → c≤1 →
      |(((G N).filter (fun n => a≤shift b x n ∧ shift b x n<c)).card:ℝ)-(G N).card*(c-a)|≤e*N) :
    limsup (radixDiscrepancy b x) atTop ≤ 1-g := by
  classical
  apply (limsup_le_iff (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds b x N).1)) (isBoundedUnder_of_eventually_le (.of_forall (fun N => (radix_discrepancy_bounds b x N).2)))).mpr
  intro z hz; let e := (z-(1-g))/3; have ep : 0<e := div_pos (sub_pos.mpr hz) (by norm_num)
  filter_upwards [cover e ep,uniform e ep,eventually_gt_atTop 0] with N cov unif hn
  have nr : (0:ℝ)<N := by exact_mod_cast hn
  suffices h : radixDiscrepancy b x N≤1-g+2*e by dsimp [e] at h; linarith
  apply radix_le
  intro a c ha ac hc
  let pred := fun n => a≤shift b x n ∧ shift b x n<c
  let R := range N \ G N
  have part := filter_union pred (G N) R
  have union : G N∪R=range N := union_sdiff_of_subset (sub N)
  rw [union] at part
  have dis : Disjoint ((G N).filter pred) (R.filter pred) := Finset.disjoint_sdiff.mono (filter_subset ..) (filter_subset ..)
  have count := congrArg Finset.card part; rw [card_union_of_disjoint dis] at count
  have size := card_sdiff_add_card_eq_card (sub N); rw [card_range] at size
  have sz : (R.card:ℝ)+(G N).card=N := by exact_mod_cast size
  have bd : ((R.filter pred).card:ℝ)≤R.card := by exact_mod_cast card_filter_le R pred
  have u := abs_le.mp (unif a c ha ac hc); change -_≤(((G N).filter pred).card:ℝ)-_ ∧ _ at u
  rw [le_div_iff₀ nr] at cov
  unfold frequency; change |(((range N).filter pred).card:ℝ)/N-(c-a)|≤_
  rw [count,Nat.cast_add,abs_le]; constructor <;> field_simp [nr.ne'] <;>
    nlinarith only [u.1,u.2,bd,cov,sz,mul_nonneg (Nat.cast_nonneg (α:=ℝ) R.card) (sub_nonneg.mpr ac.le),mul_nonneg (Nat.cast_nonneg (α:=ℝ) R.card) (show 0≤1-(c-a) by linarith),Nat.cast_nonneg (α:=ℝ) (R.filter pred).card,show (R.card:ℝ)*(c-a)+(G N).card*(c-a)=N*(c-a) by rw [← add_mul,sz]]

end NormalityChecker
