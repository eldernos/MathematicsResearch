module

public import NormalityChecker.ExactProfile
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Lebesgue measure of the nested modular cancellation regions. -/
@[expose] public section
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace NormalityChecker.LocalizedSupport

/-- A collection of half-open cells on the real mesh of width `1/q`. -/
def meshRegion (q : ℕ) (U : Finset ℕ) : Set ℝ :=
  ⋃ u ∈ U, Set.Ico ((u:ℝ)/q) (((u:ℝ)+1)/q)

lemma mesh_measurable (q : ℕ) (U : Finset ℕ) : MeasurableSet (meshRegion q U) :=
  MeasurableSet.biUnion U.countable_toSet (fun _ _ => measurableSet_Ico)

theorem mesh_mass {q : ℕ} (hq : 0<q) (U : Finset ℕ) :
    volume.real (meshRegion q U) = (U.card:ℝ)/q := by
  have pos : (0:ℝ)<q := by exact_mod_cast hq
  unfold meshRegion
  rw [measureReal_biUnion_finset (h:=fun _ _ => by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)]
  · have width (u : ℕ) : volume.real (Set.Ico ((u:ℝ)/q) (((u:ℝ)+1)/q))=1/q := by
      rw [Real.volume_real_Ico_of_le (by gcongr; linarith)]; ring
    simp only [width,sum_const,nsmul_eq_mul]; ring
  · intro i _ j _ ne; apply Set.disjoint_left.mpr; intro t hi hj
    rcases lt_or_gt_of_ne ne with lt|lt
    · have h : (i:ℝ)+1≤j := by exact_mod_cast lt
      exact (hi.2.trans_le ((div_le_div_of_nonneg_right h pos.le).trans hj.1)).false
    · have h : (j:ℝ)+1 ≤ i := by exact_mod_cast lt
      exact (hj.2.trans_le ((div_le_div_of_nonneg_right h pos.le).trans hi.1)).false
  · exact fun _ _ => measurableSet_Ico

private theorem mesh_cut {q : ℕ} (hq : 0<q) (U : Finset ℕ) (v : ℕ) :
    meshRegion q U ∩ Set.Iio ((v:ℝ)/q)=meshRegion q (U.filter (·<v)) := by
  have pos : (0:ℝ)<q := by exact_mod_cast hq
  ext t; simp only [meshRegion,Set.mem_inter_iff,Set.mem_iUnion,Set.mem_Ico,Set.mem_Iio,mem_filter]
  constructor
  · rintro ⟨⟨u,hu,l,h⟩,tv⟩; exact ⟨u,⟨hu,by exact_mod_cast (div_lt_div_iff_of_pos_right pos).mp (l.trans_lt tv)⟩,l,h⟩
  · rintro ⟨u,⟨hu,lt⟩,l,h⟩; refine ⟨⟨u,hu,l,h⟩,h.trans_le ?_⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast lt) pos.le

def failedRegion (b s p k : ℕ) (S : Finset ℕ) := meshRegion (p^k) (failedCells b s p k S)

def persistentRegion (b s p : ℕ) (S : Finset ℕ) := ⋂ k, failedRegion b s p k S

theorem failed_region_inside {b s p k : ℕ} {S : Finset ℕ} (hp : 0<p) :
    failedRegion b s p k S ⊆ Set.Icc 1 (p:ℝ) := by
  intro t h; obtain ⟨u,hu,l,h⟩ := Set.mem_iUnion₂.mp h
  obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp hu).1
  have pos : (0:ℝ)<(p^k:ℕ) := by exact_mod_cast pow_pos hp k
  constructor
  · apply le_trans _ l; rw [le_div_iff₀ pos,one_mul]; exact_mod_cast lo
  · apply h.le.trans; rw [div_le_iff₀ pos]; exact_mod_cast hi

/-- Refining the precision can only shrink the failed subset of the phase interval. -/
theorem failed_region_antitone {b s p : ℕ} {S : Finset ℕ} (hs : 0<s) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) : Antitone (fun k => failedRegion b s p k S) := by
  apply antitone_nat_of_succ_le; intro k t ht
  obtain ⟨u,hu,l,h⟩ := Set.mem_iUnion₂.mp ht
  have pos : (0:ℝ)<p := by exact_mod_cast hp.pos
  have pp : (0:ℝ)<(p^k:ℕ) := by exact_mod_cast pow_pos hp.pos k
  have prod : (↑(p^(k+1)):ℝ)=(p^k:ℕ)*p := by push_cast; ring
  refine Set.mem_iUnion₂.mpr ⟨u/p,failed_cell_refines hs hp outside cop hu,?_,?_⟩
  · apply le_trans _ l; rw [prod,← div_div,(le_div_iff₀ pos)]; rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right pp]; exact_mod_cast Nat.div_mul_le_self u p
  · apply h.trans_le; rw [prod,← div_div,div_le_iff₀ pos,mul_comm _ (p:ℝ),mul_div_assoc',div_le_div_iff_of_pos_right pp]; exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_mul_div_succ u hp.pos))

theorem region_mass_tendsto {b s p : ℕ} {S : Finset ℕ} (hs : 0<s) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) : Tendsto (fun k => volume.real (failedRegion b s p k S)) atTop
      (𝓝 (volume.real (persistentRegion b s p S))) := by
  have finite (k : ℕ) : volume (failedRegion b s p k S)≠⊤ := measure_ne_top_of_subset (failed_region_inside hp.pos) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have small := Set.iInter_subset (failedRegion b s p · S) 0
  exact (ENNReal.tendsto_toReal (measure_ne_top_of_subset small (finite 0))).comp
    (tendsto_measure_iInter_atTop (fun _ => (mesh_measurable ..).nullMeasurableSet) (failed_region_antitone hs hp outside cop) ⟨0,finite 0⟩)

/-- Prefix score, including mass inherited from complete earlier scales. -/
def regionScore (p : ℕ) (Z : Set ℝ) (t : ℝ) :=
  (volume.real Z/((p:ℝ)-1)+volume.real (Z ∩ Set.Iio t))/t

private theorem score_at_mesh {p q : ℕ} (hp : 1<p) (hq : 0<q) (U : Finset ℕ) {v : ℕ} (hv : 0<v) :
    regionScore p (meshRegion q U) (v/q:ℝ)=(CellProfile.score p U v:ℝ) := by
  have pp : (p:ℝ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  unfold regionScore CellProfile.score CellProfile.mass
  rw [mesh_cut hq,mesh_mass hq,mesh_mass hq]; push_cast; field_simp

private lemma cut_lipschitz (Z : Set ℝ) (finite : volume Z≠⊤) :
    LipschitzWith 1 (fun t : ℝ => volume.real (Z ∩ Set.Iio t)) := by
  apply LipschitzWith.of_le_add_mul 1; intro a b
  have fin (x : ℝ) : volume (Z ∩ Set.Iio x)≠⊤ := measure_ne_top_of_subset Set.inter_subset_left finite
  simp only [NNReal.coe_one,one_mul,Real.dist_eq]
  rcases le_total a b with h|h
  · exact (measureReal_mono (Set.inter_subset_inter_right Z (Set.Iio_subset_Iio h)) (fin b)).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have sub : Z ∩ Set.Iio a ⊆ (Z ∩ Set.Iio b) ∪ Set.Ico b a := by intro t ht; by_cases l : t<b; exact Or.inl ⟨ht.1,l⟩; exact Or.inr ⟨le_of_not_gt l,ht.2⟩
    have bd := (measureReal_mono (μ:=volume) sub (measure_union_ne_top (fin b) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))).trans (measureReal_union_le _ _)
    simpa [Real.volume_real_Ico_of_le h,abs_of_nonneg (sub_nonneg.mpr h)] using bd

private theorem score_comparison {p : ℕ} (hp : 1<p) {A Z : Set ℝ} (sub : Z⊆A)
    (meas : MeasurableSet Z) (finite : volume A≠⊤) {t : ℝ} (one : 1≤t) :
    regionScore p Z t ≤ regionScore p A t ∧ regionScore p A t ≤ regionScore p Z t +
      (1/((p:ℝ)-1)+1)*(volume.real A-volume.real Z) := by
  have pos : (0:ℝ)<t := by linarith
  have den : 0<(p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hp)
  have fin : volume (A ∩ Set.Iio t)≠⊤ := measure_ne_top_of_subset Set.inter_subset_left finite
  have mono := measureReal_mono (μ:=volume) sub finite
  have cs := Set.inter_subset_inter_left (Set.Iio t) sub
  have cut := measureReal_mono (μ:=volume) cs fin
  have gap : volume.real (A ∩ Set.Iio t)-volume.real (Z ∩ Set.Iio t) ≤ volume.real A-volume.real Z := by
    rw [← measureReal_sdiff cs (meas.inter measurableSet_Iio) fin,← measureReal_sdiff sub meas finite]
    apply measureReal_mono _ (measure_ne_top_of_subset Set.sdiff_subset finite)
    exact fun x h => ⟨h.1.1,fun hz => h.2 ⟨hz,h.1.2⟩⟩
  unfold regionScore; constructor
  · gcongr
  · have factor : 0≤(1/((p:ℝ)-1)+1)*(volume.real A-volume.real Z) := mul_nonneg (by positivity) (sub_nonneg.mpr mono)
    have grow := le_mul_of_one_le_right factor one
    apply (div_le_iff₀ pos).mpr
    rw [add_mul,div_mul_cancel₀ _ pos.ne']
    calc _ ≤ volume.real Z/(p-1)+volume.real (Z ∩ Set.Iio t)+(1/((p:ℝ)-1)+1)*(volume.real A-volume.real Z) := by
               ring_nf at gap ⊢; linarith
         _ ≤ _ := by linarith

/-- With a single off-base prime at order one, the true extreme interval discrepancy
is the maximum of the prefix score of the persistent cancellation set on `[1,p]`. -/
theorem discrepancy_eq_persistent_max {b p : ℕ} {S : Finset ℕ} (hb : 2≤b) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime) (base : ∀ r∈S,r∣b) :
    IsGreatest (regionScore p (persistentRegion b 1 p S) '' Set.Icc 1 (p:ℝ))
      (limsup (radixDiscrepancy b (value b (insert p S))) atTop) := by
  let A := fun k => failedRegion b 1 p k S
  let Z := persistentRegion b 1 p S
  let C := fun k => (discrepancyCertificate b 1 p k S:ℝ)
  let D := limsup (radixDiscrepancy b (value b (insert p S))) atTop
  have limC : Tendsto C atTop (𝓝 D) := certificate_tendsTo_discrepancy hb hp outside cop primes base
  have limA : Tendsto (fun k => volume.real (A k)) atTop (𝓝 (volume.real Z)) := region_mass_tendsto (by decide) hp outside cop
  have sub (k : ℕ) : Z⊆A k := Set.iInter_subset A k
  have finite (k : ℕ) : volume (A k)≠⊤ := measure_ne_top_of_subset (failed_region_inside hp.pos) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have meas : MeasurableSet Z := MeasurableSet.iInter (fun k => mesh_measurable ..)
  have cut := (cut_lipschitz Z (measure_ne_top_of_subset (sub 0) (finite 0))).continuous
  have cont {t : ℝ} (ht : 1≤t) : ContinuousAt (regionScore p Z) t :=
    (continuousAt_const.add cut.continuousAt).div continuousAt_id (by linarith)
  have pp : (1:ℝ)≤p := by exact_mod_cast hp.one_le
  obtain ⟨t,ht,maxim⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr pp)
    (show ContinuousOn (regionScore p Z) (Set.Icc 1 (p:ℝ)) from fun x hx => (cont hx.1).continuousWithinAt)
  have qpos (k : ℕ) : 0<p^k := pow_pos hp.pos k
  have inside {k v : ℕ} (hv : v∈Icc (p^k) (p*p^k)) : (v/(p^k:ℕ):ℝ)∈Set.Icc 1 (p:ℝ) := by
    have pos : (0:ℝ)<(p^k:ℕ) := by exact_mod_cast qpos k
    constructor
    · rw [le_div_iff₀ pos,one_mul]; exact_mod_cast (mem_Icc.mp hv).1
    · rw [div_le_iff₀ pos]; exact_mod_cast (mem_Icc.mp hv).2
  let err := fun k => (1/((p:ℝ)-1)+1)*(volume.real (A k)-volume.real Z)
  have small : Tendsto err atTop (𝓝 0) := by simpa [err] using (limA.sub_const (volume.real Z)).const_mul (1/((p:ℝ)-1)+1)
  have bound (k : ℕ) : C k≤regionScore p Z t+err k := by
    let U := failedCells b 1 p k S
    let scores := insert (0:ℚ) ((Icc (p^k) (p*p^k)).image (CellProfile.score p U))
    suffices all : ∀ r∈scores,(r:ℝ)≤regionScore p Z t+err k from all _ (max'_mem scores (insert_nonempty ..))
    intro r hr; rcases mem_insert.mp hr with rfl|mem
    · have nonneg : 0≤err k := mul_nonneg (add_nonneg (div_nonneg zero_le_one (by linarith)) zero_le_one) (sub_nonneg.mpr (measureReal_mono (sub k) (finite k)))
      have score0 : 0≤regionScore p Z t := div_nonneg (add_nonneg (div_nonneg measureReal_nonneg (by linarith)) measureReal_nonneg) (by linarith [ht.1])
      simpa using add_nonneg score0 nonneg
    obtain ⟨v,hv,rfl⟩ := mem_image.mp mem
    have loc := inside hv
    rw [← score_at_mesh hp.one_lt (qpos k) U ((qpos k).trans_le (mem_Icc.mp hv).1)]
    exact (score_comparison hp.one_lt (sub k) meas (finite k) loc.1).2.trans (add_le_add_left (isMaxOn_iff.mp maxim _ loc) _)
  have upper : D≤regionScore p Z t := by simpa using le_of_tendsto_of_tendsto' limC (small.const_add (regionScore p Z t)) bound
  let v := fun k : ℕ => ⌊t*(p^k:ℕ)⌋₊
  let u := fun k : ℕ => (v k/(p^k:ℕ):ℝ)
  have grid (k : ℕ) : v k∈Icc (p^k) (p*p^k) := by
    apply mem_Icc.mpr; constructor
    · apply Nat.le_floor; exact le_mul_of_one_le_left (by positivity) ht.1
    · apply Nat.floor_le_of_le; push_cast; gcongr; exact ht.2
  have smallMesh := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_pow_atTop_atTop_of_one_lt hp.one_lt)
  have approx : Tendsto u atTop (𝓝 t) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun k => t-1/(p^k:ℕ)) (h:=fun _ => t) (by simpa using (tendsto_const_nhds (x:=t)).sub smallMesh) tendsto_const_nhds
    · intro k; apply (le_div_iff₀ (by exact_mod_cast qpos k : (0:ℝ)<(p^k:ℕ))).mpr
      rw [sub_mul,div_mul_cancel₀ _ (by exact_mod_cast (qpos k).ne')]; linarith [Nat.lt_floor_add_one (t*(p^k:ℕ))]
    · intro k; exact (div_le_iff₀ (by exact_mod_cast qpos k : (0:ℝ)<(p^k:ℕ))).mpr (Nat.floor_le (mul_nonneg (by linarith [ht.1]) (Nat.cast_nonneg _)))
  have lower : regionScore p Z t≤D := by
    apply le_of_tendsto_of_tendsto' ((cont ht.1).tendsto.comp approx) limC; intro k
    refine (score_comparison hp.one_lt (sub k) meas (finite k) (inside (grid k)).1).1.trans ?_
    rw [show regionScore p (A k) (u k)=_ from score_at_mesh hp.one_lt (qpos k) _ ((qpos k).trans_le (mem_Icc.mp (grid k)).1)]
    change _ ≤ ((CellProfile.bound p (p^k) (failedCells b 1 p k S):ℚ):ℝ)
    exact_mod_cast CellProfile.score_le_bound (failedCells b 1 p k S) (grid k)
  have eqn := le_antisymm lower upper
  exact ⟨⟨t,ht,eqn⟩,fun y hy => by obtain ⟨x,hx,rfl⟩ := hy; exact (isMaxOn_iff.mp maxim _ hx).trans lower⟩

/-- Digit normality is equivalent to Lebesgue-null persistent failure. -/
theorem normal_iff_persistent_null {b p : ℕ} {S : Finset ℕ} (hb : 2≤b) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime) (base : ∀ r∈S,r∣b) :
    NormalIn b (value b (insert p S)) ↔ volume (persistentRegion b 1 p S)=0 := by
  let Z := persistentRegion b 1 p S
  let A := fun k => failedRegion b 1 p k S
  have finite (k : ℕ) : volume (A k)≠⊤ := measure_ne_top_of_subset (failed_region_inside hp.pos) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have sub (k : ℕ) : Z⊆A k := Set.iInter_subset A k
  rw [← measureReal_eq_zero_iff (measure_ne_top_of_subset (sub 0) (finite 0))]
  constructor
  · intro normal
    apply le_antisymm _ measureReal_nonneg; by_contra! pos
    obtain ⟨ε,ep,small⟩ := exists_rat_btwn pos
    obtain ⟨k,h⟩ := (normal_iff_shrinking_cells hb hp outside cop primes base).mp normal ε (by exact_mod_cast ep)
    have le := measureReal_mono (sub k) (finite k)
    change volume.real Z≤volume.real (meshRegion _ _) at le
    rw [mesh_mass (pow_pos hp.pos _)] at le
    have h' : ((failedCells b 1 p k S).card:ℝ)≤(ε:ℝ)*(p^k:ℕ) := by exact_mod_cast h
    exact small.not_ge (le.trans ((div_le_iff₀ (by exact_mod_cast pow_pos hp.pos k : (0:ℝ)<(p^k:ℕ))).mpr h'))
  · intro zero
    obtain ⟨⟨t,ht,eqn⟩,_⟩ := discrepancy_eq_persistent_max hb hp outside cop primes base
    apply normal_of_radix_limsup_zero hb; rw [← eqn]
    have cut := measureReal_mono (μ:=volume) (Set.inter_subset_left (s:=Z) (t:=Set.Iio t)) (measure_ne_top_of_subset (sub 0) (finite 0))
    change volume.real Z=0 at zero
    have z : volume.real (Z ∩ Set.Iio t)=0 := le_antisymm (cut.trans_eq zero) measureReal_nonneg
    change (volume.real Z/_+volume.real (Z ∩ Set.Iio t))/t≤0; simp [zero,z]

end NormalityChecker.LocalizedSupport
end
