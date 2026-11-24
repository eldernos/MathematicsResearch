module

public import NormalityChecker.HigherOrderCells
public import NormalityChecker.HigherOrderDominance
public import NormalityChecker.HigherOrderDiscrepancy

/-! All-cutoff discrepancy of finite-support polylogarithms and the simultaneous
persistent failure regions of their lower orders. -/
@[expose] public section
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace NormalityChecker.LocalizedSupport

/-- The normalized real phase of a digit position, on the scale of the prime `p`. -/
def digitPhase (p : ℕ) (y : ℝ) := y / (p:ℝ)^(Nat.log p ⌊y⌋₊)

private lemma phase_digit {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : 1 ≤ y) :
    digitPhase p y ∈ Set.Ico 1 (p:ℝ) ∧
      ⌊digitPhase p y * (p:ℝ)^(Nat.log p ⌊y⌋₊)⌋₊ = ⌊y⌋₊ := by
  let n := ⌊y⌋₊
  let k := Nat.log p n
  have np : 0<n := (Nat.le_floor (by simpa using hy : (↑(1:ℕ):ℝ) ≤ y))
  have pos : 0 < (p:ℝ)^k := by exact_mod_cast pow_pos hp.pos k
  have lo : (p:ℝ)^k ≤ (n:ℝ) := by exact_mod_cast Nat.pow_log_le_self p np.ne'
  have hi : (n:ℝ)+1 ≤ (p:ℝ)^(k+1) := by exact_mod_cast Nat.lt_pow_succ_log_self hp.one_lt n
  change y/(p:ℝ)^k ∈ Set.Ico 1 (p:ℝ) ∧ _
  refine ⟨⟨(one_le_div pos).mpr (lo.trans (Nat.floor_le (by linarith))),
    (div_lt_iff₀ pos).mpr ?_⟩, ?_⟩
  · rw [← pow_succ']
    exact (Nat.lt_floor_add_one y).trans_le hi
  · simp [digitPhase, hp.ne_zero]

/-- Positions in a real prefix whose normalized phases all lie in the prescribed
persistent regions. The interval begins at one, the first nonzero integer scale. -/
def jointPhaseSet (b s : ℕ) (A : Finset ℕ) : Set ℝ :=
  {y | 1 ≤ y ∧ ∀ p ∈ A.filter (fun q => ¬q ∣ b), ∀ d ∈ Icc 1 s,
    digitPhase p y ∈ persistentRegion b d p (A.erase p)}

/-- Ordinary length in a prefix divided by its cutoff. -/
def prefixMass (E : Set ℝ) (N : ℕ) : ℝ := volume.real (Set.Ico 0 (N:ℝ) ∩ E) / N

private lemma prefix_finite (E : Set ℝ) (N : ℕ) : volume (Set.Ico 0 (N:ℝ) ∩ E) ≠ ⊤ :=
  measure_ne_top_of_subset Set.inter_subset_left (by simp)

private lemma mesh_mem_one {n : ℕ} {y : ℝ} (hy : y ∈ Set.Ico (n:ℝ) (n+1)) :
    ⌊y⌋₊ = n := (Nat.floor_eq_iff (by linarith [hy.1, Nat.cast_nonneg (α:=ℝ) n])).mpr hy

private lemma mesh_finite (U : Finset ℕ) : volume (meshRegion 1 U) ≠ ⊤ := by
  apply measure_biUnion_ne_top U.finite_toSet
  intro i _
  simp

private lemma prefixMass_le_share {E : Set ℝ} {P : ℕ → Prop} [DecidablePred P]
    (cover : ∀ y ∈ E, P ⌊y⌋₊) (N : ℕ) :
    prefixMass E N ≤ prefixShare P N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  let U := (range N).filter P
  have sub : Set.Ico 0 (N:ℝ) ∩ E ⊆ meshRegion 1 U := by
    intro y hy
    refine Set.mem_iUnion₂.mpr ⟨⌊y⌋₊,mem_filter.mpr
      ⟨mem_range.mpr ((Nat.floor_lt hy.1.1).mpr hy.1.2),cover _ hy.2⟩,?_⟩
    simpa only [Nat.cast_one,div_one] using
      (show y ∈ Set.Ico (⌊y⌋₊:ℝ) (⌊y⌋₊+1) from ⟨Nat.floor_le hy.1.1,Nat.lt_floor_add_one _⟩)
  simpa [U,mesh_mass (q:=1) (by decide)] using measureReal_mono sub (mesh_finite U)

private lemma share_le_prefixMass {E : Set ℝ} {P : ℕ → Prop} [DecidablePred P]
    (cover : ∀ n, P n → Set.Ico (n:ℝ) (n+1) ⊆ E) (N : ℕ) :
    prefixShare P N ≤ prefixMass E N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  let U := (range N).filter P
  have sub : meshRegion 1 U ⊆ Set.Ico 0 (N:ℝ) ∩ E := by
    intro y hy
    obtain ⟨n,hn,lo,hi⟩ := Set.mem_iUnion₂.mp hy
    simp only [Nat.cast_one,div_one] at lo hi
    obtain ⟨rn,pn⟩ := mem_filter.mp hn
    have endpt : (n:ℝ)+1 ≤ N := by exact_mod_cast mem_range.mp rn
    exact ⟨⟨(Nat.cast_nonneg _).trans lo,hi.trans_le endpt⟩,cover n pn ⟨lo,hi⟩⟩
  simpa [U,mesh_mass (q:=1) (by decide)] using measureReal_mono sub (prefix_finite E N)

/-- The share of any one-coordinate error set is bounded uniformly over *all*
cutoffs. The factor two is the geometric sum over complete and partial scales. -/
theorem digitPhase_prefix_bound {p : ℕ} (hp : p.Prime) (Z : Set ℝ) (finite : volume Z ≠ ⊤)
    (N : ℕ) : prefixMass {y | 1 ≤ y ∧ digitPhase p y ∈ Z} N ≤ 2 * volume.real Z := by
  rcases N.eq_zero_or_pos with rfl | npos
  · simp [prefixMass,measureReal_nonneg]
  let k := Nat.log p N
  let V (j : ℕ) := (fun y : ℝ => y*((p:ℝ)^j)⁻¹) ⁻¹' Z
  have pp : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have vp (j : ℕ) : 0 < (p:ℝ)^j := by positivity
  have vm (j : ℕ) : volume (V j) = ENNReal.ofReal ((p:ℝ)^j)*volume Z := by
    dsimp only [V]
    rw [Real.volume_preimage_mul_right (inv_ne_zero (vp j).ne'),inv_inv,abs_of_pos (vp j)]
  have vfin (j : ℕ) : volume (V j) ≠ ⊤ := by rw [vm]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top finite
  have sub : Set.Ico 0 (N:ℝ) ∩ {y | 1 ≤ y ∧ digitPhase p y ∈ Z} ⊆ ⋃ j ∈ range (k+1), V j := by
    intro y hy
    have low : ⌊y⌋₊ ≤ N := ((Nat.floor_lt hy.1.1).mpr hy.1.2).le
    exact Set.mem_iUnion₂.mpr ⟨_,mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right low)),
      by simpa [V,digitPhase,div_eq_mul_inv] using hy.2.2⟩
  have bound := (measureReal_mono sub (measure_biUnion_ne_top (range (k+1)).finite_toSet (fun j _ => vfin j))).trans
    (measureReal_biUnion_finset_le (μ:=volume) (range (k+1)) V)
  have vr (j : ℕ) : volume.real (V j) = (p:ℝ)^j * volume.real Z := by
    simp [Measure.real,vm]
  simp_rw [vr] at bound
  rw [← sum_mul, geom_sum_eq pp.ne'] at bound
  have pk : (p:ℝ)^k ≤ N := by exact_mod_cast Nat.pow_log_le_self p npos.ne'
  have factor : ((p:ℝ)^(k+1)-1)/(p-1) ≤ 2*N := by
    apply (div_le_iff₀ (by linarith)).mpr
    have two : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_right pk (zero_le_one.trans pp.le),
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (sub_nonneg.mpr two)]
  change volume.real _ / (N:ℝ) ≤ _
  rw [div_le_iff₀ (Nat.cast_pos.mpr npos)]
  exact bound.trans ((mul_le_mul_of_nonneg_right factor measureReal_nonneg).trans_eq (by ring))

private def lostRegion (b d p l : ℕ) (S : Finset ℕ) :=
  failedRegion b d p l S \ persistentRegion b d p S

private lemma lost_width_zero {b d p : ℕ} {S : Finset ℕ} (hp : p.Prime) (outside : p ∉ S)
    (hd : 0 < d) (cop : b.Coprime p) :
    Tendsto (fun l => volume.real (lostRegion b d p l S)) atTop (𝓝 0) := by
  have eqn (l : ℕ) : volume.real (lostRegion b d p l S) =
      volume.real (failedRegion b d p l S) - volume.real (persistentRegion b d p S) :=
    measureReal_sdiff (Set.iInter_subset _ l)
      (MeasurableSet.iInter (fun _ => mesh_measurable ..))
      (measure_ne_top_of_subset (failed_region_inside hp.pos) (by simp))
  simp_rw [eqn]
  simpa using (region_mass_tendsto hd hp outside cop).sub_const (volume.real (persistentRegion b d p S))

private lemma prime_survival {b s p : ℕ} {S : Finset ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (odd : Odd p) (outside : p ∉ S) (cop : b.Coprime p) (l M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Ico 1 (p:ℝ), ⌊t*(p:ℝ)^(Nat.log p n)⌋₊ = n →
      (∃ d ∈ Icc 1 s, t ∉ persistentRegion b d p S) →
      (∀ d ∈ Icc 1 s, t ∉ lostRegion b d p l S) →
      M ≤ (powerShifted b s (insert p S) n).den := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨w,z,fixed,unit,factor⟩ := inverse_radix_factors cop
  obtain ⟨C,N,dominant⟩ := dominant_order_denominator (s:=s) hb cop odd outside unit fixed factor
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (p^(C+(l+1)+M+1))] with n hn large
  intro t ht cut nonempty noLoss
  let V := (Icc 1 s).filter (fun d => t ∉ persistentRegion b d p S)
  have ne : V.Nonempty := by obtain ⟨d,hd,pass⟩ := nonempty; exact ⟨d,mem_filter.mpr ⟨hd,pass⟩⟩
  let d := V.max' ne
  obtain ⟨hd,pass⟩ := mem_filter.mp (V.max'_mem ne)
  obtain ⟨dp,ds⟩ := mem_Icc.mp hd
  have survive : t ∉ failedRegion b d p l S := fun h => noLoss d hd ⟨h,pass⟩
  have red := mt (failedRegion_iff_phaseReduction_zero outside dp fixed factor cop ht l).mpr survive
  have normlarge : ((p:ℝ)⁻¹)^(l+1) ≤ ‖phaseMoment S w d t‖ := by
    apply le_of_not_gt
    intro h
    apply red
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow,
      zpow_neg, zpow_natCast, ← inv_pow]
    exact h.le
  have allzero (j : ℕ) (gt : d < j) (js : j ≤ s) : phaseMoment S w j t = 0 := by
    apply (persistent_iff_phaseMoment_zero outside (by omega) fixed factor cop ht).mp
    by_contra miss
    exact gt.not_ge (V.le_max' j (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,js⟩,miss⟩))
  have kbig := Nat.le_log_of_pow_le hp.one_lt large
  have denom := dominant hn (by omega : C+(l+1) < Nat.log p n)
    (Nat.lt_pow_succ_log_self hp.one_lt n) cut dp ds normlarge allzero
  exact (Nat.lt_pow_self hp.one_lt (n:=M)).le.trans
    ((Nat.pow_le_pow_right hp.pos (by omega : M ≤ Nat.log p n - (C+(l+1)))).trans denom)

private lemma support_off_product {A : Finset ℕ} {b p : ℕ} (mem : p ∈ A) :
    p ∣ b * ∏ q ∈ A.filter (fun r => ¬r ∣ b), q := by
  by_cases base : p ∣ b
  · exact base.trans (dvd_mul_right ..)
  · exact (dvd_prod_of_mem id (mem_filter.mpr ⟨mem,base⟩)).trans (dvd_mul_left ..)

/-- The length of the simultaneous persistent set gives a lower bound at every
sufficiently large cutoff, for arbitrary radix primes and every positive order. -/
theorem jointPhase_prefix_lower {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b) (hs : 0 < s)
    (primes : ∀ p ∈ A, p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, prefixMass (jointPhaseSet b s A) N - ε ≤
      radixDiscrepancy b (powerValue b s A) N := by
  classical
  let J := A.filter (fun r => ¬r ∣ b)
  let c := ∏ q ∈ J,q
  have cp : 0 < c := prod_pos (fun q hq => (primes q (mem_filter.mp hq).1).pos)
  have each (N : ℕ) : prefixMass (jointPhaseSet b s A) N ≤
      prefixShare (fun n => c.Coprime (powerShifted b s A n).den) N := by
    apply prefixMass_le_share
    intro y hy
    obtain ⟨one,allmem⟩ := hy
    apply Nat.Coprime.symm
    apply Nat.Coprime.prod_right
    intro p hp
    obtain ⟨mem,off⟩ := mem_filter.mp hp
    have pp := primes p mem
    let : Fact p.Prime := ⟨pp⟩
    have cop := (pp.coprime_iff_not_dvd.mpr off).symm
    obtain ⟨w,z,fixed,unit,factor⟩ := inverse_radix_factors cop
    obtain ⟨ht,cut⟩ := phase_digit pp one
    have clear := prime_cleared_of_phase_zeros (s:=s) (notMem_erase p A) fixed factor
      (Nat.lt_pow_succ_log_self pp.one_lt ⌊y⌋₊) cut (fun d hd ds =>
        (persistent_iff_phaseMoment_zero (notMem_erase p A) hd fixed factor cop ht).mp
          (allmem p hp d (mem_Icc.mpr ⟨hd,ds⟩)))
    simpa only [insert_erase mem] using clear.symm
  filter_upwards [prefix_discrepancy_lower A hb cp hs (fun _ => support_off_product) hε] with N h
  exact (sub_le_sub_right (each N) ε).trans h

private lemma prefixMass_union {ι : Type*} (E : Set ℝ) (T : Finset ι) (V : ι → Set ℝ) (N : ℕ) :
    prefixMass (E ∪ ⋃ i ∈ T,V i) N ≤ prefixMass E N + ∑ i ∈ T, prefixMass (V i) N := by
  unfold prefixMass
  simp only [Set.inter_union_distrib_left, Set.inter_iUnion]
  rw [← sum_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact (measureReal_union_le ..).trans (add_le_add_right (measureReal_biUnion_finset_le T _) _)

private theorem jointPhase_upper_odd {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b) (hs : 0 < s)
    (primes : ∀ p ∈ A, p.Prime) (odd : ∀ p ∈ A.filter (fun r => ¬r∣b), Odd p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, radixDiscrepancy b (powerValue b s A) N ≤ prefixMass (jointPhaseSet b s A) N + ε := by
  classical
  let J := A.filter (fun r => ¬r∣b)
  let T := J ×ˢ Icc 1 s
  let B := jointPhaseSet b s A
  let Z (i : ℕ × ℕ) (l : ℕ) := lostRegion b i.2 i.1 l (A.erase i.1)
  let V (l : ℕ) (i : ℕ × ℕ) := {y : ℝ | 1 ≤ y ∧ digitPhase i.1 y ∈ Z i l}
  have cop (p : ℕ) (h : p∈J) : b.Coprime p :=
    ((primes p (mem_filter.mp h).1).coprime_iff_not_dvd.mpr (mem_filter.mp h).2).symm
  have mass (i : ℕ × ℕ) (hi : i ∈ T) :
      Tendsto (fun l => 2 * volume.real (Z i l)) atTop (𝓝 0) := by
    obtain ⟨pj,ds⟩ := mem_product.mp hi
    have a := lost_width_zero (primes _ (mem_filter.mp pj).1) (notMem_erase i.1 A)
      (mem_Icc.mp ds).1 (cop _ pj)
    simpa [Z] using a.const_mul 2
  have total := tendsto_finsetSum T mass
  simp only [sum_const_zero] at total
  obtain ⟨l,small⟩ := (total.eventually_lt_const (half_pos hε)).exists
  let E := B ∪ ⋃ i ∈ T,V l i
  let bad (n : ℕ) := Set.Ico (n:ℝ) (n+1) ⊆ E
  let c := (b+1) * ∏ q ∈ J,q
  have cp : 0 < ∏ q ∈ J,q := prod_pos fun q h => (primes q (mem_filter.mp h).1).pos
  have big : 1 < c := (by omega : 1 < b+1).trans_le (Nat.le_mul_of_pos_right _ cp)
  have bc : b.Coprime c := (Nat.coprime_self_add_right.mpr b.coprime_one_right).mul_right
    (Nat.Coprime.prod_right cop)
  have support (p : ℕ) (h : p ∈ A) : p ∣ b*c := by
    have dd := support_off_product (b:=b) h
    dsimp [c]
    rw [mul_left_comm b]
    exact dd.trans (dvd_mul_left ..)
  have grow (M : ℕ) : ∀ᶠ n : ℕ in atTop, ¬bad n → M ≤ (powerShifted b s A n).den := by
    have allp := (eventually_all_finset J).mpr (fun p hp => prime_survival (s:=s) hb
      (primes _ (mem_filter.mp hp).1) (odd p hp) (notMem_erase p A) (cop p hp) l M)
    filter_upwards [allp,eventually_ge_atTop 1] with n good np notBad
    obtain ⟨y,hy,miss⟩ := Set.not_subset.mp notBad
    have one : 1 ≤ y := (by exact_mod_cast np : (1:ℝ) ≤ n).trans hy.1
    have ne : y ∉ B := fun h => miss (Or.inl h)
    obtain ⟨p,hp,d,hd,nonzero⟩ : ∃ p ∈ J, ∃ d ∈ Icc 1 s,
        digitPhase p y ∉ persistentRegion b d p (A.erase p) := by
      by_contra! all
      exact ne ⟨one, all⟩
    have pp := primes _ (mem_filter.mp hp).1
    obtain ⟨inside,cut⟩ := phase_digit pp one
    rw [mesh_mem_one hy] at cut
    have low := good p hp _ inside cut ⟨d,hd,nonzero⟩ (fun j hj lost =>
      miss (Or.inr (Set.mem_iUnion₂.mpr ⟨(p,j),mem_product.mpr ⟨hp,hj⟩,one,lost⟩)))
    simpa only [insert_erase (mem_filter.mp hp).1] using low
  filter_upwards [prefix_discrepancy_of_survival A hb big bc hs support bad grow (half_pos hε)] with N upper
  have cost (i : ℕ × ℕ) (hi : i ∈ T) : prefixMass (V l i) N ≤ 2*volume.real (Z i l) := by
    have pp := primes _ (mem_filter.mp (mem_product.mp hi).1).1
    apply digitPhase_prefix_bound pp
    apply measure_ne_top_of_subset Set.sdiff_subset
    exact measure_ne_top_of_subset (failed_region_inside pp.pos) (by simp)
  have totalCost := (prefixMass_union B T (V l) N).trans
    (add_le_add_right (sum_le_sum cost) _)
  have share := share_le_prefixMass (P:=bad) (fun _ h => h) N
  linarith only [upper,share,totalCost,small]

/-- For every positive order and finite prime support, discrepancy tracks the
normalized real length of the simultaneous persistent set along all integer cutoffs. -/
theorem discrepancy_tracks_jointPhase {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b) (hs : 0 < s)
    (primes : ∀ p ∈ A, p.Prime) :
    Tendsto (fun N => radixDiscrepancy b (powerValue b s A) N -
      prefixMass (jointPhaseSet b s A) N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let J := A.filter (fun r => ¬r∣b)
  have half := half_pos hε
  have up : ∀ᶠ N : ℕ in atTop, radixDiscrepancy b (powerValue b s A) N ≤
      prefixMass (jointPhaseSet b s A) N + ε/2 := by
    by_cases two : 2 ∈ J
    · obtain ⟨mem,off⟩ := mem_filter.mp two
      have hz := discrepancy_le_of_support_prime hb hs Nat.prime_two (notMem_erase 2 A)
        (Nat.prime_two.coprime_iff_not_dvd.mpr off).symm (fun r hr => primes r (mem_of_mem_erase hr))
      norm_num [insert_erase mem] at hz
      have large := eventually_lt_of_limsup_lt (hz.trans_lt half)
        (isBoundedUnder_of_eventually_le (.of_forall (fun N => (radix_discrepancy_bounds b _ N).2)))
      filter_upwards [large] with N h
      exact h.le.trans (le_add_of_nonneg_left (by unfold prefixMass; positivity))
    · apply jointPhase_upper_odd A hb hs primes _ half
      intro p hp
      exact Nat.odd_iff.mpr ((primes p (mem_filter.mp hp).1).eq_two_or_odd.resolve_left
        (fun eq => two (eq ▸ hp)))
  filter_upwards [up,jointPhase_prefix_lower A hb hs primes half] with N upper lower
  rw [Real.dist_eq,sub_zero,abs_lt]
  constructor <;> linarith

/-- The checker share at a fixed precision across all lower orders and all
off-radix primes. As in the single-order checker, early scales may be omitted. -/
def jointOrderShare (b s l : ℕ) (A : Finset ℕ) (N : ℕ) : ℝ := by
  classical
  exact prefixShare (fun n => ∀ p ∈ A.filter (fun q => ¬q∣b), ∀ d ∈ Icc 1 s,
    CellProfile.coordinate p (p^l) n ∈ failedCells b d p l (A.erase p)) N

private lemma mesh_digit_iff {b d p l n : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (large : p^l ≤ n) {y : ℝ} (hy : y ∈ Set.Ico (n:ℝ) (n+1)) :
    digitPhase p y ∈ failedRegion b d p l S ↔
      CellProfile.coordinate p (p^l) n ∈ failedCells b d p l S := by
  let k := Nat.log p n
  have lk : l ≤ k := Nat.le_log_of_pow_le hp.one_lt large
  let u := n / p^(k-l)
  have coord : CellProfile.coordinate p (p^l) n = u := by simp [CellProfile.coordinate,Nat.log_div_base_pow,k,u]
  let q := (p:ℝ)^l
  have qp : 0 < q := pow_pos (by exact_mod_cast hp.pos) _
  let t := digitPhase p y
  have tn : 0 ≤ t*q := by
    have yn := (Nat.cast_nonneg (α:=ℝ) n).trans hy.1
    dsimp [t,digitPhase,q]; positivity
  have floor : ⌊t*q⌋₊ = u := by
    dsimp only [t,digitPhase,q,u]
    rw [mesh_mem_one hy]
    have pw : (p:ℝ)^k = (p:ℝ)^l * (p:ℝ)^(k-l) := by rw [← pow_add]; congr 1; omega
    change ⌊y/(p:ℝ)^k * (p:ℝ)^l⌋₊ = _
    have hfloor := Nat.floor_div_natCast y (p^(k-l))
    rw [Nat.cast_pow, mesh_mem_one hy] at hfloor
    rw [← hfloor,pw]
    congr 1
    field_simp [hp.ne_zero]
  rw [coord]
  constructor
  · intro h
    obtain ⟨v,hv,lo,hi⟩ := Set.mem_iUnion₂.mp h
    push_cast at lo hi
    have eq : ⌊t*q⌋₊ = v := (Nat.floor_eq_iff tn).mpr ⟨(div_le_iff₀ qp).mp lo,(lt_div_iff₀ qp).mp hi⟩
    rwa [← floor,eq]
  · intro h
    refine Set.mem_iUnion₂.mpr ⟨u,h,?_,?_⟩ <;> push_cast
    · exact (div_le_iff₀ qp).mpr (floor ▸ Nat.floor_le tn)
    · exact (lt_div_iff₀ qp).mpr (floor ▸ Nat.lt_floor_add_one _)

private lemma prefixMass_union_le (E F : Set ℝ) (N : ℕ) :
    prefixMass (E ∪ F) N ≤ prefixMass E N + prefixMass F N := by
  unfold prefixMass
  rw [Set.inter_union_distrib_left,← add_div]
  exact div_le_div_of_nonneg_right (measureReal_union_le ..) (Nat.cast_nonneg N)

private lemma prefixMass_compare {E F : Set ℝ} (K N : ℕ)
    (h : ∀ y : ℝ, (K:ℝ) ≤ y → y ∈ E → y ∈ F) :
    prefixMass E N ≤ prefixMass F N + K/N := by
  let I := Set.Ico (0:ℝ) (K:ℝ)
  have cover : Set.Ico 0 (N:ℝ) ∩ E ⊆ Set.Ico 0 (N:ℝ) ∩ (F ∪ I) := by
    intro y hy
    by_cases early : y < K
    · exact ⟨hy.1,Or.inr ⟨hy.1.1,early⟩⟩
    · exact ⟨hy.1,Or.inl (h y (le_of_not_gt early) hy.2)⟩
  have small : prefixMass I N ≤ K/N := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    simpa [I] using measureReal_mono (μ:=volume) (s₁:=Set.Ico 0 (N:ℝ) ∩ I) Set.inter_subset_right
      (show volume I ≠ ⊤ by simp [I])
  exact (div_le_div_of_nonneg_right (measureReal_mono cover (prefix_finite _ N)) (Nat.cast_nonneg N)).trans
    ((prefixMass_union_le F I N).trans (add_le_add_right small _))

/-- Taking the limsup over *all* integer cutoffs and then refining the checker
recovers the exact asymptotic discrepancy, simultaneously at every order. -/
theorem jointOrder_density_tendsTo_discrepancy {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b)
    (hs : 0 < s) (primes : ∀ p ∈ A, p.Prime) :
    Tendsto (fun l => limsup (jointOrderShare b s l A) atTop) atTop
      (𝓝 (limsup (radixDiscrepancy b (powerValue b s A)) atTop)) := by
  classical
  let J := A.filter (fun r => ¬r∣b)
  let T := J ×ˢ Icc 1 s
  let B := jointPhaseSet b s A
  let D := radixDiscrepancy b (powerValue b s A)
  let P (l n : ℕ) := ∀ p ∈ J, ∀ d ∈ Icc 1 s,
    CellProfile.coordinate p (p^l) n ∈ failedCells b d p l (A.erase p)
  let F (l : ℕ) := {y : ℝ | P l ⌊y⌋₊}
  let Z (i : ℕ × ℕ) (l : ℕ) := lostRegion b i.2 i.1 l (A.erase i.1)
  let V (l : ℕ) (i : ℕ × ℕ) := {y : ℝ | 1 ≤ y ∧ digitPhase i.1 y ∈ Z i l}
  have exactShare (l N : ℕ) : prefixMass (F l) N = jointOrderShare b s l A N := by
    change _ = prefixShare (P l) N
    apply le_antisymm (prefixMass_le_share (fun _ h => h) N)
    apply share_le_prefixMass
    intro n h y hy
    change P l ⌊y⌋₊
    rwa [mesh_mem_one hy]
  have bounds (l N : ℕ) : 0 ≤ jointOrderShare b s l A N ∧ jointOrderShare b s l A N ≤ 1 := by
    change 0 ≤ (((range N).filter (P l)).card:ℝ)/N ∧ _ ≤ 1
    refine ⟨by positivity,?_⟩
    rcases N.eq_zero_or_pos with rfl|pos
    · simp [jointOrderShare,prefixShare]
    · change (((range N).filter (P l)).card:ℝ)/N ≤ 1
      apply (div_le_one (Nat.cast_pos.mpr pos)).mpr
      exact_mod_cast (card_filter_le ..).trans_eq (card_range N)
  have mass (i : ℕ × ℕ) (hi : i ∈ T) : Tendsto (fun l => 2*volume.real (Z i l)) atTop (𝓝 0) := by
    obtain ⟨pj,ds⟩ := mem_product.mp hi
    have pp := primes _ (mem_filter.mp pj).1
    have cop := (pp.coprime_iff_not_dvd.mpr (mem_filter.mp pj).2).symm
    simpa [Z] using (lost_width_zero pp (notMem_erase i.1 A) (mem_Icc.mp ds).1 cop).const_mul 2
  have total := tendsto_finsetSum T mass
  simp only [sum_const_zero] at total
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ep : 0 < ε/5 := by positivity
  filter_upwards [total.eventually_lt_const ep] with l small
  let K := J.sup (fun p => p^l) + 1
  have correspond (y : ℝ) (large : (K:ℝ) ≤ y) :
      y ∈ F l ↔ ∀ p ∈ J, ∀ d ∈ Icc 1 s, digitPhase p y ∈ failedRegion b d p l (A.erase p) := by
    have nbig : K ≤ ⌊y⌋₊ := Nat.le_floor large
    have yn : 0 ≤ y := (Nat.cast_nonneg K).trans large
    have hy : y ∈ Set.Ico (⌊y⌋₊:ℝ) (⌊y⌋₊+1) := ⟨Nat.floor_le yn,Nat.lt_floor_add_one _⟩
    have eq (p : ℕ) (hp : p ∈ J) (d : ℕ) := mesh_digit_iff (b:=b) (d:=d)
      (primes _ (mem_filter.mp hp).1) (A.erase p)
      ((J.le_sup (f:=fun p => p^l) hp).trans ((Nat.le_succ _).trans nbig)) hy
    exact forall₂_congr fun p hp => forall₂_congr fun d _ => (eq p hp d).symm
  let avg := jointOrderShare b s l A
  have fk (N : ℕ) : prefixMass B N ≤ avg N + K/N := by
    change prefixMass B N ≤ jointOrderShare b s l A N + _
    rw [← exactShare]
    apply prefixMass_compare
    intro y hy mem
    exact (correspond y hy).mpr fun p hp d hd =>
      Set.iInter_subset (failedRegion b d p · (A.erase p)) l (mem.2 p hp d hd)
  have bk (N : ℕ) : avg N ≤ prefixMass B N + ε/5 + K/N := by
    change jointOrderShare b s l A N ≤ _
    rw [← exactShare]
    have early := prefixMass_compare (E:=F l) (F:=B ∪ ⋃ i ∈ T, V l i) K N (by
      intro y hy mem
      by_cases yes : y ∈ B
      · exact Or.inl yes
      · have one : 1 ≤ y := (by exact_mod_cast (Nat.succ_pos _ : 1 ≤ K) : (1:ℝ) ≤ K).trans hy
        obtain ⟨p,hp,d,hd,out⟩ : ∃ p∈J, ∃ d∈Icc 1 s, digitPhase p y ∉ persistentRegion b d p (A.erase p) := by
          by_contra! all
          exact yes ⟨one,all⟩
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨(p,d),mem_product.mpr ⟨hp,hd⟩,one,(correspond y hy).mp mem p hp d hd,out⟩))
    have cost := sum_le_sum (s:=T) (f:=fun i => prefixMass (V l i) N) (g:=fun i => 2*volume.real (Z i l)) (by
      intro i hi
      have pp := primes _ (mem_filter.mp (mem_product.mp hi).1).1
      apply digitPhase_prefix_bound pp
      exact measure_ne_top_of_subset (Set.sdiff_subset.trans (failed_region_inside pp.pos)) (by simp))
    linarith only [early,prefixMass_union B T (V l) N,cost,small]
  have track := Metric.tendsto_nhds.mp (discrepancy_tracks_jointPhase A hb hs primes) _ ep
  have loss := (tendsto_const_div_atTop_nhds_zero_nat (K:ℝ)).eventually_lt_const ep
  have avUpper := eventually_lt_of_limsup_lt (lt_add_of_pos_right (limsup avg atTop) ep)
    (isBoundedUnder_of_eventually_le (.of_forall (fun n => (bounds l n).2)))
  have dUpper := eventually_lt_of_limsup_lt (lt_add_of_pos_right (limsup D atTop) ep)
    (isBoundedUnder_of_eventually_le (.of_forall (fun n => (radix_discrepancy_bounds b _ n).2)))
  have h₁ : limsup D atTop ≤ limsup avg atTop + 3*(ε/5) := by
    apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun n => (radix_discrepancy_bounds b _ n).1))
    filter_upwards [track,loss,avUpper] with n tr lo av
    change dist (D n-prefixMass B n) 0 < _ at tr
    rw [Real.dist_eq,sub_zero,abs_lt] at tr
    linarith only [tr.2,lo,av,fk n]
  have h₂ : limsup avg atTop ≤ limsup D atTop + 4*(ε/5) := by
    apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun n => (bounds l n).1))
    filter_upwards [track,loss,dUpper] with n tr lo du
    change dist (D n-prefixMass B n) 0 < _ at tr
    rw [Real.dist_eq,sub_zero,abs_lt] at tr
    linarith only [tr.1,lo,du,bk n]
  change dist (limsup avg atTop) (limsup D atTop) < ε
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end NormalityChecker.LocalizedSupport
