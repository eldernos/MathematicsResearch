module

public import NormalityChecker.HigherOrderPrefix
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Instances.AddCircle.Defs

/-! Compact normalized cutoff phases and their ordinary-length score. -/
@[expose] public section
noncomputable section
open Filter Finset MeasureTheory
open scoped Topology
namespace NormalityChecker.LocalizedSupport

/-- All real dilates of a normalized region by integer powers of `p`. -/
def periodized (p : ℕ) (Z : Set ℝ) : Set ℝ := ⋃ j : ℤ, (fun x : ℝ => x*(p:ℝ)^j) ⁻¹' Z

private lemma periodized_shift {p : ℕ} (hp : p.Prime) (Z : Set ℝ) (x : ℝ) (k : ℤ) :
    x*(p:ℝ)^k ∈ periodized p Z ↔ x ∈ periodized p Z := by
  have pp : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  simp only [periodized,Set.mem_iUnion,Set.mem_preimage,mul_assoc,← zpow_add₀ pp]
  constructor
  · rintro ⟨j,h⟩; exact ⟨k+j,h⟩
  · rintro ⟨j,h⟩; exact ⟨j-k,by rwa [add_sub_cancel]⟩

private lemma periodized_on_scale {p : ℕ} (hp : p.Prime) {Z : Set ℝ} (inside : Z ⊆ Set.Ico (1:ℝ) (p:ℝ))
    {t : ℝ} (ht : t ∈ Set.Ico (1:ℝ) (p:ℝ)) : t ∈ periodized p Z ↔ t ∈ Z := by
  have pp : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have pos : (0:ℝ) < p := zero_lt_one.trans pp
  constructor
  · intro h
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
    change t*(p:ℝ)^j ∈ Z at hj
    suffices j = 0 by simpa [this] using hj
    obtain ⟨lo,hi⟩ := inside hj
    by_contra hj0
    rcases lt_or_gt_of_ne hj0 with neg|gt
    · have pow : (p:ℝ)^j ≤ (p:ℝ)⁻¹ := by
        rw [← zpow_neg_one]
        exact zpow_le_zpow_right₀ pp.le (by omega)
      have sm := mul_le_mul_of_nonneg_left pow (zero_le_one.trans ht.1)
      rw [← div_eq_mul_inv] at sm
      exact lo.not_gt (sm.trans_lt ((div_lt_one pos).mpr ht.2))
    · have pow : (p:ℝ) ≤ (p:ℝ)^j := by
        calc _ = (p:ℝ)^(1:ℤ) := (zpow_one _).symm
             _ ≤ _ := zpow_le_zpow_right₀ pp.le (by omega)
      exact hi.not_ge (pow.trans (le_mul_of_one_le_left (zpow_pos pos _).le ht.1))
  · intro h; exact Set.mem_iUnion.mpr ⟨0,by simpa using h⟩

/-- Product of the normalized scale intervals, indexed by the off-radix support. -/
abbrev CutoffPhaseBox (b : ℕ) (A : Finset ℕ) :=
  (i : ↥(A.filter (fun p => ¬p∣b))) → Set.Icc (1:ℝ) (i.val:ℝ)

/-- Joint persistent phase region at one prime, periodized in the positive real coordinate. -/
def phaseLifts (b s p : ℕ) (A : Finset ℕ) : Set ℝ :=
  periodized p (Set.Ico (1:ℝ) p ∩ ⋂ d ∈ Icc 1 s, persistentRegion b d p (A.erase p))

private lemma phaseLifts_measurable (b s p : ℕ) (A : Finset ℕ) : MeasurableSet (phaseLifts b s p A) := by
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.preimage _ (measurable_id.mul_const _)
  apply measurableSet_Ico.inter
  exact MeasurableSet.iInter fun d => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => mesh_measurable ..

def phaseScoreSet {b : ℕ} {A : Finset ℕ} (s : ℕ) (T : CutoffPhaseBox b A) : Set ℝ :=
  {u | u ∈ Set.Ico (0:ℝ) 1 ∧ ∀ i, u*(T i).val ∈ phaseLifts b s i.val A}

/-- The ordinary-length compact score. A real unit interval supplies all past scales. -/
def compactPhaseScore {b : ℕ} {A : Finset ℕ} (s : ℕ) (T : CutoffPhaseBox b A) : ℝ :=
  volume.real (phaseScoreSet s T)

/-- The normalized coordinates of the integer cutoff. Zero uses the first positive cutoff. -/
def cutoffPhase {b : ℕ} {A : Finset ℕ} (primes : ∀ p ∈ A, p.Prime) (N : ℕ) : CutoffPhaseBox b A :=
  fun i => ⟨digitPhase i.val (max N 1 : ℕ), (Set.Ico_subset_Icc_self
    (phase_digit (primes i (mem_filter.mp i.prop).1) (by exact_mod_cast le_max_right N 1)).1)⟩

private lemma phaseLifts_iff {p b s : ℕ} (hp : p.Prime) (A : Finset ℕ) {y : ℝ} (hy : 1 ≤ y) :
    y ∈ phaseLifts b s p A ↔ ∀ d ∈ Icc 1 s, digitPhase p y ∈ persistentRegion b d p (A.erase p) := by
  have ht := (phase_digit hp hy).1
  let Z := Set.Ico (1:ℝ) p ∩ ⋂ d ∈ Icc 1 s, persistentRegion b d p (A.erase p)
  have lift : y ∈ periodized p Z ↔ digitPhase p y ∈ periodized p Z := by
    convert (periodized_shift hp Z y (-(Nat.log p ⌊y⌋₊ : ℤ))).symm using 1
    simp [digitPhase,div_eq_mul_inv]
  exact lift.trans ((periodized_on_scale hp Set.inter_subset_left ht).trans
    (by simp [ht]))

/-- At an integer cutoff the compact score differs from the real-prefix share
only on the initial interval of length one. -/
theorem compactPhaseScore_cutoff {b s N : ℕ} (A : Finset ℕ) (primes : ∀ p ∈ A,p.Prime) (pos : 0 < N) :
    0 ≤ compactPhaseScore s (cutoffPhase (b:=b) primes N) - prefixMass (jointPhaseSet b s A) N ∧
    compactPhaseScore s (cutoffPhase (b:=b) primes N) - prefixMass (jointPhaseSet b s A) N ≤ 1/N := by
  let T := cutoffPhase (b:=b) primes N
  let F : Set ℝ := {y | ∀ p ∈ A.filter (fun q => ¬q∣b), y ∈ phaseLifts b s p A}
  let B := jointPhaseSet b s A
  have np : (0:ℝ) < N := Nat.cast_pos.mpr pos
  have eqSet : phaseScoreSet s T = (fun u : ℝ => u*N) ⁻¹' (Set.Ico 0 (N:ℝ) ∩ F) := by
    ext u
    have eqn (i : ↥(A.filter (fun q => ¬q∣b))) : u*(T i).val ∈ phaseLifts b s i.val A ↔
        u*N ∈ phaseLifts b s i.val A := by
      let k := Nat.log i.val N
      have eqv : u*(T i).val = (u*N) * (i.val:ℝ)^(-(k:ℤ)) := by
        change u * digitPhase _ (max N 1 : ℕ) = _
        rw [max_eq_left pos]
        simp [k,digitPhase,div_eq_mul_inv,mul_assoc]
      rw [eqv]
      apply periodized_shift (primes i (mem_filter.mp i.prop).1)
    change (u ∈ Set.Ico 0 1 ∧ ∀ i, _) ↔ u*N ∈ Set.Ico 0 (N:ℝ) ∧ _
    have ur : u ∈ Set.Ico 0 1 ↔ u*N ∈ Set.Ico 0 (N:ℝ) := by
      simp only [Set.mem_Ico, mul_nonneg_iff_of_pos_right np]
      exact and_congr_right fun _ => (by constructor <;> intro h <;> nlinarith)
    rw [ur]
    apply and_congr_right
    intro _
    exact (forall_congr' eqn).trans (by simp [F])
  have value : compactPhaseScore s T = prefixMass F N := by
    unfold compactPhaseScore prefixMass Measure.real
    rw [eqSet,Real.volume_preimage_mul_right np.ne',ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr np),div_eq_mul_inv,mul_comm]
  have agree {y : ℝ} (hy : 1 ≤ y) : y ∈ F ↔ y ∈ B := by
    change (∀ p ∈ _, _) ↔ (1 ≤ y ∧ _)
    rw [and_iff_right hy]
    exact forall₂_congr fun p hp => phaseLifts_iff (primes p (mem_filter.mp hp).1) A hy
  have lower : prefixMass B N ≤ prefixMass F N := by
    apply div_le_div_of_nonneg_right _ np.le
    apply measureReal_mono _ (prefix_finite _ _)
    intro y hy; exact ⟨hy.1,(agree hy.2.1).mpr hy.2⟩
  have upper := prefixMass_compare (E:=F) (F:=B) 1 N (by simpa using fun y h => (agree (y:=y) h).mp)
  change 0 ≤ compactPhaseScore s T - prefixMass B N ∧ _
  rw [value]
  push_cast at upper
  constructor <;> linarith

private def crossing (V : Set ℝ) (a b : ℝ) : Set ℝ :=
  {u | u ∈ Set.Ico (0:ℝ) 1 ∧ u*a ∈ V ∧ u*b ∉ V}

/-- Dilation of a finite measurable set varies continuously in measure on the
unit interval. Compact inner and open outer approximations handle rough boundaries. -/
private lemma crossing_small (V : Set ℝ) (meas : MeasurableSet V) (finite : volume V ≠ ⊤)
    {ε : ℝ} (pos : 0 < ε) : ∃ δ > 0, ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → dist a b < δ →
      volume.real (crossing V a b) < ε := by
  let η := ENNReal.ofReal (ε/2)
  have η0 : η ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos pos)).ne'
  obtain ⟨K,KV,compact,inner⟩ := meas.exists_isCompact_sdiff_lt finite η0
  obtain ⟨U,VU,openU,finiteU,outer⟩ := meas.exists_isOpen_sdiff_lt finite η0
  obtain ⟨δ,dp,neighborhood⟩ := compact.exists_thickening_subset_open openU (KV.trans VU)
  refine ⟨δ,dp,fun a b ha hb close => ?_⟩
  let E := (fun u : ℝ => u*a) ⁻¹' (V \ K)
  let F := (fun u : ℝ => u*b) ⁻¹' (U \ V)
  have sub : crossing V a b ⊆ E ∪ F := by
    rintro u ⟨ur,ua,ub⟩
    by_cases inside : u*a ∈ K
    · have near : dist (u*b) (u*a) < δ := by
        rw [dist_comm,Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg ur.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) ur.2.le).trans_lt close
      exact Or.inr ⟨neighborhood (Metric.mem_thickening_iff.mpr ⟨_,inside,near⟩),ub⟩
    · exact Or.inl ⟨ua,inside⟩
  have scale (W : Set ℝ) {x : ℝ} (hx : 1 ≤ x) (sm : volume W < η) :
      volume ((fun u : ℝ => u*x) ⁻¹' W) < η := by
    have xp : 0<x := zero_lt_one.trans_le hx
    rw [Real.volume_preimage_mul_right xp.ne',abs_of_pos (inv_pos.mpr xp)]
    apply lt_of_le_of_lt _ sm
    exact mul_le_of_le_one_left' (ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ hx))
  have leE := scale _ ha inner
  have leF := scale _ hb outer
  have realLt {W : Set ℝ} (h : volume W < η) : volume.real W < ε/2 := by
    simpa [η,Measure.real,ENNReal.toReal_ofReal (half_pos pos).le] using
      (ENNReal.toReal_lt_toReal (h.trans_le le_top).ne ENNReal.ofReal_ne_top).mpr h
  have le := (measureReal_mono sub (measure_union_ne_top ((leE.trans_le le_top).ne)
    ((leF.trans_le le_top).ne))).trans (measureReal_union_le E F)
  exact le.trans_lt (by linarith only [realLt leE,realLt leF])

private lemma score_le_crossings {b s : ℕ} {A : Finset ℕ} (T U : CutoffPhaseBox b A)
    (V : (i : ↥(A.filter (fun p => ¬p∣b))) → Set ℝ)
    (clip : ∀ i u (a : Set.Icc (1:ℝ) (i.val:ℝ)), u ∈ Set.Ico (0:ℝ) 1 →
      (u*a.val ∈ V i ↔ u*a.val ∈ phaseLifts b s i.val A)) :
    compactPhaseScore s T ≤ compactPhaseScore s U +
      ∑ i, volume.real (crossing (V i) (T i).val (U i).val) := by
  classical
  let E i := crossing (V i) (T i).val (U i).val
  have cover : phaseScoreSet s T ⊆ phaseScoreSet s U ∪ ⋃ i,E i := by
    rintro u ⟨ur,all⟩
    by_cases ok : ∀ i, u*(U i).val ∈ phaseLifts b s i.val A
    · exact Or.inl ⟨ur,ok⟩
    · obtain ⟨i,miss⟩ := not_forall.mp ok
      exact Or.inr (Set.mem_iUnion.mpr ⟨i,ur,(clip i u _ ur).mpr (all i),
        (fun h => miss ((clip i u _ ur).mp h))⟩)
  have bounded : phaseScoreSet s U ∪ ⋃ i,E i ⊆ Set.Ico (0:ℝ) 1 := by
    intro x hx; rcases hx with h|h
    · exact h.1
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h; exact hi.1
  have h := (measureReal_mono (μ:=volume) cover (measure_ne_top_of_subset bounded (by simp))).trans
    (measureReal_union_le ..)
  exact h.trans (add_le_add_right (measureReal_iUnion_fintype_le E) _)

/-- The score is continuous on the whole compact phase box for arbitrary
persistent regions, including regions with boundaries of positive measure. -/
theorem continuous_compactPhaseScore {b s : ℕ} {A : Finset ℕ} :
    Continuous (compactPhaseScore (b:=b) (A:=A) s) := by
  classical
  let J := A.filter (fun p => ¬p∣b)
  let V (i : ↥J) := Set.Icc (0:ℝ) (i.val:ℝ) ∩ phaseLifts b s i.val A
  have clip (i : ↥J) (u : ℝ) (a : Set.Icc (1:ℝ) (i.val:ℝ)) (ur : u ∈ Set.Ico (0:ℝ) 1) :
      u*a.val ∈ V i ↔ u*a.val ∈ phaseLifts b s i.val A := by
    have ap : 0 ≤ a.val := zero_le_one.trans a.prop.1
    have lo := mul_nonneg ur.1 ap
    have hi := (mul_le_of_le_one_left ap ur.2.le).trans a.prop.2
    exact and_iff_right ⟨lo,hi⟩
  rw [continuous_iff_continuousAt]
  intro T
  rw [ContinuousAt,Metric.tendsto_nhds]
  intro ε hε
  let η := ε/(J.card+1)
  have pos : 0<η := by dsimp [η]; positivity
  choose δ dp bounds using fun i : ↥J => crossing_small (V i)
    (measurableSet_Icc.inter (phaseLifts_measurable ..))
    (measure_ne_top_of_subset Set.inter_subset_left (by simp)) pos
  have near (i : ↥J) : ∀ᶠ U in 𝓝 T, dist ((U i).val : ℝ) (T i).val < δ i :=
    (continuous_subtype_val.comp (continuous_apply i)).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds _ (dp i))
  filter_upwards [(eventually_all.mpr near)] with U small
  have up (x y : CutoffPhaseBox b A) (nearby : ∀ i, dist (x i).val (y i).val < δ i) :
      compactPhaseScore s x ≤ compactPhaseScore s y + J.card * η := by
    apply (score_le_crossings x y V (clip:=clip)).trans
    apply add_le_add_right
    simpa using (sum_le_sum (s:=univ) (fun i _ =>
      (bounds i (x i).val (y i).val (x i).prop.1 (y i).prop.1 (nearby i)).le))
  have budget : J.card*η < ε := by
    dsimp [η]; rw [← mul_div_assoc,div_lt_iff₀ (by positivity)]; linarith
  have hi := up U T small
  have lo := up T U (fun i => by rw [dist_comm]; exact small i)
  rw [Real.dist_eq,abs_lt]; constructor <;> linarith

/-- At every integer cutoff, discrepancy tracks the score at its actual phase. -/
theorem discrepancy_tracks_compactPhaseScore {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b) (hs : 0 < s)
    (primes : ∀ p ∈ A,p.Prime) :
    Tendsto (fun N => radixDiscrepancy b (powerValue b s A) N -
      compactPhaseScore s (cutoffPhase (b:=b) primes N)) atTop (𝓝 0) := by
  have err : Tendsto (fun N => compactPhaseScore s (cutoffPhase (b:=b) primes N) -
        prefixMass (jointPhaseSet b s A) N) atTop (𝓝 0) :=
    squeeze_zero' ((eventually_gt_atTop 0).mono fun _ hn => (compactPhaseScore_cutoff A primes hn).1)
      ((eventually_gt_atTop 0).mono fun _ hn => (compactPhaseScore_cutoff A primes hn).2)
      (tendsto_const_div_atTop_nhds_zero_nat 1)
  simpa only [sub_sub_sub_cancel_right,sub_zero] using (discrepancy_tracks_jointPhase A hb hs primes).sub err

/-- The ordinary limsup is attained at a compact accumulation phase of the integer
cutoffs. Endpoint representatives 1 and p give the same periodic phase. -/
theorem discrepancy_eq_attainable_max {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b) (hs : 0 < s)
    (primes : ∀ p ∈ A,p.Prime) :
    IsGreatest (compactPhaseScore s '' {T | MapClusterPt T atTop (cutoffPhase (b:=b) primes)})
      (limsup (radixDiscrepancy b (powerValue b s A)) atTop) := by
  let D := radixDiscrepancy b (powerValue b s A)
  let T := cutoffPhase (b:=b) primes
  let Q := compactPhaseScore (b:=b) (A:=A) s
  have upper := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall (fun n => (radix_discrepancy_bounds b (powerValue b s A) n).2))
  have lower := isCoboundedUnder_le_of_le atTop (fun n => (radix_discrepancy_bounds b (powerValue b s A) n).1)
  have track := discrepancy_tracks_compactPhaseScore A hb hs primes
  have lift {φ : ℕ → ℕ} (mono : StrictMono φ) {t : CutoffPhaseBox b A}
      (lim : Tendsto (T ∘ φ) atTop (𝓝 t)) : Tendsto (D ∘ φ) atTop (𝓝 (Q t)) := by
    have h₁ := track.comp mono.tendsto_atTop
    have h₂ := (continuous_compactPhaseScore (s:=s)).continuousAt.tendsto.comp lim
    simpa [Function.comp_def,D,Q,T] using h₁.add h₂
  constructor
  · obtain ⟨φ,mono,lim⟩ := (MapClusterPt.limsup lower upper).tendsto_subseq
    obtain ⟨t,ψ,inc,tl⟩ := CompactSpace.tendsto_subseq (T ∘ φ)
    have m := mono.comp inc
    have pt : MapClusterPt t atTop T := tl.mapClusterPt.of_comp m.tendsto_atTop
    exact ⟨t,pt,tendsto_nhds_unique (lift m tl) (lim.comp inc.tendsto_atTop)⟩
  · rintro _ ⟨t,pt,rfl⟩
    obtain ⟨φ,m,tl⟩ := pt.tendsto_subseq
    exact ((lift m tl).mapClusterPt.of_comp m.tendsto_atTop).le_limsup upper

/-- Torus of logarithmic phases, with one coordinate per off-radix prime. -/
abbrev LogPhaseTorus (b : ℕ) (A : Finset ℕ) :=
  (i : ↥(A.filter (fun p => ¬p∣b))) → AddCircle (1:ℝ)

/-- The real flow with coordinate velocities `1 / log p`. -/
def logPhaseFlow (b : ℕ) (A : Finset ℕ) : ℝ →+ LogPhaseTorus b A where
  toFun t i := ((t / Real.log (i.val:ℝ) : ℝ) : AddCircle (1:ℝ))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [add_div]

/-- Logarithmic angle of each representative in the compact phase box. -/
def phaseAngles {b : ℕ} {A : Finset ℕ} (T : CutoffPhaseBox b A) : LogPhaseTorus b A :=
  fun i => ((Real.log (T i).val / Real.log (i.val:ℝ) : ℝ) : AddCircle (1:ℝ))

private lemma continuous_phaseAngles {b : ℕ} {A : Finset ℕ} : Continuous (phaseAngles (b:=b) (A:=A)) := by
  apply continuous_pi
  intro i; apply (AddCircle.continuous_mk' (1:ℝ)).comp
  apply Continuous.div_const
  exact (continuous_subtype_val.comp (continuous_apply i)).log
    (fun T => (zero_lt_one.trans_le (T i).prop.1).ne')

private lemma cutoff_angles {b : ℕ} {A : Finset ℕ} (primes : ∀ p ∈ A,p.Prime) (N : ℕ) :
    phaseAngles (cutoffPhase (b:=b) primes N) = logPhaseFlow b A (Real.log ((max N 1:ℕ):ℝ)) := by
  funext i
  let n := max N 1
  have pp : (1:ℝ) < i.val := by exact_mod_cast (primes i (mem_filter.mp i.prop).1).one_lt
  have pos : (0:ℝ)<n := by exact_mod_cast (by dsimp [n]; omega : 0<n)
  have lp := (Real.log_pos pp).ne'
  let k := Nat.log i.val n
  change ((Real.log (digitPhase i.val (n:ℝ)) / Real.log (i.val:ℝ) : ℝ) : AddCircle (1:ℝ)) = _
  rw [digitPhase,Nat.floor_natCast,Real.log_div pos.ne' (pow_ne_zero _ (zero_lt_one.trans pp).ne'),
    Real.log_pow,sub_div,mul_div_cancel_right₀ _ lp, AddCircle.coe_sub]
  have zero : (((k:ℕ):ℝ) : AddCircle (1:ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).mpr ⟨(k:ℤ),by simp⟩
  change _ - (((k:ℕ):ℝ) : AddCircle (1:ℝ)) = _
  rw [zero,sub_zero]; rfl

/-- For any continuous real flow on a first-countable compact abelian group,
the integer logarithms sample the entire orbit closure arbitrarily late. -/
theorem log_nat_flow_cluster {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [FirstCountableTopology G] [IsTopologicalAddGroup G] (f : ℝ →+ G) (cont : Continuous f) :
    {x | MapClusterPt x atTop (fun n : ℕ => f (Real.log ((max n 1:ℕ):ℝ)))} =
      closure (Set.range f) := by
  let sample (n : ℕ) := f (Real.log ((max n 1:ℕ):ℝ))
  apply Set.Subset.antisymm
  · intro x hx
    apply mem_closure_iff_clusterPt.mpr
    apply hx.clusterPt.mono
    rw [le_principal_iff]
    change ∀ᶠ n : ℕ in atTop, f (Real.log ((max n 1:ℕ):ℝ)) ∈ Set.range f
    exact .of_forall fun n => ⟨_,rfl⟩
  · apply closure_minimal _ isClosed_setOfPred_clusterPt
    rintro _ ⟨t,rfl⟩
    obtain ⟨φ,mono,returns⟩ := (mapClusterPt_zero_atTop_nsmul (f 1)).tendsto_subseq
    let time (n : ℕ) := t + (φ n:ℝ)
    have tt : Tendsto time atTop atTop :=
      tendsto_atTop_add_const_left _ t ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp mono.tendsto_atTop)
    have orbit : Tendsto (fun n => f (time n)) atTop (𝓝 (f t)) := by
      have lift (n : ℕ) : f (n:ℝ) = n • f 1 := by simpa using f.map_nsmul n (1:ℝ)
      simpa [time,map_add,lift,Function.comp_def] using (tendsto_const_nhds (x:=f t)).add returns
    let ψ (n : ℕ) := ⌊Real.exp (time n)⌋₊
    have expLarge := Real.tendsto_exp_atTop.comp tt
    have ψlarge : Tendsto ψ atTop atTop := tendsto_nat_floor_atTop.comp expLarge
    have ratio := (tendsto_nat_floor_div_atTop (R:=ℝ)).comp expLarge
    have err : Tendsto (fun n => Real.log ((max (ψ n) 1 : ℕ):ℝ) - time n) atTop (𝓝 0) := by
      have h := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp ratio
      rw [Real.log_one] at h
      apply h.congr'
      filter_upwards [ψlarge.eventually_ge_atTop 1] with n hn
      change Real.log ((ψ n:ℝ)/Real.exp (time n)) = _
      rw [max_eq_left hn,Real.log_div (by exact_mod_cast (by omega : ψ n ≠ 0))
        (Real.exp_pos _).ne',Real.log_exp]
    have lift := (cont.continuousAt.tendsto.comp err).add orbit
    simp only [map_zero,zero_add] at lift
    have hsample : Tendsto (sample ∘ ψ) atTop (𝓝 (f t)) := by
      apply lift.congr
      intro n
      change f (_ - _) + f _ = f _
      rw [← map_add,sub_add_cancel]
    exact hsample.mapClusterPt.of_comp ψlarge

/-- Mapping the accumulated cutoff phases to the torus gives exactly the closed
real flow, including in dimensions where reciprocal-log independence is unknown. -/
theorem attainable_angles_eq_flow_closure {b : ℕ} (A : Finset ℕ) (primes : ∀ p ∈ A,p.Prime) :
    phaseAngles '' {T | MapClusterPt T atTop (cutoffPhase (b:=b) primes)} = closure (Set.range (logPhaseFlow b A)) := by
  let T := cutoffPhase (b:=b) primes
  let sample (n : ℕ) := logPhaseFlow b A (Real.log ((max n 1:ℕ):ℝ))
  have same : phaseAngles ∘ T = sample := funext (cutoff_angles primes)
  have cont : Continuous (logPhaseFlow b A) := continuous_pi (fun i =>
    (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_id.div_const _))
  rw [← log_nat_flow_cluster (logPhaseFlow b A) cont]
  ext x
  change (_ ↔ MapClusterPt x atTop sample)
  constructor
  · rintro ⟨t,pt,rfl⟩
    rw [← same]
    exact pt.continuousAt_comp continuous_phaseAngles.continuousAt
  · intro pt
    obtain ⟨φ,mono,hx⟩ := pt.tendsto_subseq
    obtain ⟨t,ψ,inc,ht⟩ := CompactSpace.tendsto_subseq (T ∘ φ)
    refine ⟨t,ht.mapClusterPt.of_comp (mono.comp inc).tendsto_atTop,?_⟩
    have ang := continuous_phaseAngles.continuousAt.tendsto.comp ht
    have hx' := hx.comp inc.tendsto_atTop
    rw [← same] at hx'
    exact tendsto_nhds_unique ang hx'

private lemma score_eq_of_angles {b s : ℕ} {A : Finset ℕ} (primes : ∀ p ∈ A,p.Prime)
    {T U : CutoffPhaseBox b A} (eq : phaseAngles T = phaseAngles U) :
    compactPhaseScore s T = compactPhaseScore s U := by
  suffices setEq : phaseScoreSet s T = phaseScoreSet s U by rw [compactPhaseScore,setEq]; rfl
  ext u
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  have pp := primes i (mem_filter.mp i.prop).1
  have pos : (1:ℝ) < i.val := by exact_mod_cast pp.one_lt
  have eqi := congrFun eq i
  let a := (T i).val
  let c := (U i).val
  let l := Real.log (i.val:ℝ)
  have diff : ((Real.log a/l - Real.log c/l : ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [AddCircle.coe_sub]; exact sub_eq_zero.mpr eqi
  obtain ⟨j,hj⟩ := (AddCircle.coe_eq_zero_iff _).mp diff
  have l0 : l ≠ 0 := (Real.log_pos pos).ne'
  simp only [zsmul_eq_mul,mul_one,← sub_div,eq_div_iff l0] at hj
  have cpos : 0<c := zero_lt_one.trans_le (U i).prop.1
  have scale : a = c*(i.val:ℝ)^j := by
    apply Real.log_injOn_pos (zero_lt_one.trans_le (T i).prop.1) (mul_pos cpos (zpow_pos (zero_lt_one.trans pos) _))
    rw [Real.log_mul cpos.ne' (zpow_ne_zero _ (zero_lt_one.trans pos).ne'), Real.log_zpow]
    change Real.log a = Real.log c + (j:ℝ)*l
    linarith
  change u*a ∈ phaseLifts b s i.val A ↔ u*c ∈ phaseLifts b s i.val A
  rw [scale,← mul_assoc]
  exact periodized_shift pp _ _ _

/-- Compact phase formula on the closure of the real logarithmic orbit. The
box representatives use `T = p^θ`; opposite endpoints yield the same score. -/
theorem discrepancy_eq_log_flow_max {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b) (hs : 0 < s)
    (primes : ∀ p ∈ A,p.Prime) :
    IsGreatest (compactPhaseScore s '' (phaseAngles ⁻¹' closure (Set.range (logPhaseFlow b A))))
      (limsup (radixDiscrepancy b (powerValue b s A)) atTop) := by
  have max := discrepancy_eq_attainable_max A hb hs primes
  rw [← attainable_angles_eq_flow_closure A primes]
  refine ⟨?_,?_⟩
  · obtain ⟨t,pt,eq⟩ := max.1
    exact ⟨t,⟨t,pt,rfl⟩,eq⟩
  · rintro _ ⟨t,⟨u,pt,eq⟩,rfl⟩
    rw [← score_eq_of_angles (s:=s) primes eq]
    exact max.2 ⟨u,pt,rfl⟩

end NormalityChecker.LocalizedSupport
