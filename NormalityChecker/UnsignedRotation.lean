module

public import NormalityChecker.UnsignedPhase
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Jacobian

/-! Passage between a failed real phase and positive Haar measure on the log circle. -/
@[expose] public section
noncomputable section
open Finset Filter MeasureTheory Set
open scoped Topology
namespace NormalityChecker.LocalizedSupport.Unsigned

variable {p : ℕ} [hp : Fact p.Prime]

instance logPrimePositive : Fact (0 < Real.log (p : ℝ)) :=
  ⟨Real.log_pos (by exact_mod_cast hp.out.one_lt)⟩

/-- A positive-measure event on which the moment vanishes, for every
representative below p, including those below the fundamental interval. -/
def PositiveZeros (S : Finset ℕ) (A : ℕ → ℤ_[p]) (s : ℕ) : Prop :=
  ∃ E : Set (AddCircle (Real.log (p:ℝ))), MeasurableSet E ∧ volume E ≠ 0 ∧
    ∀ t : ℝ, 0 < t → t < p → (Real.log t : AddCircle (Real.log (p:ℝ))) ∈ E →
      moment S A s t = 0

private lemma normalize_log {t : ℝ} (ht : 0 < t) (top : t < p) :
    let T := Real.log (p:ℝ)
    let y : ℝ := (AddCircle.equivIco T 0 (Real.log t : AddCircle T)).val
    ∃ k : ℕ, t = Real.exp y / (p:ℝ)^k := by
  intro T y
  have pp : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  have pos : 0 < T := logPrimePositive.out
  have yn : 0 ≤ y := (AddCircle.equivIco T 0 _).property.1
  have same : (y : AddCircle T) = (Real.log t : AddCircle T) := AddCircle.coe_equivIco
  obtain ⟨k,hk⟩ := QuotientAddGroup.eq_iff_sub_mem.mp same
  change k • T = y - Real.log t at hk
  rw [zsmul_eq_mul] at hk
  have kn : 0 ≤ k := by
    by_contra! neg
    have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have bound := mul_le_mul_of_nonneg_right hk' pos.le
    have below : Real.log t < T := Real.log_lt_log ht top
    linarith
  lift k to ℕ using kn with k
  push_cast at hk
  refine ⟨k,Real.log_injOn_pos ht (div_pos (Real.exp_pos _) (pow_pos pp _)) ?_⟩
  rw [Real.log_div (Real.exp_pos _).ne' (pow_ne_zero _ pp.ne'),Real.log_pow,Real.log_exp]
  change _ = y - k*T
  linarith

theorem positiveZeros_of_persistent {b s : ℕ} {S : Finset ℕ} (out : p ∉ S)
    (hs : 0 < s) {w z : ℤ_[p]} (fixed : w^p = w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p])*(1+(p:ℚ_[p])*z)) (cop : b.Coprime p)
    (pos : volume (persistentRegion b s p S) ≠ 0) :
    PositiveZeros S (fun m => w^m) s := by
  let T := Real.log (p:ℝ)
  let rep (x : AddCircle T) : ℝ := (AddCircle.equivIco T 0 x).val
  let Z := persistentRegion b s p S
  let E : Set (AddCircle T) := (fun x => Real.exp (rep x)) ⁻¹' Z
  have zmeas : MeasurableSet Z := MeasurableSet.iInter (fun _ => mesh_measurable ..)
  have emeas : MeasurableSet E := zmeas.preimage (Real.continuous_exp.measurable.comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco T 0).measurable))
  have pp : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  refine ⟨E,emeas,?_,?_⟩
  · intro null
    let H := ((↑) : ℝ → AddCircle T) ⁻¹' E ∩ Ioc 0 (0+T)
    have Hnull : volume H = 0 := (AddCircle.add_projection_respects_measure T 0 emeas).symm.trans null
    have enull := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      Real.differentiable_exp.differentiableOn Hnull
    apply pos
    apply measure_mono_null (t := Real.exp '' H ∪ ({1,(p:ℝ)} : Set ℝ)) _ (measure_union_null enull ((Set.finite_singleton (p:ℝ)).insert 1 |>.measure_zero volume))
    intro t ht
    have inside := failed_region_inside hp.out.pos (Set.iInter_subset (fun k => failedRegion b s p k S) 0 ht)
    by_cases lo : t = 1
    · simp [lo]
    by_cases hi : t = p
    · simp [hi]
    have tpos : 0 < t := zero_lt_one.trans_le inside.1
    have a := Real.log_pos (lt_of_le_of_ne inside.1 (Ne.symm lo))
    have bnd := Real.log_lt_log tpos (lt_of_le_of_ne inside.2 hi)
    have mem : Real.log t ∈ Ico 0 (0+T) := ⟨a.le,by simpa [T] using bnd⟩
    apply Or.inl
    refine ⟨Real.log t,⟨?_,a,by simpa [T] using bnd.le⟩,Real.exp_log tpos⟩
    change Real.exp ((AddCircle.equivIco T 0 (Real.log t : AddCircle T)).val) ∈ Z
    simpa [AddCircle.equivIco_coe_eq mem,Real.exp_log tpos] using ht
  · intro t ht top he
    let x := (Real.log t : AddCircle T)
    have loc := (AddCircle.equivIco T 0 x).property
    have lo : 0 ≤ rep x := loc.1
    have hi : rep x < T := by simpa [rep] using loc.2
    have inside : Real.exp (rep x) ∈ Ico 1 (p:ℝ) :=
      ⟨Real.one_le_exp lo, (Real.exp_lt_exp.mpr hi).trans_eq (Real.exp_log pp)⟩
    have zero := (persistent_iff_phaseMoment_zero out hs fixed factor cop inside).mp he
    obtain ⟨k,eqn⟩ := normalize_log ht top
    change t = Real.exp (rep x) / (p:ℝ)^k at eqn
    conv_lhs => rw [eqn, moment_scale_down _ _ hs inside.2, moment_unsigned, zero, mul_zero]

/-- Recurrence chooses a positive multiple of any prescribed stride. The shifted
representative can cross the end of the log circle. -/
theorem positiveZeros_difference {S : Finset ℕ} (out : p ∉ S) {A : ℕ → ℤ_[p]} {s q h : ℕ}
    (hs : 0 < s) (hq : q.Prime) (qS : q ∈ S) (event : PositiveZeros S A s) :
    ∃ n : ℕ, 0 < n ∧ PositiveZeros S (difference (q^(h*n)) A) s := by
  obtain ⟨E,em,ep,zeros⟩ := event
  let T := Real.log (p:ℝ)
  let shift : AddCircle T := ((-Real.log ((q:ℝ)^h) : ℝ) : AddCircle T)
  let rot (x : AddCircle T) := shift+x
  have mp : MeasurePreserving rot volume volume := measurePreserving_add_left volume shift
  obtain ⟨ts,eqn,times,pos⟩ := ThresholdDifferences.positive_intersection_cube [rot]
    (by intro f hf; simpa using (List.mem_singleton.mp hf ▸ mp : MeasurePreserving f volume volume))
    E em ep 0
  obtain ⟨⟨f,n⟩,tail,rfl⟩ := List.exists_cons_of_ne_nil (l:=ts) (by rintro rfl; simp at eqn)
  simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at eqn
  obtain ⟨rfl,rfl⟩ := eqn
  have hn := times (rot,n) (by simp)
  refine ⟨n,hn, E ∩ (rot^[n]) ⁻¹' E, em.inter (em.preimage (mp.iterate n).measurable),pos,?_⟩
  intro t ht top both
  let Q := q^(h*n)
  have qpos : (0:ℝ) < Q := by exact_mod_cast pow_pos hq.pos (h*n)
  have lower : (1:ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q from pow_pos hq.pos _)
  have mem : Q ∈ Nat.factoredNumbers S := prime_power_mem hq qS _
  have move : rot^[n] (Real.log t : AddCircle T) = (Real.log (t / Q) : AddCircle T) := by
    change (shift + ·)^[n] _ = _
    rw [add_left_iterate_apply, ← AddCircle.coe_nsmul, ← AddCircle.coe_add,
      Real.log_div ht.ne' qpos.ne']
    apply congrArg ((↑) : ℝ → AddCircle T)
    simp [Q,Real.log_pow,nsmul_eq_mul]
    ring
  rw [moment_difference out mem A hs, zeros t ht top both.1,
    zeros _ (div_pos ht qpos) ((div_le_self ht.le lower).trans_lt top) (move ▸ both.2),mul_zero,sub_zero]

end NormalityChecker.LocalizedSupport.Unsigned
