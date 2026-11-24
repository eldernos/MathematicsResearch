module

public import Mathlib.Dynamics.Ergodic.Conservative
public import NormalityChecker.PersistentRegion

/-! Recurrence of the common zero set, annihilation on cofactor tails, and separation
of logarithmic thresholds on finitely many geometric rays. -/
@[expose] public section
open MeasureTheory Filter Set
namespace NormalityChecker.ThresholdDifferences

/-- At each stage retain points for which both the original and the shifted event occur. -/
def intersectionCube {X : Type*} (s : Set X) : List ((X → X) × ℕ) → Set X
  | [] => s
  | (T,n)::ts => intersectionCube (s ∩ (T^[n]) ⁻¹' s) ts

/-- Finite Poincaré recurrence supplies a positive-measure common event for all
subset combinations of the chosen rotations. Each return time can be arbitrarily large. -/
theorem positive_intersection_cube {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (maps : List (X → X)) (pres : ∀ T∈maps, MeasurePreserving T μ μ)
    (s : Set X) (meas : MeasurableSet s) (pos : μ s≠0) (B : ℕ) :
    ∃ ts : List ((X → X) × ℕ), ts.map Prod.fst=maps ∧
       (∀ x∈ts,B<x.2) ∧ μ (intersectionCube s ts)≠0 := by
  induction maps generalizing s with
  | nil => exact ⟨[],rfl,by simp,pos⟩
  | cons T maps ih =>
    have hp := pres T (List.mem_cons_self ..)
    have recurs := hp.conservative.frequently_measure_inter_ne_zero meas.nullMeasurableSet pos
    obtain ⟨n,hn,common⟩ := (recurs.and_eventually (eventually_gt_atTop B)).exists
    obtain ⟨ts,eqn,times,nonzero⟩ := ih (fun f h => pres f (List.mem_cons_of_mem _ h))
      _ (meas.inter (meas.preimage ((hp.iterate n).measurable))) hn
    refine ⟨(T,n)::ts,by simp [eqn],?_,nonzero⟩
    intro x hx
    rcases List.mem_cons.mp hx with eq|h
    · simpa [eq] using common
    · exact times x h

/-- If two exponents agree after the preperiod, the matching terms cancel
at every larger q-exponent, with any other cofactor u. -/
theorem stabilized_weight {R : Type*} [Monoid R] (w : R) {q L a j : ℕ}
    (period : w^(q^(L+a))=w^(q^L)) (late : L≤j) (u : ℕ) :
    w^(q^(j+a)*u)=w^(q^j*u) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le late
  rw [show L+k+a=L+a+k by omega, pow_add q (L+a) k,pow_add q L k]
  simp only [pow_mul,period]

private theorem lattice_gap (c t : ℝ) (pos : 0<t) :
    ∃ e : ℝ, 0<e ∧ ∀ z : ℤ, |c+z*t|<e → c+z*t=0 := by
  let k := ⌊-c/t⌋
  have low := (le_div_iff₀ pos).mp (Int.floor_le (-c/t))
  have high := (div_lt_iff₀ pos).mp (Int.lt_floor_add_one (-c/t))
  change (k:ℝ)*t≤-c at low
  change -c<((k:ℝ)+1)*t at high
  by_cases hit : c+k*t=0
  · refine ⟨t,pos,fun z small => ?_⟩
    obtain ⟨l,u⟩ := abs_lt.mp small
    rcases lt_trichotomy z k with h|h|h
    · have hz : (z:ℝ)+1≤k := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_right hz pos.le]
    · simpa [h] using hit
    · have hz : (k:ℝ)+1≤z := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_right hz pos.le]
  · have neg : c+k*t<0 := lt_of_le_of_ne (by linarith) hit
    let e := min (-(c+k*t)) (c+(k+1)*t)
    refine ⟨e,lt_min (by linarith) (by linarith),fun z small => ?_⟩
    obtain ⟨l,u⟩ := abs_lt.mp small
    by_cases h : z≤k
    · have hz : (z:ℝ)≤k := by exact_mod_cast h
      linarith [mul_le_mul_of_nonneg_right hz pos.le,min_le_left (-(c+k*t)) (c+(k+1)*t)]
    · have hz : (k:ℝ)+1≤z := by exact_mod_cast (show k+1≤z by omega)
      nlinarith [mul_le_mul_of_nonneg_right hz pos.le,min_le_right (-(c+k*t)) (c+(k+1)*t)]

/-- A finite union of translates of a fixed real lattice has a gap around zero,
allowing zero itself. This is applied to differences of log thresholds in nearby rows. -/
theorem finite_ray_gap (C : Finset ℝ) {t : ℝ} (pos : 0<t) :
    ∃ e : ℝ, 0<e ∧ ∀ c∈C, ∀ z : ℤ, |c+z*t|<e → c+z*t=0 := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | insert c C _ ih =>
    obtain ⟨a,ap,one⟩ := lattice_gap c t pos
    obtain ⟨b,bp,prior⟩ := ih
    refine ⟨min a b,lt_min ap bp,?_⟩
    intro d hd z small
    rcases Finset.mem_insert.mp hd with eq|h
    · exact eq ▸ one z (eq ▸ small.trans_le (min_le_left ..))
    · exact prior d h z (small.trans_le (min_le_right ..))

end NormalityChecker.ThresholdDifferences
