module

public import NormalityChecker.LogTwoTransitions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Escape from integers measured by the real part of the first circle character. -/
noncomputable def cosineEscape (v : ℝ) : ℝ := 1 - Real.cos (2 * Real.pi * v)

noncomputable def escapeAverage (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, cosineEscape (u n)) / N

private lemma escape_bounds (v : ℝ) : 0 ≤ cosineEscape v ∧ cosineEscape v ≤ 2 := by
  unfold cosineEscape
  constructor <;> linarith [Real.cos_le_one (2 * Real.pi * v), Real.neg_one_le_cos (2 * Real.pi * v)]

private lemma escape_fract (v : ℝ) : cosineEscape (Int.fract v) = cosineEscape v := by
  simp only [cosineEscape, Int.fract, mul_sub, mul_comm (2 * Real.pi) (⌊v⌋ : ℝ), Real.cos_sub_int_mul_two_pi]

private lemma escape_double (v : ℝ) :
    cosineEscape (2*v) = 4*cosineEscape v - 2*(cosineEscape v)^2 := by
  simp only [cosineEscape, show 2*Real.pi*(2*v) = 2*(2*Real.pi*v) by ring, Real.cos_two_mul]
  ring

private noncomputable def transIndicator (x : ℝ) (n : ℕ) : ℝ :=
  if 1/4 ≤ shift 2 x n ∧ shift 2 x n < 3/4 then 1 else 0

private lemma escape_step (x : ℝ) (n : ℕ) :
    let f := fun j : ℕ => cosineEscape ((2:ℝ)^j*x)
    transIndicator x n ≤ f n ∧ f n ≤ 4*transIndicator x n + (f (n+1)-f n) := by
  let y := shift 2 x n
  let v := (2:ℝ)^n*x
  have h0 : 0 ≤ y := Int.fract_nonneg v
  have h1 : y < 1 := Int.fract_lt_one v
  have hfy : cosineEscape v = cosineEscape y := (escape_fract v).symm
  have hy := escape_bounds v
  have hnext : cosineEscape ((2:ℝ)^(n+1)*x) = 4*cosineEscape v - 2*(cosineEscape v)^2 := by
    rw [show (2:ℝ)^(n+1)*x = 2*v by simp [v,pow_succ]; ring, escape_double]
  change transIndicator x n ≤ cosineEscape v ∧ cosineEscape v ≤
    4*transIndicator x n + (cosineEscape ((2:ℝ)^(n+1)*x) - cosineEscape v)
  rw [hnext]; unfold transIndicator
  change (if 1/4 ≤ y ∧ y < 3/4 then (1:ℝ) else 0) ≤ cosineEscape v ∧ _
  split_ifs with h
  · have hc := Real.cos_nonpos_of_pi_div_two_le_of_le
        (show Real.pi/2 ≤ 2*Real.pi*y by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h.1)])
        (show 2*Real.pi*y ≤ Real.pi + Real.pi/2 by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h.2.le)])
    exact ⟨by rw [hfy]; dsimp [cosineEscape]; linarith,
      by nlinarith [mul_nonneg (sub_nonneg.mpr hy.2) (by linarith [hy.1] : 0 ≤ cosineEscape v + 1)]⟩
  · have hc : 0 ≤ Real.cos (2*Real.pi*y) := by
      by_cases hl : y < 1/4
      · exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [mul_nonneg Real.pi_pos.le h0,Real.pi_pos],
            by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hl.le)]⟩
      · have hr : 3/4 ≤ y := le_of_not_gt (fun hh => h ⟨le_of_not_gt hl,hh⟩)
        rw [← Real.cos_sub_two_pi]
        exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr)],
          by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h1.le),Real.pi_pos]⟩
    have hsmall : cosineEscape v ≤ 1 := by rw [hfy]; dsimp [cosineEscape]; linarith
    exact ⟨hy.1, by nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hsmall)]⟩

/-- The endpoint term in the upper estimate is at most two before normalization. -/
theorem escapeAverage_transition_bounds (x : ℝ) (N : ℕ) :
    transitionFrequency x N ≤ escapeAverage (fun n => (2:ℝ)^n*x) N ∧
    escapeAverage (fun n => (2:ℝ)^n*x) N ≤ 2/(N:ℝ) + 4*transitionFrequency x N := by
  let f := fun n : ℕ => cosineEscape ((2:ℝ)^n*x)
  have ident : transitionFrequency x N = (∑ n ∈ range N, transIndicator x n)/N := by
    simp [transitionFrequency,frequency,transIndicator,sum_boole]
  rw [ident]; unfold escapeAverage
  constructor
  · exact div_le_div_of_nonneg_right (sum_le_sum fun n _ => (escape_step x n).1) (by positivity)
  · have H := sum_le_sum (s := range N) (fun n _ => (escape_step x n).2)
    change ∑ n ∈ range N, f n ≤ ∑ n ∈ range N, (4*transIndicator x n+(f (n+1)-f n)) at H
    rw [sum_add_distrib,← mul_sum,sum_range_sub] at H
    have H' : ∑ n ∈ range N, f n ≤ 2+4*(∑ n ∈ range N, transIndicator x n) := by
      linarith [(escape_bounds ((2:ℝ)^N*x)).2,(escape_bounds ((2:ℝ)^0*x)).1,
        show f N = cosineEscape ((2:ℝ)^N*x) from rfl, show f 0 = cosineEscape ((2:ℝ)^0*x) from rfl]
    exact (div_le_div_of_nonneg_right H' (by positivity)).trans_eq (by ring)

/-- Rational or real approximants with vanishing shift error give the same two limiting bounds. -/
theorem first_frequency_bounds (x : ℝ) (u : ℕ → ℝ)
    (hu : Tendsto (fun n => (2:ℝ)^n*x - u n) atTop (𝓝 0)) :
    transitionDensity x ≤ liminf (escapeAverage u) atTop ∧
    liminf (escapeAverage u) atTop ≤ 4*transitionDensity x := by
  let exactMean := escapeAverage (fun n => (2:ℝ)^n*x)
  have hd : Tendsto (fun N => exactMean N - escapeAverage u N) atTop (𝓝 0) := by
    have hz : Tendsto (fun n => cosineEscape ((2:ℝ)^n*x)-cosineEscape (u n)) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp only [Real.norm_eq_abs]
      apply squeeze_zero (fun _ => abs_nonneg _) _ (by simpa using hu.abs.const_mul (2*Real.pi))
      intro n
      simp only [cosineEscape, sub_sub_sub_cancel_left, abs_sub_comm (Real.cos (2*Real.pi*u n))]
      convert Real.abs_cos_sub_cos_le (2*Real.pi*((2:ℝ)^n*x)) (2*Real.pi*u n) using 1
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0<2*Real.pi)]
    simpa [exactMean,escapeAverage,sum_sub_distrib, div_eq_inv_mul,mul_sub] using hz.cesaro
  have hE (N : ℕ) : 0 ≤ escapeAverage u N ∧ escapeAverage u N ≤ 2 := by
    unfold escapeAverage
    constructor
    · exact div_nonneg (sum_nonneg fun n _ => (escape_bounds _).1) (by positivity)
    · obtain rfl | hN := Nat.eq_zero_or_pos N
      · simp
      apply (div_le_iff₀ (by positivity : (0:ℝ)<N)).mpr
      simpa [mul_comm] using (sum_le_sum (s:=range N) fun n _ => (escape_bounds (u n)).2)
  have ht (n : ℕ) : 0 ≤ transitionFrequency x n ∧ transitionFrequency x n ≤ 1 := frequency_bounds (shift 2 x) (1/4) (3/4) n
  constructor
  · simpa only [transitionDensity,one_mul] using liminf_le_mul_of_error (A:=1) hE (fun n => (ht n).1) hd
      (fun N => by have h := (escapeAverage_transition_bounds x N).1; change _ ≤ exactMean N at h; linarith)
  · have hz := (tendsto_const_div_atTop_nhds_zero_nat 2).sub hd
    rw [sub_zero] at hz
    exact liminf_le_mul_of_error ht (fun n => (hE n).1) hz
      (fun N => by have h := (escapeAverage_transition_bounds x N).2; change exactMean N ≤ _ at h; linarith)

/-- Positive lower escape of the exact logarithmic prefixes rules out maximal discrepancy. -/
theorem logTwo_discrepancy_lt_one_iff_escape : asymptoticDiscrepancy (Real.log 2) < 1 ↔
    0 < liminf (escapeAverage (fun n => (logPrefix n : ℝ))) atTop := by
  rw [discrepancy_lt_one_iff_transitions]
  obtain ⟨hl,hu⟩ := first_frequency_bounds _ _ logTwo_shift_error_tendsTo_zero
  constructor <;> intro h <;> linarith

private lemma escape_of_middle (n : ℕ) (hit : MiddleHit n) :
    3/2 ≤ cosineEscape (logPrefix n : ℝ) := by
  let y := prefixResidue n
  obtain ⟨lo,hi⟩ := hit
  change 1/3 ≤ y at lo; change y ≤ 2/3 at hi
  have cap {z : ℝ} (hz : 2*Real.pi/3 ≤ z) (hu : z ≤ Real.pi) : Real.cos z ≤ -(1/2) := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0≤2*Real.pi/3) hu hz
    rwa [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three] at hc
  have hc : Real.cos (2*Real.pi*y) ≤ -(1/2) := by
    by_cases h : 2*Real.pi*y ≤ Real.pi
    · exact cap (by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr lo)]) h
    · rw [← Real.cos_two_pi_sub]; apply cap
      · nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hi)]
      · linarith
  rw [← escape_fract]; change 3/2 ≤ 1 - Real.cos (2*Real.pi*y); linarith

/-- A lower bound for the unnormalized cosine sum along the rational recurrence. -/
theorem logTwo_escape_logarithmic : ∃ C : ℕ, ∀ N : ℕ,
    (3/2:ℝ)*(Nat.log 34 N-C : ℕ) ≤ ∑ i ∈ range N, cosineEscape (logPrefix i : ℝ) := by
  classical
  obtain ⟨C,hC⟩ := logTwo_logarithmic_count
  refine ⟨C,fun N => ?_⟩
  let hits := (range N).filter MiddleHit
  have hc : (Nat.log 34 N-C:ℕ) ≤ hits.card := (hC N).1
  calc (3/2:ℝ)*(Nat.log 34 N-C : ℕ) ≤ (3/2:ℝ)*hits.card := by exact_mod_cast (mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hc) (by norm_num : (0:ℝ)≤3/2))
       _ = ∑ _i ∈ hits, (3/2:ℝ) := by simp [mul_comm]
       _ ≤ ∑ i ∈ hits, cosineEscape (logPrefix i : ℝ) := sum_le_sum fun i hi => escape_of_middle i (mem_filter.mp hi).2
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => (escape_bounds _).1)

end NormalityChecker
