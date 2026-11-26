module

public import NormalityChecker.FirstFrequency
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section
open Finset
namespace NormalityChecker.FredholmOrbit

/-- The Fredholm lacunary series in the open unit disk. -/
noncomputable def fredholm (w : ℂ) : ℂ := ∑' n : ℕ, w ^ (2 ^ n : ℕ)

theorem summable_fredholm {w : ℂ} (h : ‖w‖ < 1) :
    Summable (fun n : ℕ => w ^ (2 ^ n : ℕ)) := by
  apply (summable_geometric_of_norm_lt_one h).comp_injective (i := fun n : ℕ => 2 ^ n)
  exact (pow_right_strictMono₀ (by norm_num : 1 < (2 : ℕ))).injective

theorem fredholm_eq {w : ℂ} (h : ‖w‖ < 1) :
    fredholm w = w + fredholm (w ^ 2) := by
  unfold fredholm
  rw [(summable_fredholm h).tsum_eq_zero_add]
  simp only [pow_zero, pow_one, pow_succ', pow_mul]

/-- The finite product identity also holds at the removable point w = 1. -/
theorem product_at_one (w : ℂ) (N : ℕ) :
    (1 - w) * ∏ n ∈ range N, (1 + w ^ (2 ^ n : ℕ)) = 1 - w ^ (2 ^ N : ℕ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prod_range_succ, ← mul_assoc, ih, pow_succ, pow_mul]
    ring

/-- The radius at the Nth binary cutoff. -/
noncomputable def radius (N : ℕ) : ℝ := Real.exp (-(1 / (2 : ℝ) ^ N))

private lemma radius_pow (N n : ℕ) :
    radius N ^ (2 ^ n : ℕ) = Real.exp (-((2 : ℝ) ^ n / 2 ^ N)) := by
  rw [radius, ← Real.exp_nat_mul]
  push_cast
  congr 1
  ring

private lemma radial_tail (j : ℕ) :
    Real.exp (-((2 : ℝ) ^ j)) ≤ (1/2 : ℝ) ^ (j+1) := by
  have hj : (j+1 : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self (n := j)
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Real.add_one_le_exp 1]
  calc
    _ ≤ Real.exp (↑(j+1 : ℕ) * (-1 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    _ = _ := Real.exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he _

/-- Replacing radial weights by a sharp cutoff incurs error at most two
for any real nonnegative observable bounded by two. -/
theorem radial_cutoff (N : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 2) :
    |(∑' n : ℕ, radius N ^ (2 ^ n : ℕ) * f n) - ∑ n ∈ range N, f n| ≤ 2 := by
  let g (n : ℕ) := radius N ^ (2 ^ n : ℕ) * f n
  have hnon (n : ℕ) : 0 ≤ g n := mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (hf n).1
  have htail (j : ℕ) : g (j+N) ≤ (1/2 : ℝ) ^ j := by
    dsimp [g]
    rw [radius_pow, pow_add, mul_div_cancel_right₀ _ (by positivity)]
    calc
      _ ≤ (1/2 : ℝ) ^ (j+1) * 2 := mul_le_mul (radial_tail j) (hf _).2 (hf _).1 (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have geo := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have ht := Summable.of_nonneg_of_le (fun j => hnon (j+N)) htail geo
  have hg : Summable g := (summable_nat_add_iff N).mp ht
  have ht2 := ht.tsum_le_tsum htail geo
  rw [tsum_geometric_two] at ht2
  have ht0 : 0 ≤ ∑' j, g (j+N) := tsum_nonneg (fun j => hnon (j+N))
  have hle (n : ℕ) : g n ≤ f n := by
    dsimp [g]
    rw [radius_pow]
    apply mul_le_of_le_one_left (hf n).1
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hloss (n : ℕ) : f n - g n ≤ 2 * (2 : ℝ)^n / 2^N := by
    dsimp [g]
    rw [radius_pow]
    have he := Real.add_one_le_exp (-((2 : ℝ)^n / 2^N))
    calc
      _ = (1 - Real.exp (-((2:ℝ)^n / 2^N))) * f n := by ring
      _ ≤ ((2:ℝ)^n / 2^N) * f n := mul_le_mul_of_nonneg_right (by linarith) (hf n).1
      _ ≤ ((2:ℝ)^n / 2^N) * 2 := mul_le_mul_of_nonneg_left (hf n).2 (by positivity)
      _ = _ := by ring
  have hs := sum_le_sum (s := range N) (fun n _ => hloss n)
  rw [sum_sub_distrib, ← sum_div, ← mul_sum] at hs
  have hgeo := geom_sum_mul (2:ℝ) N
  norm_num at hgeo
  rw [hgeo] at hs
  have h2 : 2 * ((2:ℝ)^N - 1) / 2^N ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  change |(∑' n, g n) - _| ≤ _
  rw [← hg.sum_add_tsum_nat_add N, abs_le]
  have hu := sum_le_sum (s := range N) (fun n _ => hle n)
  constructor <;> linarith

/-- Difference of the positive-axis and angular real radial values. -/
noncomputable def radialDeficit (x : ℝ) (N : ℕ) : ℝ :=
  (fredholm (radius N)).re -
    (fredholm ((radius N : ℂ) * Complex.exp (↑(2 * Real.pi * x) * Complex.I))).re

theorem radialDeficit_eq (x : ℝ) (N : ℕ) :
    radialDeficit x N = ∑' n : ℕ, radius N ^ (2 ^ n : ℕ) * cosineEscape ((2:ℝ)^n * x) := by
  let r := radius N
  let z := Complex.exp (↑(2 * Real.pi * x) * Complex.I)
  have hr : ‖(r : ℂ)‖ < 1 := by
    dsimp [r, radius]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hrz : ‖(r : ℂ) * z‖ < 1 := by simpa [norm_mul, hz] using hr
  have sp := summable_fredholm hr
  have sq := summable_fredholm hrz
  have hchar (n : ℕ) : (z ^ (2 ^ n : ℕ)).re = Real.cos (2 * Real.pi * ((2:ℝ)^n * x)) := by
    dsimp [z]
    rw [← Complex.exp_nat_mul, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
    congr 1
    push_cast
    ring
  change (fredholm (r : ℂ)).re - (fredholm ((r : ℂ) * z)).re = _
  rw [fredholm, fredholm, Complex.re_tsum sp, Complex.re_tsum sq,
    ← (Complex.hasSum_re sp.hasSum).summable.tsum_sub (Complex.hasSum_re sq.hasSum).summable]
  simp_rw [mul_pow, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_ofReal_mul, hchar]
  have h (n : ℕ) : r ^ (2 ^ n : ℕ) - r ^ (2 ^ n : ℕ) * Real.cos (2 * Real.pi * ((2:ℝ)^n * x)) =
      radius N ^ (2 ^ n : ℕ) * cosineEscape ((2:ℝ)^n * x) := by unfold cosineEscape; dsimp [r]; ring
  simp_rw [h]

/-- Uniform radial correspondence with a sharp binary cutoff. -/
theorem fredholm_radial_deficit (x : ℝ) (N : ℕ) :
    |radialDeficit x N - ∑ n ∈ range N, cosineEscape ((2:ℝ)^n * x)| ≤ 2 := by
  rw [radialDeficit_eq]
  apply radial_cutoff
  intro n
  unfold cosineEscape
  constructor <;> linarith [Real.cos_le_one (2 * Real.pi * (2 ^ n * x)),
    Real.neg_one_le_cos (2 * Real.pi * (2 ^ n * x))]

open Filter in
/-- A positive normalized radial deficit is equivalent to strict asymptotic discrepancy. -/
theorem discrepancy_lt_one_iff_radial (x : ℝ) : asymptoticDiscrepancy x < 1 ↔
    0 < liminf (fun N : ℕ => radialDeficit x N / N) atTop := by
  let u (n : ℕ) := (2:ℝ)^n * x
  let A := escapeAverage u
  let B (N : ℕ) := radialDeficit x N / N
  have e (n : ℕ) : 0 ≤ cosineEscape (u n) ∧ cosineEscape (u n) ≤ 2 := by
    unfold cosineEscape
    constructor <;> linarith [Real.cos_le_one (2 * Real.pi * u n), Real.neg_one_le_cos (2 * Real.pi * u n)]
  have hA (N : ℕ) : 0 ≤ A N ∧ A N ≤ 2 := by
    dsimp [A, escapeAverage]
    constructor
    · exact div_nonneg (sum_nonneg fun n _ => (e n).1) (by positivity)
    · cases N with
      | zero => simp
      | succ N =>
        apply (div_le_iff₀ (by positivity)).mpr
        simpa [mul_comm] using sum_le_sum (s := range (N+1)) fun n _ => (e n).2
  have err (N : ℕ) : |B N - A N| ≤ 2 / N := by
    dsimp [A, B, escapeAverage]
    rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (fredholm_radial_deficit x N) (by positivity)
  have hB (N : ℕ) : 0 ≤ B N ∧ B N ≤ 4 := by
    constructor
    · dsimp [B]
      rw [radialDeficit_eq]
      exact div_nonneg (tsum_nonneg fun n => mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (e n).1) (by positivity)
    · cases N with
      | zero => simp [B]
      | succ N =>
        have hdiv : 2 / ((N+1 : ℕ) : ℝ) ≤ 2 := by
          apply (div_le_iff₀ (by positivity)).mpr
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) N]
        linarith [(abs_le.mp (err (N+1))).2, (hA (N+1)).2]
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)
  have h₁ := liminf_le_mul_of_error (A := 1) hA (fun n => (hB n).1) ht
    (fun N => by linarith [(abs_le.mp (err N)).2])
  have h₂ := liminf_le_mul_of_error (A := 1) hB (fun n => (hA n).1) ht
    (fun N => by linarith [(abs_le.mp (err N)).1])
  rw [discrepancy_lt_one_iff_transitions]
  obtain ⟨hl, hu⟩ := first_frequency_bounds x u (by simp [u])
  change 0 < transitionDensity x ↔ 0 < liminf B atTop
  change transitionDensity x ≤ liminf A atTop at hl
  change liminf A atTop ≤ 4 * transitionDensity x at hu
  constructor <;> intro h <;> linarith

end NormalityChecker.FredholmOrbit
