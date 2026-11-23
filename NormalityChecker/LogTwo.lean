module

public import NormalityChecker.Distribution
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

open Filter Finset
open scoped Topology

namespace NormalityChecker

/-- Exact rational recurrence for the shifted first `n` terms of the logarithm series. -/
@[expose] def logPrefix : ℕ → ℚ
  | 0 => 0
  | n + 1 => 2 * logPrefix n + 1 / ((n : ℚ) + 1)

private noncomputable abbrev logTerm (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 1) / (i + 1)

private lemma logSeries : HasSum logTerm (Real.log 2) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / 2) (by norm_num)
  norm_num [Real.log_div] at h
  unfold logTerm
  simpa [one_div] using h

theorem hasSum_logTwo : HasSum (fun j : ℕ => (1/2 : ℝ)^(j+1) / (j+1)) (Real.log 2) :=
  logSeries

private lemma prefix_eq (n : ℕ) :
    (logPrefix n : ℝ) = 2 ^ n * ∑ i ∈ range n, logTerm i := by
  induction n with
  | zero => simp [logPrefix]
  | succ n ih =>
    simp only [logPrefix, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one, ih, sum_range_succ]
    rw [mul_add]
    congr 1
    · rw [pow_succ']; ring
    · unfold logTerm
      rw [one_div_pow]
      field_simp

private lemma scaled_log_term (n i : ℕ) :
    (2 : ℝ) ^ n * logTerm (i + n) =
      ((1 / 2 : ℝ) ^ (i + 1)) / ((i : ℝ) + n + 1) := by
  unfold logTerm
  rw [show i + n + 1 = n + (i + 1) by omega, pow_add, one_div_pow, Nat.cast_add]
  field_simp

/-- The shifted infinite tail is nonnegative and at most `1/(n+1)`, for every `n`. -/
theorem logTwo_tail_bounds (n : ℕ) :
    0 ≤ (2 : ℝ) ^ n * Real.log 2 - logPrefix n ∧
    (2 : ℝ) ^ n * Real.log 2 - logPrefix n ≤ 1 / (n + 1 : ℝ) := by
  have hsplit := logSeries.summable.sum_add_tsum_nat_add n
  rw [logSeries.tsum_eq] at hsplit
  have htail : (2 : ℝ) ^ n * Real.log 2 - logPrefix n =
      ∑' i, (2 : ℝ) ^ n * logTerm (i + n) := by
    rw [prefix_eq, ← hsplit, mul_add, tsum_mul_left]; ring
  rw [htail]
  constructor
  · exact tsum_nonneg fun i => by rw [scaled_log_term]; positivity
  let c : ℝ := (1 / 2) / (n + 1)
  have hgeom := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)).mul_left c
  have hs := ((summable_nat_add_iff n).mpr logSeries.summable).mul_left ((2 : ℝ) ^ n)
  calc
    _ ≤ ∑' i : ℕ, c * (1 / 2 : ℝ) ^ i := by
      apply hs.tsum_le_tsum _ hgeom
      intro i
      rw [scaled_log_term, pow_succ]
      calc
        _ ≤ ((1 / 2 : ℝ) ^ i * (1 / 2)) / (n + 1 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        _ = _ := by dsimp [c]; ring
    _ = _ := by rw [tsum_mul_left, tsum_geometric_two]; dsimp [c]; ring

theorem logTwo_shift_error_tendsTo_zero :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * Real.log 2 - logPrefix n) atTop (𝓝 0) :=
  squeeze_zero (fun n => (logTwo_tail_bounds n).1) (fun n => (logTwo_tail_bounds n).2)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The binary normality problem for the logarithm is exactly a distribution problem
for a sequence defined using rational arithmetic alone. -/
theorem logTwo_normal_iff : NormalIn 2 (Real.log 2) ↔
    UniformModOne (fun n => (logPrefix n : ℝ)) :=
  normalIn_iff_uniform_approx (by decide) _ _ logTwo_shift_error_tendsTo_zero

private lemma step_below_quarter {n : ℕ} (hn : 0 < n) (h : Int.fract (logPrefix n) < 1/4) :
    Int.fract (logPrefix (n+1)) = 2 * Int.fract (logPrefix n) + 1 / ((n:ℚ)+1) := by
  let x := logPrefix n
  have hlo := Int.fract_nonneg x
  have hi : 1 / ((n:ℚ)+1) ≤ 1/2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1:ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have he : logPrefix (n+1) = (2*⌊x⌋ : ℤ) + (2*Int.fract x + 1/((n:ℚ)+1)) := by
    rw [logPrefix]; push_cast
    change 2*x + _ = 2*(⌊x⌋ : ℚ) + _
    linarith [Int.fract_add_floor x]
  rw [he, Int.fract_intCast_add]
  apply Int.fract_eq_self.mpr
  exact ⟨by positivity, by change Int.fract x < 1/4 at h; linarith⟩

/-- A run of `s+2` consecutive rational residues in `[0,1/4)`, starting at `n ≥ 1`,
forces `4 * 2^s < n+1`. This restricts run length, while allowing separated returns. -/
theorem logPrefix_run_bound {n s : ℕ} (hn : 0 < n)
    (h : ∀ i ≤ s+1, Int.fract (logPrefix (n+i)) < 1/4) : 4 * 2^s < n+1 := by
  have hl : ∀ t ≤ s, (2:ℚ)^t / ((n:ℚ)+1) ≤ Int.fract (logPrefix (n+t+1)) := by
    intro t ht
    induction t with
    | zero =>
      simp only [Nat.add_zero, pow_zero]
      rw [step_below_quarter hn (by simpa using h 0 (by omega))]
      linarith [Int.fract_nonneg (logPrefix n)]
    | succ t ih =>
      have hp := ih (by omega)
      rw [Nat.add_succ, step_below_quarter (by omega) (by simpa [Nat.add_assoc] using h (t+1) (by omega))]
      rw [pow_succ]
      have : (0:ℚ) ≤ 1/((↑(n+t+1):ℚ)+1) := by positivity
      change 2^t * 2 / ((n:ℚ)+1) ≤
        2 * Int.fract (logPrefix (n+t+1)) + 1/((↑(n+t+1):ℚ)+1)
      calc
        _ = 2 * (2^t / ((n:ℚ)+1)) := by ring
        _ ≤ 2 * Int.fract (logPrefix (n+t+1)) := mul_le_mul_of_nonneg_left hp (by norm_num)
        _ ≤ _ := le_add_of_nonneg_right this
  have hu := h (s+1) le_rfl
  rw [← Nat.add_assoc] at hu
  have e := (div_lt_div_iff₀ (show (0:ℚ) < n+1 by positivity) (by norm_num)).mp ((hl s le_rfl).trans_lt hu)
  exact_mod_cast (show (4:ℚ)*2^s < (n:ℚ)+1 by linarith)

end NormalityChecker
