import NormalityChecker.Correlations

/-! A finite transfer from counts of the binary word consisting of a one
followed by zeros to a deficit in a Fourier sum on the same window. -/

open Finset NormalityChecker
open scoped Classical

namespace ErdosBorweinAudit

noncomputable def lambertE : ℝ := ∑' m : ℕ, 1 / ((2 : ℝ) ^ (m + 1) - 1)

/-- Number of starts in the window whose phase lies in the cylinder for
the length-`k` binary word with value `2^(k-1)`, for positive `k`. -/
noncomputable def halfWordCount (x : ℝ) (start length k : ℕ) : ℕ :=
  ((range length).filter fun i =>
    shift 2 x (start + i) ∈ Set.Ico (1/2 : ℝ) (1/2 + 1/(2 : ℝ)^k)).card

private theorem phase_odd_half {h : ℤ} (hh : Odd h) :
    phase ((h : ℝ) / 2) = -1 := by
  obtain ⟨j, rfl⟩ := hh
  have hz : phase (j : ℝ) = 1 := by
    simpa [phase, mul_comm] using Complex.exp_int_mul_two_pi_mul_I j
  have he : phase (1 / 2) = -1 := by
    unfold phase
    convert Complex.exp_pi_mul_I using 2
    push_cast
    ring
  push_cast
  rw [show ((2 : ℝ) * j + 1) / 2 = j + 1/2 by ring, phase_add, hz, he, one_mul]

/-- A shift in the indicated cylinder makes two successive unit phases sum
to at most one in norm. The two boundary phases cost at most two in total. -/
theorem window_fourier_deficit (x : ℝ) {h : ℤ} (hh : Odd h)
    (start length k : ℕ) (hk : 2 * Real.pi * |(h : ℝ)| ≤ (2 : ℝ)^k) :
    2 * ‖∑ i ∈ range length, phase (h * ((2 : ℝ)^(start + i) * x))‖ ≤
      2 * length + 2 - halfWordCount x start length k := by
  let z (i : ℕ) := phase (h * ((2 : ℝ)^(start + i) * x))
  let hit (i : ℕ) := shift 2 x (start + i) ∈ Set.Ico (1/2 : ℝ) (1/2 + 1/(2 : ℝ)^k)
  have unit (i : ℕ) : ‖z i‖ = 1 := norm_phase _
  have step (i : ℕ) : z (i+1) = z i * z i := by
    dsimp [z]
    rw [← phase_add, ← Nat.add_assoc, pow_succ]
    congr 1
    ring
  have cost (i : ℕ) : ‖z i + z (i+1)‖ ≤ 2 - (if hit i then (1 : ℝ) else 0) := by
    by_cases hi : hit i
    · have ⟨lo, up⟩ := hi
      have near := phase_sub_le ((h : ℝ) * shift 2 x (start+i)) ((h : ℝ)/2)
      rw [shift, phase_fract, phase_odd_half hh, sub_neg_eq_add] at near
      change ‖z i + 1‖ ≤ 2 * Real.pi *
        |(h : ℝ) * shift 2 x (start+i) - (h : ℝ)/2| at near
      have dist : |(h : ℝ) * shift 2 x (start+i) - (h : ℝ)/2| ≤
          |(h : ℝ)| * (1/(2 : ℝ)^k) := by
        rw [div_eq_mul_one_div (h : ℝ), ← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr lo)]
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      simp only [hi, ite_true]
      rw [step, ← mul_one_add, norm_mul, unit, one_mul, add_comm (1 : ℂ)]
      have bound := near.trans (mul_le_mul_of_nonneg_left dist (by positivity))
      rw [← mul_assoc, mul_one_div] at bound
      linarith [(div_le_one (by positivity)).mpr hk]
    · simpa [hi, unit, one_add_one_eq_two] using norm_add_le (z i) (z (i+1))
  have pairs := (norm_sum_le (range length) (fun i => z i + z (i+1))).trans
    (sum_le_sum fun i _ => cost i)
  have mass : (∑ i ∈ range length, if hit i then (1 : ℝ) else 0) =
      (halfWordCount x start length k : ℝ) := by
    simp [halfWordCount, hit]
  rw [sum_sub_distrib, mass] at pairs
  have edge := norm_sub_le (z 0) (z length)
  rw [unit, unit] at edge
  have telescope := sum_range_sub z length
  rw [sum_sub_distrib] at telescope
  have identity : (2 : ℂ) * (∑ i ∈ range length, z i) =
      (∑ i ∈ range length, (z i + z (i+1))) + (z 0 - z length) := by
    rw [sum_add_distrib]
    linear_combination -telescope
  have tri := norm_add_le (∑ i ∈ range length, (z i + z (i+1))) (z 0 - z length)
  rw [← identity, norm_mul, Complex.norm_ofNat] at tri
  simp only [sum_const, card_range, nsmul_eq_mul] at pairs
  change 2 * ‖∑ i ∈ range length, z i‖ ≤ _
  linarith

/-- Applied to the actual Lambert constant, a lower count `c * length`
saves `c * length / 2` against the trivial Fourier bound, up to one endpoint. -/
theorem erdosBorwein_window_fourier (h : ℤ) (hh : Odd h) (start length k : ℕ)
    (hk : 2 * Real.pi * |(h : ℝ)| ≤ (2 : ℝ)^k) (c : ℝ)
    (hits : c * length ≤ halfWordCount lambertE start length k) :
    ‖∑ i ∈ range length, phase (h * ((2 : ℝ)^(start + i) * lambertE))‖ ≤
      (1 - c/2) * length + 1 := by
  linarith [window_fourier_deficit lambertE hh start length k hk]

#print axioms erdosBorwein_window_fourier

end ErdosBorweinAudit
