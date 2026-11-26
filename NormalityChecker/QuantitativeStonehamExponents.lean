module

public import Mathlib.Tactic

/-! A single differencing depth works in every positive polynomial degree. -/
@[expose] public section
namespace NormalityChecker.QuantitativeStoneham

/-- For Vandehey's exponents put `s k = (1-γₖ)/αₖ`. The displayed recurrence
follows from Theorem 5.1 and γₖ+νₖ = 2−2⁻ᵏ. This rational inequality leaves a
strict margin when the polynomial degree is `k+1`. -/
theorem differencing_margin (s : ℕ → ℚ) (init : s 0 = 2)
    (step : ∀ k : ℕ, s (k+1) = s k + 1 -
      (s k - (4 - 2 / (2 : ℚ)^k)) / (4 * (2 : ℚ)^k - 2)) (k : ℕ) :
    (k : ℚ) + 1 + 1/2 < s k ∧ s k ≤ (k : ℚ) + 2 := by
  have one : s 1 = 3 := by norm_num [step 0, init]
  have two : s 2 = 4 := by norm_num [step 1, one]
  have three : s 3 = 139/28 := by norm_num [step 2, two]
  by_cases small : k < 3
  · interval_cases k <;> norm_num [init, one, two]
  have stronger (j : ℕ) (hj : 3 ≤ j) :
      (j : ℚ) + 1 + 1/2 + j/(2 : ℚ)^j ≤ s j ∧ s j ≤ (j : ℚ) + 2 := by
    induction j, hj using Nat.le_induction with
    | base => norm_num [three]
    | succ j hj ih =>
      let z : ℚ := 2^j
      have hz : 2 ≤ z := (le_self_pow₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega : j ≠ 0))
      have hp : 0 < 4*z-2 := by linarith
      have jp : (3 : ℚ) ≤ j := by exact_mod_cast hj
      have hfrac : 0 ≤ (j : ℚ)/z := by positivity
      have hz' : 2/z ≤ 1 := (div_le_one (by linarith)).mpr hz
      change _ + _/z ≤ _ ∧ _ at ih
      have drift0 : 0 ≤ (s j - (4 - 2/z)) / (4*z-2) := div_nonneg
        (by linarith [ih.1, show 0 ≤ 2/z by positivity]) hp.le
      have drift1 : (s j - (4 - 2/z)) / (4*z-2) ≤ (j-1)/(2*z) := by
        apply le_trans (div_le_div_of_nonneg_right (by linarith [ih.2] :
          s j - (4 - 2/z) ≤ (j : ℚ)-1) hp.le)
        exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
      rw [step j]; push_cast; rw [pow_succ]
      change (j : ℚ)+1+1+1/2 + (j+1)/(z*2) ≤ s j+1-_ ∧ s j+1-_ ≤ _
      have add : (j : ℚ)/z - (j-1)/(2*z) = (j+1)/(z*2) := by field_simp; ring
      constructor <;> linarith [ih.1, ih.2]
  obtain ⟨lower, upper⟩ := stronger k (by omega)
  have hk : 0 < k := by omega
  exact ⟨by linarith [show 0 < (k : ℚ)/(2 : ℚ)^k by positivity], upper⟩

end NormalityChecker.QuantitativeStoneham
