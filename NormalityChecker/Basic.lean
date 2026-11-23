module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

@[expose] public section

open Filter Finset
open scoped Topology

namespace NormalityChecker

/-- The part of a real number exposed after shifting its radix point by `n` places. -/
noncomputable def shift (b : ℕ) (x : ℝ) (n : ℕ) : ℝ := Int.fract ((b : ℝ) ^ n * x)

/-- Fraction of the first `N` starting positions in the half-open interval `[a,c)`. -/
noncomputable def frequency (u : ℕ → ℝ) (a c : ℝ) (N : ℕ) : ℝ :=
  ((range N).filter (fun i => a ≤ u i ∧ u i < c)).card / (N : ℝ)

/-- Every length-`k` word, encoded by `m` with leading zeroes allowed, has frequency
`b⁻ᵏ`. The half-open cylinders select the terminating expansion at radix rationals. -/
def NormalIn (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ k m : ℕ, 0 < k → m < b ^ k →
    Tendsto (frequency (shift b x) (m / (b : ℝ) ^ k) ((m + 1) / (b : ℝ) ^ k))
      atTop (𝓝 (1 / (b : ℝ) ^ k))

/-- An excess of one block on arbitrarily long prefixes disproves normality. -/
theorem not_normal_of_frequent_excess {b k m : ℕ} {x δ : ℝ}
    (hk : 0 < k) (hm : m < b ^ k) (hδ : 0 < δ)
    (h : ∃ᶠ N in atTop, 1 / (b : ℝ) ^ k + δ ≤
      frequency (shift b x) (m / (b : ℝ) ^ k) ((m + 1) / (b : ℝ) ^ k) N) :
    ¬ NormalIn b x := by
  intro hn
  apply h
  filter_upwards [(hn.2 k m hk hm).eventually_lt_const (lt_add_of_pos_right _ hδ)] with N hN
  exact not_le.mpr hN

end NormalityChecker
