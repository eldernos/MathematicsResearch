module

public import NormalityChecker.Basic

/-! Empirical frequencies on finite products of the unit interval. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- The average uses the positions 0 through N-1 simultaneously in every coordinate. -/
noncomputable def rectangleFrequency {d : ℕ} (x : ℕ → Fin d → ℝ)
    (a c : Fin d → ℝ) (N : ℕ) : ℝ := by
  classical exact ((range N).filter (fun n => ∀ i, a i ≤ x n i ∧ x n i < c i)).card / (N : ℝ)

/-- Simultaneous radix shifts visit each half-open rectangle with its volume as frequency. -/
def JointUniform {d : ℕ} (b : ℕ) (x : Fin d → ℝ) : Prop :=
  ∀ a c : Fin d → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ c i) → (∀ i, c i ≤ 1) →
    Tendsto (rectangleFrequency (fun n i => shift b (x i) n) a c)
      atTop (𝓝 (∏ i, (c i - a i)))

/-- Taking a digit cylinder in one coordinate and the whole interval in the
others recovers normality of that coordinate. -/
theorem JointUniform.normalIn {b d : ℕ} {x : Fin d → ℝ} (joint : JointUniform b x)
    (hb : 2 ≤ b) (i : Fin d) : NormalIn b (x i) := by
  classical
  refine ⟨hb, fun k m _ hm => ?_⟩
  let q : ℝ := (b : ℝ)^k
  have qp : 0 < q := pow_pos (by exact_mod_cast (by omega : 0 < b)) _
  let a (j : Fin d) : ℝ := if j = i then m/q else 0
  let c (j : Fin d) : ℝ := if j = i then (m+1)/q else 1
  have high : (m : ℝ)+1 ≤ q := by dsimp [q]; exact_mod_cast Nat.succ_le_of_lt hm
  have box := joint a c (fun j => by simp only [a]; split <;> positivity)
    (fun j => by
      by_cases eq : j = i
      · simp only [a, c, ite_eq_left eq]; gcongr; linarith
      · simp [a, c, eq])
    (fun j => by simp only [c]; split <;> simp [div_le_one qp, high])
  have volume : (∏ j, (c j - a j)) = 1/q := by
    rw [prod_eq_single i (fun j _ ne => by simp [a, c, ne]) (by simp)]
    simp [a, c, add_div]
  have hit (n : ℕ) : (∀ j, a j ≤ shift b (x j) n ∧ shift b (x j) n < c j) ↔
      m/q ≤ shift b (x i) n ∧ shift b (x i) n < (m+1)/q := by
    refine ⟨fun h => by simpa [a,c] using h i, fun hi j => ?_⟩
    by_cases eq : j = i
    · simpa [a, c, eq] using hi
    · simp only [a, c, ite_eq_right eq]
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have visits : rectangleFrequency (fun n j => shift b (x j) n) a c =
      frequency (shift b (x i)) (m/q) ((m+1)/q) := by
    funext N
    simp only [rectangleFrequency, frequency, hit]
  rwa [visits, volume] at box

end NormalityChecker
