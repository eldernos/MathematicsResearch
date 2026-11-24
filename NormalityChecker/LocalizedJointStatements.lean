module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Independent statement of Paper II, Corollary 1.3, using only mathlib. -/
@[expose] public section
noncomputable section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedJointStatements

/-- Positive integers with all their prime divisors in S, including one. -/
def Smooth (S : Finset ℕ) (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ S

/-- The unsigned localized series at order s, indexed by the positive integers. -/
def value (b s : ℕ) (S : Finset ℕ) : ℝ := by
  classical
  exact ∑' i : ℕ, let m := i + 1
    if Smooth S m then 1 / (m : ℝ)^s / (b : ℝ)^m else 0

/-- The observed proportion of shift positions at which all coordinates lie in the box. -/
def visits {d : ℕ} (b : ℕ) (x a c : Fin d → ℝ) (N : ℕ) : ℝ := by
  classical
  exact ((range N).filter fun n => ∀ i,
    a i ≤ Int.fract ((b : ℝ)^n * x i) ∧ Int.fract ((b : ℝ)^n * x i) < c i).card / (N : ℝ)

/-- Corollary 1.3 for every nonempty finite list in any order. -/
def DistinctOrders : Prop :=
  ∀ {b d : ℕ}, 2 ≤ b → 0 < d → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    (∃ p ∈ S, ¬ p ∣ b) → ∀ s : Fin d → ℕ, (∀ i, 0 < s i) → Function.Injective s →
    ∀ a c : Fin d → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ c i) → (∀ i, c i ≤ 1) →
      Tendsto (visits b (fun i => value b (s i) S) a c) atTop (𝓝 (∏ i, (c i - a i)))

end NormalityChecker.LocalizedJointStatements
