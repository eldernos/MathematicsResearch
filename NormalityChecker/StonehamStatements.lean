module

public import NormalityChecker.RectangleFrequency
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Public mathematical statements for the polynomial and joint-orbit theorems. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.StonehamStatements

/-- The first term is indexed by one. -/
noncomputable def stoneham (b c : ℕ) : ℝ :=
  ∑' j : ℕ, 1 / ((c : ℝ) ^ (j+1) * (b : ℝ) ^ (c ^ (j+1) : ℕ))

/-- Simultaneous visits at the positions 0 through N-1. -/
noncomputable abbrev rectangleFrequency {d : ℕ} := @NormalityChecker.rectangleFrequency d

def PolynomialNormality : Prop :=
  ∀ {b p : ℕ}, 2 ≤ b → p.Prime → 3 ≤ p → b.Coprime p → ∀ (e : ℕ+) (P : ℚ[X]),
    0 < P.natDegree → NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (stoneham b (p^(e : ℕ))))

def JointPowerNormality : Prop :=
  ∀ {b p d : ℕ}, 2 ≤ b → p.Prime → 3 ≤ p → b.Coprime p → ∀ (e : ℕ+) (r : Fin d → ℕ),
    (∀ i, 0 < r i) → Function.Injective r → ∀ a c : Fin d → ℝ,
    (∀ i, 0 ≤ a i) → (∀ i, a i ≤ c i) → (∀ i, c i ≤ 1) →
      Tendsto (rectangleFrequency (fun n i => shift b (stoneham b (p^(e : ℕ)) ^ r i) n) a c)
        atTop (𝓝 (∏ i, (c i - a i)))

end NormalityChecker.StonehamStatements
