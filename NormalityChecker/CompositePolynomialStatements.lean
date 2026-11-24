module

public import NormalityChecker.StonehamStatements
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-! Independent statements for polynomial images on a composite Stoneham parameter. -/
@[expose] public section
open Filter Polynomial
open scoped Topology
namespace NormalityChecker.StonehamStatements

/-- Convergence of the actual inverse radix powers to a unit of the valuation ring. -/
def UnitPowerLimit (b c p : ℕ) [Fact p.Prime] : Prop :=
  ∃ w : ℚ_[p], ‖w‖ = 1 ∧
    Tendsto (fun j : ℕ => ((b : ℚ_[p])⁻¹)^(c^j)) atTop (𝓝 w)

def PolynomialNormalityAtUnitLimit : Prop :=
  ∀ {b c p : ℕ} [Fact p.Prime], 2 ≤ b → 2 < c → b.Coprime c → p ∣ c →
    UnitPowerLimit b c p → ∀ P : ℚ[X], 0 < P.natDegree →
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (stoneham b c))

def EvenParameterPolynomialNormality : Prop :=
  ∀ {b c : ℕ}, 2 ≤ b → 2 < c → b.Coprime c → Even c →
    ∀ P : ℚ[X], 0 < P.natDegree →
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (stoneham b c))

end NormalityChecker.StonehamStatements
