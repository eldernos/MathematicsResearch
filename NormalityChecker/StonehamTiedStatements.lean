module

public import NormalityChecker.StonehamStatements

/-! A coefficient neighborhood stated with products of the defining series. -/
@[expose] public section
open Finset
namespace NormalityChecker.StonehamStatements

/-- Each factor specifies a radix dilation and a positive prime-power stride. -/
noncomputable def standardProduct {d : ℕ} (b p : ℕ) (m e : Fin d → ℕ+) : ℝ :=
  ∏ i, stoneham (b^(m i:ℕ)) (p^(e i:ℕ))

/-- The list of monomials is fixed before the common power of p is chosen.
Their integer coefficients can then be chosen arbitrarily. -/
def TiedCoefficientNormality : Prop :=
  ∀ {b p d : ℕ}, 2≤b → p.Prime → 3≤p → b.Coprime p → 0<d →
    ∀ (m e : Fin d → ℕ+) (s : ℕ) (degrees : Fin s → ℕ)
      (ms es : (i : Fin s) → Fin (degrees i) → ℕ+), (∀ i, degrees i ≤ d) →
      ∃ H : ℕ, ∀ a : Fin s → ℤ,
        NormalIn b (standardProduct b p m e +
          (p:ℝ)^H * ∑ i, (a i:ℝ)*standardProduct b p (ms i) (es i))

end NormalityChecker.StonehamStatements
