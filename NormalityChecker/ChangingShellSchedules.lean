module

public import NormalityChecker.SignedShellDiscrepancy

/-! Two signed expansions with alternating ratios 3 and 9 between insertion sites. -/

@[expose] public section
open Filter
namespace NormalityChecker.SignedPhases

/-- The middle phase grows from 1 to 3, so the insertion at exponent 3^(3k+2) vanishes. -/
def shortZeroPhase (j : ℕ) : ℤ := if j%3 = 0 then 0 else if j%3 = 1 then 1 else 3

/-- The zero phase persists for two shells, so the insertion at exponent 3^(3k+1) vanishes. -/
def longZeroPhase (j : ℕ) : ℤ := if j%3 = 2 then 1 else 0

/-- Short and long zero shells have different discrepancies, even though their
grouped zero indicators are both the alternating word 1010…. -/
theorem alternating_ratio_discrepancies :
    (∀ k, jump 3 shortZeroPhase (3*k+2) = 0 ∧ jump 3 longZeroPhase (3*k+1) = 0) ∧
    limsup (radixDiscrepancy 2 (value 2 3 shortZeroPhase)) atTop = 9/13 ∧
    limsup (radixDiscrepancy 2 (value 2 3 longZeroPhase)) atTop = 12/13 := by
  constructor
  · intro k
    simp [jump, shortZeroPhase, longZeroPhase, Nat.mul_add_mod_self_left, Nat.add_assoc]
  have calcDisc (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ 3) (per : ∀ j, c (j+3) = c j) :
      limsup (radixDiscrepancy 2 (value 2 3 c)) atTop = (cycleMaximum 3 3 c : ℝ) :=
    periodic_discrepancy (by decide) (by decide) (by decide) (by decide) c cap per
  have a (j : ℕ) : (shortZeroPhase j).natAbs ≤ 3 := by unfold shortZeroPhase; split_ifs <;> decide
  have b (j : ℕ) : (longZeroPhase j).natAbs ≤ 3 := by unfold longZeroPhase; split_ifs <;> decide
  rw [calcDisc shortZeroPhase a (fun j => by simp [shortZeroPhase]),
    calcDisc longZeroPhase b (fun j => by simp [longZeroPhase])]
  have resolve (c : ℕ → ℤ) : cycleMaximum 3 3 c = max 0
      (max (cycleScore 3 3 c 2) (max (cycleScore 3 3 c 1) (cycleScore 3 3 c 0))) := by
    simp [cycleMaximum, show Finset.range 3 = {2, 1, 0} by decide, Finset.max'_insert]
  rw [resolve, resolve]
  norm_num [cycleScore, boundaryMass, shortZeroPhase, longZeroPhase]

end NormalityChecker.SignedPhases
