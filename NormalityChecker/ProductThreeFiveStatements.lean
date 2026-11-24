module

public import NormalityChecker.BinaryDiscrepancy
public import NormalityChecker.StonehamStatements

/-! Statement of the two-axis discrepancy bound using the defining series. -/
@[expose] public section
namespace NormalityChecker.StonehamStatements

/-- The upper binary extreme interval discrepancy of α(2,3)α(2,5). -/
def IndependentProductDiscrepancy : Prop :=
  asymptoticDiscrepancy (stoneham 2 3 * stoneham 2 5) ≤ 27/40

end NormalityChecker.StonehamStatements
