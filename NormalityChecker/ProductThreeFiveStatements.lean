module

public import NormalityChecker.BinaryDiscrepancy
public import NormalityChecker.StonehamStatements

/-! Statement of the two-axis discrepancy bound using the defining series. -/
@[expose] public section
open Finset
namespace NormalityChecker.StonehamStatements

/-- The upper binary extreme interval discrepancy of α(2,3)α(2,5). -/
def IndependentProductDiscrepancy : Prop :=
  asymptoticDiscrepancy (stoneham 2 3 * stoneham 2 5) ≤ 27/40

/-- Shift the finite, index-one product prefix through position n. -/
def mixedPrefix (n : ℕ) : ℚ :=
  ∑ i ∈ range (Nat.log 3 n), ∑ j ∈ range (Nat.log 5 n),
    let P := 3^(i+1)
    let Q := 5^(j+1)
    if P+Q≤n then (2:ℚ)^(n-(P+Q))/(P*Q:ℕ) else 0

/-- Exact full-power tests from the two coupled endpoints. -/
def MixedPrefixResidues : Prop :=
  ∀ n : ℕ, 5≤n →
    let K := Nat.log 3 n
    let L := Nat.log 5 n
    (3^K ∣ (mixedPrefix n).den ↔ Nat.log 5 (n-3^K)%2 ≠ 0) ∧
    (5^L ∣ (mixedPrefix n).den ↔ Nat.log 3 (n-5^L)%4 ≠ 0)

/-- Arbitrarily late, a full rectangle loses h denominator layers at both
primes throughout an interval of length greater than three quarters of 3^K. -/
def MixedPrefixPersistentLoss : Prop :=
  ∀ h A : ℕ, 0<h → ∃ K L : ℕ, A≤K ∧ h≤K ∧ h≤L ∧ 3^K<5^L ∧ 4*5^L<5*3^K ∧
    ∀ n, 3^K+5^L≤n → n<3*3^K → (mixedPrefix n).den ∣ 3^(K-h)*5^(L-h)

end NormalityChecker.StonehamStatements
