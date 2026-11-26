module

public import NormalityChecker.StonehamStatements

/-! The positive-index Stoneham square with denominator parameter two. -/
@[expose] public section
open Finset
namespace NormalityChecker.ParameterTwoSquare

/-- Index `i = 0` denotes the first positive Stoneham index. -/
def term (b i : ℕ) : ℚ := 1 / (2^(i+1) * (b : ℚ)^(2^(i+1) : ℕ))

def location (i j : ℕ) : ℕ := 2^(i+1) + 2^(j+1)

/-- Unshifted contribution from the first `k` indices in each factor,
including an ordered pair exactly when its insertion has occurred. -/
def boxSum (b n k : ℕ) : ℚ := ∑ i ∈ range k, ∑ j ∈ range k,
  if location i j ≤ n then term b i * term b j else 0

/-- The actual shifted rational prefix at digit `n`. -/
def pre (b n : ℕ) : ℚ := (b : ℚ)^n * boxSum b n (Nat.log 2 n)

/-- The single-axis weighted sum with the powers of two cleared. -/
def weightedSum (b k : ℕ) : ℚ :=
  ∑ i ∈ range k, (2 : ℚ)^(k-(i+1)) / (b : ℚ)^(2^(i+1) : ℕ)

def ExactDenominatorProfile : Prop := ∀ {b : ℕ}, 3 ≤ b → Odd b →
  (∀ n < 4, (pre b n).den = 1) ∧
  ∀ k ≥ 2, ∀ n : ℕ, 2^k ≤ n → n < 2^(k+1) →
    (pre b n).den = if n < 3*2^(k-1) then 2^(2*k-2) else 2^(k-1)

def SquareNormality : Prop := ∀ {b : ℕ}, 3 ≤ b → Odd b →
  NormalIn b ((StonehamStatements.stoneham b 2)^2)

end NormalityChecker.ParameterTwoSquare
