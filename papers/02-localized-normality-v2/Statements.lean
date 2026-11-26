module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-! Public statements for Paper II, version 2.0. Only mathlib is imported here. -/
@[expose] public section
noncomputable section
open Filter Finset Polynomial
open scoped Topology

namespace PaperII

/-- One belongs even when S is empty. Zero never belongs. -/
def Smooth (S : Finset ℕ) (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ S

/-- The positive supported indices, written as m = i+1. -/
def value (b s : ℕ) (S : Finset ℕ) (P : ℚ[X]) : ℝ := by
  classical
  exact ∑' i : ℕ, let m := i+1
    if Smooth S m then ((P.eval (m : ℚ) : ℚ) : ℝ) / (m : ℝ)^s / (b : ℝ)^m else 0

def visits (b : ℕ) (x a c : ℝ) (N : ℕ) : ℝ :=
  ((range N).filter (fun n =>
    a ≤ Int.fract ((b : ℝ)^n*x) ∧ Int.fract ((b : ℝ)^n*x) < c)).card / (N : ℝ)

/-- Half-open digit cylinders, including words with leading zeroes. -/
def Normal (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ k m : ℕ, 0 < k → m < b^k →
    Tendsto (visits b x (m / (b : ℝ)^k) ((m+1) / (b : ℝ)^k)) atTop (𝓝 (1/(b : ℝ)^k))

def discrepancy (b : ℕ) (x : ℝ) (N : ℕ) : ℝ :=
  sSup {v | ∃ a c : ℝ, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧ v = |visits b x a c N - (c-a)|}

/-- The two unsigned alternatives for every positive order and every finite prime support. -/
def UnsignedClassification : Prop :=
  ∀ b s : ℕ, ∀ S : Finset ℕ, 2 ≤ b → 0 < s → (∀ p ∈ S, Nat.Prime p) →
    ((∃ p ∈ S, ¬p ∣ b) →
      Normal b (value b s S 1) ∧ Tendsto (discrepancy b (value b s S 1)) atTop (𝓝 0)) ∧
    ((∀ p ∈ S, p ∣ b) → Tendsto (discrepancy b (value b s S 1)) atTop (𝓝 1))

/-- The polynomial statement also covers order zero. -/
def PolynomialClassification : Prop :=
  ∀ b s : ℕ, ∀ S : Finset ℕ, ∀ P : ℚ[X], 2 ≤ b → (∀ p ∈ S, Nat.Prime p) → P ≠ 0 →
    (Normal b (value b s S P) ↔ P.rootMultiplicity 0 < s ∧ ∃ p ∈ S, ¬p ∣ b)

/-- Simultaneous visits of several coordinates to a half-open box, at the positions 0..N-1. -/
def visitsVec {d : ℕ} (b : ℕ) (x : Fin d → ℝ) (a c : Fin d → ℝ) (N : ℕ) : ℝ :=
  ((range N).filter (fun n => ∀ i,
    a i ≤ Int.fract ((b : ℝ)^n*x i) ∧ Int.fract ((b : ℝ)^n*x i) < c i)).card / (N : ℝ)

/-- Joint uniformity at distinct positive orders on one fixed support, for rational
numerators that do not vanish at zero (the unit numerators give the unsigned case). -/
def JointPolynomial : Prop :=
  ∀ {b d : ℕ}, 2 ≤ b → ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∃ p ∈ S, ¬p ∣ b) →
    ∀ (P : Fin d → ℚ[X]) (s : Fin d → ℕ), (∀ i, (P i).eval 0 ≠ 0) → (∀ i, 0 < s i) →
    Function.Injective s → ∀ a c : Fin d → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ c i) → (∀ i, c i ≤ 1) →
      Tendsto (visitsVec b (fun i => value b (s i) S (P i)) a c) atTop (𝓝 (∏ i, (c i - a i)))

end PaperII
