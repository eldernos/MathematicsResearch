module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.GCD
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

@[expose] public section
open Finset
namespace NormalityChecker.AffineDenominator

/-- Gcd of the modulus and the supplied numerator differences, up to sign. -/
def differenceGcd (M : ℤ) : {k : ℕ} → (Fin k → ℤ) → ℤ
  | 0, _ => M
  | k+1, d => Int.gcd (differenceGcd M (k := k) (fun i => d i.succ)) (d 0)

private theorem eliminate (g d b : ℤ) :
    (∃ c : ℤ, g ∣ b + c*d) ↔ (Int.gcd g d : ℤ) ∣ b := by
  constructor
  · rintro ⟨c, hc⟩
    have h₁ := dvd_trans (Int.gcd_dvd_left g d) hc
    have h₂ := dvd_mul_of_dvd_right (Int.gcd_dvd_right g d) c
    simpa using dvd_sub h₁ h₂
  · rintro ⟨t, ht⟩
    refine ⟨-(Int.gcdB g d * t), Int.gcdA g d * t, ?_⟩
    rw [ht, Int.gcd_eq_gcd_ab]
    ring

private theorem linear_congruence (M : ℤ) {k : ℕ} (d : Fin k → ℤ) (b : ℤ) :
    (∃ c : Fin k → ℤ, M ∣ b + ∑ i, c i * d i) ↔ differenceGcd M d ∣ b := by
  induction k generalizing b with
  | zero => simp [differenceGcd]
  | succ k ih =>
    rw [differenceGcd, ← eliminate]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c 0, (ih _ _).mp ⟨fun i => c i.succ, ?_⟩⟩
      rwa [Fin.sum_univ_succ, ← add_assoc] at hc
    · rintro ⟨a, ha⟩
      obtain ⟨c, hc⟩ := (ih _ _).mpr ha
      refine ⟨Fin.cons a c, ?_⟩
      simpa only [Fin.sum_univ_succ (n := k), Fin.cons_zero, Fin.cons_succ, ← add_assoc] using! hc

/-- Feasibility of denominator removal in an affine integer combination.
Index zero is the reference numerator; the other coordinates are free. -/
theorem feasible_iff_gcd (M : ℤ) {k : ℕ} (A : Fin (k+1) → ℤ) :
    (∃ c : Fin (k+1) → ℤ, (∑ i, c i) = 1 ∧ M ∣ ∑ i, c i * A i) ↔
      differenceGcd M (fun i : Fin k => A i.succ - A 0) ∣ A 0 := by
  rw [← linear_congruence]
  have eqn (c : Fin k → ℤ) :
      A 0 + ∑ i, c i * (A i.succ - A 0) =
        (1 - ∑ i, c i) * A 0 + ∑ i, c i * A i.succ := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  constructor
  · rintro ⟨c, hs, hc⟩
    refine ⟨fun i => c i.succ, ?_⟩
    rw [Fin.sum_univ_succ] at hs hc
    rw [eqn, ← eq_sub_of_add_eq hs]
    exact hc
  · rintro ⟨c, hc⟩
    refine ⟨Fin.cons (1 - ∑ i, c i) c, ?_, ?_⟩
    · simp [Fin.sum_univ_succ]
    · rw [eqn] at hc
      simpa only [Fin.sum_univ_succ (n := k), Fin.cons_zero, Fin.cons_succ] using! hc

/-- The unwrapped error spent by an affine combination of approximations. -/
theorem combined_error {k : ℕ} (c : Fin k → ℤ) (R ε : Fin k → ℝ) (x : ℝ)
    (hc : ∑ i, c i = 1) (hε : ∀ i, |R i - x| ≤ ε i) :
    |(∑ i, (c i : ℝ) * R i) - x| ≤ ∑ i, |(c i : ℝ)| * ε i := by
  have hc' : ∑ i, (c i : ℝ) = 1 := by exact_mod_cast hc
  have hs : ∑ i, (c i : ℝ) * (R i - x) = (∑ i, (c i : ℝ) * R i) - x := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, hc', one_mul]
  rw [← hs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact sum_le_sum fun i _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _)

end NormalityChecker.AffineDenominator
