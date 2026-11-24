module

public import NormalityChecker.ParameterTwoSquareStatements
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Clearing the odd radix from the single-axis sum and the missing diagonal. -/
@[expose] public section
open Finset
namespace NormalityChecker.ParameterTwoSquare

/-- The integer numerator after multiplying the weighted sum by `b^(2^k)`. -/
def axisNumerator (b : ℕ) : ℕ → ℤ
  | 0 => 0
  | k+1 => 2 * (b : ℤ)^(2^k : ℕ) * axisNumerator b k + 1

theorem weighted_eq (b k : ℕ) :
    weightedSum b k = (2 : ℚ)^k * ∑ i ∈ range k, term b i := by
  rw [weightedSum, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [pow_sub₀ (2 : ℚ) (by norm_num) (mem_range.mp hi)]
  unfold term
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_comm, mul_left_comm]

theorem clear_axis {b : ℕ} (hb : 0 < b) (k : ℕ) :
    (b : ℚ)^(2^k : ℕ) * weightedSum b k = axisNumerator b k := by
  rw [weighted_eq]
  induction k with
  | zero => simp [axisNumerator]
  | succ k ih =>
    have h : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [sum_range_succ, axisNumerator]
    push_cast
    rw [← ih]
    unfold term
    rw [pow_succ (2 : ℕ) k, pow_mul]
    rw [pow_succ (2 : ℚ) k]
    field_simp

/-- Every odd square is one modulo eight. Each further squaring gains a bit. -/
private theorem radix_lift {b : ℕ} (odd : Odd b) {k : ℕ} (hk : 1 ≤ k) :
    ∃ t : ℤ, (b : ℤ)^(2^k : ℕ) = 1 + 2^(k+2) * t := by
  induction k, hk using Nat.le_induction with
  | base =>
    obtain ⟨a, ha⟩ := odd
    rcases Nat.even_or_odd a with ⟨r, hr⟩ | ⟨r, hr⟩ <;> rw [ha, hr] <;> push_cast
    · exact ⟨2*(r : ℤ)^2+r, by ring⟩
    · exact ⟨2*(r : ℤ)^2+3*r+1, by ring⟩
  | succ k hk ih =>
    obtain ⟨t, ht⟩ := ih
    rw [pow_succ (2 : ℕ) k, pow_mul, ht]
    refine ⟨t + 2^(k+1)*t^2, ?_⟩
    rw [show k+1+2=k+2+1 by omega, pow_succ (2 : ℤ) (k+2),
      show k+2=k+1+1 by omega, pow_succ (2 : ℤ) (k+1)]
    ring

private theorem axis_residue {b : ℕ} (odd : Odd b) {k : ℕ} (hk : 1 ≤ k) :
    ∃ t : ℤ, axisNumerator b k = 2^k - 1 + 2^(k+2)*t := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨0, by simp [axisNumerator]⟩
  | succ k hk ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨s, hs⟩ := radix_lift odd hk
    refine ⟨t+s*axisNumerator b k, ?_⟩
    rw [axisNumerator, hs, ht, show k+1+2=k+2+1 by omega, pow_succ (2 : ℤ) (k+2),
      pow_succ (2 : ℤ) k]
    ring

/-- The congruence for the rational weighted sum, with its odd denominator
explicitly cleared on both sides. -/
theorem weighted_congruence {b k : ℕ} (odd : Odd b) (hk : 1 ≤ k) :
    (axisNumerator b k) ≡ (2^k-1) * (b : ℤ)^(2^k : ℕ) [ZMOD 2^(k+2)] := by
  obtain ⟨t, ht⟩ := axis_residue odd hk
  obtain ⟨s, hs⟩ := radix_lift odd hk
  rw [Int.modEq_iff_dvd, ht, hs]
  exact ⟨(2^k-1)*s-t, by ring⟩

theorem axis_odd {b k : ℕ} (hk : 1 ≤ k) : Odd (axisNumerator b k) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨(b : ℤ)^(2^j : ℕ) * axisNumerator b j, by rw [axisNumerator]; ring⟩

/-- After clearing the radix, the missing-diagonal difference contains exactly
`k+1` factors of two. The quotient is exhibited as an odd integer. -/
theorem diagonal_numerator {b k : ℕ} (odd : Odd b) (hk : 2 ≤ k) :
    ∃ u : ℤ, Odd u ∧ axisNumerator b k ^ 2 - 1 = 2^(k+1)*u := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨t, ht⟩ := axis_residue odd (show 1 ≤ 2+j by omega)
  let a : ℤ := 1+4*t
  have form : axisNumerator b (2+j) = 4*2^j*a-1 := by
    rw [ht, pow_add, pow_add]; dsimp [a]; ring
  refine ⟨a*(2*2^j*a-1), ?_, ?_⟩
  · apply Odd.mul
    · exact ⟨2*t, by dsimp [a]; ring⟩
    · exact ⟨2^j*a-1, by ring⟩
  · rw [form, pow_succ, pow_add]; ring

private lemma val_odd {z : ℤ} (hz : Odd z) : padicValRat 2 (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (p:=2) (by
    obtain ⟨r, hr⟩ := hz
    rintro ⟨d, hd⟩
    norm_num at hd
    omega)]
  rfl

theorem diagonal_valuation {b k : ℕ} (odd : Odd b) (hk : 2 ≤ k) :
    padicValRat 2 (weightedSum b k ^ 2 - 1 / (b : ℚ)^(2^(k+1) : ℕ)) = k+1 := by
  obtain ⟨u, hu, eqn⟩ := diagonal_numerator odd hk
  have bp : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at odd)
  have bn : (b : ℚ) ≠ 0 := by exact_mod_cast bp.ne'
  have un : (u : ℚ) ≠ 0 := by
    apply Int.cast_ne_zero.mpr
    obtain ⟨r, hr⟩ := hu
    omega
  have eqQ : (axisNumerator b k : ℚ)^2-1 = 2^(k+1)*(u : ℚ) := by exact_mod_cast eqn
  have form : weightedSum b k ^ 2 - 1 / (b : ℚ)^(2^(k+1) : ℕ) =
      (2^(k+1)*(u : ℚ)) / (b : ℚ)^(2^(k+1) : ℕ) := by
    rw [← eqQ, ← clear_axis bp, pow_succ (2 : ℕ), pow_mul, mul_pow]
    field_simp
  have bval : padicValRat 2 (b : ℚ) = 0 :=
    val_odd (show Odd (b : ℤ) by exact_mod_cast odd)
  rw [form, padicValRat.div (mul_ne_zero (by positivity) un) (pow_ne_zero _ bn),
    padicValRat.mul (by positivity) un, padicValRat.pow, padicValRat.pow, val_odd hu, bval]
  norm_num [show padicValRat 2 (2 : ℚ) = 1 from padicValRat.self (p:=2) (by decide)]

end NormalityChecker.ParameterTwoSquare
