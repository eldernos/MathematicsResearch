module

public import NormalityChecker.Correlations

/-! Finite transfers for divisor coefficients written as powers of two times odd marks.
The arithmetic distribution of the marks is treated in the accompanying research note. -/

@[expose] public section

open Finset

namespace NormalityChecker.ErdosBorweinArrivals

/-- A coefficient with valuation at least its raw offset contributes an integral
turn. Otherwise its denominator is determined by the difference. -/
theorem source_phase (h : ℤ) (u v j : ℕ) :
    phase ((h : ℝ) * ((2 : ℝ)^v * u) / 2^j) =
      if j ≤ v then 1 else phase ((h : ℝ) * u / 2^(j-v)) := by
  split_ifs with hj
  · rw [← Nat.sub_add_cancel hj, pow_add]
    have cancel : (h : ℝ) * ((2 : ℝ)^(v-j) * 2^j * u) / 2^j =
        ((h * 2^(v-j) * (u : ℤ) : ℤ) : ℝ) := by
      push_cast
      field_simp
    rw [cancel]
    simpa [phase, mul_comm] using
      Complex.exp_int_mul_two_pi_mul_I (h * 2^(v-j) * (u : ℤ))
  · have powers : (2 : ℝ)^j = 2^v * 2^(j-v) := by
      rw [← pow_add]; congr 1; omega
    congr 1
    rw [powers]
    field_simp

/-- Collect any additive mark at the displaced source location. -/
def arrival {α : Type*} [AddCommMonoid α] (sources : Finset ℕ)
    (location : ℕ → ℤ) (mark : ℕ → α) (t : ℤ) : α :=
  ∑ m ∈ sources, if location m = t then mark m else 0

/-- Averaging one denominator level counts each source exactly once when its
displaced position belongs to the translated window. Complex marks are allowed. -/
theorem arrival_sum {α : Type*} [AddCommMonoid α] (sources : Finset ℕ)
    (window : Finset ℤ) (location : ℕ → ℤ) (mark : ℕ → α) (d : ℤ) :
    ∑ n ∈ window, arrival sources location mark (n+d) =
      ∑ m ∈ sources, if location m - d ∈ window then mark m else 0 := by
  unfold arrival
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  have criterion (n : ℤ) : location m = n+d ↔ n = location m-d := by omega
  simp_rw [criterion]
  simp

/-- Mean error after restoring discarded denominator levels. Each translated
column has mass at most `M`; the loss is proportional to the sum of its dyadic
weights. The retained phase can depend arbitrarily on the row. -/
theorem tail_phase_bound (window : Finset ℤ) (levels : Finset ℕ)
    (base coefficient : ℤ → ℝ) (h : ℤ) (M : ℝ)
    (nonneg : ∀ t, 0 ≤ coefficient t)
    (mass : ∀ d ∈ levels, ∑ n ∈ window, coefficient (n+d) ≤ M) :
    ‖(∑ n ∈ window, phase (h * (base n +
          ∑ d ∈ levels, coefficient (n+d) / (2 : ℝ)^d))) -
        ∑ n ∈ window, phase (h * base n)‖ ≤
      (2 * Real.pi * |(h : ℝ)|) * (M * ∑ d ∈ levels, 1 / (2 : ℝ)^d) := by
  let tail (n : ℤ) := ∑ d ∈ levels, coefficient (n+d) / (2 : ℝ)^d
  have nonnegTail (n : ℤ) : 0 ≤ tail n :=
    sum_nonneg fun d _ => div_nonneg (nonneg _) (by positivity)
  have row (n : ℤ) : ‖phase (h * (base n + tail n)) - phase (h * base n)‖ ≤
      (2 * Real.pi * |(h : ℝ)|) * tail n := by
    have bound := phase_sub_le ((h : ℝ) * (base n + tail n)) (h * base n)
    rwa [show (h : ℝ) * (base n + tail n) - h * base n = h * tail n by ring,
      abs_mul, abs_of_nonneg (nonnegTail n), ← mul_assoc] at bound
  have budget : ∑ n ∈ window, tail n ≤ M * ∑ d ∈ levels, 1 / (2 : ℝ)^d := by
    unfold tail
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro d hd
    rw [← sum_div, mul_one_div]
    exact div_le_div_of_nonneg_right (mass d hd) (by positivity)
  rw [← sum_sub_distrib]
  exact (norm_sum_le ..).trans <| (sum_le_sum (fun n _ => row n)).trans <|
    (mul_sum ..).ge.trans (mul_le_mul_of_nonneg_left budget (by positivity))

/-- On a grid of size `2*q`, adding a carry below `s` can create a one
only in the last `s` cells of the lower half. It can erase a one only
in the last `s` cells of the upper half. -/
theorem one_bit_carry {q s r c : ℕ} (hr : r < 2*q) (hs : s ≤ q) (hc : c < s) :
    (r < q → q ≤ (r+c) % (2*q) → q-s ≤ r) ∧
    (q ≤ r → (r+c) % (2*q) < q → 2*q-s ≤ r ∧ r < 2*q) := by
  constructor
  · intro lower gained
    rw [Nat.mod_eq_of_lt (by omega)] at gained
    omega
  · intro upper lost
    refine ⟨?_, hr⟩
    by_contra! far
    rw [Nat.mod_eq_of_lt (by omega)] at lost
    omega

end NormalityChecker.ErdosBorweinArrivals
