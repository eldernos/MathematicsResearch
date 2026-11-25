module

public import NormalityChecker.ParameterTwoSquareArithmetic
public import Mathlib.NumberTheory.Multiplicity

/-! The zero mass of the symmetric box omitting its corner in every even
dimension, and the exact second order of its positive-index, radix-weighted sum.
This box is the actual square cut on its upper half-shell. -/
@[expose] public section
open Finset
namespace NormalityChecker.ParameterTwoSquare

/-- Summing the geometric letters in a depth-`L` box and removing the origin
leaves a multiple of `2^L` in every even dimension. -/
theorem even_missing_corner_mass (L r : ℕ) :
    ((∑ j ∈ range L, (2 : ZMod (2^L))^j) ^ (2*r) - 1) = 0 := by
  have vanish : (2 : ZMod (2^L))^L = 0 := by exact_mod_cast ZMod.natCast_self (2^L)
  have geom := geom_sum_mul (2 : ZMod (2^L)) L
  rw [vanish, show (2 : ZMod (2^L))-1=1 by ring, mul_one, zero_sub] at geom
  rw [geom, pow_mul]
  simp

/-- After clearing the odd radix and `2^(2*r*k)`, the box of positive-index
tuples with just its last diagonal removed has numerator `A_k^(2*r)-1`.
Its exact order is `k+1+v₂(r)`, including the infinite-order convention at zero. -/
theorem even_missing_corner_order {b k : ℕ} (odd : Odd b) (hk : 2 ≤ k) (r : ℕ) :
    emultiplicity (2 : ℤ) (axisNumerator b k ^ (2*r) - 1) =
      (k+1 : ℕ) + emultiplicity (2 : ℤ) (r : ℤ) := by
  obtain ⟨u, hu, diag⟩ := diagonal_numerator odd hk
  have no {z : ℤ} (h : Odd z) : ¬2 ∣ z := by
    obtain ⟨a, ha⟩ := h
    rintro ⟨v, hv⟩
    omega
  have mod4 : (4 : ℤ) ∣ axisNumerator b k ^ 2 - 1 := by
    rw [diag]
    exact (pow_dvd_pow (2 : ℤ) (show 2 ≤ k+1 by omega)).trans (dvd_mul_right ..)
  have lift := Int.two_pow_sub_pow' (x:=axisNumerator b k ^ 2) (y:=1) r mod4
    (no ((axis_odd (by omega : 1 ≤ k)).pow))
  rw [pow_mul]
  simpa [diag, emultiplicity_mul Int.prime_two, emultiplicity_pow_self_of_prime Int.prime_two,
    emultiplicity_eq_zero.mpr (no hu)] using lift

end NormalityChecker.ParameterTwoSquare
