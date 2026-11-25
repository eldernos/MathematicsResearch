module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
public import Mathlib.Tactic

/-! Real coefficients, insertion exponents and prime residues for dyadic Gaussian logarithms.
The classification of all strides and the rate optimization are in the companion note. -/

@[expose] public section

namespace NormalityChecker.GaussianLogarithmRelations

local notation "𝓖" => Zsqrtd (-1)

def onePlusI : 𝓖 := ⟨1, 1⟩

/-- The sign, including zero, multiplying the dyadic magnitude of the real coefficient. -/
def realSign (j : ℕ) : ℤ :=
  match j % 8 with
  | 0 | 1 | 7 => 1
  | 3 | 4 | 5 => -1
  | _ => 0

theorem re_pow_onePlusI (j : ℕ) :
    (onePlusI^j).re = (2:ℤ)^(j/2) * realSign j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases h : j < 8
    · interval_cases j <;> decide
    · let m := j-8
      have hm : m < j := by dsimp [m]; omega
      have hj : j = m+8 := by dsimp [m]; omega
      have hs : realSign (m+8) = realSign m := by simp [realSign]
      rw [hj, pow_add, show onePlusI^8 = (⟨16,0⟩ : 𝓖) by decide,
        Zsqrtd.re_mul, ih m hm, hs, show (m+8)/2 = m/2+4 by omega, pow_add]
      change _ * 16 + (-1) * _ * 0 = _
      ring

/-- The two opposite Gaussian phases cancel outside multiples of four.
At j=4q the fourth power gives the negative real phase. -/
theorem opposite_real_coefficients (q r : ℕ) (hr : r < 4) :
    (onePlusI^(4*q+r)).re + ((-onePlusI)^(4*q+r)).re =
      if r = 0 then 2*(-4:ℤ)^q else 0 := by
  have h : onePlusI^4 = ((-4:ℤ) : 𝓖) := by decide
  have h' : (-onePlusI)^4 = ((-4:ℤ) : 𝓖) := by decide
  simp only [pow_add, pow_mul, h, h', ← Int.cast_pow, Zsqrtd.re_mul,
    Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero]
  interval_cases r <;> norm_num [onePlusI, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

/-- Real part of the j-th power of (1+i)/2^t, as a rational. -/
def dyadicRe (t j : ℕ) : ℚ := ((onePlusI^j).re : ℚ) / 2^(t*j)

theorem dyadicRe_eq (t j : ℕ) (ht : 0 < t) :
    dyadicRe t j = (realSign j : ℚ) / 2^(t*j - j/2) := by
  have hj : j/2 ≤ t*j := by
    have := Nat.mul_le_mul_right j ht
    omega
  have he : (2:ℚ)^(t*j) = 2^(t*j-j/2) * 2^(j/2) := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  simp only [dyadicRe, re_pow_onePlusI, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, he]
  field_simp

/-- Exact integer cutoff, also when the binary slope is half-integral. -/
theorem insertion_iff (t j N : ℕ) (ht : 0 < t) :
    t*j - j/2 ≤ N ↔ (2*t-1)*j ≤ 2*N := by
  rw [Nat.sub_mul, one_mul]
  have := Nat.mul_le_mul_right j ht
  rw [Nat.mul_assoc]
  omega

private def mulMatrix (z : 𝓖) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![z.re, -z.im; z.im, z.re]

private theorem mulMatrix_pow (z : 𝓖) (j : ℕ) :
    mulMatrix (z^j) = (mulMatrix z)^j := by
  induction j with
  | zero => simp [mulMatrix, Matrix.one_fin_two]
  | succ j ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp [mulMatrix, Zsqrtd.re_mul, Zsqrtd.im_mul, add_comm, mul_comm]

/-- The real residue is invariant for both odd prime classes modulo four. -/
theorem gaussian_re_frobenius (z : 𝓖) (p j : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (((z^(p*j)).re : ℤ) : ZMod p) = (((z^j).re : ℤ) : ZMod p) := by
  let f := Int.castRingHom (ZMod p)
  have trace_pow (M : Matrix (Fin 2) (Fin 2) ℤ) :
      f ((M^p).trace) = f M.trace := by
    rw [AddMonoidHom.map_trace f, Matrix.map_pow, ZMod.trace_pow_card, ZMod.pow_card,
      ← AddMonoidHom.map_trace]
  have h := trace_pow (mulMatrix (z^j))
  rw [← mulMatrix_pow, ← pow_mul, Nat.mul_comm j p] at h
  simp only [mulMatrix, Matrix.trace_fin_two_of, ← two_mul, map_mul] at h
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast mt (ZMod.natCast_eq_zero_iff 2 p).mp (Nat.not_dvd_of_pos_of_lt (by decide) hp)
  exact mul_left_cancel₀ h2 (by simpa [f] using h)

/-- A prime witness of order exactly 4n in one of the two norm numerators. -/
def normWitness (n numerator p : ℕ) : Prop :=
  p.Prime ∧ p ∣ numerator ∧ 2^(4*n) % p = 1 ∧
    ∀ j : Fin (4*n), j.val ≠ 0 → 2^j.val % p ≠ 1

instance (n numerator p : ℕ) : Decidable (normWitness n numerator p) := by
  unfold normWitness
  infer_instance

set_option maxRecDepth 4096 in
/-- Both norm factors have a primitive prime in every exceptional case
with odd n ≥ 7 and φ(n) < 16. The large-totient argument is in the note. -/
theorem small_primitive_factors :
    [(7,113,29), (9,37,109), (11,397,2113), (13,1613,53), (15,61,1321),
      (21,14449,1429)].Forall (fun (n,p,q) =>
        normWitness n (2^n + 1 - 2^((n+1)/2)) p ∧
        normWitness n (2^n + 1 + 2^((n+1)/2)) q) := by
  simp only [List.Forall, normWitness]
  repeat' apply And.intro
  all_goals norm_num1
  all_goals decide +kernel

/-- Solve the four prime-valuation equations of the surviving norm factors. -/
theorem norm_valuation_system (m a₁ a₂ a₃ a₄ a₆ u b c : ℚ) :
    (a₁+2*a₂+3*a₃+4*a₄+6*a₆+u+3*b+5*c = m ∧
      a₂+a₄+2*a₆ = 0 ∧ a₄+b+2*c = 0 ∧ a₃+a₆ = 0) ↔
    (a₆ = a₁+u+b+c-m ∧ a₂ = -a₄-2*a₆ ∧ a₃ = -a₆ ∧ a₄ = -b-2*c) := by
  constructor <;> rintro ⟨h₂,h₃,h₅,h₇⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

end NormalityChecker.GaussianLogarithmRelations
