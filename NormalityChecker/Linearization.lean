module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Tactic

public section
namespace NormalityChecker

/-- The stride L = 2·3^s lifts 1 by exactly s+1 powers of three. -/
theorem stride_lift (s : ℕ) : ∃ c : ℕ, c % 3 = 1 ∧
    2^(2*3^s) = 1 + 3^(s+1)*c := by
  induction s with
  | zero => exact ⟨1, rfl, rfl⟩
  | succ s ih =>
    obtain ⟨c,hc,he⟩ := ih
    let d := 3^s*c
    refine ⟨c*(1+3*d+3*d^2), by simp [Nat.add_mod, Nat.mul_mod, hc], ?_⟩
    rw [show 2*3^(s+1) = (2*3^s)*3 by ring, pow_mul, he]
    dsimp [d]; ring

/-- Linearization at any modulus up to the square of the lifted power. -/
theorem stride_linearization (s k : ℕ) (hk : k ≤ 2*(s+1)) :
    ∃ c : ℕ, c % 3 = 1 ∧ ∀ t : ℕ,
      2^((2*3^s)*t) ≡ 1+t*c*3^(s+1) [MOD 3^k] := by
  obtain ⟨c,hc,he⟩ := stride_lift s
  refine ⟨c,hc,fun t => ?_⟩
  let x : ZMod (3^k) := (c:ZMod (3^k)) * 3^(s+1)
  have hx : x*x = 0 := by
    have hd := pow_dvd_pow 3 hk
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at hz
    rw [mul_comm 2, pow_mul] at hz
    calc
      _ = (c:ZMod (3^k))^2 * (3^(s+1))^2 := by dsimp [x]; ring
      _ = 0 := by rw [hz,mul_zero]
  have hh : (1+x)^t = 1 + (t:ZMod (3^k))*x := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ,ih,Nat.cast_succ]
      linear_combination (t:ZMod (3^k))*hx
  rw [pow_mul, he, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  simpa [x, mul_comm, mul_assoc, mul_left_comm] using hh

/-- The chosen stride works for even and odd k, including k = 1. -/
theorem half_stride_linearization {k : ℕ} (hk : 0 < k) :
    let r := (k+1)/2
    ∃ c : ℕ, c % 3 = 1 ∧ ∀ t : ℕ,
      2^((2*3^(r-1))*t) ≡ 1+t*c*3^r [MOD 3^k] := by
  dsimp
  simpa only [show (k+1)/2-1+1 = (k+1)/2 by omega] using
    stride_linearization ((k+1)/2-1) k (by omega)

/-- Distinct powers within a full period give distinct unit residues. -/
theorem orderOf_two_three_pow (s : ℕ) :
    orderOf (2 : ZMod (3^(s+1))) = 2*3^s := by
  have he : orderOf ((2 : ZMod (3^(s+1)))^2) = 3^s := by
    convert ZMod.orderOf_one_add_prime Nat.prime_three (by decide) s using 2
    norm_num
  have hd : 3 ∣ 3^(s+1) := dvd_pow_self _ (by omega)
  let f := ZMod.castHom hd (ZMod 3)
  have h₂ : 2 ∣ orderOf (2 : ZMod (3^(s+1))) := by
    have h := orderOf_map_dvd f.toMonoidHom (2 : ZMod (3^(s+1)))
    have ho : orderOf (2 : ZMod 3) = 2 := by
      apply orderOf_eq_prime <;> decide
    change orderOf (f 2) ∣ _ at h
    rwa [map_ofNat, ho] at h
  rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) h₂] at he
  omega
end NormalityChecker
