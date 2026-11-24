module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic

public section
open Nat
namespace NormalityChecker

/-- Every divisor `Q` of a power of a fixed odd `c` has period at least
`Q / (b^φ(c)-1)`. The prime exponents in `Q` can vary independently. -/
theorem smooth_order_bound {b c Q k : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c)
    (hbc : b.Coprime c) (hQ : Q ∣ c^k) : Q ≤ (b^c.totient-1)*orderOf (b:ZMod Q) := by
  let g := b^c.totient
  let t := orderOf (b:ZMod Q)
  have hg : 1<g := one_lt_pow₀ hb (Nat.totient_pos.mpr (by omega)).ne'
  have hdiv : c ∣ g-1 := (Nat.modEq_iff_dvd' hg.le).mp (Nat.ModEq.pow_totient hbc).symm
  have hq : 0<Q := Nat.pos_of_dvd_of_pos hQ (pow_pos (by omega) _)
  have cop := Nat.Coprime.of_dvd_right hQ (hbc.pow_right k)
  have ht : 0<t := by
    apply orderOf_pos_iff.mpr
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨Q.totient, Nat.totient_pos.mpr hq, by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ Q).mpr (Nat.ModEq.pow_totient cop)⟩
  have hgt : 1<g^t := one_lt_pow₀ hg ht.ne'
  have he : (g:ZMod Q)^t=1 := by
    simp only [g,Nat.cast_pow]; rw [pow_right_comm,pow_orderOf_eq_one,one_pow]
  have hdq : Q ∣ g^t-1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub hgt.le,Nat.cast_pow,Nat.cast_one,he,sub_self]
  apply Nat.le_of_dvd (Nat.mul_pos (by omega : 0<g-1) ht)
  apply (Nat.factorization_prime_le_iff_dvd hq.ne' (Nat.mul_ne_zero (by omega : g-1≠0) ht.ne')).mp
  intro p hp
  by_cases hpc : p ∣ c
  · have hpodd : Odd p := hp.odd_of_ne_two (by rintro rfl; exact Nat.not_even_iff_odd.mpr ho (even_iff_two_dvd.mpr hpc))
    have hpG := hpc.trans hdiv
    have hnot : ¬ p ∣ g := by
      intro h
      have h1 := Nat.dvd_sub h hpG
      rw [Nat.sub_sub_self hg.le] at h1
      exact hp.not_dvd_one h1
    have : Fact p.Prime := ⟨hp⟩
    have lift := Nat.multiplicity_pow_sub_pow hpodd hg hpG hnot ht.ne'
    simp only [one_pow,Nat.multiplicity_eq_factorization hp] at lift
    have le := (Nat.factorization_prime_le_iff_dvd hq.ne' (by omega : g^t-1≠0)).mpr hdq p hp
    rw [Nat.factorization_mul (by omega : g-1≠0) ht.ne',Finsupp.add_apply, ← lift]; exact le
  · rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hpc (hp.dvd_of_dvd_pow (h.trans hQ)))]; exact Nat.zero_le _

/-- For a fixed odd denominator parameter coprime to b, the period of b modulo
c^k is at least c^k divided by the fixed integer b^φ(c)-1. -/
theorem stoneham_order_bound {b c : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c) (hbc : b.Coprime c)
    (k : ℕ) : c^k ≤ (b^c.totient-1) * orderOf (b:ZMod (c^k)) :=
  smooth_order_bound hb hc ho hbc (k:=k) dvd_rfl

end NormalityChecker
