module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic

public section
open Nat
namespace NormalityChecker

private lemma factor_two_lift {g t : ℕ} (hg : 1<g) (ht : 0<t) (four : 4∣g-1) (odd : ¬2∣g) :
    (g^t-1).factorization 2 = (g-1).factorization 2 + t.factorization 2 := by
  have gt := one_lt_pow₀ hg ht.ne'
  have hd : (4:ℤ) ∣ ((g-1:ℕ):ℤ) := by exact_mod_cast four
  rw [Int.natCast_sub hg.le,Int.natCast_one] at hd
  have lift := Int.two_pow_sub_pow' (x:=g) (y:=1) t hd (by exact_mod_cast odd)
  have eqn : emultiplicity 2 (g^t-1) = emultiplicity 2 (g-1) + emultiplicity 2 t := by
    rw [← Int.natCast_emultiplicity,← Int.natCast_emultiplicity,← Int.natCast_emultiplicity]
    simpa only [Int.natCast_sub gt.le,Int.natCast_sub hg.le,Int.natCast_pow,Int.natCast_one,Nat.cast_ofNat,one_pow] using lift
  simp only [← Nat.multiplicity_eq_factorization Nat.prime_two]
  rw [← Nat.cast_inj (R:=ℕ∞),Nat.cast_add]
  simpa only [multiplicity_eq_emultiplicity (Nat.sub_ne_zero_of_lt gt),
    multiplicity_eq_emultiplicity (Nat.sub_ne_zero_of_lt hg),multiplicity_eq_emultiplicity ht.ne'] using eqn

private theorem order_bound_of_exponent {b c Q k m : ℕ} (hb : 1<b) (hc : 1<c)
    (hbc : b.Coprime c) (hQ : Q ∣ c^k) (hm : 0<m) (hdiv : c ∣ b^m-1)
    (four : 2∣c → 4∣b^m-1) : Q ≤ (b^m-1)*orderOf (b:ZMod Q) := by
  let g := b^m
  let t := orderOf (b:ZMod Q)
  have hg : 1<g := one_lt_pow₀ hb hm.ne'
  change c∣g-1 at hdiv
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
  · have hpG := hpc.trans hdiv
    have hnot : ¬ p ∣ g := by
      intro h
      have h1 := Nat.dvd_sub h hpG
      rw [Nat.sub_sub_self hg.le] at h1
      exact hp.not_dvd_one h1
    have : Fact p.Prime := ⟨hp⟩
    have lift : (g^t-1).factorization p = (g-1).factorization p+t.factorization p := by
      by_cases two : p=2
      · subst p; exact factor_two_lift hg ht (four hpc) hnot
      · simpa only [one_pow,Nat.multiplicity_eq_factorization hp] using
          Nat.multiplicity_pow_sub_pow (hp.odd_of_ne_two two) hg hpG hnot ht.ne'
    have le := (Nat.factorization_prime_le_iff_dvd hq.ne' (by omega : g^t-1≠0)).mpr hdq p hp
    rw [Nat.factorization_mul (by omega : g-1≠0) ht.ne',Finsupp.add_apply, ← lift]; exact le
  · rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hpc (hp.dvd_of_dvd_pow (h.trans hQ)))]; exact Nat.zero_le _

/-- The classical period bound for a fixed odd support. -/
theorem smooth_order_bound {b c Q k : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c)
    (hbc : b.Coprime c) (hQ : Q ∣ c^k) : Q ≤ (b^c.totient-1)*orderOf (b:ZMod Q) := by
  have hm := Nat.totient_pos.mpr (by omega : 0<c)
  exact order_bound_of_exponent hb hc hbc hQ hm
    ((Nat.modEq_iff_dvd' (one_lt_pow₀ hb hm.ne').le).mp (Nat.ModEq.pow_totient hbc).symm)
    (fun two => False.elim (Nat.not_even_iff_odd.mpr ho (even_iff_two_dvd.mpr two)))

/-- Allow 2 among the denominator primes. Euler's exponent for `c²` also
makes the lifting base congruent to 1 modulo 4 whenever `c` is even. -/
theorem fixed_support_order_bound {b c Q k : ℕ} (hb : 1<b) (hc : 1<c)
    (hbc : b.Coprime c) (hQ : Q ∣ c^k) : Q ≤ (b^(c^2).totient-1)*orderOf (b:ZMod Q) := by
  have hm := Nat.totient_pos.mpr (pow_pos (by omega : 0<c) 2)
  have div := (Nat.modEq_iff_dvd' (one_lt_pow₀ hb hm.ne').le).mp (Nat.ModEq.pow_totient (hbc.pow_right 2)).symm
  exact order_bound_of_exponent hb hc hbc hQ hm ((dvd_pow_self c (by decide : 2≠0)).trans div)
    (fun two => (pow_dvd_pow_of_dvd two 2).trans div)

/-- For a fixed odd denominator parameter coprime to b, the period of b modulo
c^k is at least c^k divided by the fixed integer b^φ(c)-1. -/
theorem stoneham_order_bound {b c : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c) (hbc : b.Coprime c)
    (k : ℕ) : c^k ≤ (b^c.totient-1) * orderOf (b:ZMod (c^k)) :=
  smooth_order_bound hb hc ho hbc (k:=k) dvd_rfl

end NormalityChecker
