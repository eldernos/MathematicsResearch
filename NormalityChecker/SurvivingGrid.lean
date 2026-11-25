module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic

public section

namespace NormalityChecker.SurvivingGrid

/-- The exact return times for a stride `g` which fixes the complementary modulus
and is one modulo the distinguished odd prime. The exponent subtraction truncates at zero. -/
theorem return_iff {p Q g : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hc : p.Coprime Q) (hg : 1 < g) (hp1 : p ∣ g - 1) (hQ1 : Q ∣ g - 1)
    (e k : ℕ) :
    p ^ e * Q ∣ g ^ k - 1 ↔ p ^ (e - (g - 1).factorization p) ∣ k := by
  rcases k with _ | k
  · simp
  have hk : 0 < k + 1 := Nat.succ_pos _
  have hgk := one_lt_pow₀ hg hk.ne'
  have hnot : ¬ p ∣ g := by
    intro h
    have h1 := Nat.dvd_sub h hp1
    rw [Nat.sub_sub_self hg.le] at h1
    exact hp.not_dvd_one h1
  let : Fact p.Prime := ⟨hp⟩
  have lift : (g ^ (k + 1) - 1).factorization p =
      (g - 1).factorization p + (k + 1).factorization p := by
    simpa only [one_pow, Nat.multiplicity_eq_factorization hp] using
      Nat.multiplicity_pow_sub_pow hodd hg hp1 hnot hk.ne'
  have hfix : Q ∣ g ^ (k + 1) - 1 := by
    have hmod := (Nat.modEq_iff_dvd' hg.le).mpr hQ1
    apply (Nat.modEq_iff_dvd' hgk.le).mp
    simpa using hmod.pow (k + 1)
  have hsplit : p ^ e * Q ∣ g ^ (k + 1) - 1 ↔ p ^ e ∣ g ^ (k + 1) - 1 :=
    ⟨fun h => (dvd_mul_right _ _).trans h,
     fun h => (hc.pow_left e).mul_dvd_of_dvd_of_dvd h hfix⟩
  rw [hsplit, hp.pow_dvd_iff_le_factorization (Nat.sub_ne_zero_of_lt hgk),
    hp.pow_dvd_iff_le_factorization hk.ne', lift]
  omega

/-- Multiplicative order, hence the exact number of grid points, at any depth. -/
theorem stride_order {p Q g : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hc : p.Coprime Q) (hg : 1 < g) (hp1 : p ∣ g - 1) (hQ1 : Q ∣ g - 1)
    (e : ℕ) :
    orderOf (g : ZMod (p ^ e * Q)) = p ^ (e - (g - 1).factorization p) := by
  have ret (k : ℕ) : orderOf (g : ZMod (p ^ e * Q)) ∣ k ↔
      p ^ (e - (g - 1).factorization p) ∣ k := by
    have hge : 1 ≤ g ^ k := Nat.one_le_pow _ _ hg.le
    rw [orderOf_dvd_iff_pow_eq_one, ← return_iff hp hodd hc hg hp1 hQ1 e k,
      ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  exact Nat.dvd_antisymm ((ret _).mpr dvd_rfl) ((ret _).mp dvd_rfl)

/-- If the return period equals the number of lifts of a fixed residue, every lift
is visited. This version uses the usual integer representatives of the circle grid. -/
theorem visits_every_lift {g d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hfix : g ≡ 1 [MOD d]) (horder : orderOf (g : ZMod (d * m)) = m)
    {y : ℕ} (hy : y < d * m) (hres : y ≡ 1 [MOD d]) :
    ∃ k < m, g ^ k % (d * m) = y := by
  let rep (k : Fin m) := g ^ (k : ℕ) % (d * m)
  have small (k : Fin m) : rep k < d * m := Nat.mod_lt _ (Nat.mul_pos hd hm)
  have fixed (k : Fin m) : rep k % d = 1 % d := by
    dsimp [rep]
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right d m)]
    simpa only [one_pow, Nat.ModEq] using hfix.pow (k : ℕ)
  let index (k : Fin m) : Fin m :=
    ⟨rep k / d, (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using small k)⟩
  have injective : Function.Injective index := by
    intro i j hij
    have heq : rep i / d = rep j / d := congrArg Fin.val hij
    have same : rep i = rep j := by
      have hi := Nat.mod_add_div (rep i) d
      have hj := Nat.mod_add_div (rep j) d
      rw [fixed i, heq] at hi
      rw [fixed j] at hj
      exact hi.symm.trans hj
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := (g : ZMod (d * m)))
    · simp [Set.mem_Iio, horder]
    · simp [Set.mem_Iio, horder]
    · simpa only [Nat.cast_pow] using
        (ZMod.natCast_eq_natCast_iff _ _ (d * m)).mpr same
  have hj : y / d < m := (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using hy)
  obtain ⟨k, hk⟩ := (Finite.surjective_of_injective injective) ⟨y / d, hj⟩
  refine ⟨k, k.isLt, ?_⟩
  have heq : rep k / d = y / d := congrArg Fin.val hk
  have identity := Nat.mod_add_div (rep k) d
  rw [heq, fixed k, ← hres] at identity
  exact identity.symm.trans (Nat.mod_add_div y d)

end NormalityChecker.SurvivingGrid
