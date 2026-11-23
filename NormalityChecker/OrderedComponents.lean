module

public import NormalityChecker.PrimeCancellation
public import NormalityChecker.Resonance

public section

open Finset Nat

namespace NormalityChecker

/-- The pair `(m,j)` labels the positive term numbered `m * 3^j`.
The target uses zero-based indices for the logarithm series. -/
private def componentIndices : ({m : ℕ // ¬ 3 ∣ m} × ℕ) ≃ ℕ where
  toFun v := 3 ^ v.2 * v.1.1 - 1
  invFun n := (⟨ordCompl[3] (n+1), not_dvd_ordCompl prime_three (by omega)⟩, (n+1).factorization 3)
  left_inv := by
    rintro ⟨⟨m, hm⟩, j⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    have h : 0 < 3^j*m := by positivity
    simp only [Nat.sub_add_cancel h, Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨ordCompl_pow_mul_of_not_dvd j prime_three hm, by
      rw [factorization_mul (by positivity) hm0, Finsupp.add_apply,
        factorization_pow_self prime_three, factorization_eq_zero_of_not_dvd hm, add_zero]⟩
  right_inv := by
    intro n
    change ordProj[3] (n+1) * ordCompl[3] (n+1) - 1 = n
    rw [ordProj_mul_ordCompl_eq_self]; omega

/-- Grouping positive indices by the power of three dividing them recovers exactly log 2. -/
theorem hasSum_components_logTwo :
    HasSum (fun m : {m : ℕ // ¬ 3 ∣ m} => component m.1) (Real.log 2) := by
  let F (v : {m : ℕ // ¬ 3 ∣ m} × ℕ) :=
    (1/2 : ℝ)^(v.1.1 * 3^v.2) / ((v.1.1 : ℝ)*3^v.2)
  have H : HasSum F (Real.log 2) := by
    have H' := componentIndices.hasSum_iff.mpr hasSum_logTwo
    convert H' using 1
    symm
    funext v
    rcases v with ⟨⟨m,hm⟩,j⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    have h : 0 < 3^j*m := by positivity
    change (1/2:ℝ)^((3^j*m-1)+1) / ((↑(3^j*m-1):ℝ)+1) = _
    have e : (↑(3^j*m-1):ℝ)+1 = ((3^j*m : ℕ):ℝ) := by exact_mod_cast Nat.sub_add_cancel h
    rw [e, Nat.sub_add_cancel h, mul_comm (3^j) m]
    simp [F]
  exact H.prod_fiberwise fun m => (H.summable.prod_factor m).hasSum

/-- The arithmetic nonvanishing part of the proposed classification of ordered finite
Stoneham sums. Any choice of odd signed numerators works, including the signed powers
of three on every interval of the proposed resonance function. -/
theorem ordered_phase_ne_zero {K : ℕ} (hK : 0 < K) (f : ℕ → ℤ) (hf : ∀ m, Odd (f m)) :
    (∑ m ∈ (Icc 1 K).filter (fun m => ¬ 3 ∣ m), (f m : ℚ) / m) ≠ 0 := by
  let S := (Icc 1 K).filter (fun m => ¬ 3 ∣ m)
  let L := lcmUpto K
  let a := Nat.log 2 K
  let d := 2^a
  have hdpos : 0 < d := pow_pos (by decide) _
  have hmem : d ∈ S := by
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨hdpos, Nat.pow_log_le_self _ hK.ne'⟩,
      fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)⟩
  have hdvd (m : ℕ) (hm : m ∈ S) : m ∣ L :=
    Finset.dvd_lcm (f := id) (mem_filter.mp hm).1
  have hdL := hdvd d hmem
  have hodd : ¬ 2 ∣ L / d := by
    rintro ⟨b,hb⟩
    have he : 2^(a+1) ∣ L := ⟨b, by
      calc
        L = L / d * d := (Nat.div_mul_cancel hdL).symm
        _ = _ := by rw [hb, pow_succ]; dsimp [d]; ring⟩
    have he' := (Nat.prime_two.pow_dvd_iff_le_factorization (lcmUpto_ne_zero K)).mp he
    rw [factorization_lcmUpto _ Nat.prime_two] at he'
    exact (Nat.not_succ_le_self _) he'
  have heven (m : ℕ) (hm : m ∈ S) (hne : m ≠ d) : 2 ∣ L/m := by
    by_contra h
    have hcop := (Nat.prime_two.coprime_iff_not_dvd.mpr h).pow_left a
    have hdm : d ∣ m := hcop.dvd_of_dvd_mul_left (by rw [Nat.div_mul_cancel (hdvd m hm)]; exact hdL)
    have hlt : K < 2*d := by simpa [d, a, pow_succ, mul_comm] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) K
    obtain ⟨hm₁, hmK⟩ := mem_Icc.mp (mem_filter.mp hm).1
    exact hne (Nat.eq_of_dvd_of_lt_two_mul (by omega) hdm (hmK.trans_lt hlt))
  let w (m : ℕ) : ℕ := L / m
  let u (m : ℕ) : ℤ := f m * (w m : ℤ)
  intro hzero
  have he : (∑ m ∈ S, u m) = 0 := by
    have e : (∑ m ∈ S, (u m : ℚ)) = (L:ℚ) * ∑ m ∈ S, (f m : ℚ)/m := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      have hmpos := (mem_Icc.mp (mem_filter.mp hm).1).1
      simp only [u, Int.cast_mul, Int.cast_natCast]
      field_simp
      have e := congrArg (fun z : ℕ => (z : ℚ)) (Nat.div_mul_cancel (hdvd m hm))
      simp only [Nat.cast_mul] at e
      linear_combination (f m : ℚ) * e
    rw [hzero, mul_zero] at e
    exact_mod_cast e
  have e : (∑ m ∈ S, (u m : ZMod 2)) = 0 := by
    rw [← Int.cast_sum, he, Int.cast_zero]
  rw [sum_eq_single_of_mem d hmem] at e
  · have hn : (f d : ZMod 2) ≠ 0 := by
      obtain ⟨b,hb⟩ := hf d
      simp [hb, show (2 : ZMod 2) = 0 by decide]
    have hw := (ZMod.natCast_eq_zero_iff (L/d) 2).not.mpr hodd
    exact (mul_ne_zero hn hw) (by simpa only [u, Int.cast_mul, Int.cast_natCast] using e)
  · intro m hm hne
    simp only [u, Int.cast_mul, Int.cast_natCast]
    rw [(ZMod.natCast_eq_zero_iff (w m) 2).mpr (heven m hm hne), mul_zero]

end NormalityChecker
