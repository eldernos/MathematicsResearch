module

public import NormalityChecker.ResonantRadix
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-! A bounded upper denominator singles out one class of normalized integer
radices exactly on the matching valuation stratum. Write `k=j+1`, so the
precision condition `j=s+H+t` means `t=k-1-s-H`. -/
@[expose] public noncomputable section
open NormalityChecker.ParameterTwoQuadratic
namespace NormalityChecker.ResonantRadix

private abbrev radius (m : ℕ) : ℝ := ((2 : ℝ)^m)⁻¹

private theorem radius_lt {s t : ℕ} (h : s < t) : radius t < radius s := by
  unfold radius
  exact (inv_lt_inv₀ (by positivity) (by positivity)).mpr (pow_lt_pow_right₀ (by norm_num) h)

private lemma nat_norm {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℚ_[2])‖ = radius (multiplicity 2 n) := by
  rw [Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr hn), Padic.valuation_natCast]
  simp [radius]

private lemma radius_inj {s t : ℕ} : radius s = radius t ↔ s = t := by
  refine ⟨fun h => ?_, congrArg radius⟩
  rcases lt_trichotomy s t with h' | h' | h'
  · exact False.elim ((radius_lt h').ne h.symm)
  · exact h'
  · exact False.elim ((radius_lt h').ne h)

private theorem stratum_iff {b s : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    multiplicity 2 (b^2-1) = s+1 ↔ ‖slope b‖ = radius s := by
  have hb2 : 1 < b^2 := by nlinarith
  have e : ((b^2 - 1 : ℕ) : ℚ_[2]) = (b : ℚ_[2])^2 - 1 := by
    push_cast [Nat.cast_sub hb2.le]; rfl
  rw [slope_norm hb odd, delta_zero_norm odd, ← e, nat_norm (by omega : b^2-1 ≠ 0)]
  have step : radius (s+1) = radius s / 2 := by simp [radius, pow_succ]; ring
  rw [← radius_inj, step]
  constructor <;> intro h <;> linarith

private theorem norm_shifted_phase {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    ‖kappa b 1 (-2) + 1‖ = ‖slope b‖ := by
  obtain ⟨hm, _, hk⟩ := radix_parameter hb odd
  have hz : (0 : ℚ_[2]) ∈ quarterBall := by simp [Metric.mem_closedBall]
  simpa [hk, phaseSeries] using phase_isometry hm hz

private lemma threshold {b n j s H t : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hs : ‖slope b‖ = radius s)
    (prec : j = s+H+t) (mid : 3*2^j ≤ n) (hi : n < 2^(j+2)) :
    («prefix» b n 1 (-2) 0).den ≤ 2^H ↔
      ‖kappa b 1 (-2) + 1 - ((j+2 : ℕ) : ℚ_[2])‖ ≤ radius t := by
  have formula := upper_denominator hb odd mid hi 1 (-2) 0 (by decide)
  have d : ‖((j + 1 : ℕ) : ℚ_[2]) - kappa b 1 (-2)‖ =
      ‖kappa b 1 (-2) + 1 - ((j+2 : ℕ) : ℚ_[2])‖ := by
    rw [norm_sub_rev]; congr 1; push_cast; ring
  simp only [Int.cast_one, mul_one, norm_mul, hs, d] at formula
  rw [show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p:=2)] at formula
  have factor : (2 : ℝ)^(j+1) * (2⁻¹ * radius s) = 2^H * 2^t := by
    rw [prec, pow_succ, pow_add, pow_add]; unfold radius; field_simp
  rw [← mul_assoc, factor] at formula
  have e : ((«prefix» b n 1 (-2) 0).den ≤ 2^H) ↔
      ((«prefix» b n 1 (-2) 0).den : ℝ) ≤ (2 : ℝ)^H := by exact_mod_cast Iff.rfl
  rw [e, formula, max_le_iff, and_iff_right (one_le_pow₀ (by norm_num)), mul_assoc,
    mul_le_iff_le_one_right (by positivity), mul_comm]
  exact (le_div_iff₀ (by positivity)).symm.trans (by simp [radius])

/-- If any radix on the stratum has a bounded upper denominator at precision
`t > s`, the binary valuation of the target `k+1` must equal `s`. -/
theorem target_valuation_of_hit {b n j s H t : ℕ} (hb : 3 ≤ b) (odd : Odd b)
    (hs : multiplicity 2 (b^2-1) = s+1) (prec : j = s+H+t) (ht : s < t)
    (mid : 3*2^j ≤ n) (hi : n < 2^(j+2)) (hit : («prefix» b n 1 (-2) 0).den ≤ 2^H) :
    multiplicity 2 (j+2) = s := by
  have normS := (stratum_iff hb odd).mp hs
  have near := (threshold hb odd normS prec mid hi).mp hit
  have normK := (norm_shifted_phase hb odd).trans normS
  have equal := Padic.norm_eq_of_norm_sub_lt_left (near.trans_lt ((radius_lt ht).trans_eq normK.symm))
  exact radius_inj.mp (by rw [← nat_norm (by omega : j+2 ≠ 0), ← normK]; exact equal.symm)

private lemma close_iff_modEq (v w : ℤ) (t : ℕ) :
    ‖(v : ℚ_[2]) - w‖ ≤ radius t ↔ v ≡ w [ZMOD (2 : ℤ)^t] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd, ← Int.cast_sub]
  simpa [radius] using Padic.norm_int_le_pow_iff_dvd (p:=2) (v-w) t

private lemma fourth_dvd {t : ℕ} (ht : 2 ≤ t) : (4 : ℤ) ∣ 2^t :=
  pow_dvd_pow (2 : ℤ) ht

private lemma signed_modEq {b r t : ℕ} (hr : r % 4 = 1) (ht : 2 ≤ t) :
    ((if b % 4 = 1 then (b : ℤ) else -b) ≡ r [ZMOD (2 : ℤ)^t]) ↔
      ((b : ℤ) ≡ r [ZMOD (2 : ℤ)^t] ∨ (b : ℤ) ≡ -r [ZMOD (2 : ℤ)^t]) := by
  have left (h : (b : ℤ) ≡ r [ZMOD (2 : ℤ)^t]) : b % 4 = 1 := by
    have eq4 := (h.of_dvd (fourth_dvd ht)).eq
    omega
  have right (h : (b : ℤ) ≡ -r [ZMOD (2 : ℤ)^t]) : b % 4 ≠ 1 := by
    have eq4 := (h.of_dvd (fourth_dvd ht)).eq
    omega
  split_ifs with h
  · exact ⟨Or.inl, fun forks => forks.elim id (fun n => False.elim (right n h))⟩
  · have neg : (-(b : ℤ) ≡ r [ZMOD (2 : ℤ)^t]) ↔ (b : ℤ) ≡ -r [ZMOD (2 : ℤ)^t] := by
      simpa only [neg_neg] using (Int.neg_modEq_neg (a := (b : ℤ)) (b := -(r : ℤ))
        (n := (2 : ℤ)^t))
    rw [neg]
    exact ⟨Or.inr, fun forks => forks.elim (fun n => False.elim (h (left n))) id⟩

private lemma slope_norm_signed {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) :
    ‖slope b‖ = ‖signedRadix b - 1‖ := by
  obtain ⟨mb, eb, _⟩ := radix_parameter hb odd
  have hz : (0 : ℚ_[2]) ∈ quarterBall := by simp [Metric.mem_closedBall]
  have negm : -slope b ∈ quarterBall := by simpa [Metric.mem_closedBall] using mb
  simpa [eb] using (exp_isometry negm hz).symm

/-- The matching stratum admits precisely one normalized residue class.
`r < 2^t`, `r ≡ 1 mod 4` and `v₂(r−1)=s`. The exact iff applies on the entire
upper shell. The sign test gives the two opposite classes of ordinary radices. -/
theorem resonant_residue {j s H t : ℕ} (hs : 2 ≤ s) (prec : j = s+H+t) (ht : s < t)
    (target : multiplicity 2 (j+2) = s) :
    ∃ r : ℕ, r < 2^t ∧ r % 4 = 1 ∧ ‖(r : ℚ_[2])-1‖ = ((2 : ℝ)^s)⁻¹ ∧
      (¬ ((r : ℤ) ≡ -r [ZMOD (2 : ℤ)^t])) ∧
      ∀ {b n : ℕ}, 3 ≤ b → Odd b → 3*2^j ≤ n → n < 2^(j+2) →
        ((multiplicity 2 (b^2-1) = s+1 ∧ («prefix» b n 1 (-2) 0).den ≤ 2^H) ↔
          ((b : ℤ) ≡ r [ZMOD (2 : ℤ)^t] ∨ (b : ℤ) ≡ -r [ZMOD (2 : ℤ)^t])) := by
  let z : ℚ_[2] := (j+2 : ℕ)
  have nz : ‖z‖ = radius s := (nat_norm (by omega : j+2 ≠ 0)).trans (congrArg radius target)
  have small : radius s ≤ 1/4 := by
    calc
      radius s ≤ radius 2 := by
        rcases hs.eq_or_lt with h | h
        · rw [h]
        · exact (radius_lt h).le
      _ = _ := by norm_num [radius]
  have mz : z ∈ quarterBall := by simpa [Metric.mem_closedBall] using nz.trans_le small
  obtain ⟨u, _, nu, dist⟩ := radix_center mz
  have unit_bound : ‖u‖ ≤ 1 := by
    simpa using (Padic.nonarchimedean (u-1) 1).trans
      (max_le ((nu.trans nz).le.trans (small.trans (by norm_num))) (by simp))
  let U : ℤ_[2] := ⟨u, unit_bound⟩
  let r := U.appr t
  have near : ‖(r : ℚ_[2]) - u‖ ≤ radius t := by
    rw [norm_sub_rev]
    change ‖U - U.appr t‖ ≤ radius t
    simpa only [radius, Nat.cast_ofNat, zpow_neg, zpow_natCast] using
      ((U - U.appr t).norm_le_pow_iff_mem_span_pow t).mpr (U.appr_spec t)
  have nr : ‖(r : ℚ_[2]) - 1‖ = radius s := by
    apply Eq.trans _ (nu.trans nz)
    apply Padic.norm_eq_of_norm_sub_lt_right
    rw [sub_sub_sub_cancel_right]
    exact near.trans_lt ((radius_lt ht).trans_eq (nu.trans nz).symm)
  have mod4 : (r : ℤ) ≡ 1 [ZMOD (2 : ℤ)^2] :=
    (close_iff_modEq r 1 2).mp (by norm_num [radius] at ⊢; simpa using nr.le.trans small)
  have hr : r % 4 = 1 := by change (r : ℤ) % 4 = 1 % 4 at mod4; omega
  have ht2 := hs.trans ht.le
  refine ⟨r, U.appr_lt t, hr, nr, fun h => ?_, ?_⟩
  · have eq4 := (h.of_dvd (fourth_dvd ht2)).eq
    omega
  intro b n hb odd mid hi
  rw [← signed_modEq hr ht2, ← close_iff_modEq]
  have balls := IsUltrametricDist.closedBall_eq_of_mem (x:=u) (y:=(r : ℚ_[2]))
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using near)
  have eqv := Set.ext_iff.mp balls (signedRadix b)
  simp only [Metric.mem_closedBall, dist_eq_norm] at eqv
  have scast : ((if b % 4 = 1 then (b : ℤ) else -b : ℤ) : ℚ_[2]) = signedRadix b := by
    simp [signedRadix, apply_ite (fun a : ℤ => (a : ℚ_[2]))]
  rw [scast, Int.cast_natCast, ← eqv]
  constructor
  · rintro ⟨str, hit⟩
    rw [← dist hb odd]
    exact (threshold hb odd ((stratum_iff hb odd).mp str) prec mid hi).mp hit
  · intro h
    have normS : ‖slope b‖ = radius s := by
      rw [slope_norm_signed hb odd, ← nu.trans nz]
      apply Padic.norm_eq_of_norm_sub_lt_right
      rw [sub_sub_sub_cancel_right]
      exact h.trans_lt ((radius_lt ht).trans_eq (nu.trans nz).symm)
    exact ⟨(stratum_iff hb odd).mpr normS, (threshold hb odd normS prec mid hi).mpr
      ((dist hb odd).symm ▸ h)⟩

end NormalityChecker.ResonantRadix
