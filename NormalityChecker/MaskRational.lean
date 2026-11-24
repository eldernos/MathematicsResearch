module

public import NormalityChecker.MaskPeriods

/-! Rational coefficient normalization and finite grid conclusions for unreduced polynomials. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

/-- Split a fixed denominator into a coprime grid and factors absorbed after a fixed delay. -/
theorem split_denominator (b : ℕ) {D : ℕ} (hD : 0<D) :
    ∃ L F l : ℕ, 0<L ∧ b.Coprime L ∧ D=L*F ∧ F∣b^l := by
  induction D using induction_on_primes with
  | zero => omega
  | one => exact ⟨1,1,0,by decide,by simp,by decide,by simp⟩
  | prime_mul p a hp ih =>
    obtain ⟨L,F,l,lp,cop,rfl,div⟩ := ih (Nat.pos_of_mul_pos_left hD)
    by_cases hit : p∣b
    · exact ⟨L,p*F,l+1,lp,cop,by ring,by rw [pow_succ']; exact Nat.mul_dvd_mul hit div⟩
    · exact ⟨p*L,F,l,Nat.mul_pos hp.pos lp,(hp.coprime_iff_not_dvd.mpr hit).symm.mul_right cop,by ring,div⟩

/-- For any chosen clearing denominator, its part prime to b is the grid denominator
in both maximal cases of the integral classification. -/
theorem rational_grid {b t L l : ℕ} (hb : 2≤b) (hL : 0<L) (S : Finset ℕ) (keep : ℕ → Bool)
    (P : ℚ[X]) (G : ℤ[X]) {D : ℤ} (hD : D≠0)
    (eval : ∀ m : ℕ, (sample G m : ℚ) = D*P.eval (m:ℚ)) (clears : D.natAbs ∣ L*b^l)
    (base : t=0 ∨ ∀ p∈S,p∣b) :
    1/(L:ℝ) ≤ liminf (radixDiscrepancy b (maskedValue b S keep P t)) atTop ∧
      ¬ NormalIn b (maskedValue b S keep P t) := by
  apply grid_discrepancy hb hL (weights_growth ..) (weights_supported S keep P t)
  apply grid_of_denominator (l:=l) hb hL (weights_supported S keep P t) _ base
  intro m hm
  exact (coefficient_den hD eval S keep t m hm).trans (Nat.mul_dvd_mul clears (dvd_refl _))

/-- For an arbitrary rational polynomial, positive pole order after cancellation
is the only algebraic hypothesis in the bounded-gap discrepancy theorem. -/
theorem rational_pole_bound {b p s h : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b)
    (P : ℚ[X]) (nz : P≠0) (pole : P.rootMultiplicity 0<s)
    (S : Finset ℕ) (primes : ∀ q∈S,q.Prime) (mem : p∈S) (keep : ℕ → Bool)
    (e : ℕ → ℕ) (inc : StrictMono e) (retain : ∀ᶠ j : ℕ in atTop, keep (p^(e j))=true)
    (gap : ∀ᶠ j : ℕ in atTop, e (j+1) ≤ e j+h) :
    limsup (radixDiscrepancy b (maskedValue b S keep P s)) atTop ≤ 1-1/((p:ℝ)^h-1) := by
  let r := P.rootMultiplicity 0
  obtain ⟨Q,fac,unit⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd nz 0
  simp only [map_zero,sub_zero] at fac unit
  change P=X^r*Q at fac
  have q0 : Q.eval 0≠0 := by simpa [X_dvd_iff,coeff_zero_eq_eval_zero] using unit
  rw [fac,show s=r+(s-r) by change r<s at pole; omega,masked_cancel]
  exact bounded_gap_discrepancy hb hp off (Nat.sub_pos_of_lt pole) q0 S primes mem keep e inc retain gap

/-- Every rational polynomial in either integral-classification maximal case
is nonnormal on every mask; some positive reciprocal grid gap persists. -/
theorem rational_boundary {b s : ℕ} (hb : 2≤b) (S : Finset ℕ) (keep : ℕ → Bool)
    (P : ℚ[X]) (nz : P≠0) (cases : s≤P.rootMultiplicity 0 ∨ ∀ p∈S,p∣b) :
    ∃ L : ℕ, 0<L ∧ b.Coprime L ∧
      1/(L:ℝ) ≤ liminf (radixDiscrepancy b (maskedValue b S keep P s)) atTop ∧
      ¬ NormalIn b (maskedValue b S keep P s) := by
  have grid (Q : ℚ[X]) (t : ℕ) (base : t=0 ∨ ∀ p∈S,p∣b) :
      ∃ L : ℕ, 0<L ∧ b.Coprime L ∧
        1/(L:ℝ) ≤ liminf (radixDiscrepancy b (maskedValue b S keep Q t)) atTop ∧
          ¬NormalIn b (maskedValue b S keep Q t) := by
    obtain ⟨D,G,hd,eval⟩ := normalize Q
    obtain ⟨L,F,l,lp,cop,split,div⟩ := split_denominator b (Int.natAbs_pos.mpr hd)
    exact ⟨L,lp,cop,rational_grid hb lp S keep Q G hd eval
      (split ▸ Nat.mul_dvd_mul_left L div) base⟩
  rcases cases with le|base
  · obtain ⟨G,fac,_⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd nz 0
    simp only [map_zero,sub_zero] at fac
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le le
    rw [hj,pow_add,mul_assoc] at fac
    have he := masked_cancel b s 0 S keep (X^j*G)
    simp only [Nat.add_zero] at he
    rw [fac,he]; exact grid _ _ (Or.inl rfl)
  · exact grid _ _ (Or.inr base)

end NormalityChecker.PolynomialMasks
