module

public import NormalityChecker.CompositePolynomialStatements
public import NormalityChecker.StonehamPolynomial

/-! Polynomial normality for a composite parameter with one stabilizing prime divisor. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

/-- Convergence to a p-adic unit gives eventual equality at every finite precision. -/
theorem stablePowers_of_unitPowerLimit {b c p : ℕ} [hp : Fact p.Prime]
    (h : StonehamStatements.UnitPowerLimit b c p) : StablePowers b c p := by
  obtain ⟨w, hw, conv⟩ := h
  have nw : w ≠ 0 := by intro zero; simp [zero] at hw
  have forward : Tendsto (fun j : ℕ => (b : ℚ_[p])^(c^j)) atTop (𝓝 w⁻¹) := by
    simpa only [inv_pow, inv_inv] using conv.inv₀ nw
  intro L
  have positive : 0 < (p : ℝ)^(-(L : ℤ)) := zpow_pos (by exact_mod_cast hp.out.pos) _
  obtain ⟨N, close⟩ := Metric.cauchySeq_iff.mp forward.cauchySeq _ positive
  refine ⟨N, fun j k hj hk => ?_⟩
  have bound := (close k hk j hj).le
  rw [dist_eq_norm] at bound
  let difference : ℤ := (b : ℤ)^(c^k) - (b : ℤ)^(c^j)
  have div := (Padic.norm_int_le_pow_iff_dvd (p:=p) difference L).mp (by
    simpa only [difference, Int.cast_sub, Int.cast_pow, Int.cast_natCast] using bound)
  have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd difference (p^L)).mpr (by exact_mod_cast div)
  simpa [difference, sub_eq_zero] using zero

/-- At an even parameter, Euler's theorem makes every sufficiently late power of an odd
radix equal to one modulo any prescribed power of two. -/
theorem stablePowers_two {b c : ℕ} (even : Even c) (cop : b.Coprime c) :
    StablePowers b c 2 := by
  have two : 2 ∣ c := even_iff_two_dvd.mp even
  have unit := cop.coprime_dvd_right two
  intro L
  have one (j : ℕ) (hj : L ≤ j) : (b : ZMod (2^L))^(c^j) = 1 := by
    by_cases zero : L = 0
    · subst L; change (_ : ZMod 1) = _; exact Subsingleton.elim ..
    have euler : (b : ZMod (2^L))^(2^L).totient = 1 := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ (2^L)).mpr (Nat.ModEq.pow_totient (unit.pow_right L))
    have div : (2^L).totient ∣ c^j := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp only [Nat.reduceSub, mul_one]
      exact (pow_dvd_pow_of_dvd two _).trans (pow_dvd_pow c (by omega))
    obtain ⟨q, hq⟩ := div
    rw [hq, pow_mul, euler, one_pow]
  exact ⟨L, fun j k hj hk => (one k hk).trans (one j hj).symm⟩

/-- Every nonconstant rational polynomial of the positive-index series is normal when
one prime divisor of the parameter has eventually constant radix powers at all precisions. -/
theorem composite_polynomial_normal {b c p : ℕ} (hb : 2 ≤ b) (hc : 2 < c)
    (cop : b.Coprime c) (hp : p.Prime) (pc : p ∣ c) (stable : StablePowers b c p)
    (P : ℚ[X]) (degree : 0 < P.natDegree) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) := by
  simpa using polynomial_normal_at hb hc hp pc stable cop 1 P degree

theorem unit_limit_polynomial_normal : StonehamStatements.PolynomialNormalityAtUnitLimit := by
  intro b c p hp hb hc cop pc limit P degree
  exact composite_polynomial_normal hb hc cop hp.out pc (stablePowers_of_unitPowerLimit limit) P degree

theorem even_polynomial_normal : StonehamStatements.EvenParameterPolynomialNormality := by
  intro b c hb hc cop even P degree
  exact composite_polynomial_normal hb hc cop Nat.prime_two (even_iff_two_dvd.mp even)
    (stablePowers_two even cop) P degree

end NormalityChecker.StonehamPolynomial
