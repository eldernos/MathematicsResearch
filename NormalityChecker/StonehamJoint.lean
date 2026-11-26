module

public import NormalityChecker.StonehamPolynomial
public import NormalityChecker.StonehamStatements
public import NormalityChecker.JointWeyl

/-! Joint normality of distinct powers of a Stoneham constant. -/
@[expose] public section
noncomputable section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

/-- Testing scalar characters by polynomials gives joint uniformity of distinct powers. -/
theorem joint_powers_of_polynomial_normal {b d : ℕ} {x : ℝ}
    (normal : ∀ P : ℚ[X], 0 < P.natDegree → NormalIn b (P.eval₂ (algebraMap ℚ ℝ) x))
    (r : Fin d → ℕ) (pos : ∀ i, 0 < r i) (inj : Function.Injective r)
    (a c : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (hac : ∀ i, a i ≤ c i) (hc : ∀ i, c i ≤ 1) :
    Tendsto (StonehamStatements.rectangleFrequency (fun n i => shift b (x ^ r i) n) a c)
      atTop (𝓝 (∏ i, (c i - a i))) := by
  apply JointWeyl.rectangle_of_scalar_normal _ _ a c ha hac hc
  intro t zero
  classical
  obtain ⟨j,hj⟩ := Function.ne_iff.mp zero
  change t j ≠ 0 at hj
  let P : ℚ[X] := ∑ i, monomial (r i) (t i : ℚ)
  have coeff : P.coeff (r j) = t j := by
    simp only [P, finsetSum_coeff, coeff_monomial, Finsupp.single_apply, inj.eq_iff]
    simp
  have degree : 0 < P.natDegree := (pos j).trans_le (le_natDegree_of_ne_zero
    (coeff.trans_ne (by exact_mod_cast hj)))
  have ev : P.eval₂ (algebraMap ℚ ℝ) x = ∑ i, (t i : ℝ)*x^r i := by
    simp [P, eval₂_finsetSum, eval₂_monomial]
  have scalar := normal P degree
  rwa [ev] at scalar

/-- All finite lists of distinct positive powers of the standard prime-power Stoneham
constant visit every half-open rectangle with limiting frequency equal to its volume. -/
theorem joint_uniform_powers {b p d : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (e : ℕ+) (r : Fin d → ℕ) (pos : ∀ i, 0 < r i) (inj : Function.Injective r)
    (a c : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (hac : ∀ i, a i ≤ c i) (hc : ∀ i, c i ≤ 1) :
    Tendsto (StonehamStatements.rectangleFrequency
      (fun n i => shift b (alpha b (p^(e : ℕ)) ^ r i) n) a c)
      atTop (𝓝 (∏ i, (c i - a i))) :=
  joint_powers_of_polynomial_normal (prime_power_polynomial_normal hb hp odd cop e) r pos inj a c ha hac hc

/-- Independent public statement checks use only definitional identification of the series. -/
theorem polynomial_statement_checked : StonehamStatements.PolynomialNormality :=
  fun hb hp odd cop => prime_power_polynomial_normal hb hp odd cop

theorem joint_statement_checked : StonehamStatements.JointPowerNormality :=
  fun hb hp odd cop => joint_uniform_powers hb hp odd cop

end NormalityChecker.StonehamPolynomial
