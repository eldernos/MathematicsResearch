import NormalityChecker.PeriodicPolynomialNormal
import NormalityChecker.ParameterTwoSquare
import NormalityChecker.ParameterTwoQuadraticOrbits
import NormalityChecker.DyadicQuartic
import NormalityChecker.StonehamOddDegree
import NormalityChecker.Phase16StonehamBounds
import NormalityChecker.Phase17DiscrepancyBounds
import Lean.Util.CollectAxioms

open NormalityChecker StonehamPolynomial

example : StonehamStatements.stoneham = StonehamPolynomial.alpha := rfl
example : StonehamStatements.CoprimePolynomialNormality := coprime_polynomial_statement_checked
example : ParameterTwoSquare.ExactDenominatorProfile := ParameterTwoSquare.exact_profile
example : ParameterTwoSquare.SquareNormality := ParameterTwoSquare.square_normal

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``coprime_polynomial_normal, ``coprime_joint_powers, ``periodic_upper_mass_nonzero,
      ``ParameterTwoSquare.square_normal, ``ParameterTwoSquare.exact_profile,
      ``ParameterTwoQuadratic.normal_iff_upper_denominator, ``odd_prime_power_degree_polynomial_normal,
      ``quartic_polynomial_normal, ``Phase16StonehamBounds.quadratic_upper_den_eq_quadZ,
      ``Phase17DiscrepancyBounds.descent31Check_true, ``Phase17DiscrepancyBounds.descent31_all_words_nonzero,
      ``Phase17DiscrepancyBounds.jointUniform_of_echelon_degrees] do
    let deps ← collectAxioms decl
    unless deps.all allowed.contains do
      throwError "{decl} has unexpected dependencies {deps}"
    logInfo m!"{decl}: {deps}"
