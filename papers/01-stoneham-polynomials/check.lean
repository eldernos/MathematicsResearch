import NormalityChecker.StonehamJoint
import NormalityChecker.StonehamSquare
import NormalityChecker.ProductThreeFive
import Lean.Util.CollectAxioms

open NormalityChecker StonehamPolynomial
open scoped BigOperators
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``polynomial_statement_checked, ``joint_statement_checked, ``joint_uniform_powers,
      ``prime_power_product_normal, ``same_prime_sum_normal, ``StonehamSquare.exact_profile,
      ``StonehamSquare.initial_profile, ``ProductThreeFive.discrepancy, ``ProductThreeFive.irrational] do
    let deps ← collectAxioms decl
    unless deps.all allowed.contains do
      throwError "{decl} has unexpected dependencies {deps}"
    logInfo m!"{decl}: {deps}"

-- These identifications also check the positive starting index across three developments.
example : StonehamStatements.stoneham = StonehamPolynomial.alpha := rfl
example : StonehamSquare.alpha = StonehamStatements.stoneham 2 3 := rfl
example (q : ℕ) : ProductThreeFive.alpha q = StonehamStatements.stoneham 2 q := rfl
example : StonehamStatements.PolynomialNormality := polynomial_statement_checked
example : StonehamStatements.JointPowerNormality := joint_statement_checked
