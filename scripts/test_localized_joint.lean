import NormalityChecker.LocalizedJoint
import NormalityChecker.LocalizedCertificateModulus
import NormalityChecker.LocalizedDenominatorPrimes
import NormalityChecker.LocalizedSignedAxis
import NormalityChecker.StonehamJoint
import Lean.Util.CollectAxioms

open Finset Filter Polynomial
open scoped Topology
open NormalityChecker NormalityChecker.LocalizedSupport NormalityChecker.PolynomialMasks
open NormalityChecker.LocalizedJointStatements

-- The order list is unsorted, the support is mixed, and one side is the whole unit interval.
example : Tendsto (visits 10 (fun i : Fin 3 => LocalizedJointStatements.value 10 (![4,1,3] i) {2,3,5})
    ![1/4,0,1/2] ![1/2,1,3/4]) atTop (𝓝 (1/16 : ℝ)) := by
  have result := distinct_orders_checked (b := 10) (d := 3) (by decide) (by decide) {2,3,5}
    (by decide) ⟨3, by decide, by decide⟩ ![4,1,3] (by decide) (by decide)
    ![1/4,0,1/2] ![1/2,1,3/4] (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
  convert result using 2
  norm_num [Fin.prod_univ_succ]

-- Copies of one coordinate miss this rectangle of area 1/4 at every cutoff.
example (b : ℕ) (x : ℝ) (N : ℕ) :
    visits b (fun _ : Fin 2 => x) ![0,1/2] ![1/2,1] N = 0 := by
  unfold visits
  have nohit (n : ℕ) : ¬ ∀ i : Fin 2,
      (![0, 1/2] i : ℝ) ≤ Int.fract ((b : ℝ)^n*x) ∧ Int.fract ((b : ℝ)^n*x) < (![1/2,1] i : ℝ) := by
    intro hit
    exact (not_lt_of_ge (hit 1).1) (hit 0).2
  rw [filter_false_of_mem (fun n _ => nohit n)]
  simp

-- The retained exponents are 2^j, and their successive gaps are unbounded.
example : ∃ keep : ℕ → Bool,
    (∀ m, keep m = true ↔ ∃ j : ℕ, m = 3^(2^j : ℕ)) ∧
    JointUniform 10 (fun i : Fin 2 => maskedValue 10 {3} keep (![X+1, C (-2)] i) (![5,2] i)) := by
  classical
  let keep (m : ℕ) := decide (∃ j : ℕ, m = 3^(2^j : ℕ))
  refine ⟨keep, by simp [keep], joint_infinite_axis_orders (by decide) (by decide) (by decide) keep
    (fun J => ⟨2^J, (Nat.lt_two_pow_self (n := J)).le, by simp [keep]⟩)
    _ (by intro i; fin_cases i <;> norm_num) _ (by decide) (by decide)⟩

-- The search stops with surviving failed cells. The search index k uses modulus p^(k+1).
private def exampleDepth := certificateModulus (b := 4) (p := 3) (S := {2,11}) (T := {1,2})
  (by decide) (by decide) (by decide) (by decide) (by decide) (ε := 9/10) (by norm_num)

example : exampleDepth = 2 := by
  apply (Nat.find_eq_iff _).2
  constructor
  · decide +kernel
  · intro m hm
    interval_cases m <;> decide +kernel

/-- info: 2 -/
#guard_msgs in
#eval exampleDepth

example : failedWidthBound 4 1 3 2 {2,11} = 8/9 ∧
    discrepancyCertificate 4 1 3 2 {2,11} = 3/11 := by decide +kernel

-- The same prime cycle gives both outcomes as its signed weights change.
example : NormalIn 2 (periodicAxisValue 2 3 (fun z : ZMod 4 => if z = 1 then 1 else -1)) := by
  apply (periodic_axis_normal_iff (J := 0) (L := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide) _).mpr
  decide +kernel

example : ¬ NormalIn 2 (periodicAxisValue 2 3 (fun z : ZMod 4 => if z = 1 then 1 else -3)) :=
  periodic_axis_counterexample

-- A pole at zero together with a second denominator factor already escapes on the dyadic axis.
example (S : Finset ℕ) (K : ℕ) : ∃ k ≥ K, ∃ q : ℕ, q.Prime ∧ q ∉ S ∧
    q ∣ (1 / (2 : ℚ)^k / (2^k+1)).den := by
  obtain ⟨k, hk, q, prime, out, div⟩ := rational_denominator_prime_outside (p := 2)
    (by decide) 1 (X+1) ⟨1, 0, by simp⟩ (by simp) (by simp) 1 S K
  refine ⟨k, hk, q, prime, out, ?_⟩
  have val : ((X+1 : ℤ[X]).eval ((2 : ℤ)^k)) = 2^k+1 := by rw [eval_add, eval_X, eval_one]
  simpa only [rationalAxisCoefficient, val, eval_one, Int.cast_one, Int.cast_add, Int.cast_pow,
    Int.cast_ofNat, pow_one, Nat.cast_ofNat] using div

open Lean in
run_cmd do
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``JointWeyl.rectangle_of_scalar_normal, ``StonehamPolynomial.joint_statement_checked,
      ``distinct_orders_checked, ``joint_full_polynomial_orders, ``joint_infinite_axis_orders,
      ``joint_axis_orders_iff, ``joint_late_twos_orders, ``certificateModulus_spec, ``periodic_axis_normal_iff,
      ``periodic_axis_counterexample, ``rational_denominator_prime_outside, ``finite_denominator_primes_iff] do
    let axioms ← collectAxioms decl
    let unexpected := axioms.filter fun ax => !permitted.contains ax
    unless unexpected.isEmpty do
      throwError "{decl} depends on unexpected axioms {unexpected}"
    logInfo m!"{decl}: {axioms}"
