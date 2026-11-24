import NormalityChecker.QualityCoverage
import NormalityChecker.OrbitRigidity
import NormalityChecker.JointFiveThirteen
import NormalityChecker.ModelCounting
import Lean.Util.CollectAxioms

open Finset Filter NormalityChecker
open scoped Topology

-- The lower denominator cutoff in AC-01 is chosen before the scale.
example {b c B L d : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) (cop : b.Coprime c)
    (hB : 0 < B) (hL : 1 < L) (x : ℝ) (P : ℕ → ℚ)
    (tail : Tendsto (fun n => (b:ℝ)^n*x-(P n:ℝ)) atTop (𝓝 0))
    (blocks : ∀ u ∈ Ico 1 (L*B), ∀ M : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∃ E : Finset ℕ, (E.card:ℝ) ≤ η*(L:ℝ)^k ∧ ∀ j < L^k, j ∉ E →
        ∃ y : ℚ, M ≤ y.den ∧ (∃ v : ℕ, y.den ∣ c^v) ∧ y.den ≤ (B^k)^d ∧
          ∑ i ∈ range (B^k), turnDistance ((P (u*(L*B)^k+j*B^k+i):ℝ)-(b:ℝ)^i*y)
            ≤ η*(B:ℝ)^k) : NormalIn b x := by
  apply normal_of_approximate_arithmetic_certificate hb hB hL x P tail
    (fixed_support_orbit_estimate hb hc cop) d
  simpa only [mul_pow, Nat.add_mul, Nat.mul_assoc] using blocks

-- AC-02 sums the covered positions once, including at a truncated prefix.
example {b N : ℕ} {x δ : ℝ} (hN : 0 < N) (J : Finset ℕ) (piece : ℕ → Finset ℕ)
    (inside : ∀ j ∈ J, piece j ⊆ range N)
    (disjoint : (J : Set ℕ).PairwiseDisjoint piece)
    (localBound : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ j ∈ J,
      ‖∑ i ∈ piece j, Localized.centered (shift b x) u v i‖ ≤ δ*(piece j).card) :
    radixDiscrepancy b x N ≤ 1-(1-δ)*((J.biUnion piece).card/N : ℝ) :=
  Coverage.fixed_quality_cover J piece hN inside disjoint localBound

-- The denominator cap in AC-03 uses the common length T for both models.
example {b c : ℕ} (hb : 1 < b) (hc : 1 < c) (cop : b.Coprime c) (d : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (y z : ℚ) (T : ℕ), 0 < T →
      (∃ j : ℕ, y.den ∣ c^j) → (∃ j : ℕ, z.den ∣ c^j) →
      y.den ≤ T^d → z.den ≤ T^d → (y-z).den ≠ 1 → ∀ f : ℕ → ℝ,
      γ*T ≤ (∑ i ∈ range T, turnDistance (f i-(b:ℝ)^i*y)) +
        ∑ i ∈ range T, turnDistance (f i-(b:ℝ)^i*z) :=
  smooth_overlap_separation hb hc cop d

open Lean Elab Command in
run_cmd do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let results := #[
    ``NormalityChecker.fixed_support_order_bound,
    ``NormalityChecker.fixed_support_orbit_estimate,
    ``NormalityChecker.phase_model_sum_bound,
    ``NormalityChecker.approximate_prefix_bound,
    ``NormalityChecker.normal_of_approximate_arithmetic_certificate,
    ``NormalityChecker.normal_of_arithmetic_certificate,
    ``NormalityChecker.Coverage.fixed_quality_cover,
    ``NormalityChecker.Coverage.asymptotic_fixed_quality,
    ``NormalityChecker.discrepancy_of_uniform_share,
    ``NormalityChecker.discrepancy_of_fixed_cells,
    ``NormalityChecker.Coverage.endpoint_path,
    ``NormalityChecker.Coverage.restrict_edge,
    ``NormalityChecker.Coverage.fourier_of_path,
    ``NormalityChecker.Coverage.discrepancy_of_paths,
    ``NormalityChecker.LocalizedSupport.cell_power_denominator,
    ``NormalityChecker.LocalizedSupport.discrepancy_of_survival,
    ``NormalityChecker.LocalizedSupport.discrepancy_of_joint_failures,
    ``NormalityChecker.LocalizedSupport.five_thirteen_first_failures,
    ``NormalityChecker.LocalizedSupport.joint_five_thirteen_count,
    ``NormalityChecker.LocalizedSupport.first_precision_joint_discrepancy,
    ``NormalityChecker.LocalizedSupport.five_thirteen_precision_two,
    ``NormalityChecker.LocalizedSupport.five_thirteen_binary_normal,
    ``NormalityChecker.smooth_overlap_separation,
    ``NormalityChecker.smooth_overlap_rigidity,
    ``NormalityChecker.overlap_chain_denominator,
    ``NormalityChecker.few_symbol_words]
  for result in results do
    let dependencies ← collectAxioms result
    unless dependencies.all permitted.contains do
      throwError "{result} has unexpected dependencies {dependencies}"
  logInfo m!"Checked the axiom dependencies of {results.size} declarations."
