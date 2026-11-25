import NormalityChecker.QualityCoverage
import NormalityChecker.PartialUniformity
import NormalityChecker.OrbitRigidity
import NormalityChecker.ModelCounting
import NormalityChecker.ComputableNormalityUndecidability
import Lean.Util.CollectAxioms

open Finset Filter NormalityChecker
open scoped Topology

-- Theorem 1.1 (AC-01) composed with Theorem 1.2 (AC-04):
-- the lower denominator cutoff is chosen before the scale.
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

-- Proposition 2.1 (AC-02): finite coverage bound specialized to radix orbits.
example {b N : ℕ} {x δ : ℝ} (hN : 0 < N) (J : Finset ℕ) (piece : ℕ → Finset ℕ)
    (inside : ∀ j ∈ J, piece j ⊆ range N)
    (disjoint : (J : Set ℕ).PairwiseDisjoint piece)
    (localBound : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ j ∈ J,
      ‖∑ i ∈ piece j, Localized.centered (shift b x) u v i‖ ≤ δ*(piece j).card) :
    radixDiscrepancy b x N ≤ 1-(1-δ)*((J.biUnion piece).card/N : ℝ) :=
  Coverage.fixed_quality_cover J piece hN inside disjoint localBound

-- Theorem 3.1 (AC-03): uniform separation on an overlap of length T.
example {b c : ℕ} (hb : 1 < b) (hc : 1 < c) (cop : b.Coprime c) (d : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (y z : ℚ) (T : ℕ), 0 < T →
      (∃ j : ℕ, y.den ∣ c^j) → (∃ j : ℕ, z.den ∣ c^j) →
      y.den ≤ T^d → z.den ≤ T^d → (y-z).den ≠ 1 → ∀ f : ℕ → ℝ,
      γ*T ≤ (∑ i ∈ range T, turnDistance (f i-(b:ℝ)^i*y)) +
        ∑ i ∈ range T, turnDistance (f i-(b:ℝ)^i*z) :=
  smooth_overlap_separation hb hc cop d

-- Theorem 7.4 (AC-11): nonrecognizability on arbitrary digit-oracle codes.
example {a b : ℕ → Bool}
    (ha_comp : Computable a) (hb_comp : Computable b)
    (ha_tr : Transcendental ℚ (ComputableNormalityUndecidability.binarySeries a))
    (ha_norm : NormalIn 2 (ComputableNormalityUndecidability.binarySeries a))
    (hb_tr : Transcendental ℚ (ComputableNormalityUndecidability.binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (ComputableNormalityUndecidability.binarySeries b)) atTop (𝓝 1)) :
    (¬ ∃ P : Nat.Partrec.Code → Prop,
        ComputablePred P ∧ ∀ code s,
          ComputableNormalityUndecidability.Names code s →
          ComputableNormalityUndecidability.TranscendentalZeroOnePromise s →
          (P code ↔ NormalIn 2 (ComputableNormalityUndecidability.binarySeries s))) ∧
    (¬ ∃ P : Nat.Partrec.Code → Prop,
        REPred P ∧ ∀ code s,
          ComputableNormalityUndecidability.Names code s →
          ComputableNormalityUndecidability.TranscendentalZeroOnePromise s →
          (P code ↔ NormalIn 2 (ComputableNormalityUndecidability.binarySeries s))) ∧
    (¬ ∃ P : Nat.Partrec.Code → Prop,
        REPred P ∧ ∀ code s,
          ComputableNormalityUndecidability.Names code s →
          ComputableNormalityUndecidability.TranscendentalZeroOnePromise s →
          (P code ↔ ¬ NormalIn 2 (ComputableNormalityUndecidability.binarySeries s))) :=
  ⟨ComputableNormalityUndecidability.no_computable_normality_decider_on_names
      ha_comp hb_comp ha_tr ha_norm hb_tr hb_disc,
   ComputableNormalityUndecidability.no_re_normality_recognizer_on_names
      ha_comp hb_comp ha_tr ha_norm hb_tr hb_disc,
   ComputableNormalityUndecidability.no_re_nonnormality_recognizer_on_names
      ha_comp hb_comp ha_tr ha_norm hb_tr hb_disc⟩

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
    ``NormalityChecker.smooth_overlap_separation,
    ``NormalityChecker.smooth_overlap_rigidity,
    ``NormalityChecker.overlap_chain_denominator,
    ``NormalityChecker.few_symbol_words,
    ``NormalityChecker.ComputableNormalityUndecidability.binarySeries_finite_edit_dyadic,
    ``NormalityChecker.ComputableNormalityUndecidability.transcendental_add_rat,
    ``NormalityChecker.ComputableNormalityUndecidability.shift_add_dyadic_eq,
    ``NormalityChecker.ComputableNormalityUndecidability.binaryDiscrepancy_sub_le_of_eventually_eq,
    ``NormalityChecker.ComputableNormalityUndecidability.binaryDiscrepancy_tendsto_iff_add_dyadic,
    ``NormalityChecker.ComputableNormalityUndecidability.normalIn_two_iff_add_dyadic,
    ``NormalityChecker.ComputableNormalityUndecidability.switchedDigit_computable,
    ``NormalityChecker.ComputableNormalityUndecidability.switched_real_promise_and_reduction,
    ``NormalityChecker.ComputableNormalityUndecidability.reversed_switched_real_reduction,
    ``NormalityChecker.ComputableNormalityUndecidability.normality_not_computable,
    ``NormalityChecker.ComputableNormalityUndecidability.normality_not_re,
    ``NormalityChecker.ComputableNormalityUndecidability.normality_not_co_re,
    ``NormalityChecker.ComputableNormalityUndecidability.exists_switchedDigit_index_map,
    ``NormalityChecker.ComputableNormalityUndecidability.no_re_normality_recognizer_on_names,
    ``NormalityChecker.ComputableNormalityUndecidability.no_re_nonnormality_recognizer_on_names,
    ``NormalityChecker.ComputableNormalityUndecidability.no_computable_normality_decider_on_names]
  for result in results do
    let dependencies ← collectAxioms result
    unless dependencies.all permitted.contains do
      throwError "{result} has unexpected dependencies {dependencies}"
  logInfo m!"Checked the axiom dependencies of {results.size} declarations."
