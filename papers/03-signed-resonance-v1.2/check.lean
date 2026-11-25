import NormalityChecker.CyclotomicExamples
import NormalityChecker.ShellHistories
import NormalityChecker.TranslatedShellExamples
import Lean.Util.CollectAxioms

open Filter Finset Polynomial NormalityChecker NormalityChecker.SignedPhases
open scoped Topology

-- The finite family includes its zeroth insertion for every multiplier.
example (b p : ℕ) (M : Finset ℕ) (v : ℕ → ℚ) :
    radixSum b p M v =
      ∑ m ∈ M, (v m : ℝ) * ∑' j : ℕ, (1 / (b : ℝ))^(m * p^j) / ((m : ℝ) * (p : ℝ)^j) := rfl

-- The criterion applies to signed rational coefficients, including for M empty.
example {b p S : ℕ} [Fact p.Prime] (hb : 1 < b) (ho : Odd p) (cop : b.Coprime p)
    (hs : 0 < S) (M : Finset ℕ) (v : ℕ → ℚ) (hm : ∀ m ∈ M, 0 < m ∧ m ≤ S) :
    NormalIn b (radixSum b p M v) ↔ ∀ u ∈ Ico S (p*S),
      ¬ cyclotomic (orderOf (b : ZMod p)) ℚ ∣
        ∑ m ∈ M, C ((v m / m) / (p : ℚ)^(Nat.log p (u / m))) * X^m :=
  cyclotomic_normal_iff hb ho cop hs M v hm

-- Position zero is regular, even if the initial phase vanishes.
example (p : ℕ) (c : ℕ → ℤ) (N : ℕ) :
    zeroDensity p c N =
      ((N : ℝ) - ((range N).filter (fun n => n = 0 ∨ c (Nat.log p n) ≠ 0)).card) / N := rfl

example (p : ℕ) (c : ℕ → ℤ) (j : ℕ) :
    jump p c 0 = c 0 ∧ jump p c (j+1) = c (j+1) - p * c j := ⟨rfl, rfl⟩

section
variable {b p B : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (cop : b.Coprime p)
    (c : ℕ → ℤ) (bound : ∀ j, (c j).natAbs ≤ B)

example : Tendsto (fun N => radixDiscrepancy b (value b p c) N - zeroDensity p c N) atTop (𝓝 0) :=
  discrepancy_sub_zeroDensity_tendsto hb hp cop c bound

example {L : ℕ} (hL : 0 < L) (period : ∀ j, c (j+L) = c j) :
    limsup (radixDiscrepancy b (value b p c)) atTop = (cycleMaximum p L c : ℝ) :=
  periodic_discrepancy hb hp cop hL c bound period

example (m : ℤ) (hm : m ≠ 0) (r : ℚ) :
    Tendsto (fun N => radixDiscrepancy b ((m : ℝ)*value b p c+r) N -
      zeroDensity p c N * limsup (radixDiscrepancy b r) atTop) atTop (𝓝 0) :=
  translated_discrepancy hb hp cop c bound m hm r

example (δ : ℝ) :
    (∃ (ph : ℕ → ℤ) (K : ℕ), (∀ j, (ph j).natAbs ≤ K) ∧
      limsup (radixDiscrepancy b (value b p ph)) atTop = δ) ↔
      ∃ s : ShellWord, (∀ h, WordLE (fun i => s (i+h)) s) ∧ historyValue hp.one_lt s = δ :=
  attainable_discrepancy_iff hb hp cop δ
end

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``cyclotomic_normal_iff, ``cyclotomicNormalTest_correct, ``cyclotomic_distribution,
      ``seventh_triple_distributions, ``severe_normal_summands, ``discrepancy_sub_zeroDensity_tendsto,
      ``periodic_discrepancy, ``binary_three_periods, ``attainable_discrepancy_iff,
      ``cycleMaximum_approximates_historyValue, ``translated_discrepancy, ``translated_limsup,
      ``translated_third_examples, ``de_bruijn_discrepancy_bounds, ``de_bruijn_eight_cells,
      ``arbitrarily_small_translations, ``division_by_nine_example, ``irrational_iff_frequently_nonzero] do
    let deps ← collectAxioms decl
    unless deps.all allowed.contains do
      throwError "{decl} has unexpected dependencies {deps}"
    logInfo m!"{decl}: {deps}"
