module

public import NormalityChecker.UnsignedNormality

/-! An executable common depth for positive-error certificates of finitely many orders. -/
@[expose] public section
open Finset Filter MeasureTheory
open scoped Topology
namespace NormalityChecker.LocalizedSupport

/-- Twice the width of all failed cells, computed exactly on the integer mesh. -/
def failedWidthBound (b s p k : ℕ) (S : Finset ℕ) : ℚ :=
  2 * ((failedCells b s p k S).card : ℚ) / (p^k : ℕ)

private theorem cast_width {b s p k : ℕ} {S : Finset ℕ} (hp : p.Prime) :
    (failedWidthBound b s p k S : ℝ) = 2 * volume.real (failedRegion b s p k S) := by
  rw [failedRegion, mesh_mass (pow_pos hp.pos k)]
  simp [failedWidthBound, mul_div_assoc]

/-- A common failed-width threshold exists for every finite family of positive orders. -/
theorem exists_common_depth {b p : ℕ} {S T : Finset ℕ} (hp : p.Prime)
    (outside : p ∉ S) (cop : b.Coprime p) (primes : ∀ q ∈ S, q.Prime)
    (orders : ∀ s ∈ T, 0 < s) {ε : ℚ} (pos : 0 < ε) :
    ∃ k : ℕ, ∀ s ∈ T, failedWidthBound b s p k S < ε := by
  apply Filter.Eventually.exists (f := (atTop : Filter ℕ))
  apply (eventually_all_finset T).mpr
  intro s hs
  have lim := region_mass_tendsto (orders s hs) hp outside cop
  rw [measureReal_def, unsigned_persistent_null hp outside cop (orders s hs) primes,
    ENNReal.toReal_zero] at lim
  have eps : (0 : ℝ) < ε := by exact_mod_cast pos
  have small := (lim.const_mul 2).eventually_lt_const (by simpa only [mul_zero] using eps)
  filter_upwards [small] with k hk
  exact_mod_cast (cast_width hp).trans_lt hk

/-- Search from depth zero for a common positive-error threshold. The proof of
termination is erased on execution. The parameter S omits the selected prime p. -/
def certificateModulus {b p : ℕ} {S T : Finset ℕ} (hp : p.Prime)
    (outside : p ∉ S) (cop : b.Coprime p) (primes : ∀ q ∈ S, q.Prime)
    (orders : ∀ s ∈ T, 0 < s) {ε : ℚ} (pos : 0 < ε) : ℕ :=
  Nat.find (exists_common_depth hp outside cop primes orders pos)

/-- The returned depth works at every finer precision for each requested order. -/
theorem certificateModulus_spec {b p : ℕ} {S T : Finset ℕ} (hp : p.Prime)
    (outside : p ∉ S) (cop : b.Coprime p) (primes : ∀ q ∈ S, q.Prime)
    (orders : ∀ s ∈ T, 0 < s) {ε : ℚ} (pos : 0 < ε) {k : ℕ}
    (late : certificateModulus hp outside cop primes orders pos ≤ k) {s : ℕ} (hs : s ∈ T) :
    discrepancyCertificate b s p k S < ε := by
  let K := certificateModulus hp outside cop primes orders pos
  have small : failedWidthBound b s p K S < ε :=
    Nat.find_spec (exists_common_depth hp outside cop primes orders pos) s hs
  have incl := failed_region_antitone (orders s hs) hp outside cop late
  have finite : volume (failedRegion b s p K S) ≠ ⊤ :=
    measure_ne_top_of_subset (failed_region_inside hp.pos) (by simp [Real.volume_Icc])
  apply Rat.cast_lt (K := ℝ) |>.mp
  calc (discrepancyCertificate b s p k S : ℝ)
      ≤ 2 * volume.real (failedRegion b s p k S) := certificate_le_twice_mass hp
    _ ≤ 2 * volume.real (failedRegion b s p K S) := mul_le_mul_of_nonneg_left (measureReal_mono incl finite) (by norm_num)
    _ < (ε : ℝ) := (cast_width hp).symm.trans_lt (by exact_mod_cast small)

end NormalityChecker.LocalizedSupport
