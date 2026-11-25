module

public import NormalityChecker.ParameterTwoQuadraticHeight
public import NormalityChecker.QuadraticOrbitLog

/-! Distribution of rational quadratic images of the positive-index Stoneham
series in every odd radix. In all statements D clears the rational coefficients. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ParameterTwoQuadratic
open QuadraticOrbit

/-- The denominator at the midpoint is constant up to the next power of two.
Its growth is necessary and sufficient for full ordinary normality. -/
theorem normal_iff_upper_denominator {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C₀ : ℤ) (hA : A ≠ 0) :
    NormalIn b (value b A B C₀ / D) ↔
      Tendsto (fun j : ℕ => («prefix» b (3*2^j) A B C₀).den) atTop atTop :=
  normal_iff_upper_growth hb odd hd A B C₀ hA

theorem normal_of_algebraic_kappa {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C₀ : ℤ) (hA : A ≠ 0) (alg : IsAlgebraic ℚ (kappa b A B)) :
    NormalIn b (value b A B C₀ / D) := by
  apply (normal_iff_upper_denominator hb odd hd A B C₀ hA).mpr
  apply tendsto_atTop.mpr
  intro M
  exact ((algebraic_upper_growth hb odd A B C₀ hA alg).eventually_ge_atTop (M:ℝ)).mono
    (fun n hn => by exact_mod_cast hn)

/-- Extreme interval discrepancy at ordinary prefixes, including endpoints
inside an exceptional upper half. -/
theorem quadratic_discrepancy_limits {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C₀ : ℤ) (hA : A ≠ 0) :
    let x := value b A B C₀ / D
    limsup (radixDiscrepancy b x) atTop ≤ 1/4 ∧ liminf (radixDiscrepancy b x) atTop = 0 :=
  ordinary_limits (rational_good_halves hb odd hd A B C₀ hA)
    (midpoint_window_unique hb odd A B C₀ hA)

/-- Harmonic weights on digit positions give the correct length for every
interval, without a growth or algebraicity hypothesis. -/
theorem quadratic_log_equidistribution {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C₀ : ℤ) (hA : A ≠ 0) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    Tendsto (logFrequency (shift b (value b A B C₀ / D)) a c) atTop (𝓝 (c-a)) :=
  log_equidistribution_of_separated (rational_good_halves hb odd hd A B C₀ hA)
    (midpoint_window_unique hb odd A B C₀ hA) a c ha hac hc

end NormalityChecker.ParameterTwoQuadratic
