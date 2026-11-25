module

public import NormalityChecker.DyadicMassCells
public import NormalityChecker.StonehamPolynomialRetention
import all NormalityChecker.StonehamPolynomialPrefix
import all NormalityChecker.StonehamPolynomial

/-! An effective grid test for the positive-index dyadic axis, and normality
of every rational quartic polynomial in that axis. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.StonehamPolynomial
open DyadicMassCells

/-- The zero-index internal monomial giving `2^d * alpha(b,2)^d`. -/
def shiftedBinaryPower (d : ℕ) : Monomial := ⟨d, fun _ => 2, fun _ => by decide, fun _ => 1⟩

private lemma mass_on_grid {d k n D L : ℕ} (depth : L ≤ D+1) (late : D ≤ k) :
    (mass 2 L (cut 2 (fun _ : Fin d => 1) (fun _ => 2) k n) : ZMod (2^L)) =
      through (n / (2*2^(k-D))) (axisPoly D L ^ d) := by
  rw [← grid_mass]
  congr 1
  unfold mass weightedMass
  congr 1
  ext v
  simp only [mem_filter]
  apply and_congr_right
  intro hv
  have step (i : Fin d) : k - v i = (k-D) + (D-v i) := by
    have := mem_box.mp hv i
    omega
  have eqn : position 2 (fun _ : Fin d => 1) (fun _ => 2)
      (reflect (fun _ => 1) k v) = gridPosition D v * (2 * 2^(k-D)) := by
    simp only [position, stretch, reflect, caps, PNat.val_ofNat, Nat.div_one, one_mul,
      step, pow_add, gridPosition, sum_mul]
    exact sum_congr rfl fun _ _ => by ring
  simp only [cut, Set.mem_ofPred_eq, eqn, Nat.le_div_iff_mul_le (by positivity : 0 < 2*2^(k-D))]

/-- The finite grid covers a whole late shell, including the insertion at its
left endpoint. A nonzero residue supplies the leading-pole hypothesis used by
the arithmetic normality criterion. -/
theorem retention_of_binary_grid {d D L b : ℕ} (cop : b.Coprime 2)
    (depth : L ≤ D+1) (Dpos : 1 ≤ D)
    (cert : ∀ q : ℕ, 2^(D-1) ≤ q → q < 2^D →
      through q (axisPoly D L ^ d) ≠ 0) :
    RetainsDenominator b 2 (shiftedBinaryPower d) := by
  refine ⟨L, max (2*L) D, fun n hn pos => ?_⟩
  let k := Nat.log 2 n
  have late : D ≤ k := (le_max_right ..).trans hn
  have freeze : 2*L ≤ k := (le_max_left ..).trans hn
  let s := 2*2^(k-D)
  have sp : 0 < s := by dsimp [s]; positivity
  have lo : 2^(D-1) * s = 2^k := by
    dsimp [s]
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hi : 2^D * s = 2^(k+1) := by
    dsimp [s]
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have grid := cert (n/s) ((Nat.le_div_iff_mul_le sp).mpr
    (lo ▸ Nat.pow_log_le_self 2 pos.ne')) ((Nat.div_lt_iff_lt_mul sp).mpr
    (hi ▸ Nat.lt_pow_succ_log_self (by decide) n))
  rw [← mass_on_grid (d:=d) depth late] at grid
  have stable (j k' : ℕ) (hj : L ≤ j) (hk : L ≤ k') :
      (b : ZMod (2^L))^(2^k') = b^(2^j) :=
    (stable_power Nat.prime_two cop le_rfl hk).trans (stable_power Nat.prime_two cop le_rfl hj).symm
  have nz := numerator_nonzero (b:=b) (dvd_rfl : 2 ∣ 2) cop stable
    (fun _ : Fin d => 1) (fun _ => 2) (fun _ => by simpa [caps, two_mul] using freeze) grid
  have bound := factorization_le_of_numerator Nat.prime_two (by decide : 0 < 2) _ _ nz
  simp only [scale, weight, stretch, caps, PNat.val_ofNat, one_mul, Nat.div_one, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.Prime.factorization_self Nat.prime_two] at bound
  exact (Nat.prime_two.pow_dvd_iff_le_factorization (Rat.pos _).ne').mpr (by
    change d * Nat.log 2 n - L ≤ (productPrefix b 2 (fun _ : Fin d => 1) (fun _ => 2) n).den.factorization 2
    exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.mul_comm] using bound))

/-- A retained dyadic degree permits arbitrary rational lower coefficients. -/
theorem binary_polynomial_normal_of_retention {b : ℕ} (hb : 2 ≤ b) (odd : Odd b)
    (P : ℚ[X]) (degree : 0 < P.natDegree)
    (retain : RetainsDenominator b 2 (shiftedBinaryPower P.natDegree)) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b 2)) := by
  let c (d : ℕ) := P.coeff d / 2^d
  have lead : c P.natDegree ≠ 0 :=
    div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (fun h => by simp [h] at degree)) (by positivity)
  have result := rational_sum_normal_of_retention hb Nat.prime_two (Nat.coprime_two_right.mpr odd)
    (shiftedBinaryPower P.natDegree) retain degree _ lead (range P.natDegree) shiftedBinaryPower c
    (fun _ hi => mem_range.mp hi)
  have shifted : axis b 2 2 = 2 * alpha b 2 := by
    simpa using axis_shift (b:=b) (p:=2) (by decide) 1
  have val (d : ℕ) :
      (c d : ℝ) * (shiftedBinaryPower d).value b 2 = (P.coeff d : ℝ) * alpha b 2 ^ d := by
    change (c d : ℝ) * (∏ _i : Fin d, axis b 2 2) = _
    simp [c, shifted, mul_pow]
    field_simp
  rw [Polynomial.eval₂_eq_sum_range, sum_range_succ, add_comm]
  simpa only [val, show ∀ q : ℚ, (algebraMap ℚ ℝ) q = (q:ℝ) from fun _ => rfl] using result

theorem quartic_retains_denominator {b : ℕ} (odd : Odd b) :
    RetainsDenominator b 2 (shiftedBinaryPower 4) := by
  apply retention_of_binary_grid (D:=12) (L:=13) (Nat.coprime_two_right.mpr odd) (by decide) (by decide)
  intro q lo hi
  rw [quartic_grid_profile q lo hi]
  split_ifs <;> decide

/-- Every rational polynomial of degree four evaluated at the standard
positive-index Stoneham number of parameter two is normal in its odd radix. -/
theorem quartic_polynomial_normal {b : ℕ} (hb : 2 ≤ b) (odd : Odd b)
    (P : ℚ[X]) (degree : P.natDegree = 4) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b 2)) := by
  apply binary_polynomial_normal_of_retention hb odd P (by omega)
  rw [degree]
  exact quartic_retains_denominator odd

theorem fourth_power_normal {b : ℕ} (hb : 2 ≤ b) (odd : Odd b) :
    NormalIn b (alpha b 2 ^ 4) := by
  have deg : ((X : ℚ[X]) ^ 4).natDegree = 4 := by simp
  simpa only [eval₂_pow, eval₂_X] using quartic_polynomial_normal hb odd _ deg

end NormalityChecker.StonehamPolynomial
