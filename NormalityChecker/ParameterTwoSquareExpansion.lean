module

public import NormalityChecker.ParameterTwoSquareStatements
public import NormalityChecker.StonehamPolynomialExpansion

/-! Identification of the positive-index prefix with the two-axis product expansion. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ParameterTwoSquare

private def pairs (n : ℕ) := ((range (Nat.log 2 n)) ×ˢ range (Nat.log 2 n)).filter
  (fun v : ℕ × ℕ => location v.1 v.2 ≤ n)

private lemma mem_pairs {n : ℕ} {v : ℕ × ℕ} : v ∈ pairs n ↔ location v.1 v.2 ≤ n := by
  refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,h⟩⟩
  · exact mem_range.mpr (Nat.le_log_of_pow_le (by decide) ((Nat.le_add_right ..).trans h))
  · exact mem_range.mpr (Nat.le_log_of_pow_le (by decide) ((Nat.le_add_left ..).trans h))

private abbrev strides : StonehamPolynomial.Strides 2 := fun _ => 1
private abbrev dilations : StonehamPolynomial.Vector 2 := fun _ => 2

private lemma position_eq (v : StonehamPolynomial.Vector 2) :
    StonehamPolynomial.position 2 strides dilations v = location (v 0) (v 1) := by
  simp [StonehamPolynomial.position, StonehamPolynomial.stretch, Fin.sum_univ_two,
    strides, dilations, location, pow_succ']

private lemma weight_eq (v : StonehamPolynomial.Vector 2) :
    StonehamPolynomial.weight (StonehamPolynomial.stretch strides v) = v 0 + v 1 := by
  simp [StonehamPolynomial.weight, StonehamPolynomial.stretch, Fin.sum_univ_two, strides]

private theorem product_eq {b : ℕ} (hb : 0 < b) (n : ℕ) :
    StonehamPolynomial.productPrefix b 2 strides dilations n = 4 * pre b n := by
  have bn : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [pre, boxSum, ← sum_product', ← sum_filter]
  change _ = 4 * ((b : ℚ)^n * ∑ v ∈ pairs n, term b v.1 * term b v.2)
  rw [← mul_assoc, mul_sum]
  unfold StonehamPolynomial.productPrefix
  apply sum_bij' (fun v _ => (v 0, v 1)) (fun v _ => ![v.1, v.2])
  · intro v hv
    exact mem_pairs.mpr ((position_eq v) ▸ (StonehamPolynomial.mem_active (by decide)
      (fun _ => (by decide : 0 < 2))).mp hv)
  · intro v hv
    apply (StonehamPolynomial.mem_active (by decide) (fun _ => (by decide : 0 < 2))).mpr
    simpa [position_eq] using mem_pairs.mp hv
  · intro v hv; funext i; fin_cases i <;> rfl
  · intro v hv; rfl
  · intro v hv
    have loc := (StonehamPolynomial.mem_active (by decide) (fun _ => (by decide : 0<2))).mp hv
    rw [position_eq] at loc
    rw [position_eq, weight_eq, pow_sub₀ _ bn loc]
    simp only [term, location, pow_add (2 : ℚ), pow_succ (2 : ℚ), pow_add (b : ℚ)]
    ring

private lemma axis_eq (b : ℕ) : StonehamPolynomial.axis b 2 2 =
    2 * StonehamStatements.stoneham b 2 := by
  rw [StonehamPolynomial.axis, StonehamStatements.stoneham, ← tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [Nat.cast_ofNat, pow_succ' (2 : ℕ), pow_succ' (2 : ℝ), inv_pow]
  ring

theorem shifted_tail {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun n : ℕ => (b : ℝ)^n * (StonehamStatements.stoneham b 2)^2 - (pre b n : ℝ))
      atTop (𝓝 0) := by
  have h := StonehamPolynomial.product_tail (d:=2) (e:=strides) (m:=dilations)
    hb (by decide : 1<2) (fun _ => (by decide : 0<2))
  simp only [strides, dilations, PNat.val_ofNat, pow_one, Fin.prod_univ_two, axis_eq] at h
  have dec := h.const_mul (1/4 : ℝ)
  rw [mul_zero] at dec
  apply dec.congr
  intro n
  rw [product_eq (by omega)]
  push_cast
  ring

theorem follows {b n i : ℕ} (hb : 0 < b)
    (free : ∀ a c, n < location a c → n+i < location a c) :
    pre b (n+i) = (b : ℚ)^i * pre b n := by
  have h := StonehamPolynomial.prefix_follows (b:=b) (p:=2) (e:=strides) (m:=dilations)
    (by decide) (fun _ => (by decide : 0<2)) (n:=n) (i:=i) (fun v => by
      rw [position_eq]; exact free _ _)
  rw [product_eq hb, product_eq hb] at h
  linarith only [h]

/-- All shifted prefixes have a power-of-two common denominator. -/
theorem dyadic {b : ℕ} (hb : 0 < b) (n : ℕ) : ∃ D : ℕ, (pre b n).den ∣ 2^D := by
  have h := StonehamPolynomial.denominator_dvd (d:=2) (b:=b) (p:=2) (n:=n)
    (by decide) strides dilations
  let P := StonehamPolynomial.productPrefix b 2 strides dilations n
  have eqn : pre b n = (1/4 : ℚ)*P := by dsimp [P]; rw [product_eq hb]; ring
  rw [eqn]
  refine ⟨2+2*Nat.log 2 n, (Rat.mul_den_dvd ..).trans ?_⟩
  rw [pow_add]
  rw [show (1/4 : ℚ).den = 4 by
    simpa only [one_div, Nat.cast_ofNat] using Rat.inv_natCast_den_of_pos (by decide : 0<4)]
  exact Nat.mul_dvd_mul_left 4 h

end NormalityChecker.ParameterTwoSquare
