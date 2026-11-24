module

public import NormalityChecker.PeriodicClassification

/-! Order-one periodic signed weights on the sparse prime-power axis. -/
@[expose] public section
open Finset
namespace NormalityChecker.LocalizedSupport

/-- The order-one localized sum with rational numerator H(m mod d) at each m = p^j. -/
noncomputable def periodicAxisValue {d : ℕ} (b p : ℕ) (H : ZMod d → ℚ) : ℝ :=
  ∑' j : ℕ, (H ((p : ZMod d)^j) : ℝ) / (p : ℝ)^j / (b : ℝ)^(p^j)

private theorem antidifference_step {b d : ℕ} [NeZero d] (hb : 2 ≤ b) (H : ZMod d → ℚ) :
    periodicAntidifference b d (fun z => H z - H (z+1)/b) = H := by
  let A (z : ZMod d) := H z - H (z+1)/b
  obtain ⟨_, _, nz⟩ := periodic_data hb A
  funext z
  let f (i : ℕ) := H (z+i) * ((b : ℚ)⁻¹)^i
  have step (i : ℕ) : A (z+i) * ((b : ℚ)⁻¹)^i = f i - f (i+1) := by
    simp [A, f, pow_succ, div_eq_mul_inv, ← add_assoc]
    ring
  change periodWeight b d A z / _ = H z
  rw [div_eq_iff nz]
  -- The two endpoints are the same residue after a full period.
  simp only [periodWeight, step, sum_range_sub']
  simp [f]
  ring

/-- For an arbitrary signed rational residue weight, normality at order one on a
single off-radix prime axis is decided by the finite windows of its eventual power cycle. -/
theorem periodic_axis_normal_iff {b p d J L : ℕ} [NeZero d] (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (len : 0 < L) (cycle : (p : ZMod d)^(J+L) = (p : ZMod d)^J)
    (H : ZMod d → ℚ) :
    NormalIn b (periodicAxisValue b p H) ↔
      ∀ i : Fin L, phaseWindow p H L ((p : ZMod d)^(J+i.val)) ≠ 0 := by
  let A (z : ZMod d) := H z - H (z+1)/b
  have recover : periodicAntidifference b d A = H := antidifference_step hb H
  have test := periodic_normal_iff_phases hb hp cop len cycle A
  rw [recover] at test
  obtain ⟨step, summ, _⟩ := periodic_data hb A
  rw [recover] at step summ
  have identity := dense_boundary_identity (s := 1) (b := b) hp.two_le
    (fun n => A n) (fun n => H n) step summ
  let D : ℤ := 1 - (p : ℤ)
  let r : ℚ := p * H 1 / b
  have scaled : (∑' n : ℕ, (A ((n : ZMod d)+1) : ℝ) / (p : ℝ)^(Nat.log p (n+1)) /
      (b : ℝ)^(n+1)) = (D : ℝ) * periodicAxisValue b p H + r := by
    simpa [periodicAxisValue, D, r, add_comm] using identity
  have nz : D ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.one_lt.ne : (1 : ℤ) ≠ p)
  rwa [scaled, normal_add_rat_iff hb, normal_mul_int_iff hb nz] at test

/-- Every numerator on the ternary axis is nonzero, but the weights alternate
between 1 and -3. A recurring zero window prevents binary normality. -/
theorem periodic_axis_counterexample :
    ¬ NormalIn 2 (periodicAxisValue 2 3 (fun z : ZMod 4 => if z = 1 then 1 else -3)) := by
  have test := periodic_axis_normal_iff (b := 2) (p := 3) (J := 0) (L := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide : (3 : ZMod 4)^(0+2) = (3 : ZMod 4)^0)
    (fun z => if z = 1 then 1 else -3)
  intro normal
  exact test.mp normal (1 : Fin 2) (by decide +kernel)

end NormalityChecker.LocalizedSupport
