import «papers».«02-localized-normality».Statements
import NormalityChecker.FullPolynomialNormality
import Lean.Util.CollectAxioms

open Filter Finset Polynomial
open NormalityChecker NormalityChecker.LocalizedSupport NormalityChecker.PolynomialMasks
namespace PaperII

private theorem smooth_iff (S : Finset ℕ) (m : ℕ) :
    Smooth S m ↔ m ∈ Nat.factoredNumbers S := by
  constructor
  · intro h
    exact Nat.mem_factoredNumbers'.mpr h.2
  · intro h
    exact ⟨Nat.pos_of_ne_zero h.1, Nat.mem_factoredNumbers'.mp h⟩

/-- In the unsigned library the summation variable also counts from m = i+1. -/
theorem unsignedValue_eq (b s : ℕ) (S : Finset ℕ) :
    value b s S 1 = powerValue b s S := by
  classical
  apply tsum_congr
  intro i
  by_cases hi : i+1 ∈ Nat.factoredNumbers S <;>
    simp [powerCoefficient, smooth_iff, hi, Nat.cast_add, Nat.cast_one]

/-- The masked library instead sums over m = 0,1,...; its m = 0 coefficient vanishes. -/
theorem polynomialValue_eq (b s : ℕ) (S : Finset ℕ) (P : ℚ[X]) :
    value b s S P = maskedValue b S (fun _ => true) P s := by
  classical
  let f (m : ℕ) := ((weights S (fun _ => true) P s m : ℚ) : ℝ) / (b : ℝ)^m
  have cover : Function.support f ⊆ Set.range Nat.succ := by
    rintro (_ | m) hm
    · have excluded : 0 ∉ Nat.factoredNumbers S := fun h => h.1 rfl
      exact False.elim (hm (by simp [f, weights, excluded]))
    · exact ⟨m, rfl⟩
  change value b s S P = ∑' m, f m
  rw [← Nat.succ_injective.tsum_eq cover]
  apply tsum_congr
  intro i
  by_cases hi : i+1 ∈ Nat.factoredNumbers S <;>
    simp [f, weights, smooth_iff, hi, Nat.succ_eq_add_one]

theorem unsignedClassification : UnsignedClassification := by
  intro b s S hb hs primes
  rw [unsignedValue_eq]
  have limit := unsigned_discrepancy_limit S hb hs primes
  constructor
  · intro off
    obtain ⟨p, hp, hpb⟩ := off
    have mixed : ¬ ∀ q ∈ S, q ∣ b := fun h => hpb (h p hp)
    rw [ite_eq_right mixed] at limit
    exact ⟨unsigned_finite_support_normal S hb hs primes ⟨p,hp,hpb⟩, limit⟩
  · intro base
    rw [ite_eq_left base] at limit
    exact limit

theorem polynomialClassification : PolynomialClassification := by
  intro b s S P hb primes nonzero
  rw [polynomialValue_eq]
  exact full_rational_normal_iff hb S primes P nonzero

end PaperII

open Lean in
run_cmd do
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``PaperII.unsignedClassification, ``PaperII.polynomialClassification] do
    let axioms ← collectAxioms decl
    let unexpected := axioms.filter fun a => !permitted.contains a
    unless unexpected.isEmpty do
      throwError "{decl} depends on unexpected axioms {unexpected}"
    logInfo m!"{decl}: {axioms}"
