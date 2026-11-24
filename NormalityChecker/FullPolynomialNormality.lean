module

public import NormalityChecker.MaskExamples
public import NormalityChecker.UnsignedNormality

/-! Complete qualitative classification on full finite support, with rational coefficients. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks
open LocalizedSupport

/-- A full-support rational polynomial expansion is normal exactly when a pole
remains at zero and at least one support prime is coprime to the radix. -/
theorem full_rational_normal_iff {b s : ℕ} (hb : 2≤b) (S : Finset ℕ)
    (primes : ∀ p∈S,p.Prime) (P : ℚ[X]) (nz : P≠0) :
    NormalIn b (maskedValue b S (fun _ => true) P s) ↔
      P.rootMultiplicity 0<s ∧ ∃ p∈S,¬p∣b := by
  constructor
  · intro normal
    by_contra! bad
    have cases : s≤P.rootMultiplicity 0 ∨ ∀ p∈S,p∣b := by
      by_cases pole : P.rootMultiplicity 0<s
      · exact Or.inr (bad pole)
      · exact Or.inl (le_of_not_gt pole)
    obtain ⟨_,_,_,_,no⟩ := rational_boundary hb S _ P nz cases
    exact no normal
  · rintro ⟨pole,p,mem,off⟩
    let r := P.rootMultiplicity 0
    obtain ⟨Q,fac,unit⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd nz 0
    simp only [map_zero,sub_zero] at fac unit
    change P=X^r*Q at fac
    have q0 : Q.eval 0≠0 := by simpa [X_dvd_iff,coeff_zero_eq_eval_zero] using unit
    have hp := primes p mem
    have pp : ∀ q∈S.erase p,q.Prime := fun q h => primes q (mem_of_mem_erase h)
    have vanish := unsigned_certificate_tendsTo_zero hp (notMem_erase p S)
      (hp.coprime_iff_not_dvd.mpr off).symm (Nat.sub_pos_of_lt pole) pp
    rw [fac,show s=r+(s-r) by dsimp [r]; omega,masked_cancel]
    rw [←insert_erase mem]
    apply normal_of_unsigned_certificates hb hp off (Nat.sub_pos_of_lt pole) Q q0 _ pp (notMem_erase p S)
    intro ε hε; obtain ⟨k,h⟩ := (vanish.eventually_lt_const hε).exists
    exact ⟨k,h.le⟩

end NormalityChecker.PolynomialMasks
