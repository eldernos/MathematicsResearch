module

public import NormalityChecker.MaskDominance
public import NormalityChecker.MaskQuotients
public import NormalityChecker.MaskThirds

/-! Worked polynomial and periodic-mask examples. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

/-- The degree-ten polynomial in the notes, on any ternary/quinary/dyadic
smooth mask containing every sufficiently late power of two. -/
theorem base_five_degree_ten (keep : ℕ → Bool) (retained : ∀ᶠ k : ℕ in atTop, keep (2^k)=true) :
    NormalIn 5 (maskedValue 5 {2,3,5} keep (C 12*X^4+X^5+C 3*X^10) 5) := by
  let G : ℚ[X] := C 12+X+C 3*X^6
  have poly : C 12*X^4+X^5+C 3*X^10=X^4*G := by dsimp [G]; ring
  rw [poly,show 5=4+1 from rfl,masked_cancel]
  exact normal_of_late_twos (by decide) (by decide) (by decide) (by norm_num [G]) _
    (fun q h => by simp at h; rcases h with rfl|rfl|rfl <;> decide) (by decide) keep retained

/-- The same polynomial loses exactly two factors of two at each retained
dyadic scale k≥3. The statement concerns the actual rational prefix. -/
theorem base_five_dyadic_exponent (keep : ℕ → Bool) {k n : ℕ} (late : 3≤k)
    (hit : keep (2^k)=true) (lo : 2^k≤n) (hi : n<2*2^k) :
    (pre 5 (weights {2,3,5} keep (C 12*X^4+X^5+C 3*X^10) 5) n).den.factorization 2=k-2 := by
  let G : ℤ[X] := C 12+X+C 3*X^6
  let A := (LocalizedSupport.indices {2,3,5} n).filter (fun m => keep m=true)
  have ps : 2^k ∈ Nat.factoredNumbers {2,3,5} := by
    simpa using Nat.pow_mul_mem_factoredNumbers (s:={3,5}) Nat.prime_two k
      (Nat.mem_factoredNumbers_of_primeFactors_subset (by decide : (1:ℕ)≠0) (by simp))
  have eqn : pre 5 (weights {2,3,5} keep (C 12*X^4+X^5+C 3*X^10) 5) n =
      shiftedPrefix 5 1 n G A := by
    simp only [pre,shiftedPrefix,A,LocalizedSupport.indices,sum_filter]
    apply sum_congr rfl; intro m _
    by_cases sm : m∈Nat.factoredNumbers {2,3,5} <;> by_cases km : keep m=true <;>
      simp [weights,G,sample,sm,km]
    field_simp [sm.1]
  have v : (sample G 0).natAbs.factorization 2=2 := by
    have c : sample G 0=12 := by norm_num [G,sample]
    rw [c]; change (12:ℕ).factorization 2=2
    rw [show 12=2^2*3 by decide,Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣3)]; simp
  have ex := first_cell_den_exponent (b:=5) Nat.prime_two (by decide) (by decide : 0<1) G
    (by norm_num [G,sample]) A (mem_filter.mpr ⟨LocalizedSupport.mem_indices.mpr ⟨lo,ps⟩,hit⟩)
    (fun m hm => by obtain ⟨le,ms⟩ := LocalizedSupport.mem_indices.mp (mem_filter.mp hm).1; exact ⟨Nat.pos_of_ne_zero ms.1,le⟩)
    hi (by rw [v]; omega)
  simpa only [eqn,v,mul_one] using ex

/-- A rational polynomial having integer values after division by mˢ has
maximal discrepancy on every smooth mask, in every base. -/
theorem consecutive_product_maximal {b : ℕ} (hb : 2≤b) (s : ℕ) (S : Finset ℕ) (keep : ℕ → Bool) :
    Tendsto (radixDiscrepancy b (maskedValue b S keep (C (1/2)*X^(s+1)*(X-1)) s)) atTop (𝓝 1) := by
  let Q : ℚ[X] := C (1/2)*X*(X-1)
  have eqn : C (1/2)*X^(s+1)*(X-1)=X^s*Q := by dsimp [Q]; rw [pow_succ]; ring
  have cancel := masked_cancel b s 0 S keep Q
  simp only [Nat.add_zero] at cancel; rw [eqn,cancel]
  apply maximal_of_grid_one hb (weights_growth ..) (weights_supported S keep Q 0)
  apply grid_of_denominator (t:=0) (l:=0) hb (by decide) (weights_supported S keep Q 0) _ (Or.inl rfl)
  intro m sm
  by_cases km : keep m=true
  · obtain ⟨z,hz⟩ := (Int.even_mul_pred_self (m:ℤ)).two_dvd
    have eqn : weights S keep Q 0 m=(z:ℚ) := by
      simp [weights,Q,sm,km]
      have h : (m:ℚ)*(m-1)=2*z := by exact_mod_cast hz
      linarith
    simp [eqn]
  · simp [weights,km]

/-- The depth-two unsigned certificate for 5 and 13 proves binary normality
for every rational numerator nonzero at zero and a simple residual pole. -/
theorem five_thirteen_polynomial_normal (P : ℚ[X]) (p0 : P.eval 0 ≠ 0) :
    NormalIn 2 (maskedValue 2 {2,5,13} (fun _ => true) P 1) := by
  apply normal_of_radix_limsup_zero (by decide)
  have cert := polynomial_certificate_bound (b:=2) (p:=5) (t:=1) (by decide) (by decide)
    (by decide) (by decide) P p0 {2,13} (by intro q hq; simp at hq; rcases hq with rfl|rfl <;> decide) (by decide) 1
  rw [LocalizedSupport.five_thirteen_precision_two.1,Rat.cast_zero] at cert
  simpa only [Finset.insert_comm] using cert

end NormalityChecker.PolynomialMasks
