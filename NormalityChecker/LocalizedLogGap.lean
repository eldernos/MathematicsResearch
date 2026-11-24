module

public import NormalityChecker.SmoothCertificates

/-! Uniform unshifted error for finite-support approximations to the binary logarithm. -/
@[expose] public section
open Finset
namespace NormalityChecker.LocalizedSupport

/-- The first missing positive index determines the approximation error within
an absolute factor of two, independent of every other prime in the support. -/
theorem first_omission_bounds (A : Finset ℕ) (k : ℕ) (missing : k+1∉Nat.factoredNumbers A)
    (before : ∀ i<k, i+1∈Nat.factoredNumbers A) :
    let first := (1/2:ℝ)^(k+1)/(k+1)
    first ≤ Real.log 2-powerValue 2 1 A ∧ Real.log 2-powerValue 2 1 A ≤ 2*first := by
  classical
  let t (i : ℕ) := (1/2:ℝ)^(i+1)/(i+1)
  let g (i : ℕ) := if i+1∈Nat.factoredNumbers A then 0 else t i
  have pos (i : ℕ) : 0≤g i := by dsimp [g,t]; split <;> positivity
  have cap (i : ℕ) : g i≤t i := by dsimp [g]; split <;> first | exact le_rfl | dsimp [t]; positivity
  have sm : Summable g := Summable.of_nonneg_of_le pos cap hasSum_logTwo.summable
  have eqn : Real.log 2-powerValue 2 1 A=∑' i,g i := by
    have sub := hasSum_logTwo.sub sm.hasSum
    have term (i : ℕ) : t i-g i=(powerCoefficient 1 A i:ℝ)/(2:ℝ)^(i+1) := by
      unfold g t powerCoefficient; split_ifs <;> push_cast <;> rw [one_div_pow] <;> ring_nf
    have H : powerValue 2 1 A=Real.log 2-∑' i,g i := (sub.congr_fun (fun i => (term i).symm)).tsum_eq
    linarith
  rw [eqn]; dsimp only
  have first : t k=g k := by simp [g,missing]
  refine ⟨first.trans_le (sm.le_tsum k (fun i _ => pos i)),?_⟩
  have prefixZero : ∑ i∈range k,g i=0 := sum_eq_zero (fun i hi => by simp [g,before i (mem_range.mp hi)])
  rw [← sm.sum_add_tsum_nat_add k,prefixZero,zero_add]
  have geom := (summable_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).mul_left (t k)
  apply (((summable_nat_add_iff k).mpr sm).tsum_le_tsum (g:=fun i => t k*(1/2:ℝ)^i) _ geom).trans_eq
  · rw [tsum_mul_left,tsum_geometric_two]; ring
  · intro i; apply (cap _).trans
    unfold t; rw [show i+k+1=k+1+i by omega,pow_add,div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); push_cast; linarith

end NormalityChecker.LocalizedSupport
