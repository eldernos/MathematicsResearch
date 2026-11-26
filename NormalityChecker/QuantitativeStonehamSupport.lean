module

public import NormalityChecker.QuantitativeStonehamDiscrepancy
public import Mathlib.NumberTheory.EulerProduct.Basic

/-! Fixed-support averaging and a shell bound that permits unequal denominator slopes. -/
@[expose] public section
open Finset
namespace NormalityChecker.QuantitativeStoneham

/-- Euler factor for the frequency loss on a fixed set of allowed primes. -/
noncomputable def supportFactor (s : ℕ) (α : ℝ) :=
  ∏ p ∈ s.primeFactors, (1 - (p : ℝ)^(α-1))⁻¹

/-- The uniform Euler product also covers a proper subset of the allowed
primes and the empty support of `Q = 1`. -/
theorem divisor_sum_le_supportFactor {s Q : ℕ} (hQ : 0 < Q)
    (support : Q.primeFactors ⊆ s.primeFactors) {α : ℝ} (hα : α < 1) :
    ∑ t ∈ Q.divisors, (t : ℝ)^(α-1) ≤ supportFactor s α := by
  classical
  let f : ℕ →* ℝ := ⟨⟨fun n => (n : ℝ)^(α-1), by simp⟩, fun x y => by
    simp [Real.mul_rpow (Nat.cast_nonneg x) (Nat.cast_nonneg y)]⟩
  have nonneg (n : ℕ) : 0 ≤ f n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have small {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    rw [Real.norm_of_nonneg (nonneg _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have mass := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    small s.primeFactors).2
  have memQ := Nat.mem_factoredNumbers_of_primeFactors_subset hQ.ne' support
  let incl : Q.divisors ↪ Nat.factoredNumbers s.primeFactors :=
    ⟨fun t => ⟨t.val, Nat.mem_factoredNumbers_of_dvd memQ (Nat.dvd_of_mem_divisors t.property)⟩,
      fun _ _ h => Subtype.ext (congrArg (fun t : Nat.factoredNumbers s.primeFactors => t.val) h)⟩
  have bound := mass.summable.sum_le_tsum (Q.divisors.attach.map incl) (fun i _ => nonneg i.val)
  rw [mass.tsum_eq, sum_map, filter_true_of_mem (fun _ => Nat.prime_of_mem_primeFactors)] at bound
  change (∑ t ∈ Q.divisors.attach, f t.val) ≤ supportFactor s α at bound
  rwa [sum_attach] at bound

private lemma sum_lengths (cut : ℕ → ℕ) (first : cut 0 = 0) (J : ℕ)
    (inc : ∀ j < J, cut j < cut (j+1)) : ∑ j ∈ range J, (cut (j+1)-cut j) = cut J := by
  induction J with
  | zero => simp [first]
  | succ J ih =>
    rw [sum_range_succ, ih (fun j hj => inc j (by omega))]
    have := inc J (Nat.lt_succ_self J); omega

/-- Unnormalized discrepancy at every cut. `lo` and `hi` bound the reduced
starting denominators, without a common growth exponent. The two external
inequalities are explicit hypotheses. The lengths can include singletons. -/
theorem discrepancy_of_denominator_range {b s J H lo hi : ℕ} {C τ A B α γ ν r : ℝ}
    (orbit : FixedSupportBound b s (orbitBound A B α γ ν r)) (et : ErdosTuran C)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ α) (ha' : α < 1) (hr : 0 ≤ r)
    (hs : 0 < s) (hlo : 0 < lo) (u : ℕ → ℝ) (cut : ℕ → ℕ) (y : ℕ → ℚ)
    (first : cut 0 = 0) (inc : ∀ j < J, cut j < cut (j+1)) (len : 0 < cut J) (freq : 0 < H)
    (smooth : ∀ j < J, ∃ k, (y j).den ∣ s^k) (bounds : ∀ j < J, lo ≤ (y j).den ∧ (y j).den ≤ hi)
    (close : ∀ j < J, ∀ i < cut (j+1)-cut j, |u (cut j+i) - (b : ℝ)^i*y j| ≤ τ) :
    let L (j : ℕ) := ((cut (j+1)-cut j : ℕ) : ℝ)
    cut J * CircleDiscrepancy.disc u (cut J) ≤ C * (cut J / ((H : ℝ)+1) +
      (1 + Real.log hi)^r * (1 + Real.log H) *
        (A * (hi : ℝ)^α * (∑ j ∈ range J, (L j)^γ) +
          B * (lo : ℝ)^(-α) * supportFactor s α * (∑ j ∈ range J, (L j)^ν)) +
      H * (cut J * (2*Real.pi*τ))) := by
  let L (j : ℕ) := ((cut (j+1)-cut j : ℕ) : ℝ)
  let Z := (1 + Real.log hi)^r * (1 + Real.log H)
  have posQ (j : ℕ) : (1 : ℝ) ≤ (y j).den := by exact_mod_cast (y j).pos
  have posH : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast freq)
  have each (j : ℕ) (hj : j ∈ range J) := bounds j (mem_range.mp hj)
  have eachBound (j : ℕ) (hj : j ∈ range J) :
      let Q := (y j).den
      (1+Real.log Q)^r * (1+Real.log H) *
        (A*(Q : ℝ)^α*(L j)^γ + B*(Q : ℝ)^(-α)*(L j)^ν*∑ t ∈ Q.divisors, (t : ℝ)^(α-1)) ≤
        Z*(A*(hi : ℝ)^α*(L j)^γ + B*(lo : ℝ)^(-α)*(L j)^ν*supportFactor s α) := by
    obtain ⟨k, div⟩ := smooth j (mem_range.mp hj)
    have support := (Nat.exists_dvd_pow_iff (y j).pos.ne' hs.ne').mp ⟨k,div⟩
    have upper : ((y j).den : ℝ) ≤ hi := by exact_mod_cast (each j hj).2
    have lower : (lo : ℝ) ≤ (y j).den := by exact_mod_cast (each j hj).1
    have inv := Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hlo : 0 < (lo : ℝ)) lower (neg_nonpos.mpr ha)
    have euler := divisor_sum_le_supportFactor (y j).pos support ha'
    have logQ := Real.log_nonneg (posQ j)
    have logHi := Real.log_nonneg ((posQ j).trans upper)
    dsimp only [Z]
    gcongr
  apply (discrepancy_of_vandehey orbit et hC hA hB ha hr u cut y first inc len freq smooth close).trans
  apply mul_le_mul_of_nonneg_left _ hC
  change _ ≤ _ + Z * _ + _
  rw [add_assoc]
  apply add_le_add le_rfl
  rw [sum_add_distrib]
  apply add_le_add
  · apply (sum_le_sum eachBound).trans_eq
    rw [← mul_sum, sum_add_distrib, ← mul_sum]
    congr 2
    simp_rw [mul_right_comm (B * (lo : ℝ)^(-α)) _ (supportFactor s α), mul_sum, L]
  · have lengths : ∑ j ∈ range J, L j = (cut J : ℝ) := by
      dsimp [L]; exact_mod_cast sum_lengths cut first J inc
    dsimp only [L] at lengths
    rw [← mul_sum, ← sum_mul, lengths]

end NormalityChecker.QuantitativeStoneham
