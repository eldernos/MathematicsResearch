module

public import NormalityChecker.StonehamSymmetricMass
public import NormalityChecker.StonehamPolynomialRetention
import all NormalityChecker.StonehamPolynomialPrefix
import all NormalityChecker.StonehamPolynomial

/-! Odd prime-power degrees for the Stoneham number with denominator parameter two. -/

@[expose] public section
open Finset Polynomial
namespace NormalityChecker.StonehamPolynomial

private lemma symmetric_cut (d m k n : ℕ) :
    SymmetricSet (cut 2 (fun _ : Fin d => 1) (fun _ => m) k n) := by
  intro v σ
  simp only [cut, Set.mem_ofPred_eq, position, stretch, reflect, caps, PNat.val_ofNat,
    Nat.div_one, one_mul, Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => m * 2^(k - v i))]

/-- The prefix of a product of identical binary axes in odd prime-power
dimension retains all but a bounded number of its expected denominator factors. -/
theorem binary_power_retained_denominator {b d q r : ℕ} (cop : b.Coprime 2)
    (hq : q.Prime) (odd : 2 < q) (hd : d = q^r) (m : ℕ) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log 2 n → 0 < n →
      2^(d * Nat.log 2 n - L) ∣ (productPrefix b 2 (fun _ : Fin d => 1) (fun _ => m) n).den := by
  let e : Strides d := fun _ => 1
  let t : Vector d := fun _ => m
  let J := d*m
  obtain ⟨L,pass⟩ := symmetric_binary_uniform_precision hq odd hd J
  refine ⟨L,max (2*L) J,fun n late pos => ?_⟩
  let k := Nat.log 2 n
  have jl : J ≤ k := (le_max_right ..).trans late
  have near (i : Fin d) : 2*L ≤ caps e k i := by
    simpa [e,caps] using (le_max_left (2*L) J).trans late
  have hit : (fun _ => J) ∈ cut 2 e t k n := by
    have h : J * 2^(k-J) ≤ 2^k := calc
      _ ≤ 2^J * 2^(k-J) := Nat.mul_le_mul_right _ (Nat.lt_pow_self (n:=J) (by decide : 1<2)).le
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le jl]
    simpa [cut, position, stretch, reflect, caps, e, t, J, mul_assoc] using h.trans (Nat.pow_log_le_self 2 pos.ne')
  have stable (j k' : ℕ) (hj : L ≤ j) (hk : L ≤ k') :
      (b : ZMod (2^L))^(2^k') = b^(2^j) :=
    (stable_power Nat.prime_two cop le_rfl hk).trans (stable_power Nat.prime_two cop le_rfl hj).symm
  have nz := numerator_nonzero (dvd_rfl : 2 ∣ 2) cop stable e t (fun i => by
    simpa only [two_mul] using near i)
    (pass _ (cut_upper (by decide) e t k n) (symmetric_cut d m k n) hit)
  let A := numerator b 2 e t k n
  let x := productPrefix b 2 e t n
  have no : ¬2^L ∣ A := fun div => nz ((ZMod.natCast_eq_zero_iff ..).mpr div)
  have ne : A ≠ 0 := fun h => no (h ▸ dvd_zero _)
  have low : A.factorization 2 < L :=
    lt_of_not_ge fun h => no ((Nat.prime_two.pow_dvd_iff_le_factorization ne).mpr h)
  have sc : scale e k = d*k := by simp [scale, weight, stretch, caps, e]
  have reduced := reduced_info (S:=A) (x:=x) (pow_pos (by decide : 0<2) (scale e k))
    (by exact_mod_cast scaled (b:=b) (n:=n) (by decide : 0<2) e t)
  have div : 2^(scale e k) ∣ A*x.den := reduced.2 ▸ dvd_mul_right _ _
  have le := (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.mul_ne_zero ne x.pos.ne')).mp div
  rw [Nat.factorization_mul ne x.pos.ne', Finsupp.add_apply, sc] at le
  exact (Nat.prime_two.pow_dvd_iff_le_factorization x.pos.ne').mpr (by change d*k-L ≤ _; omega)

/-- Every rational polynomial of odd prime-power degree in the standard
Stoneham number with denominator parameter two is normal in its odd radix. -/
theorem odd_prime_power_degree_polynomial_normal {b q r : ℕ} (hb : 2 ≤ b) (oddBase : Odd b)
    (hq : q.Prime) (oddPrime : 2 < q) (P : ℚ[X]) (hd : P.natDegree = q^r) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b 2)) := by
  have cop : b.Coprime 2 := Nat.coprime_two_right.mpr oddBase
  let term (d : ℕ) : Monomial := ⟨d, fun _ => 2, fun _ => by decide, fun _ => 1⟩
  let c (d : ℕ) := P.coeff d / 2^d
  have degree : 0 < P.natDegree := hd ▸ pow_pos hq.pos _
  have lead : c P.natDegree ≠ 0 :=
    div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (fun h => by simp [h] at degree)) (by positivity)
  have retain : RetainsDenominator b 2 (term P.natDegree) :=
    binary_power_retained_denominator cop hq oddPrime hd 2
  have result := rational_sum_normal_of_retention hb Nat.prime_two cop (term P.natDegree) retain
    degree _ lead (range P.natDegree) term c (fun _ hi => mem_range.mp hi)
  have shifted : axis b 2 2 = 2 * alpha b 2 := by
    simpa using axis_shift (b:=b) (p:=2) (by decide) 1
  have val (d : ℕ) : (c d : ℝ) * (term d).value b 2 = (P.coeff d : ℝ) * alpha b 2 ^ d := by
    simp [c, Monomial.value, term, shifted, mul_pow]
    field_simp
  rw [Polynomial.eval₂_eq_sum_range, sum_range_succ, add_comm]
  simpa only [val, show ∀ q : ℚ, (algebraMap ℚ ℝ) q = (q:ℝ) from fun _ => rfl] using result

/-- In particular, arbitrary rational cubic polynomials are allowed. -/
theorem cubic_polynomial_normal {b : ℕ} (hb : 2 ≤ b) (odd : Odd b)
    (P : ℚ[X]) (degree : P.natDegree = 3) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b 2)) :=
  odd_prime_power_degree_polynomial_normal (r:=1) hb odd Nat.prime_three (by decide) P (by simpa)

/-- The corresponding pure powers, including exponent one. -/
theorem odd_prime_power_degree_power_normal {b q : ℕ} (hb : 2 ≤ b) (oddBase : Odd b)
    (hq : q.Prime) (oddPrime : 2 < q) (r : ℕ) :
    NormalIn b ((alpha b 2) ^ (q^r)) := by
  simpa using odd_prime_power_degree_polynomial_normal (r:=r) hb oddBase hq oddPrime
    ((X : ℚ[X]) ^ (q^r)) (by simp)

/-- The cube of the parameter-two Stoneham number is normal in every odd radix. -/
theorem cube_normal {b : ℕ} (hb : 2 ≤ b) (odd : Odd b) :
    NormalIn b (alpha b 2 ^ 3) := by
  simpa using odd_prime_power_degree_power_normal hb odd Nat.prime_three (by decide) 1

end NormalityChecker.StonehamPolynomial
