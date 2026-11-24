module

public import NormalityChecker.StonehamPolynomialNormal
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Rational polynomials of the standard Stoneham number and same-prime products. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.StonehamPolynomial

/-- The single leading monomial criterion allows arbitrary rational coefficients. -/
theorem rational_sum_normal_at {ι : Type*} {b c p : ℕ} (hb : 2 ≤ b) (hc : 3 ≤ c)
    (hp : p.Prime) (pc : p ∣ c) (stable : StablePowers b c p)
    (cop : b.Coprime c) (t : Monomial) (degree : 0 < t.degree) (lead : ℚ) (nc : lead ≠ 0)
    (s : Finset ι) (u : ι → Monomial) (a : ι → ℚ) (lt : ∀ i ∈ s, (u i).degree < t.degree) :
    NormalIn b ((lead:ℝ) * t.value b c + ∑ i ∈ s, (a i:ℝ)*(u i).value b c) := by
  classical
  let S := insert lead (s.image a)
  let D := ∏ q ∈ S, q.den
  have pos : 0 < D := prod_pos (fun q _ => q.pos)
  let z (q : ℚ) : ℤ := (D/q.den:ℕ)*q.num
  have eqn (q : ℚ) (hq : q ∈ S) : (z q:ℝ) = D*(q:ℝ) := by
    have div : q.den ∣ D := dvd_prod_of_mem Rat.den hq
    have fac : ((D/q.den:ℕ):ℝ)*q.den = D := by exact_mod_cast Nat.div_mul_cancel div
    have cross : (q.num:ℝ) = (q.den:ℝ)*(q:ℝ) := by exact_mod_cast (Rat.den_mul_eq_num q).symm
    simp only [z,Int.cast_mul,Int.cast_natCast]; rw [cross,← mul_assoc,fac]
  have member : lead ∈ S := mem_insert_self ..
  have nz : z lead ≠ 0 := fun h =>
    (mul_ne_zero (Nat.cast_ne_zero.mpr pos.ne') (Rat.cast_ne_zero.mpr nc) : (D:ℝ)*(lead:ℝ) ≠ 0)
      ((eqn lead member).symm.trans (by simp [h]))
  have result := integer_sum_normal_at hb hc hp pc stable cop t degree (z lead) nz s u (z ∘ a) lt
  apply (normal_mul_nat_iff hb pos _).mp
  rw [mul_add,mul_sum]
  have e : (∑ i ∈ s, ((z ∘ a) i:ℝ)*(u i).value b c) =
      ∑ i ∈ s, (D:ℝ)*((a i:ℝ)*(u i).value b c) := by
    apply sum_congr rfl
    intro i hi
    rw [Function.comp_apply,eqn (a i) (mem_insert_of_mem (mem_image_of_mem _ hi)),mul_assoc]
  rwa [eqn lead member,mul_assoc,e] at result

/-- The odd-prime specialization of the rational leading-monomial criterion. -/
theorem rational_sum_normal {ι : Type*} {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (t : Monomial) (degree : 0 < t.degree) (c : ℚ) (nc : c ≠ 0)
    (s : Finset ι) (u : ι → Monomial) (a : ι → ℚ) (lt : ∀ i ∈ s, (u i).degree < t.degree) :
    NormalIn b ((c:ℝ) * t.value b p + ∑ i ∈ s, (a i:ℝ)*(u i).value b p) :=
  rational_sum_normal_at hb odd hp dvd_rfl (stablePowers_prime hp cop) cop t degree c nc s u a lt

/-- The classical Stoneham series, starting at the first positive index. -/
noncomputable def alpha (b p : ℕ) : ℝ :=
  ∑' j : ℕ, 1 / ((p:ℝ)^(j+1) * (b:ℝ)^(p^(j+1):ℕ))

private lemma axis_shift {b p : ℕ} (hp : 0 < p) (m : ℕ) :
    axis b p (m*p) = (p:ℝ)*alpha (b^m) p := by
  rw [alpha,axis,← tsum_mul_left]; apply tsum_congr
  intro j
  rw [Nat.cast_pow,← pow_mul,pow_succ' p, pow_succ' (p:ℝ),← Nat.mul_assoc,inv_pow]
  field_simp

namespace Monomial

/-- Each factor chooses a positive power of the radix and of the common prime. -/
noncomputable def standardValue (t : Monomial) (b p : ℕ) :=
  ∏ i, alpha (b^(t.parameter i)) (p^(t.stride i : ℕ))

/-- Shift each factor by its first positive stride. -/
def shifted (t : Monomial) {p : ℕ} (hp : 0 < p) : Monomial :=
  ⟨t.degree,fun i => t.parameter i*p^(t.stride i : ℕ),fun i => Nat.mul_pos (t.positive i) (pow_pos hp _),t.stride⟩

/-- Convert an index-zero product to the standard index-one normalization. -/
lemma shifted_value (t : Monomial) {b p : ℕ} (hp : 0 < p) :
    (t.shifted hp).value b p = (p:ℝ)^(∑ i, (t.stride i : ℕ)) * t.standardValue b p := by
  change (∏ i : Fin t.degree, axis b (p^(t.stride i : ℕ)) (t.parameter i * p^(t.stride i : ℕ))) = _
  simp only [standardValue, axis_shift (pow_pos hp _),Nat.cast_pow,prod_mul_distrib,prod_pow_eq_pow_sum]

end Monomial

/-- In a finite rational linear combination of products of `α(bᵐ,pᵉ)`, one
nonzero monomial of positive degree strictly above every other degree suffices
for normality in base `b`. -/
theorem standard_sum_normal_at {ι : Type*} {b c p : ℕ} (hb : 2 ≤ b) (hc : 3 ≤ c)
    (hp : p.Prime) (pc : p ∣ c) (stable : StablePowers b c p)
    (cop : b.Coprime c) (t : Monomial) (degree : 0 < t.degree) (lead : ℚ) (nc : lead ≠ 0)
    (s : Finset ι) (u : ι → Monomial) (a : ι → ℚ) (lt : ∀ i ∈ s, (u i).degree < t.degree) :
    NormalIn b ((lead:ℝ) * t.standardValue b c + ∑ i ∈ s, (a i:ℝ)*(u i).standardValue b c) := by
  have hc₀ : 0 < c := by omega
  let normalize (v : Monomial) (q : ℚ) := q/(c:ℚ)^(∑ i, (v.stride i : ℕ))
  have scaled (v : Monomial) (q : ℚ) : ((normalize v q:ℚ):ℝ)*(v.shifted hc₀).value b c =
      (q:ℝ)*v.standardValue b c := by
    simp only [normalize, Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Monomial.shifted_value v hc₀]
    field_simp
  have res := rational_sum_normal_at hb hc hp pc stable cop (t.shifted hc₀) degree (normalize t lead)
    (div_ne_zero nc (pow_ne_zero _ (by positivity))) s
    (fun i => (u i).shifted hc₀) (fun i => normalize (u i) (a i)) lt
  simpa only [scaled] using res

/-- The odd-prime specialization for products of positive-index generators. -/
theorem same_prime_sum_normal {ι : Type*} {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (t : Monomial) (degree : 0 < t.degree) (c : ℚ) (nc : c ≠ 0)
    (s : Finset ι) (u : ι → Monomial) (a : ι → ℚ) (lt : ∀ i ∈ s, (u i).degree < t.degree) :
    NormalIn b ((c:ℝ) * t.standardValue b p + ∑ i ∈ s, (a i:ℝ)*(u i).standardValue b p) :=
  standard_sum_normal_at hb odd hp dvd_rfl (stablePowers_prime hp cop) cop t degree c nc s u a lt

/-- Every nonempty product of standard Stoneham numbers with parameters that
are powers of the same odd prime is normal in the common radix. The first
parameter of each factor can also be a positive power of that radix. -/
theorem prime_power_product_normal {b p d : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (hd : 0 < d) (m : Vector d) (hm : ∀ i, 0 < m i) (e : Strides d) :
    NormalIn b (∏ i, alpha (b^(m i)) (p^(e i : ℕ))) := by
  let t : Monomial := ⟨d,m,hm,e⟩
  simpa [t,Monomial.standardValue] using same_prime_sum_normal hb hp odd cop t hd 1 one_ne_zero
    (∅ : Finset Unit) (fun _ => t) (fun _ => 0) (by simp)

theorem same_prime_product_normal {b p d : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (hd : 0 < d) (m : Vector d) (hm : ∀ i, 0 < m i) :
    NormalIn b (∏ i, alpha (b^(m i)) p) := by
  simpa using prime_power_product_normal hb hp odd cop hd m hm (fun _ => 1)

/-- A mixed example with the two denominator parameters three and nine. -/
theorem binary_three_nine_product : NormalIn 2 (alpha 2 3 * alpha 2 9) := by
  have h := prime_power_product_normal (b:=2) (p:=3) (d:=2) (by decide) Nat.prime_three
    (by decide) (by decide) (by decide) (fun _ => 1) (fun _ => Nat.zero_lt_one) ![1,2]
  simpa [Fin.prod_univ_two] using h

/-- Every positive integral power of the standard number is normal. -/
theorem power_normal {b p d : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (hd : 0 < d) : NormalIn b (alpha b p ^ d) := by
  simpa using same_prime_product_normal hb hp odd cop hd (fun _ => 1) (fun _ => Nat.zero_lt_one)

/-- Every nonconstant rational polynomial of the standard Stoneham number is
normal in its radix. -/
theorem polynomial_normal_at {b c p : ℕ} (hb : 2 ≤ b) (hc : 3 ≤ c) (hp : p.Prime)
    (pc : p ∣ c) (stable : StablePowers b c p) (cop : b.Coprime c) (e : ℕ+) (P : ℚ[X]) (degree : 0 < P.natDegree) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b (c^(e : ℕ)))) := by
  let term (d : ℕ) : Monomial := ⟨d,fun _ => 1, fun _ => Nat.zero_lt_one, fun _ => e⟩
  have lead : P.coeff P.natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (fun eqn => by simp [eqn] at degree)
  have h := standard_sum_normal_at hb hc hp pc stable cop (term P.natDegree) degree _ lead
    (range P.natDegree) term P.coeff (fun _ hi => mem_range.mp hi)
  rw [Polynomial.eval₂_eq_sum_range, sum_range_succ, add_comm]
  simpa only [Monomial.standardValue,term,pow_one,prod_const,card_univ,Fintype.card_fin,
    show ∀ q : ℚ, (algebraMap ℚ ℝ) q = (q:ℝ) from fun _ => rfl] using h

/-- Rational polynomials of a generator with odd prime-power parameter. -/
theorem prime_power_polynomial_normal {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (e : ℕ+) (P : ℚ[X]) (degree : 0 < P.natDegree) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b (p^(e : ℕ)))) :=
  polynomial_normal_at hb odd hp dvd_rfl (stablePowers_prime hp cop) cop e P degree

theorem polynomial_normal {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (P : ℚ[X]) (degree : 0 < P.natDegree) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b p)) := by
  simpa using prime_power_polynomial_normal hb hp odd cop 1 P degree

theorem binary_power_normal {d : ℕ} (hd : 0 < d) : NormalIn 2 (alpha 2 3 ^ d) :=
  power_normal (by decide) Nat.prime_three (by decide) (by decide) hd

theorem binary_polynomial_normal (P : ℚ[X]) (degree : 0 < P.natDegree) :
    NormalIn 2 (P.eval₂ (algebraMap ℚ ℝ) (alpha 2 3)) :=
  polynomial_normal (by decide) Nat.prime_three (by decide) (by decide) P degree

end NormalityChecker.StonehamPolynomial
