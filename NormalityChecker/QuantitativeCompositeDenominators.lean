module

public import NormalityChecker.PeriodicPolynomialNormal
public import NormalityChecker.StonehamOddDegree
public import NormalityChecker.ParameterTwoSquareProfile
public import NormalityChecker.QuantitativeStonehamDiscrepancy
import all NormalityChecker.StonehamPolynomialRetention

/-! Two-sided denominator bounds for the quantitative single-generator theorem. -/
@[expose] public section
open Finset
namespace NormalityChecker.QuantitativeStoneham
open StonehamPolynomial

/-- Combine bounded losses at every prime of `c` into one fixed power of `c`.
The threshold and loss can both be taken to be maxima over the prime divisors. -/
theorem denominator_of_prime_losses {c d : ℕ} (hc : 0 < c) (Q : ℕ → ℕ) (hQ : ∀ n, 0 < Q n)
    (retain : ∀ p ∈ c.primeFactors, ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log c n → 0 < n →
      p^(c.factorization p * (d * Nat.log c n) - L) ∣ Q n) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log c n → 0 < n → c^(d * Nat.log c n - L) ∣ Q n := by
  classical
  choose loss start pass using fun p : {p // p ∈ c.primeFactors} => retain p p.property
  let L := c.primeFactors.attach.sup loss
  let K := c.primeFactors.attach.sup start
  refine ⟨L, K, fun n late pos => ?_⟩
  apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ hc.ne') (hQ n).ne').mp
  intro p hp
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.mul_comm _ (c.factorization p)]
  by_cases pc : p ∣ c
  · let i : {p // p ∈ c.primeFactors} := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, pc, hc.ne'⟩⟩
    have lp : loss i ≤ L := le_sup (mem_attach _ i)
    have kp : start i ≤ K := le_sup (mem_attach _ i)
    have ep := hp.factorization_pos_of_dvd hc.ne' pc
    have bound := (hp.pow_dvd_iff_le_factorization (hQ n).ne').mp (pass i n (kp.trans late) pos)
    change c.factorization p * (d * Nat.log c n) - loss i ≤ (Q n).factorization p at bound
    rw [Nat.mul_sub]
    exact (Nat.sub_le_sub_left (lp.trans (Nat.le_mul_of_pos_left L ep)) _).trans bound
  · simp [Nat.factorization_eq_zero_of_not_dvd pc]

/-- `productPrefix` uses zero-based indices. With multiplier `c` in every
coordinate it is `c^a` times the positive-index prefix of the `a`-th power. -/
def powerAxis (c a : ℕ) (hc : 0 < c) : Monomial := ⟨a, fun _ => c, fun _ => hc, fun _ => 1⟩

/-- Prefix with the integer coefficients obtained after clearing the finite
indexing factors and the rational coefficient denominators. -/
def integerPowerPrefix (b c d : ℕ) (hc : 0 < c) (a : ℕ → ℤ) (n : ℕ) : ℚ :=
  ∑ i ∈ range (d+1), (a i : ℚ) * (powerAxis c i hc).model b c n

/-- At every late cutoff, a polynomial prefix of a single axis has the full
degree as denominator slope. Division by a fixed `D` preserves the lower bound
and adds at most `D` to the upper bound as a factor. -/
theorem polynomial_prefix_denominators {b c d D : ℕ} (hc : 2 ≤ c) (cop : b.Coprime c)
    (family : 2 < c ∨ ∃ q r : ℕ, q.Prime ∧ 2 < q ∧ d = q^r)
    (hd : 0 < d) (a : ℕ → ℤ) (lead : a d ≠ 0) (hD : 0 < D) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log c n → 0 < n →
      let Q := (integerPowerPrefix b c d (by omega) a n / D).den
      c^(d * Nat.log c n - L) ∣ Q ∧ Q ∣ D * c^(d * Nat.log c n) := by
  let hc' : 0 < c := by omega
  let t := powerAxis c d hc'
  let R (n : ℕ) := ∑ i ∈ range d, (a i : ℚ) * (powerAxis c i hc').model b c n
  let Y := integerPowerPrefix b c d hc' a
  have eqn (n : ℕ) : Y n = (a d : ℚ) * t.model b c n + R n := by
    simp only [Y, integerPowerPrefix, sum_range_succ, t, R, add_comm]
  have lower (n : ℕ) : (R n).den ∣ c^((d-1)*Nat.log c n) :=
    combination_denominator hc' _ _ _ (fun i hi => by
      change i ≤ d-1; have := mem_range.mp hi; omega) n
  have upper (n : ℕ) : (Y n).den ∣ c^(d*Nat.log c n) :=
    combination_denominator hc' _ _ _ (fun i hi => by
      change i ≤ d; have := mem_range.mp hi; omega) n
  have localLoss (p : ℕ) (mem : p ∈ c.primeFactors) :
      ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log c n → 0 < n →
        p^(c.factorization p * (d * Nat.log c n) - L) ∣ (Y n).den := by
    obtain ⟨hp, pc, _⟩ := Nat.mem_primeFactors.mp mem
    simp_rw [eqn]
    by_cases big : 2 < c
    · apply retained_with_lower_terms_of_retainsAt hp big pc t _ hd _ lead _ lower
      exact periodic_power_retained_denominator big hp pc (cop.coprime_dvd_right pc) c
    · obtain rfl : c = 2 := by omega
      have pp : p = 2 := (Nat.prime_two.eq_one_or_self_of_dvd p pc).resolve_left hp.ne_one
      subst p
      obtain ⟨q, r, hq, odd, hdeg⟩ := family.resolve_left big
      simp only [Nat.prime_two.factorization_self, one_mul]
      apply perturbation_retains_denominator Nat.prime_two t _ hd _ lead _ lower
      exact binary_power_retained_denominator cop hq odd hdeg 2
  obtain ⟨L, K, pass⟩ := denominator_of_prime_losses hc' _ (fun n => (Y n).pos) localLoss
  refine ⟨L, K, fun n late pos => ?_⟩
  obtain ⟨keep, bound⟩ := divided_prefix_denominator (Y n) hD
  exact ⟨(pass n late pos).trans keep, bound.trans (Nat.mul_dvd_mul_left D (upper n))⟩

/-- The two different denominator slopes on a dyadic square shell give a
uniform interval from `2^(k-1)` to `2^(2*k-2)`, including the midpoint. -/
theorem square_shell_denominator {b k n : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hk : 2 ≤ k)
    (lo : 2^k ≤ n) (hi : n < 2^(k+1)) :
    2^(k-1) ∣ (ParameterTwoSquare.pre b n).den ∧
      (ParameterTwoSquare.pre b n).den ∣ 2^(2*k-2) := by
  rw [(ParameterTwoSquare.exact_profile hb odd).2 k hk n lo hi]
  have h := pow_dvd_pow 2 (show k-1 ≤ 2*k-2 by omega)
  split <;> simp [h]

end NormalityChecker.QuantitativeStoneham
