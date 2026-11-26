module

public import NormalityChecker.ErdosBorweinArrivals
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic

/-! Exact finite arithmetic identities for the weighted Lambert series
`ln 2 = ∑ a_m / (2^m - 1)` with `a_m = (1/m) ∏_{p | m} (1 - p)` and its
integer-valued multiplicative counterparts. -/

@[expose] public section

open Finset

namespace NormalityChecker.WeightedLambertIdentities

/-- Finite Lambert-to-Taylor head reindexing: for any rational weight sequence `a`,
summing `a m * ∑_{r=1}^{⌊N/m⌋} 2^{N - m*r}` over `1 ≤ m ≤ N` equals the binary-level
head `∑_{n=1}^N (∑_{m | n} a m) * 2^{N - n}`. -/
theorem lambert_head_eq_taylor (a : ℕ → ℚ) (N : ℕ) :
    ∑ m ∈ Icc 1 N, a m * (∑ r ∈ Icc 1 (N / m), (2 : ℚ) ^ (N - m * r)) =
      ∑ n ∈ Icc 1 N, (∑ m ∈ n.divisors, a m) * (2 : ℚ) ^ (N - n) := by
  have lhs_eq :
      ∑ m ∈ Icc 1 N, a m * (∑ r ∈ Icc 1 (N / m), (2 : ℚ) ^ (N - m * r)) =
        ∑ m ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
          if m * r ≤ N then a m * (2 : ℚ) ^ (N - m * r) else 0 := by
    apply sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
    have hm0 : 0 < m := by omega
    rw [mul_sum, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext r
    simp only [mem_Icc, mem_filter]
    constructor
    · rintro ⟨hr1, hr2⟩
      have hmul : m * r ≤ N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm0).mp hr2
      have hrN : r ≤ N := le_trans (Nat.le_mul_of_pos_left r hm0) hmul
      exact ⟨⟨hr1, hrN⟩, hmul⟩
    · rintro ⟨⟨hr1, _⟩, hmul⟩
      exact ⟨hr1, (Nat.le_div_iff_mul_le hm0).mpr (by rw [mul_comm]; exact hmul)⟩
  have rhs_eq :
      ∑ n ∈ Icc 1 N, (∑ m ∈ n.divisors, a m) * (2 : ℚ) ^ (N - n) =
        ∑ m ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
          if m * r ≤ N then a m * (2 : ℚ) ^ (N - m * r) else 0 := by
    have step1 :
        ∑ n ∈ Icc 1 N, (∑ m ∈ n.divisors, a m) * (2 : ℚ) ^ (N - n) =
          ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
            if m ∣ n then a m * (2 : ℚ) ^ (N - n) else 0 := by
      apply sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      have hnN : n ≤ N := (mem_Icc.mp hn).2
      rw [sum_mul, ← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext m
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
        have hmle : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
        exact ⟨⟨hmpos, le_trans hmle hnN⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩
        exact ⟨hdvd, hn0⟩
    rw [step1, sum_comm]
    apply sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
    have hm0 : 0 < m := by omega
    rw [← sum_filter, ← sum_filter]
    refine Finset.sum_nbij (fun n => n / m) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      obtain ⟨⟨hn1, hnN⟩, ⟨r, rfl⟩⟩ := hn
      have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · simp at hn1
        · exact hr
      rw [Nat.mul_div_cancel_left r hm0]
      exact ⟨⟨hr0, le_trans (Nat.le_mul_of_pos_left r hm0) hnN⟩, hnN⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      dsimp only at heq
      have h1 := Nat.mul_div_cancel' (mem_filter.mp hn₁).2
      have h2 := Nat.mul_div_cancel' (mem_filter.mp hn₂).2
      rw [← h1, ← h2, heq]
    · intro r hr
      have hr' := mem_filter.mp hr
      have hrc := mem_Icc.mp hr'.1
      refine ⟨m * r, ?_, Nat.mul_div_cancel_left r hm0⟩
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega)), hr'.2⟩,
        dvd_mul_right m r⟩
    · intro n hn
      rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]
  rw [lhs_eq, rhs_eq]

/-- Exact prime-band identity in the Lambert head: for every prime `p` with `N/2 < p ≤ N`,
the single Lambert term `a_p * 2^{N - p}` differs from the Taylor term `2^{N - p} / p`
by the integer `-2^{N - p}`. -/
theorem lambert_prime_band_mod_one (p N : ℕ) (hp : p ≠ 0) :
    ((1 - (p : ℚ)) / p) * (2 : ℚ) ^ (N - p) + (2 : ℚ) ^ (N - p) =
      (2 : ℚ) ^ (N - p) / p := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  field_simp [hpq]
  ring

/-- Non-cancellation at the largest prime factor: if `p` is prime and every prime `q ∈ S`
satisfies `q ≤ p`, then `p` does not divide `∏ q ∈ S, (q - 1)`. In particular, for `m ≥ 2`
and `p = P^+(m)`, `p` never cancels from the denominator of `a_m = (1/m) ∏_{q|m} (1 - q)`. -/
theorem largest_prime_not_dvd_prod_sub_one {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≤ p) :
    ¬ (p ∣ ∏ q ∈ S, (q - 1)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [hp.not_dvd_one]
  | insert a s has ih =>
    rw [prod_insert has]
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with ha | hs
    · obtain ⟨ha_prime, ha_le⟩ := hS a (mem_insert_self a s)
      have ha_pos : 0 < a - 1 := by have := ha_prime.two_le; omega
      have ha_lt : a - 1 < p := by have := ha_prime.two_le; omega
      exact Nat.not_dvd_of_pos_of_lt ha_pos ha_lt ha
    · exact ih (fun q hq => hS q (mem_insert_of_mem hq)) hs

/-- Local Bernoulli bound for the integer-cleared numerator `g(m) = m a_m = ∏_{p|m}(1-p)`:
for every prime `p` and exponent `e ≥ 1`, `|1 + e * (1 - p)| < p^e`. -/
theorem cleared_local_abs_lt {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    |(1 : ℤ) + (e : ℤ) * (1 - (p : ℤ))| < (p : ℤ) ^ e := by
  have hp2z : (2 : ℤ) ≤ (p : ℤ) := Int.ofNat_le.mpr hp.two_le
  have h1 : (1 : ℤ) + (e : ℤ) * ((p : ℤ) - 1) ≤ (p : ℤ) ^ e := by
    clear he
    induction e with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      push_cast
      have hsq : (0 : ℤ) ≤ (k : ℤ) * ((p : ℤ) - 1) ^ 2 := by positivity
      have hmul : (1 + (k : ℤ) * ((p : ℤ) - 1)) * (p : ℤ) ≤ (p : ℤ) ^ k * (p : ℤ) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      linarith
  have hez : (1 : ℤ) ≤ (e : ℤ) := Int.ofNat_le.mpr he
  rw [abs_lt]
  constructor <;> nlinarith

/-- Parity of the local factor of `(m a_m) * 1`: for every odd prime `p` and `e ≥ 1`,
`1 + e * (1 - p)` is odd (so odd primes contribute zero 2-adic valuation). -/
theorem cleared_local_odd {p e : ℕ} (hp : Odd p) :
    Odd ((1 : ℤ) + (e : ℤ) * (1 - (p : ℤ))) := by
  obtain ⟨k, hk⟩ := hp
  refine ⟨-(e : ℤ) * (k : ℤ), ?_⟩
  rw [hk]
  push_cast
  ring

/-- At `p = 2`, the local factor `1 + e * (1 - 2) = 1 - e` vanishes iff `e = 1`,
explaining the exact zero locus `n ≡ 2 (mod 4)` of `(m a_m) * 1`. -/
theorem cleared_local_two_eq_zero_iff (e : ℕ) :
    (1 : ℤ) + (e : ℤ) * (1 - 2) = 0 ↔ e = 1 := by
  omega

/-- Markov 1-bit upper bound for nonnegative integer Lambert series (such as `L_{chi_4}`):
if each position `n ∈ window` has nonnegative unwrapped sum `S n ≥ 0` and bit `1` forces
`1/2 ≤ S n`, then the count of `1`-bits in `window` is at most `2 * ∑ n ∈ window, S n`. -/
theorem nonneg_one_bit_count_le (window : Finset ℤ) (S : ℤ → ℝ) (bit : ℤ → Bool)
    (hnonneg : ∀ n ∈ window, 0 ≤ S n)
    (hbit : ∀ n ∈ window, bit n = true → (1 / 2 : ℝ) ≤ S n) :
    ((window.filter (fun n => bit n = true)).card : ℝ) ≤ 2 * ∑ n ∈ window, S n := by
  have h1 : ∑ n ∈ window.filter (fun n => bit n = true), (1 / 2 : ℝ) ≤
      ∑ n ∈ window.filter (fun n => bit n = true), S n :=
    sum_le_sum (fun n hn => hbit n (mem_filter.mp hn).1 (mem_filter.mp hn).2)
  have h2 : ∑ n ∈ window.filter (fun n => bit n = true), S n ≤ ∑ n ∈ window, S n :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ => hnonneg n hn)
  rw [sum_const, nsmul_eq_mul] at h1
  linarith

end NormalityChecker.WeightedLambertIdentities
