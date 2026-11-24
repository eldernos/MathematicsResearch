module

public import NormalityChecker.ParameterTwoSquareArithmetic
public import NormalityChecker.ParameterTwoSquareExpansion

/-! The two denominator regimes of the actual shifted square. -/
@[expose] public section
open Finset
namespace NormalityChecker.ParameterTwoSquare

private def arm (b n k : ℕ) : ℚ := ∑ j ∈ range k,
  if location k j ≤ n then term b k * term b j else 0

private lemma split_box (b n k : ℕ) (hi : n < 2^(k+2)) :
    boxSum b n (k+1) = boxSum b n k + 2 * arm b n k := by
  have no : ¬location k k ≤ n := by
    dsimp [location]; rw [pow_succ (2 : ℕ) (k+1)] at hi; omega
  have swap (i : ℕ) : (if location i k ≤ n then term b i * term b k else 0) =
      (if location k i ≤ n then term b k * term b i else 0) := by
    rw [location, location, add_comm, mul_comm]
  simp only [boxSum, sum_range_succ, sum_add_distrib, no, ite_false, add_zero, swap, arm]
  ring

private lemma full_box (b n k : ℕ) (lo : 2^(k+1) ≤ n) :
    boxSum b n k = (∑ i ∈ range k, term b i)^2 := by
  rw [sq, sum_mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply ite_eq_left
  have a := Nat.pow_le_pow_right (by decide : 0 < 2) (mem_range.mp hi : i+1 ≤ k)
  have c := Nat.pow_le_pow_right (by decide : 0 < 2) (mem_range.mp hj : j+1 ≤ k)
  rw [pow_succ] at lo
  dsimp [location]; omega

/-- Once both arms are full, the single missing term is the newest diagonal. -/
private lemma missing_diagonal (b n k : ℕ) (mid : 3*2^k ≤ n) (hi : n < 2^(k+2)) :
    boxSum b n (k+1) = (∑ i ∈ range (k+1), term b i)^2 - (term b k)^2 := by
  have lo : 2^(k+1) ≤ n := by rw [pow_succ]; omega
  have full : arm b n k = term b k * ∑ j ∈ range k, term b j := by
    rw [arm, mul_sum]
    apply sum_congr rfl
    intro j hj
    apply ite_eq_left
    have := Nat.pow_le_pow_right (by decide : 0<2) (mem_range.mp hj : j+1 ≤ k)
    dsimp [location]; rw [pow_succ (2 : ℕ) k]; omega
  rw [split_box b n k hi, full_box b n k lo, full, sum_range_succ]
  ring

private lemma sum_eq {b : ℕ} (hb : 0 < b) (k : ℕ) :
    (∑ i ∈ range k, term b i) =
      (axisNumerator b k : ℚ) / ((b : ℚ)^(2^k : ℕ) * 2^k) := by
  rw [eq_div_iff (by positivity), ← clear_axis hb, weighted_eq]
  ring

private lemma den_odd {u : ℤ} (hu : Odd u) (e : ℕ) : ((u : ℚ)/2^e).den = 2^e := by
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat] using
    Rat.den_div_eq_of_coprime (a:=u) (b:=((2^e : ℕ) : ℤ)) (by positivity)
      (by simpa only [Int.natAbs_natCast] using hu.natAbs.coprime_two_right.pow_right e)

private lemma odd_mul_den {x : ℚ} {a D : ℕ} (odd : Odd a) (dyad : x.den ∣ 2^D) :
    ((a : ℚ)*x).den = x.den := by
  have cop : a.Coprime x.den := Nat.Coprime.of_dvd_right dyad (odd.coprime_two_right.pow_right D)
  simp only [Rat.mul_den, Rat.den_natCast, Rat.num_natCast, one_mul, Int.natAbs_mul,
    Int.natAbs_natCast, (cop.mul_left x.reduced).gcd_eq_one, Nat.div_one]

/-- With the previous square's denominator cleared, the new arm has an
integral numerator until the midpoint. Both ordered arms contribute it. -/
def armNumerator (b n k : ℕ) : ℤ := ∑ j ∈ range k,
  if location k j ≤ n then (b : ℤ)^(n-location k j)*2^(k+k-((k+1)+(j+1))) else 0

private lemma clear_arm {b n k : ℕ} (hb : 0 < b) (early : n < 3*2^k) :
    (2 : ℚ)^(k+k)*(b : ℚ)^n*arm b n k = armNumerator b n k := by
  have bn : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [arm, mul_sum, armNumerator, Int.cast_sum]
  apply sum_congr rfl
  intro j _
  by_cases on : location k j ≤ n
  · have short : 2^(j+1) < 2^k := by
      dsimp [location] at on
      rw [pow_succ (2 : ℕ) k] at on
      omega
    have deg := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp short
    simp only [on, ite_true, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    rw [pow_sub₀ _ bn on, pow_sub₀ (2 : ℚ) (by norm_num) (by omega)]
    simp only [term, location, pow_add (b : ℚ), pow_add (2 : ℚ)]
    ring
  · simp [on]

/-- Reduced numerator and denominator before the midpoint. Here `k` is
the last index in the previous complete square. -/
theorem first_half_reduction {b n k : ℕ} (hb : 0 < b) (odd : Odd b) (hk : 1 ≤ k)
    (lo : 2^(k+1) ≤ n) (hi : n < 2^(k+2)) (early : n < 3*2^k) :
    (pre b n).num = (b : ℤ)^(n-2^(k+1))*axisNumerator b k^2 + 2*armNumerator b n k ∧
    (pre b n).den = 2^(k+k) := by
  let a : ℤ := (b : ℤ)^(n-2^(k+1)) * axisNumerator b k ^ 2
  have oddb : Odd (b : ℤ) := by exact_mod_cast odd
  have oa : Odd a := oddb.pow.mul (axis_odd hk).pow
  have bn : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have old : (2 : ℚ)^(k+k)*(b : ℚ)^n*(∑ i ∈ range k, term b i)^2 = a := by
    dsimp [a]; push_cast
    rw [sum_eq hb, pow_sub₀ _ bn lo, pow_succ (2 : ℕ) k, pow_mul, pow_add]
    field_simp
  have logn := Nat.log_eq_of_pow_le_of_lt_pow lo hi
  have scaled : (2 : ℚ)^(k+k)*pre b n = (a + 2 * armNumerator b n k : ℤ) := by
    push_cast
    rw [pre, logn, split_box b n k hi, full_box b n k lo, ← old, ← clear_arm hb early]
    ring
  have form : pre b n = ((a + 2*armNumerator b n k : ℤ) : ℚ) / 2^(k+k) := by
    rw [eq_div_iff (by positivity), mul_comm]; exact scaled
  have den : (pre b n).den = 2^(k+k) := form ▸ den_odd (oa.add_even (even_two_mul _)) _
  refine ⟨?_, den⟩
  exact_mod_cast (calc ((pre b n).num : ℚ) = ((pre b n).den : ℚ)*pre b n :=
                          (Rat.den_mul_eq_num _).symm
                       _ = ((a+2*armNumerator b n k : ℤ) : ℚ) := by
                         rw [den]; push_cast; simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
                           using scaled)

/-- At and after the midpoint the reduced numerator is the odd quotient of
the missing diagonal, with the remaining (odd) radix power divided out. -/
theorem second_half_reduction {b n k : ℕ} (hb : 0 < b) (odd : Odd b) (hk : 1 ≤ k)
    (lo : 2^(k+1) ≤ n) (hi : n < 2^(k+2)) (mid : 3*2^k ≤ n) :
    2^(k+2)*(b : ℤ)^(2^(k+2)-n)*(pre b n).num = axisNumerator b (k+1)^2-1 ∧
    (pre b n).den = 2^k := by
  obtain ⟨u, ou, diag⟩ := diagonal_numerator odd (show 2 ≤ k+1 by omega)
  have logn := Nat.log_eq_of_pow_le_of_lt_pow lo hi
  have bn : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have diagQ : (axisNumerator b (k+1) : ℚ)^2 - 1 = 2^(k+1+1)*(u : ℚ) := by
    exact_mod_cast diag
  let r := b^(2^(k+2)-n)
  have form : (r : ℚ)*pre b n = (u : ℚ)/2^k := by
    dsimp [r]; push_cast
    rw [pre, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi.le, logn, missing_diagonal b n k mid hi,
      sum_eq hb, term, pow_succ (2 : ℕ) (k+1), pow_mul]
    have divide : (u : ℚ) = ((axisNumerator b (k+1) : ℚ)^2-1) / 2^(k+1+1) := by
      rw [eq_div_iff (by positivity), mul_comm, diagQ]
    rw [divide, pow_succ (2 : ℚ) (k+1), pow_succ (2 : ℚ) k]
    field_simp
  obtain ⟨D, hd⟩ := dyadic hb n
  have den : (pre b n).den = 2^k := by
    rw [← odd_mul_den (a:=r) odd.pow hd, form]
    exact den_odd ou _
  have num : (r : ℚ)*((pre b n).num : ℚ) = u := by
    rw [← Rat.den_mul_eq_num, den, mul_left_comm, form]
    push_cast
    field_simp
  have numZ : (r : ℤ)*(pre b n).num = u := by exact_mod_cast num
  refine ⟨?_, den⟩
  rw [diag, ← numZ, mul_assoc]
  simp [r]

/-- All cutoffs, including the empty prefix before the first pair at four. -/
theorem exact_profile : ExactDenominatorProfile := by
  intro b hb odd
  constructor
  · intro n hn
    have empty : boxSum b n (Nat.log 2 n) = 0 := by
      apply sum_eq_zero
      intro i _
      apply sum_eq_zero
      intro j _
      apply ite_eq_right
      have a := Nat.pow_le_pow_right (by decide : 0<2) (show 1 ≤ i+1 by omega)
      have c := Nat.pow_le_pow_right (by decide : 0<2) (show 1 ≤ j+1 by omega)
      dsimp [location]; omega
    simp [pre, empty]
  · intro k hk n lo hi
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Nat.succ_sub_one]
    split_ifs with early
    · rw [(first_half_reduction (by omega) odd (by omega) lo hi early).2]
      congr 1; omega
    · exact (second_half_reduction (by omega) odd (by omega) lo hi (by omega)).2

end NormalityChecker.ParameterTwoSquare
