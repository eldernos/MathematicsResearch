module

public import NormalityChecker.DigitMassTransfer
public import NormalityChecker.Phase22Cores

/-! # Phase 25 Stage 3: non-adjacent signed-digit geometric transfer and `E_+(2^k)`

Kernel-checked formalization of `notes/phase25/naf-geometric-transfer.md`
(Lemma A.1, Theorem A.2(1)–(3), Theorem B.1(2) and the multiplicative majorant of Theorem B.2(1)).
All results below are `Kernel-verified` and depend only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

1. **Integer signed weight (Lemma A.1, `w_rec ≤ w_min`):** `signedWeight_natAbs_add_le`,
   `signedWeight_natAbs_sum_le`, `signedWeight_natAbs_le_card_of_signed_sum` (every signed
   power-of-two representation of `A`, repeated exponents allowed, has at least `w_±(|A|)` terms)
   and `signedWeight_natAbs_le_card_support`.
2. **Canonical NAF (Lemma A.1):** `nafHead`, `nafTail`, `nafDigit`, `nafRest`, `nafWeight`;
   digits in `{-1, 0, 1}` (`nafDigit_cases`), non-adjacency (`nafDigit_mul_nafDigit_succ`),
   value reconstruction (`nafDigit_sum_add_nafRest`, `nafDigit_sum_eq`), finite support
   (`nafDigit_eq_zero_of_le`), the exact identity `nafWeight_eq_signedWeight`
   (`W(naf(A)) = w_±(|A|)`), the packaged statement `exists_naf`, and minimality
   `nafWeight_le_card_support`.
3. **Geometric tail and orbit covering (Theorem A.2(1)):** `three_mul_abs_sum_add_one_le`
   (`3 |∑_{i<K} d_i 2^i| + 1 ≤ 2^{K+1}` for non-adjacent digits), `abs_nafLow_div_lt`
   (`ℓ` vanishing digits force a tail `< (2/3) 2^{-ℓ}`), `exists_nafDigit_ne_zero_of_fract_mem`,
   `naf_dyadic_count_le` (at most `r · w_±(|A|)` of the shifts `{2^{sm} A / 2^M}`,
   `m < N`, `sN ≤ M`, meet `[c, 1 - c]`, `c = 2/(3 · 2^{sr})`) and its binary form
   `naf_orbit_count_le` (at most `ℓ · w_±(|A|)` shifts `n < N ≤ M` in
   `((2/3) 2^{-ℓ}, 1 - (2/3) 2^{-ℓ})`).
4. **Universal real transfer (Theorem A.2(2)):** `frequency_naf_interval_le` (finite form),
   `NafDensityLE`, `nafDensityLE_of_limsup_le`, `eventually_frequency_le_of_nafDensity`,
   `radixDiscrepancy_eventually_ge_of_nafDensity` (`D_N(x; 2^s) ≥ 1 - (4/3) 2^{-sr} - rsρ - ε`),
   `binary_radixDiscrepancy_eventually_ge_of_nafDensity` (`D_N(x; 2) ≥ 1 - (4/3) 2^{-ℓ} - ℓρ - ε`),
   the `ℓ = 2` forms in bases `2` and `4`, and the exact order-normality exclusions
   `not_orderNormal_two_four_of_nafDensity` and `not_orderNormal_four_two_of_nafDensity`
   (`ρ < 5/16`, via the ten cylinders `[3/16, 13/16) ⊂ (1/6, 5/6)` of total length `5/8`).
5. **Signed series transfer (Theorem A.2(3)):** `nafDensityLE_of_series` for
   `x = ∑_{n ≥ 1} a(n) 2^{-kn}` with `|a(n)| ≤ C₀ n^B` and mean signed weight `≤ C`.
6. **`E_+(2^k)`:** `erdosBorweinPlusPow`, `aPlus` (`a_+(n) = (1 - v₂(n)) τ_odd(n)`),
   `erdosBorweinPlusPow_eq_signed_series`, the multiplicative majorant `ePlusMajorant`
   (`G₀(2^e) = w_±(|1 - e|)`, `G₀(p^e) = w_±(e + 1)`), `signedWeight_aPlus_le`, and the
   DP-free Euler-product certificate `ePlusMean_le` (`W_+^{maj} ≤ 93694/100000 < 937/1000`,
   with `71` explicit odd primes below `361` and an elementary `±1 (mod 6)` prime tail).
7. **Headline theorems (every `k ≥ 3`, including `E_+(8)`):**
   `erdosBorweinPlus_two_pow_radixDiscrepancy_eventually_ge`
   (`D_N(E_+(2^k); 2) ≥ 2/3 - 2 (937/1000)/k - ε`),
   `erdosBorweinPlus_two_pow_lowerDiscrepancy_pos` (`D_N(E_+(2^k); 2) ≥ 21/500` eventually),
   `erdosBorweinPlus_two_pow_not_orderNormal_four` (`E_+(2^k)` is not `4`-normal in base `2`),
   `erdosBorweinPlus_two_pow_not_orderNormal_base4_two` (not `2`-normal in base `4`), and the
   base-`4` discrepancy and `NormalIn` corollaries. Simple normality of `E_+(8)` in base `2`
   is **not** claimed and remains open.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.NafGeometricTransfer

open HigherOrderTower SimpleNormalityKernel DigitMassTransfer

/-! ### Part 1: the signed weight of integers -/

private theorem signedWeight_succ_le' (n : ℕ) :
    signedWeight (n + 1) ≤ signedWeight n + 1 ∧ signedWeight n ≤ signedWeight (n + 1) + 1 := by
  constructor
  · simpa using signedWeight_add_le n 1
  · simpa using signedWeight_sub_le (n + 1) 1 (by omega)

/-- `|w_±(n + 1) - w_±(n)| ≤ 1`. -/
theorem abs_signedWeight_succ_sub_le (n : ℕ) :
    |(signedWeight (n + 1) : ℝ) - signedWeight n| ≤ 1 := by
  obtain ⟨h1, h2⟩ := signedWeight_succ_le' n
  have h1' : (signedWeight (n + 1) : ℝ) ≤ signedWeight n + 1 := by exact_mod_cast h1
  have h2' : (signedWeight n : ℝ) ≤ signedWeight (n + 1) + 1 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- `w_±(n) ≤ n`. -/
theorem signedWeight_le_self (n : ℕ) : signedWeight n ≤ n :=
  (signedWeight_le_digitSum n).trans (digitSum_le_self (le_refl 2) n)

/-- **Parity monotonicity:** `w_±(2q) ≤ w_±(2q + 1)` and `w_±(2q + 2) ≤ w_±(2q + 1)`. -/
theorem signedWeight_parity_mono (q : ℕ) :
    signedWeight (2 * q) ≤ signedWeight (2 * q + 1) ∧
      signedWeight (2 * q + 2) ≤ signedWeight (2 * q + 1) := by
  rw [signedWeight_two_mul_add_one, signedWeight_two_mul,
    show 2 * q + 2 = 2 * (q + 1) by ring, signedWeight_two_mul]
  obtain ⟨h1, h2⟩ := signedWeight_succ_le' q
  constructor <;> omega

/-- Subadditivity of `w_±(|·|)` on `ℤ`. -/
theorem signedWeight_natAbs_add_le (u v : ℤ) :
    signedWeight (u + v).natAbs ≤ signedWeight u.natAbs + signedWeight v.natAbs := by
  have key : ∀ a b : ℕ, signedWeight ((a : ℤ) - b).natAbs ≤ signedWeight a + signedWeight b := by
    intro a b
    rcases le_total b a with h | h
    · have e : ((a : ℤ) - b).natAbs = a - b := by omega
      rw [e]
      exact signedWeight_sub_le a b h
    · have e : ((a : ℤ) - b).natAbs = b - a := by omega
      rw [e, add_comm]
      exact signedWeight_sub_le b a h
  rcases Int.natAbs_eq u with hu | hu <;> rcases Int.natAbs_eq v with hv | hv
  · have e : (u + v).natAbs = u.natAbs + v.natAbs := by omega
    rw [e]
    exact signedWeight_add_le _ _
  · have e : u + v = (u.natAbs : ℤ) - v.natAbs := by omega
    rw [e]
    exact key _ _
  · have e : u + v = (v.natAbs : ℤ) - u.natAbs := by omega
    rw [e, add_comm (signedWeight u.natAbs)]
    exact key _ _
  · have e : (u + v).natAbs = u.natAbs + v.natAbs := by omega
    rw [e]
    exact signedWeight_add_le _ _

theorem signedWeight_natAbs_mul_two_pow (c : ℤ) (e : ℕ) :
    signedWeight (c * 2 ^ e).natAbs = signedWeight c.natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  exact signedWeight_mul_two_pow _ _

/-- Finite signed sums: `w_±(|∑_{i ∈ S} c_i 2^{e_i}|) ≤ ∑_{i ∈ S} w_±(|c_i|)`. -/
theorem signedWeight_natAbs_sum_le (S : Finset ℕ) (c : ℕ → ℤ) (e : ℕ → ℕ) :
    signedWeight (∑ i ∈ S, c i * 2 ^ e i).natAbs ≤ ∑ i ∈ S, signedWeight (c i).natAbs := by
  induction S using Finset.induction with
  | empty => simp
  | insert j S hj ih =>
    rw [sum_insert hj, sum_insert hj]
    have h := signedWeight_natAbs_add_le (c j * 2 ^ e j) (∑ i ∈ S, c i * 2 ^ e i)
    rw [signedWeight_natAbs_mul_two_pow] at h
    omega

/-- **Lemma A.1 (`w_rec ≤ w_min`).** If `A = ∑_{i ∈ S} ε_i 2^{m_i}` with every `ε_i ∈ {1, -1}`
(repeated exponents allowed), then `w_±(|A|) ≤ #S`. -/
theorem signedWeight_natAbs_le_card_of_signed_sum (S : Finset ℕ) (ε : ℕ → ℤ) (m : ℕ → ℕ)
    (hε : ∀ i ∈ S, ε i = 1 ∨ ε i = -1) :
    signedWeight (∑ i ∈ S, ε i * 2 ^ m i).natAbs ≤ S.card := by
  refine (signedWeight_natAbs_sum_le S ε m).trans ?_
  rw [card_eq_sum_ones]
  refine sum_le_sum (fun i hi => ?_)
  rcases hε i hi with h | h <;> simp [h]

/-- Digit representations: if `|c_i| ≤ 1`, then `w_±(|∑_{i<K} c_i 2^i|) ≤ #{i < K : c_i ≠ 0}`. -/
theorem signedWeight_natAbs_le_card_support {c : ℕ → ℤ} (hc : ∀ i, |c i| ≤ 1) (K : ℕ) :
    signedWeight (∑ i ∈ range K, c i * 2 ^ i).natAbs ≤
      ((range K).filter fun i => c i ≠ 0).card := by
  refine (signedWeight_natAbs_sum_le (range K) c (fun i => i)).trans ?_
  rw [card_filter]
  refine sum_le_sum (fun i _ => ?_)
  have h := hc i
  rw [abs_le] at h
  rcases (show c i = 0 ∨ c i = 1 ∨ c i = -1 by omega) with h0 | h0 | h0 <;> simp [h0]

/-! ### Part 2: the canonical non-adjacent form (Lemma A.1) -/

/-- The least significant canonical NAF digit of `A`: `0` if `A` is even, `+1` if
`A ≡ 1 (mod 4)` and `-1` if `A ≡ 3 (mod 4)`. -/
def nafHead (A : ℤ) : ℤ := if A % 2 = 0 then 0 else if A % 4 = 1 then 1 else -1

/-- The integer `(A - e₀) / 2` encoded by the remaining canonical NAF digits. -/
def nafTail (A : ℤ) : ℤ := (A - nafHead A) / 2

/-- The `i`-th canonical NAF digit `e_i(A) ∈ {-1, 0, 1}`. -/
def nafDigit : ℤ → ℕ → ℤ
  | A, 0 => nafHead A
  | A, i + 1 => nafDigit (nafTail A) i

/-- The integer left after stripping the `K` least significant canonical NAF digits. -/
def nafRest : ℤ → ℕ → ℤ
  | A, 0 => A
  | A, K + 1 => nafRest (nafTail A) K

@[simp] theorem nafDigit_zero (A : ℤ) : nafDigit A 0 = nafHead A := rfl

@[simp] theorem nafDigit_succ (A : ℤ) (i : ℕ) : nafDigit A (i + 1) = nafDigit (nafTail A) i :=
  rfl

@[simp] theorem nafRest_zero (A : ℤ) : nafRest A 0 = A := rfl

@[simp] theorem nafRest_succ (A : ℤ) (K : ℕ) : nafRest A (K + 1) = nafRest (nafTail A) K := rfl

theorem nafHead_cases (A : ℤ) : nafHead A = 0 ∨ nafHead A = 1 ∨ nafHead A = -1 := by
  unfold nafHead
  split_ifs <;> simp

theorem abs_nafHead_le (A : ℤ) : |nafHead A| ≤ 1 := by
  rcases nafHead_cases A with h | h | h <;> rw [h] <;> norm_num

theorem nafHead_eq_zero_iff (A : ℤ) : nafHead A = 0 ↔ A % 2 = 0 := by
  unfold nafHead
  by_cases h : A % 2 = 0
  · simp [h]
  · rw [ite_eq_right h]
    constructor
    · intro h'
      split_ifs at h'
      omega
    · intro h'
      exact absurd h' h

theorem two_mul_nafTail_add (A : ℤ) : 2 * nafTail A + nafHead A = A := by
  unfold nafTail nafHead
  split_ifs <;> omega

theorem nafHead_mul_nafHead_nafTail (A : ℤ) : nafHead A * nafHead (nafTail A) = 0 := by
  by_cases h : A % 2 = 0
  · rw [(nafHead_eq_zero_iff A).2 h, zero_mul]
  · have ht : nafTail A % 2 = 0 := by
      unfold nafTail nafHead
      rw [ite_eq_right h]
      split_ifs <;> omega
    rw [(nafHead_eq_zero_iff _).2 ht, mul_zero]

theorem nafDigit_eq_nafHead_nafRest (A : ℤ) (i : ℕ) : nafDigit A i = nafHead (nafRest A i) := by
  induction i generalizing A with
  | zero => rfl
  | succ i ih => exact ih (nafTail A)

/-- **Lemma A.1:** every canonical NAF digit lies in `{0, 1, -1}`. -/
theorem nafDigit_cases (A : ℤ) (i : ℕ) :
    nafDigit A i = 0 ∨ nafDigit A i = 1 ∨ nafDigit A i = -1 := by
  rw [nafDigit_eq_nafHead_nafRest]
  exact nafHead_cases _

theorem abs_nafDigit_le (A : ℤ) (i : ℕ) : |nafDigit A i| ≤ 1 := by
  rw [nafDigit_eq_nafHead_nafRest]
  exact abs_nafHead_le _

/-- **Lemma A.1 (non-adjacency):** `e_i(A) e_{i+1}(A) = 0`. -/
theorem nafDigit_mul_nafDigit_succ (A : ℤ) (i : ℕ) : nafDigit A i * nafDigit A (i + 1) = 0 := by
  induction i generalizing A with
  | zero => exact nafHead_mul_nafHead_nafTail A
  | succ i ih => exact ih (nafTail A)

/-- **Lemma A.1 (value reconstruction):** `∑_{i < K} e_i(A) 2^i + 2^K rest_K(A) = A`. -/
theorem nafDigit_sum_add_nafRest (A : ℤ) (K : ℕ) :
    ∑ i ∈ range K, nafDigit A i * 2 ^ i + 2 ^ K * nafRest A K = A := by
  induction K generalizing A with
  | zero => simp
  | succ K ih =>
    have h := ih (nafTail A)
    have h2 := two_mul_nafTail_add A
    rw [sum_range_succ', nafRest_succ]
    have e : ∑ i ∈ range K, nafDigit A (i + 1) * 2 ^ (i + 1) =
        2 * ∑ i ∈ range K, nafDigit (nafTail A) i * 2 ^ i := by
      rw [mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      rw [nafDigit_succ, pow_succ]
      ring
    rw [e, pow_zero, mul_one, nafDigit_zero, pow_succ]
    linear_combination 2 * h + h2

theorem natAbs_nafTail_le (A : ℤ) : (nafTail A).natAbs ≤ A.natAbs - 1 := by
  unfold nafTail nafHead
  split_ifs <;> omega

theorem natAbs_nafRest_le (A : ℤ) (K : ℕ) : (nafRest A K).natAbs ≤ A.natAbs - K := by
  induction K generalizing A with
  | zero => simp
  | succ K ih =>
    rw [nafRest_succ]
    have h1 := ih (nafTail A)
    have h2 := natAbs_nafTail_le A
    omega

/-- **Lemma A.1 (termination):** `rest_K(A) = 0` once `K ≥ |A|`. -/
theorem nafRest_eq_zero {A : ℤ} {K : ℕ} (hK : A.natAbs ≤ K) : nafRest A K = 0 := by
  have := natAbs_nafRest_le A K
  omega

/-- **Lemma A.1 (finite support):** `e_i(A) = 0` for `i ≥ |A|`. -/
theorem nafDigit_eq_zero_of_le {A : ℤ} {i : ℕ} (hi : A.natAbs ≤ i) : nafDigit A i = 0 := by
  rw [nafDigit_eq_nafHead_nafRest, nafRest_eq_zero hi]
  simp [nafHead]

/-- **Lemma A.1 (existence):** `A = ∑_{i < K} e_i(A) 2^i` for every `K ≥ |A|`. -/
theorem nafDigit_sum_eq {A : ℤ} {K : ℕ} (hK : A.natAbs ≤ K) :
    ∑ i ∈ range K, nafDigit A i * 2 ^ i = A := by
  have h := nafDigit_sum_add_nafRest A K
  rwa [nafRest_eq_zero hK, mul_zero, add_zero] at h

/-- The weight `W(naf(A)) = #{i : e_i(A) ≠ 0}` of the canonical NAF. -/
def nafWeight (A : ℤ) : ℕ := ((range A.natAbs).filter fun i => nafDigit A i ≠ 0).card

/-- One canonical NAF step: `w_±(|tail(A)|) + |e₀(A)| ≤ w_±(|A|)`. -/
theorem signedWeight_natAbs_nafTail_add_le (A : ℤ) :
    signedWeight (nafTail A).natAbs + (nafHead A).natAbs ≤ signedWeight A.natAbs := by
  by_cases h : A % 2 = 0
  · rw [(nafHead_eq_zero_iff A).2 h, Int.natAbs_zero, add_zero]
    have e : A.natAbs = 2 * (nafTail A).natAbs := by
      unfold nafTail nafHead
      rw [ite_eq_left h]
      omega
    rw [e, signedWeight_two_mul]
  · have hh : (nafHead A).natAbs = 1 := by
      unfold nafHead
      rw [ite_eq_right h]
      split_ifs <;> rfl
    rw [hh]
    obtain ⟨q, hq | hq⟩ : ∃ q, A.natAbs = 4 * q + 1 ∨ A.natAbs = 4 * q + 3 :=
      ⟨A.natAbs / 4, by omega⟩
    · have e : (nafTail A).natAbs = 2 * q := by
        unfold nafTail nafHead
        rw [ite_eq_right h]
        split_ifs <;> omega
      rw [hq, e, show 4 * q + 1 = 2 * (2 * q) + 1 by ring, signedWeight_two_mul_add_one]
      have := (signedWeight_parity_mono q).1
      omega
    · have e : (nafTail A).natAbs = 2 * q + 2 := by
        unfold nafTail nafHead
        rw [ite_eq_right h]
        split_ifs <;> omega
      rw [hq, e, show 4 * q + 3 = 2 * (2 * q + 1) + 1 by ring, signedWeight_two_mul_add_one,
        show 2 * q + 1 + 1 = 2 * q + 2 by ring]
      have := (signedWeight_parity_mono q).2
      omega

/-- The number of nonzero canonical NAF digits below `K`, as `∑_{i<K} |e_i(A)|`. -/
theorem card_nafDigit_ne_zero_eq_sum (A : ℤ) (K : ℕ) :
    ((range K).filter fun i => nafDigit A i ≠ 0).card = ∑ i ∈ range K, (nafDigit A i).natAbs := by
  rw [card_filter]
  refine sum_congr rfl (fun i _ => ?_)
  rcases nafDigit_cases A i with h | h | h <;> simp [h]

theorem sum_natAbs_nafDigit_le (A : ℤ) (K : ℕ) :
    ∑ i ∈ range K, (nafDigit A i).natAbs ≤ signedWeight A.natAbs := by
  induction K generalizing A with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ']
    simp only [nafDigit_succ, nafDigit_zero]
    have h1 := ih (nafTail A)
    have h2 := signedWeight_natAbs_nafTail_add_le A
    omega

/-- **Lemma A.1 (`w_NAF ≤ w_rec`):** for every `K`, the canonical NAF has at most `w_±(|A|)`
nonzero digits below position `K`. -/
theorem card_nafDigit_ne_zero_le (A : ℤ) (K : ℕ) :
    ((range K).filter fun i => nafDigit A i ≠ 0).card ≤ signedWeight A.natAbs := by
  rw [card_nafDigit_ne_zero_eq_sum]
  exact sum_natAbs_nafDigit_le A K

theorem nafWeight_eq_card_range {A : ℤ} {K : ℕ} (hK : A.natAbs ≤ K) :
    ((range K).filter fun i => nafDigit A i ≠ 0).card = nafWeight A := by
  unfold nafWeight
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, hne⟩
    refine ⟨?_, hne⟩
    by_contra hlt
    exact hne (nafDigit_eq_zero_of_le (by omega))
  · rintro ⟨hi, hne⟩
    exact ⟨by omega, hne⟩

/-- **Lemma A.1 (exact equivalence):** `W(naf(A)) = w_±(|A|) = signedWeight |A|`. -/
theorem nafWeight_eq_signedWeight (A : ℤ) : nafWeight A = signedWeight A.natAbs := by
  refine le_antisymm (card_nafDigit_ne_zero_le A _) ?_
  have h := signedWeight_natAbs_le_card_support (abs_nafDigit_le A) A.natAbs
  rwa [nafDigit_sum_eq le_rfl] at h

/-- **Lemma A.1 (packaged):** every integer has a finitely supported non-adjacent signed binary
representation with exactly `w_±(|A|)` nonzero digits. -/
theorem exists_naf (A : ℤ) : ∃ d : ℕ → ℤ, (∀ i, d i = 0 ∨ d i = 1 ∨ d i = -1) ∧
    (∀ i, d i * d (i + 1) = 0) ∧ (∀ i, A.natAbs ≤ i → d i = 0) ∧
    ∑ i ∈ range A.natAbs, d i * 2 ^ i = A ∧
    ((range A.natAbs).filter fun i => d i ≠ 0).card = signedWeight A.natAbs :=
  ⟨nafDigit A, nafDigit_cases A, nafDigit_mul_nafDigit_succ A,
    fun _ hi => nafDigit_eq_zero_of_le hi, nafDigit_sum_eq le_rfl, nafWeight_eq_signedWeight A⟩

/-- **Lemma A.1 (minimality):** every signed binary representation `A = ∑_{i<K} c_i 2^i` with
`|c_i| ≤ 1` has at least `W(naf(A)) = w_±(|A|)` nonzero digits. -/
theorem nafWeight_le_card_support {A : ℤ} {c : ℕ → ℤ} (hc : ∀ i, |c i| ≤ 1) {K : ℕ}
    (hA : ∑ i ∈ range K, c i * 2 ^ i = A) :
    nafWeight A ≤ ((range K).filter fun i => c i ≠ 0).card := by
  rw [nafWeight_eq_signedWeight, ← hA]
  exact signedWeight_natAbs_le_card_support hc K

/-! ### Part 3: finite-NAF geometric tail bound and orbit covering (Theorem A.2(1)) -/

/-- Non-adjacent digit sums: `3 |∑_{i<K} d_i 2^i| + 1 ≤ 2^{K+1}` whenever `|d_i| ≤ 1` and
`d_i d_{i+1} = 0`. -/
theorem three_mul_abs_sum_add_one_le {d : ℕ → ℤ} (hd : ∀ i, |d i| ≤ 1)
    (hna : ∀ i, d i * d (i + 1) = 0) (K : ℕ) :
    3 * |∑ i ∈ range K, d i * 2 ^ i| + 1 ≤ 2 ^ (K + 1) := by
  suffices H : ∀ K, (3 * |∑ i ∈ range K, d i * 2 ^ i| + 1 ≤ 2 ^ (K + 1)) ∧
      (3 * |∑ i ∈ range (K + 1), d i * 2 ^ i| + 1 ≤ 2 ^ (K + 2)) from (H K).1
  intro K
  induction K with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [sum_range_one, pow_zero, mul_one]
    have h0 := hd 0
    have e : (2 : ℤ) ^ (0 + 2) = 4 := by norm_num
    rw [e]
    linarith
  | succ K ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    rw [sum_range_succ]
    by_cases hz : d (K + 1) = 0
    · rw [hz, zero_mul, add_zero]
      calc 3 * |∑ i ∈ range (K + 1), d i * 2 ^ i| + 1 ≤ 2 ^ (K + 2) := h1
        _ ≤ 2 ^ (K + 1 + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    · have hK : d K = 0 := by
        rcases mul_eq_zero.mp (hna K) with h | h
        · exact h
        · exact absurd h hz
      rw [sum_range_succ, hK, zero_mul, add_zero]
      have hp : (0 : ℤ) < 2 ^ (K + 1) := by positivity
      have habs : |∑ i ∈ range K, d i * 2 ^ i + d (K + 1) * 2 ^ (K + 1)| ≤
          |∑ i ∈ range K, d i * 2 ^ i| + 2 ^ (K + 1) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hp]
        have := hd (K + 1)
        nlinarith
      have e1 : (2 : ℤ) ^ (K + 1 + 2) = 4 * 2 ^ (K + 1) := by ring
      rw [e1]
      linarith

/-- The canonical NAF integer prefix `∑_{i < r} e_i(A) 2^i`. -/
def nafLow (A : ℤ) (r : ℕ) : ℤ := ∑ i ∈ range r, nafDigit A i * 2 ^ i

/-- Dyadic shift: `2^j (A / 2^M) = rest_{M-j}(A) + low_{M-j}(A) / 2^{M-j}` for `j ≤ M`. -/
theorem two_pow_mul_div_eq (A : ℤ) {M j : ℕ} (hj : j ≤ M) :
    (2 : ℝ) ^ j * ((A : ℝ) / 2 ^ M) =
      (nafRest A (M - j) : ℝ) + (nafLow A (M - j) : ℝ) / 2 ^ (M - j) := by
  have hv : (A : ℝ) = (nafLow A (M - j) : ℝ) + 2 ^ (M - j) * (nafRest A (M - j) : ℝ) := by
    have := nafDigit_sum_add_nafRest A (M - j)
    unfold nafLow
    exact_mod_cast this.symm
  have hM : (2 : ℝ) ^ M = 2 ^ j * 2 ^ (M - j) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hv, hM]
  field_simp
  ring

/-- **Theorem A.2(1), strict geometric tail:** if the `ℓ` NAF digits just below position `r`
vanish, then `|low_r(A) / 2^r| < (2/3) 2^{-ℓ}`. -/
theorem abs_nafLow_div_lt (A : ℤ) {r l : ℕ}
    (hz : ∀ u, u < r → r ≤ u + l → nafDigit A u = 0) :
    |(nafLow A r : ℝ) / 2 ^ r| < 2 / (3 * 2 ^ l) := by
  have hlow : nafLow A r = nafLow A (r - l) := by
    unfold nafLow
    rw [← sum_range_add_sum_Ico _ (Nat.sub_le r l)]
    have hz' : ∑ u ∈ Ico (r - l) r, nafDigit A u * 2 ^ u = 0 := by
      refine sum_eq_zero (fun u hu => ?_)
      rw [mem_Ico] at hu
      rw [hz u hu.2 (by omega), zero_mul]
    rw [hz', add_zero]
  rcases le_or_gt l r with hlr | hlr
  · have hb := three_mul_abs_sum_add_one_le (abs_nafDigit_le A) (nafDigit_mul_nafDigit_succ A)
      (r - l)
    have hb' : (3 : ℝ) * |(nafLow A (r - l) : ℝ)| + 1 ≤ 2 ^ (r - l + 1) := by
      unfold nafLow
      exact_mod_cast hb
    have e : (2 : ℝ) ^ r = 2 ^ (r - l) * 2 ^ l := by rw [← pow_add, Nat.sub_add_cancel hlr]
    have h2l : (0 : ℝ) < 2 ^ l := by positivity
    have h2rl : (0 : ℝ) < 2 ^ (r - l) := by positivity
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ r), hlow, e,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [pow_succ] at hb'
    nlinarith [mul_le_mul_of_nonneg_right hb' h2l.le]
  · have e : r - l = 0 := by omega
    rw [hlow, e]
    simp only [nafLow, range_zero, sum_empty, Int.cast_zero, zero_div, abs_zero]
    positivity

/-- A real number within `c ≤ 1/2` of `0` has fractional part in `[0, c) ∪ (1 - c, 1)`. -/
theorem fract_lt_or_gt_of_abs_lt {s c : ℝ} (hc : c ≤ 1 / 2) (hs : |s| < c) :
    Int.fract s < c ∨ 1 - c < Int.fract s := by
  rcases le_or_gt 0 s with h | h
  · left
    rw [abs_of_nonneg h] at hs
    rw [Int.fract_eq_self.mpr ⟨h, by linarith⟩]
    exact hs
  · right
    rw [abs_of_neg h] at hs
    have hfl : ⌊s⌋ = -1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [Int.fract, hfl]
    push_cast
    linarith

/-- **Theorem A.2(1), contrapositive form:** if `{2^j A / 2^M} ∈ [c_ℓ, 1 - c_ℓ]`,
`c_ℓ = 2/(3 · 2^ℓ)`, then some NAF digit `e_u(A) ≠ 0` with `M - j - ℓ ≤ u < M - j`. -/
theorem exists_nafDigit_ne_zero_of_fract_mem (A : ℤ) {M j l : ℕ} (hj : j ≤ M) (hl : 1 ≤ l)
    (h : 2 / (3 * 2 ^ l) ≤ Int.fract ((2 : ℝ) ^ j * ((A : ℝ) / 2 ^ M)) ∧
      Int.fract ((2 : ℝ) ^ j * ((A : ℝ) / 2 ^ M)) ≤ 1 - 2 / (3 * 2 ^ l)) :
    ∃ u, u < M - j ∧ M - j ≤ u + l ∧ nafDigit A u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hs := abs_nafLow_div_lt A hcon
  have hc : (2 : ℝ) / (3 * 2 ^ l) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ 2 ^ l := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
    linarith
  rw [two_pow_mul_div_eq A hj, Int.fract_intCast_add] at h
  rcases fract_lt_or_gt_of_abs_lt hc hs with h1 | h1 <;> linarith [h.1, h.2]

private theorem window_card_le {s r M u N : ℕ} (hs : 1 ≤ s) :
    ((range N).filter fun m => s * m + u < M ∧ M ≤ u + s * r + s * m).card ≤ r := by
  rcases le_or_gt M u with hMu | huM
  · have : (range N).filter (fun m => s * m + u < M ∧ M ≤ u + s * r + s * m) = ∅ := by
      rw [filter_eq_empty_iff]
      intro m _ hm
      omega
    rw [this, card_empty]
    exact Nat.zero_le _
  · have hsub : (range N).filter (fun m => s * m + u < M ∧ M ≤ u + s * r + s * m) ⊆
        Icc ((M - u - 1) / s + 1 - r) ((M - u - 1) / s) := by
      intro m hm
      simp only [mem_filter, mem_range] at hm
      obtain ⟨_, h1, h2⟩ := hm
      rw [mem_Icc]
      have hle : m ≤ (M - u - 1) / s := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
        omega
      have hlt : (M - u - 1) / s < m + r := by
        have h3 : (M - u - 1) / s * s ≤ M - u - 1 := Nat.div_mul_le_self (M - u - 1) s
        by_contra hc
        push Not at hc
        have h4 : s * (m + r) ≤ s * ((M - u - 1) / s) := Nat.mul_le_mul_left s hc
        rw [Nat.mul_comm ((M - u - 1) / s) s] at h3
        rw [mul_add] at h4
        omega
      omega
    calc _ ≤ (Icc ((M - u - 1) / s + 1 - r) ((M - u - 1) / s)).card := card_le_card hsub
      _ = (M - u - 1) / s + 1 - ((M - u - 1) / s + 1 - r) := Nat.card_Icc _ _
      _ ≤ r := by omega

/-- **Theorem A.2(1), orbit covering:** for every `A : ℤ`, `s, r ≥ 1` and `sN ≤ M`, at most
`r · w_±(|A|)` of the shifts `{2^{sm} A / 2^M}`, `0 ≤ m < N`, lie in `[c, 1 - c]`, where
`c = 2/(3 · 2^{sr})`. -/
theorem naf_dyadic_count_le (A : ℤ) {M s r N : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r) (hN : s * N ≤ M) :
    ((range N).filter fun m =>
      2 / (3 * 2 ^ (s * r)) ≤ Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ∧
      Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ≤ 1 - 2 / (3 * 2 ^ (s * r))).card ≤
      r * signedWeight A.natAbs := by
  have hU : ((range M).filter fun u => nafDigit A u ≠ 0).card ≤ signedWeight A.natAbs :=
    card_nafDigit_ne_zero_le A M
  have hsr : 1 ≤ s * r := by nlinarith
  have hsub : ((range N).filter fun m =>
      2 / (3 * 2 ^ (s * r)) ≤ Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ∧
      Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ≤ 1 - 2 / (3 * 2 ^ (s * r))) ⊆
      ((range M).filter fun u => nafDigit A u ≠ 0).biUnion
        (fun u => (range N).filter fun m => s * m + u < M ∧ M ≤ u + s * r + s * m) := by
    intro m hm
    rw [mem_filter, mem_range] at hm
    obtain ⟨hmN, hfr⟩ := hm
    have hsm : s * m ≤ M := (Nat.mul_le_mul_left s hmN.le).trans hN
    obtain ⟨u, hu1, hu2, hu3⟩ := exists_nafDigit_ne_zero_of_fract_mem A hsm hsr hfr
    rw [mem_biUnion]
    refine ⟨u, ?_, ?_⟩
    · rw [mem_filter, mem_range]
      exact ⟨by omega, hu3⟩
    · rw [mem_filter, mem_range]
      exact ⟨hmN, by omega, by omega⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ u ∈ (range M).filter (fun u => nafDigit A u ≠ 0),
          ((range N).filter fun m => s * m + u < M ∧ M ≤ u + s * r + s * m).card :=
        card_biUnion_le
    _ ≤ ∑ _u ∈ (range M).filter (fun u => nafDigit A u ≠ 0), r :=
        sum_le_sum (fun u _ => window_card_le hs)
    _ = ((range M).filter fun u => nafDigit A u ≠ 0).card * r := by rw [sum_const, smul_eq_mul]
    _ ≤ r * signedWeight A.natAbs := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left r hU

/-- **Theorem A.2(1), binary orbit covering:** for every `A : ℤ`, `ℓ ≥ 1` and `N ≤ M`, at most
`ℓ · w_±(|A|)` of the shifts `{2^n A / 2^M}`, `0 ≤ n < N`, lie in
`((2/3) 2^{-ℓ}, 1 - (2/3) 2^{-ℓ})`. -/
theorem naf_orbit_count_le (A : ℤ) {M N l : ℕ} (hl : 1 ≤ l) (hN : N ≤ M) :
    ((range N).filter fun n =>
      2 / (3 * 2 ^ l) < Int.fract ((2 : ℝ) ^ n * ((A : ℝ) / 2 ^ M)) ∧
      Int.fract ((2 : ℝ) ^ n * ((A : ℝ) / 2 ^ M)) < 1 - 2 / (3 * 2 ^ l)).card ≤
      l * signedWeight A.natAbs := by
  have h := naf_dyadic_count_le A (M := M) (s := 1) (r := l) (N := N) le_rfl hl (by omega)
  simp only [one_mul] at h
  refine le_trans (card_le_card (fun n hn => ?_)) h
  simp only [mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1.le, hn.2.2.le⟩

/-! ### Part 4: universal real-number transfer (Theorem A.2(2)) -/

/-- **Theorem A.2(2), finite form.** For every real `x`, `s, r ≥ 1`, `R` and `N`,
`F_N([c + 2^{-R}, 1 - c); x, 2^s) ≤ r · w_±(⌊2^{sN + R} x⌋) / N`, `c = 2/(3 · 2^{sr})`. -/
theorem frequency_naf_interval_le (x : ℝ) {s r : ℕ} (R N : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    frequency (shift (2 ^ s) x) (2 / (3 * 2 ^ (s * r)) + (2⁻¹ : ℝ) ^ R)
        (1 - 2 / (3 * 2 ^ (s * r))) N ≤
      (r : ℝ) * (signedWeight ⌊(2 : ℝ) ^ (s * N + R) * x⌋.natAbs : ℝ) / N := by
  set M := s * N + R with hMdef
  set A := ⌊(2 : ℝ) ^ M * x⌋ with hAdef
  set c : ℝ := 2 / (3 * 2 ^ (s * r)) with hcdef
  have hcount := naf_dyadic_count_le A hs hr (show s * N ≤ M by omega)
  have hsub : (range N).filter (fun i => c + 2⁻¹ ^ R ≤ shift (2 ^ s) x i ∧
        shift (2 ^ s) x i < 1 - c) ⊆
      (range N).filter (fun m => c ≤ Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ∧
        Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ≤ 1 - c) := by
    intro m hm
    rw [mem_filter, mem_range] at hm ⊢
    obtain ⟨hmN, h1, h2⟩ := hm
    refine ⟨hmN, ?_⟩
    have hshift : shift (2 ^ s) x m = Int.fract ((2 : ℝ) ^ (s * m) * x) := by
      unfold shift
      push_cast
      rw [← pow_mul]
    rw [hshift] at h1 h2
    have hA0 : (A : ℝ) ≤ 2 ^ M * x := Int.floor_le _
    have hA1 : 2 ^ M * x < (A : ℝ) + 1 := Int.lt_floor_add_one _
    have hpos : (0 : ℝ) < 2 ^ M := by positivity
    have hsm : s * m + R ≤ M := by
      have := Nat.mul_le_mul_left s hmN.le
      omega
    set δ : ℝ := (2 : ℝ) ^ (s * m) * x - (2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M) with hδdef
    have hδ : δ = (2 : ℝ) ^ (s * m) * ((2 : ℝ) ^ M * x - A) / 2 ^ M := by
      rw [hδdef]
      field_simp
    have hδ0 : 0 ≤ δ := by
      rw [hδ]
      exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hpos.le
    have hδ1 : δ < 2⁻¹ ^ R := by
      rw [hδ, div_lt_iff₀ hpos]
      have hle : (2 : ℝ) ^ (s * m) * 2 ^ R ≤ 2 ^ M := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (by norm_num) hsm
      have hinv : (2⁻¹ : ℝ) ^ R * 2 ^ R = 1 := by
        rw [← mul_pow]
        norm_num
      have hlt : (2 : ℝ) ^ (s * m) * ((2 : ℝ) ^ M * x - A) < (2 : ℝ) ^ (s * m) :=
        by nlinarith [show (0 : ℝ) < 2 ^ (s * m) by positivity]
      have : (2 : ℝ) ^ (s * m) = (2 : ℝ) ^ (s * m) * 2 ^ R * 2⁻¹ ^ R := by
        rw [mul_assoc, mul_comm ((2 : ℝ) ^ R), hinv, mul_one]
      nlinarith [show (0 : ℝ) < 2⁻¹ ^ R by positivity]
    have hc0 : 0 < c := by positivity
    have hfr : Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) =
        Int.fract ((2 : ℝ) ^ (s * m) * x) - δ := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith [Int.fract_lt_one ((2 : ℝ) ^ (s * m) * x)],
        ⌊(2 : ℝ) ^ (s * m) * x⌋, ?_⟩
      have e : (2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M) = (2 : ℝ) ^ (s * m) * x - δ := by
        rw [hδdef]
        ring
      rw [e, Int.fract]
      ring
    rw [hfr]
    constructor <;> linarith
  unfold frequency
  have hcard : (((range N).filter (fun i => c + 2⁻¹ ^ R ≤ shift (2 ^ s) x i ∧
      shift (2 ^ s) x i < 1 - c)).card : ℝ) ≤ (r : ℝ) * (signedWeight A.natAbs : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans hcount
  exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg N)

/-- `x` has **upper prefix NAF density** at most `ρ`: for every `ρ' > ρ`, eventually
`w_±(⌊2^M x⌋) ≤ ρ' M`. -/
def NafDensityLE (x ρ : ℝ) : Prop :=
  ∀ ρ' > ρ, ∀ᶠ M : ℕ in atTop, (signedWeight ⌊(2 : ℝ) ^ M * x⌋.natAbs : ℝ) ≤ ρ' * M

/-- The `limsup` form: `limsup_M w_±(⌊2^M x⌋)/M ≤ ρ` implies `NafDensityLE x ρ`. -/
theorem nafDensityLE_of_limsup_le {x ρ : ℝ}
    (hb : IsBoundedUnder (· ≤ ·) atTop
      fun M : ℕ => (signedWeight ⌊(2 : ℝ) ^ M * x⌋.natAbs : ℝ) / M)
    (h : limsup (fun M : ℕ => (signedWeight ⌊(2 : ℝ) ^ M * x⌋.natAbs : ℝ) / M) atTop ≤ ρ) :
    NafDensityLE x ρ := by
  intro ρ' hρ'
  have hlt := eventually_lt_of_limsup_lt (lt_of_le_of_lt h hρ') hb
  filter_upwards [hlt, eventually_ge_atTop 1] with M hM hM1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  rw [div_lt_iff₀ hMr] at hM
  exact hM.le

/-- **Theorem A.2(2), asymptotic frequency bound:**
`F_N([c + 2^{-R}, 1 - c); x, 2^s) ≤ rsρ + ε` eventually. -/
theorem eventually_frequency_le_of_nafDensity {x ρ : ℝ} (hx : NafDensityLE x ρ) {s r : ℕ}
    (hs : 1 ≤ s) (hr : 1 ≤ r) (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, frequency (shift (2 ^ s) x) (2 / (3 * 2 ^ (s * r)) + (2⁻¹ : ℝ) ^ R)
        (1 - 2 / (3 * 2 ^ (s * r))) N ≤ r * s * ρ + ε := by
  have hrs : (0 : ℝ) < r * s := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs
    positivity
  set ρ' := ρ + ε / (2 * (r * s)) with hρ'def
  have hρ' : ρ' > ρ := by
    have : 0 < ε / (2 * (r * s)) := by positivity
    linarith
  have hcomp : Tendsto (fun N : ℕ => s * N + R) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right_of_le (Nat.le_mul_of_pos_left N hs)) tendsto_id
  have h1 := hcomp.eventually (hx ρ' hρ')
  have h2 : ∀ᶠ N : ℕ in atTop, (r : ℝ) * |ρ'| * R / N < ε / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat ((r : ℝ) * |ρ'| * R)).eventually
      (gt_mem_nhds (by positivity))
  filter_upwards [h1, h2, eventually_ge_atTop 1] with N hN1 hN2 hN3
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN3
  have hfreq := frequency_naf_interval_le x R N hs hr
  have e1 : (r : ℝ) * s * ρ' = r * s * ρ + ε / 2 := by
    rw [hρ'def]
    field_simp
  calc _ ≤ (r : ℝ) * (signedWeight ⌊(2 : ℝ) ^ (s * N + R) * x⌋.natAbs : ℝ) / N := hfreq
    _ ≤ (r : ℝ) * (ρ' * ((s * N + R : ℕ) : ℝ)) / N := by gcongr
    _ = r * s * ρ' + r * ρ' * R / N := by
        push_cast
        field_simp
    _ ≤ r * s * ρ' + r * |ρ'| * R / N := by
        gcongr
        exact le_abs_self _
    _ ≤ r * s * ρ + ε := by linarith

/-- **Theorem A.2(2), discrepancy form in base `2^s`:**
`D_N(x; 2^s) ≥ 1 - (4/3) 2^{-sr} - rsρ - ε` eventually. -/
theorem radixDiscrepancy_eventually_ge_of_nafDensity {x ρ : ℝ} (hx : NafDensityLE x ρ)
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 1 - 4 / (3 * 2 ^ (s * r)) - r * s * ρ - ε ≤
      radixDiscrepancy (2 ^ s) x N := by
  obtain ⟨R, hR⟩ : ∃ R : ℕ, (2⁻¹ : ℝ) ^ R < min (ε / 2) (1 / 4) :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  have hRε : (2⁻¹ : ℝ) ^ R < ε / 2 := lt_of_lt_of_le hR (min_le_left _ _)
  have hR4 : (2⁻¹ : ℝ) ^ R < 1 / 4 := lt_of_lt_of_le hR (min_le_right _ _)
  filter_upwards [eventually_frequency_le_of_nafDensity hx hs hr R (half_pos hε)] with N hN
  set κ : ℝ := 2 / (3 * 2 ^ (s * r)) with hκdef
  have hκ0 : 0 < κ := by positivity
  have hκ3 : κ ≤ 1 / 3 := by
    rw [hκdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ 2 ^ (s * r) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (s * r) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
    linarith
  have hR0 : (0 : ℝ) < 2⁻¹ ^ R := by positivity
  have hI := interval_le_radixDiscrepancy (2 ^ s) x N (a := κ + 2⁻¹ ^ R) (c := 1 - κ)
    (by positivity) (by linarith) (by linarith)
  have hab := neg_abs_le (frequency (shift (2 ^ s) x) (κ + 2⁻¹ ^ R) (1 - κ) N -
    (1 - κ - (κ + 2⁻¹ ^ R)))
  have e : (4 : ℝ) / (3 * 2 ^ (s * r)) = 2 * κ := by
    rw [hκdef]
    ring
  rw [e]
  linarith

/-- **Theorem A.2(2), base `2`:** `D_N(x; 2) ≥ 1 - (4/3) 2^{-ℓ} - ℓρ - ε` eventually. -/
theorem binary_radixDiscrepancy_eventually_ge_of_nafDensity {x ρ : ℝ} (hx : NafDensityLE x ρ)
    {l : ℕ} (hl : 1 ≤ l) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 1 - 4 / (3 * 2 ^ l) - l * ρ - ε ≤ radixDiscrepancy 2 x N := by
  filter_upwards [radixDiscrepancy_eventually_ge_of_nafDensity hx (s := 1) le_rfl hl hε]
    with N hN
  simpa only [pow_one, one_mul, Nat.cast_one, mul_one] using hN

/-- **`ℓ = 2` in base `2`:** `D_N(x; 2) ≥ 2/3 - 2ρ - ε` eventually. -/
theorem binary_radixDiscrepancy_eventually_ge_two_thirds {x ρ : ℝ} (hx : NafDensityLE x ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 2 / 3 - 2 * ρ - ε ≤ radixDiscrepancy 2 x N := by
  filter_upwards [binary_radixDiscrepancy_eventually_ge_of_nafDensity hx (l := 2) (by norm_num) hε]
    with N hN
  norm_num at hN ⊢
  linarith

/-- **`r = 1` in base `4`:** `D_N(x; 4) ≥ 2/3 - 2ρ - ε` eventually (no radix-descent loss). -/
theorem base4_radixDiscrepancy_eventually_ge_two_thirds {x ρ : ℝ} (hx : NafDensityLE x ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 2 / 3 - 2 * ρ - ε ≤ radixDiscrepancy 4 x N := by
  filter_upwards [radixDiscrepancy_eventually_ge_of_nafDensity hx (s := 2) (r := 1)
    (by norm_num) le_rfl hε] with N hN
  norm_num at hN ⊢
  linarith

/-- Frequencies of half-open intervals are monotone under enlargement. -/
theorem frequency_mono_interval (u : ℕ → ℝ) {a a' c c' : ℝ} (ha : a' ≤ a) (hc : c ≤ c')
    (N : ℕ) : frequency u a c N ≤ frequency u a' c' N := by
  unfold frequency
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  exact_mod_cast card_le_card (fun i hi => by
    simp only [mem_filter] at hi ⊢
    exact ⟨hi.1, by linarith [hi.2.1], by linarith [hi.2.2]⟩)

/-- Unions of adjacent length-`L` cylinders: `∑_{v₁ ≤ v < v₂} f_N(v) = F_N([v₁/b^L, v₂/b^L))`. -/
theorem sum_wordFreq_eq_frequency {b L : ℕ} (hb : 1 ≤ b) (x : ℝ) (v₁ v₂ N : ℕ) :
    ∑ v ∈ Ico v₁ v₂, wordFreq b L x v N =
      frequency (shift b x) ((v₁ : ℝ) / (b : ℝ) ^ L) ((v₂ : ℝ) / (b : ℝ) ^ L) N := by
  have hB : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by exact_mod_cast hb) L
  unfold wordFreq frequency
  rw [← sum_div, ← Nat.cast_sum]
  congr 2
  unfold wordCount
  symm
  rw [card_eq_sum_card_fiberwise (f := fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊) (t := Ico v₁ v₂)]
  · refine sum_congr rfl (fun v hv => ?_)
    rw [mem_Ico] at hv
    congr 1
    ext n
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨⟨hn, _⟩, hfl⟩
      exact ⟨hn, hfl⟩
    · rintro ⟨hn, hfl⟩
      have hy0 : 0 ≤ (b : ℝ) ^ L * shift b x n :=
        mul_nonneg hB.le (Int.fract_nonneg _)
      have h1 : ((⌊(b : ℝ) ^ L * shift b x n⌋₊ : ℕ) : ℝ) ≤ (b : ℝ) ^ L * shift b x n :=
        Nat.floor_le hy0
      have h2 : (b : ℝ) ^ L * shift b x n < (⌊(b : ℝ) ^ L * shift b x n⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      rw [hfl] at h1 h2
      have hv1 : (v₁ : ℝ) ≤ v := by exact_mod_cast hv.1
      have hv2 : (v : ℝ) + 1 ≤ v₂ := by exact_mod_cast hv.2
      refine ⟨⟨hn, ?_, ?_⟩, hfl⟩
      · rw [div_le_iff₀ hB]
        linarith
      · rw [lt_div_iff₀ hB]
        linarith
  · intro n hn
    have hn' : n ∈ (range N).filter (fun i => (v₁ : ℝ) / (b : ℝ) ^ L ≤ shift b x i ∧
        shift b x i < (v₂ : ℝ) / (b : ℝ) ^ L) := hn
    simp only [mem_filter, mem_range] at hn'
    obtain ⟨_, h1, h2⟩ := hn'
    have hy0 : 0 ≤ (b : ℝ) ^ L * shift b x n := mul_nonneg hB.le (Int.fract_nonneg _)
    rw [div_le_iff₀ hB] at h1
    rw [lt_div_iff₀ hB] at h2
    show ⌊(b : ℝ) ^ L * shift b x n⌋₊ ∈ Ico v₁ v₂
    rw [mem_Ico]
    constructor
    · exact Nat.le_floor (by linarith)
    · exact (Nat.floor_lt hy0).2 (by linarith)

/-- A uniform frequency gap on a union of cylinders excludes `L`-normality in base `b`. -/
theorem not_orderNormal_of_frequency_le {b L : ℕ} (hb : 1 ≤ b) {x : ℝ} {v₁ v₂ : ℕ} {θ : ℝ}
    (hv : v₁ ≤ v₂) (hv₂ : v₂ ≤ b ^ L) (hθ : θ < ((v₂ : ℝ) - v₁) / (b : ℝ) ^ L)
    (hfreq : ∀ᶠ N in atTop,
      frequency (shift b x) ((v₁ : ℝ) / (b : ℝ) ^ L) ((v₂ : ℝ) / (b : ℝ) ^ L) N ≤ θ) :
    ¬ OrderNormal b L x := by
  intro hON
  have hlim : Tendsto (fun N => ∑ v ∈ Ico v₁ v₂, wordFreq b L x v N) atTop
      (𝓝 (∑ _v ∈ Ico v₁ v₂, 1 / (b : ℝ) ^ L)) :=
    tendsto_finsetSum _ (fun v hv' => hON v (by rw [mem_Ico] at hv'; omega))
  have hval : ∑ _v ∈ Ico v₁ v₂, 1 / (b : ℝ) ^ L = ((v₂ : ℝ) - v₁) / (b : ℝ) ^ L := by
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hv]
    ring
  rw [hval] at hlim
  obtain ⟨N, hN1, hN2⟩ := ((hlim.eventually (lt_mem_nhds hθ)).and hfreq).exists
  rw [sum_wordFreq_eq_frequency hb] at hN1
  linarith

/-- **Theorem B.1(2) mechanism:** `ρ < 5/16` excludes `4`-normality in base `2`
(ten binary cylinders `[3/16, 13/16) ⊂ (1/6, 5/6)`, total length `5/8`). -/
theorem not_orderNormal_two_four_of_nafDensity {x ρ : ℝ} (hx : NafDensityLE x ρ)
    (hρ : ρ < 5 / 16) : ¬ OrderNormal 2 4 x := by
  have hε : (0 : ℝ) < (5 / 8 - 2 * ρ) / 2 := by linarith
  refine not_orderNormal_of_frequency_le (b := 2) (L := 4) (v₁ := 3) (v₂ := 13)
    (θ := 2 * ρ + (5 / 8 - 2 * ρ) / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num; linarith) ?_
  filter_upwards [eventually_frequency_le_of_nafDensity hx (s := 1) (r := 2) le_rfl
    (by norm_num) 6 hε] with N hN
  have hmono := frequency_mono_interval (shift 2 x) (N := N)
    (a := ((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) ^ 4) (c := ((13 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) ^ 4)
    (a' := 2 / (3 * 2 ^ (1 * 2)) + (2⁻¹ : ℝ) ^ 6) (c' := 1 - 2 / (3 * 2 ^ (1 * 2)))
    (by norm_num) (by norm_num)
  rw [pow_one] at hN
  push_cast at hN ⊢
  linarith

/-- **Theorem B.1(2) mechanism in base `4`:** `ρ < 5/16` excludes `2`-normality in base `4`. -/
theorem not_orderNormal_four_two_of_nafDensity {x ρ : ℝ} (hx : NafDensityLE x ρ)
    (hρ : ρ < 5 / 16) : ¬ OrderNormal 4 2 x := by
  have hε : (0 : ℝ) < (5 / 8 - 2 * ρ) / 2 := by linarith
  refine not_orderNormal_of_frequency_le (b := 4) (L := 2) (v₁ := 3) (v₂ := 13)
    (θ := 2 * ρ + (5 / 8 - 2 * ρ) / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num; linarith) ?_
  filter_upwards [eventually_frequency_le_of_nafDensity hx (s := 2) (r := 1) (by norm_num)
    le_rfl 6 hε] with N hN
  have hmono := frequency_mono_interval (shift 4 x) (N := N)
    (a := ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ^ 2) (c := ((13 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ^ 2)
    (a' := 2 / (3 * 2 ^ (2 * 1)) + (2⁻¹ : ℝ) ^ 6) (c' := 1 - 2 / (3 * 2 ^ (2 * 1)))
    (by norm_num) (by norm_num)
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hN
  push_cast at hN ⊢
  linarith

/-- Normality in base `b` implies `L`-normality for every `L ≥ 1`. -/
theorem orderNormal_of_normalIn {b : ℕ} {x : ℝ} (h : NormalIn b x) {L : ℕ} (hL : 0 < L) :
    OrderNormal b L x := by
  intro v hv
  have hb : 1 ≤ b := by have := h.1; omega
  exact (h.2 L v hL hv).congr (fun N => (wordFreq_eq_frequency hb L x v N).symm)

/-! ### Part 5: signed series transfer (Theorem A.2(3)) -/

private theorem digitSum_two_le_log' (T : ℕ) : digitSum 2 T ≤ Nat.log 2 T + 1 := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  rcases Nat.lt_or_ge T 2 with hT | hT
  · interval_cases T
    · simp [digitSum]
    · simp [digitSum]
  · rw [digitSum_eq (le_refl 2)]
    have h1 := ih (T / 2) (Nat.div_lt_self (by omega) (by norm_num))
    have h2 : Nat.log 2 (T / 2) = Nat.log 2 T - 1 := Nat.log_div_base 2 T
    have h3 : 0 < Nat.log 2 T := Nat.log_pos (by norm_num) hT
    have h4 := Nat.mod_lt T (show 2 > 0 by norm_num)
    omega

/-- `w_±(T) ≤ ⌊log₂ T⌋ + 1`. -/
theorem signedWeight_le_log (T : ℕ) : signedWeight T ≤ Nat.log 2 T + 1 :=
  (signedWeight_le_digitSum T).trans (digitSum_two_le_log' T)

private theorem signedWeight_le_real_log {T : ℕ} {D : ℝ} (hD : 1 ≤ D) (hT : (T : ℝ) ≤ D) :
    (signedWeight T : ℝ) ≤ Real.log D / Real.log 2 + 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (signedWeight T : ℝ) ≤ Nat.log 2 T + 1 := by exact_mod_cast signedWeight_le_log T
  rcases Nat.eq_zero_or_pos T with rfl | hT0
  · simp only [Nat.log_zero_right, CharP.cast_eq_zero, zero_add] at h1
    have : 0 ≤ Real.log D / Real.log 2 := div_nonneg (Real.log_nonneg hD) hlog2.le
    linarith
  · have h2 : (2 : ℝ) ^ Nat.log 2 T ≤ D := by
      have := Nat.pow_log_le_self 2 hT0.ne'
      calc (2 : ℝ) ^ Nat.log 2 T = ((2 ^ Nat.log 2 T : ℕ) : ℝ) := by push_cast; ring
        _ ≤ T := by exact_mod_cast this
        _ ≤ D := hT
    have h3 : (Nat.log 2 T : ℝ) ≤ Real.log D / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      have := (Real.pow_le_iff_le_log (by norm_num) (by linarith)).1 h2
      linarith
    linarith

private theorem tendsto_log_poly_div {c : ℝ} (hc : 0 ≤ c) (B : ℕ) :
    Tendsto (fun M : ℕ => (Real.log (c * ((M : ℝ) + 1) ^ B + 2) / Real.log 2 + 1) / M)
      atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 1) / M) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
    have hg : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    refine (h.comp hg).congr' (Eventually.of_forall (fun M => ?_))
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have hinv : Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hup : Tendsto (fun M : ℕ => (Real.log (c + 2) / Real.log 2 + 1) * (1 / (M : ℝ)) +
      (B / Real.log 2) * (Real.log ((M : ℝ) + 1) / M)) atTop (𝓝 0) := by
    have := (hinv.const_mul (Real.log (c + 2) / Real.log 2 + 1)).add
      (hlogM.const_mul (B / Real.log 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hpow : 0 ≤ c * ((M : ℝ) + 1) ^ B := by positivity
    have : 0 ≤ Real.log (c * ((M : ℝ) + 1) ^ B + 2) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith
    have hpow : (1 : ℝ) ≤ ((M : ℝ) + 1) ^ B := one_le_pow₀ hM1
    have hle : c * ((M : ℝ) + 1) ^ B + 2 ≤ (c + 2) * ((M : ℝ) + 1) ^ B := by nlinarith
    have hlog : Real.log (c * ((M : ℝ) + 1) ^ B + 2) ≤
        Real.log (c + 2) + B * Real.log ((M : ℝ) + 1) := by
      calc _ ≤ Real.log ((c + 2) * ((M : ℝ) + 1) ^ B) :=
            Real.log_le_log (by positivity) hle
        _ = Real.log (c + 2) + B * Real.log ((M : ℝ) + 1) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h1 : Real.log (c * ((M : ℝ) + 1) ^ B + 2) / Real.log 2 ≤
        Real.log (c + 2) / Real.log 2 + B / Real.log 2 * Real.log ((M : ℝ) + 1) := by
      calc _ ≤ (Real.log (c + 2) + B * Real.log ((M : ℝ) + 1)) / Real.log 2 :=
            div_le_div_of_nonneg_right hlog hlog2.le
        _ = _ := by ring
    have e : (Real.log (c + 2) / Real.log 2 + 1) * (1 / (M : ℝ)) +
        (B / Real.log 2) * (Real.log ((M : ℝ) + 1) / M) =
        (Real.log (c + 2) / Real.log 2 + 1 + B / Real.log 2 * Real.log ((M : ℝ) + 1)) / M := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hMr.le

private theorem abs_series_tail_le {k : ℕ} (hk : 1 ≤ k) (a : ℕ → ℤ) {C₀ : ℝ} {B : ℕ}
    (hC₀ : 0 ≤ C₀) (hgrowth : ∀ n, 1 ≤ n → |(a n : ℝ)| ≤ C₀ * (n : ℝ) ^ B) (M : ℕ) :
    |∑' m : ℕ, (a (M / k + 1 + m) : ℝ) * (2 : ℝ) ^ M / (2 : ℝ) ^ (k * (M / k + 1 + m))| ≤
      C₀ * ((M : ℝ) + 1) ^ B * ∑' m : ℕ, ((m : ℝ) + 1) ^ B * (1 / 2) ^ (m + 1) := by
  have hg : Summable fun m : ℕ => ((m : ℝ) + 1) ^ B * (1 / 2) ^ (m + 1) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one B (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
    have h' := (summable_nat_add_iff 1).2 h
    refine h'.congr (fun m => ?_)
    push_cast
    ring
  set Q := M / k
  have hkn : ∀ m : ℕ, M + (m + 1) ≤ k * (Q + 1 + m) := by
    intro m
    have h1 : M < k * (Q + 1) := Nat.lt_mul_div_succ M (by omega)
    have h2 : m ≤ k * m := Nat.le_mul_of_pos_left m (by omega)
    have : k * (Q + 1 + m) = k * (Q + 1) + k * m := by ring
    omega
  have hterm : ∀ m : ℕ, ‖(a (Q + 1 + m) : ℝ) * (2 : ℝ) ^ M / (2 : ℝ) ^ (k * (Q + 1 + m))‖ ≤
      C₀ * ((M : ℝ) + 1) ^ B * (((m : ℝ) + 1) ^ B * (1 / 2) ^ (m + 1)) := by
    intro m
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ M),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (k * (Q + 1 + m)))]
    have ha := hgrowth (Q + 1 + m) (Nat.le_add_right_of_le (Nat.le_add_left 1 Q))
    have hQM : (Q : ℝ) ≤ M := by exact_mod_cast Nat.div_le_self M k
    have hidx : ((Q + 1 + m : ℕ) : ℝ) ≤ ((M : ℝ) + 1) * ((m : ℝ) + 1) := by
      push_cast
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hpowB : ((Q + 1 + m : ℕ) : ℝ) ^ B ≤ ((M : ℝ) + 1) ^ B * ((m : ℝ) + 1) ^ B := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hidx B
    have hpow : (2 : ℝ) ^ M / (2 : ℝ) ^ (k * (Q + 1 + m)) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
      have hE : (2 : ℝ) ^ (M + (m + 1)) ≤ (2 : ℝ) ^ (k * (Q + 1 + m)) :=
        pow_le_pow_right₀ (by norm_num) (hkn m)
      have h2 : (2 : ℝ) ^ (M + (m + 1)) = (2 : ℝ) ^ M * (2 : ℝ) ^ (m + 1) := pow_add _ _ _
      rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have ha' : |(a (Q + 1 + m) : ℝ)| ≤ C₀ * (((M : ℝ) + 1) ^ B * ((m : ℝ) + 1) ^ B) :=
      ha.trans (mul_le_mul_of_nonneg_left hpowB hC₀)
    calc |(a (Q + 1 + m) : ℝ)| * (2 : ℝ) ^ M / (2 : ℝ) ^ (k * (Q + 1 + m))
        = |(a (Q + 1 + m) : ℝ)| * ((2 : ℝ) ^ M / (2 : ℝ) ^ (k * (Q + 1 + m))) := by ring
      _ ≤ (C₀ * (((M : ℝ) + 1) ^ B * ((m : ℝ) + 1) ^ B)) * (1 / 2 : ℝ) ^ (m + 1) :=
          mul_le_mul ha' hpow (by positivity) (by positivity)
      _ = C₀ * ((M : ℝ) + 1) ^ B * (((m : ℝ) + 1) ^ B * (1 / 2) ^ (m + 1)) := by ring
  have hsn : Summable fun m : ℕ =>
      ‖(a (Q + 1 + m) : ℝ) * (2 : ℝ) ^ M / (2 : ℝ) ^ (k * (Q + 1 + m))‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm (hg.mul_left _)
  rw [← Real.norm_eq_abs]
  calc _ ≤ ∑' m : ℕ, ‖(a (Q + 1 + m) : ℝ) * (2 : ℝ) ^ M / (2 : ℝ) ^ (k * (Q + 1 + m))‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' m : ℕ, C₀ * ((M : ℝ) + 1) ^ B * (((m : ℝ) + 1) ^ B * (1 / 2) ^ (m + 1)) :=
        hsn.tsum_le_tsum hterm (hg.mul_left _)
    _ = _ := tsum_mul_left

/-- **Theorem A.2(3), signed series transfer.** If `|a(n)| ≤ C₀ n^B` and the mean signed weight
of `a` is at most `C`, then `x = ∑_{n ≥ 1} a(n) 2^{-kn}` has upper prefix NAF density `≤ C/k`. -/
theorem nafDensityLE_of_series {k : ℕ} (hk : 1 ≤ k) (a : ℕ → ℤ) {C₀ : ℝ} {B : ℕ}
    (hgrowth : ∀ n, 1 ≤ n → |(a n : ℝ)| ≤ C₀ * (n : ℝ) ^ B) {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ C' > C, ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ Icc 1 X, (signedWeight (a n).natAbs : ℝ) ≤ C' * X) :
    NafDensityLE (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (k * (n + 1))) (C / k) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hC₀ : 0 ≤ C₀ := by
    have := hgrowth 1 le_rfl
    simp only [Nat.cast_one, one_pow, mul_one] at this
    linarith [abs_nonneg (a 1 : ℝ)]
  set K : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ B * (1 / 2) ^ (m + 1) with hKdef
  have hg : Summable fun m : ℕ => ((m : ℝ) + 1) ^ B * (1 / 2) ^ (m + 1) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one B (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
    have h' := (summable_nat_add_iff 1).2 h
    refine h'.congr (fun m => ?_)
    push_cast
    ring
  have hK0 : 0 ≤ K := tsum_nonneg (fun m => by positivity)
  have hsumm : Summable fun n : ℕ =>
      |((a (n + 1) : ℤ) : ℝ)| / ((2 : ℕ) : ℝ) ^ (k * (n + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hg.mul_left C₀)
    have ha := hgrowth (n + 1) (by omega)
    have hpow : ((2 : ℕ) : ℝ) ^ (n + 1) ≤ ((2 : ℕ) : ℝ) ^ (k * (n + 1)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
    rw [div_le_iff₀ (by positivity)]
    push_cast at ha hpow ⊢
    calc |(a (n + 1) : ℝ)| ≤ C₀ * ((n : ℝ) + 1) ^ B := ha
      _ = C₀ * (((n : ℝ) + 1) ^ B * (1 / 2) ^ (n + 1)) * 2 ^ (n + 1) := by
          rw [one_div_pow]
          field_simp
      _ ≤ C₀ * (((n : ℝ) + 1) ^ B * (1 / 2) ^ (n + 1)) * 2 ^ (k * (n + 1)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  intro ρ' hρ'
  have hkρ : C < k * ρ' := by
    have := (div_lt_iff₀ hkr).1 hρ'
    linarith
  set C' := (C + k * ρ') / 2 with hC'def
  have hC'1 : C' > C := by rw [hC'def]; linarith
  have hC'0 : 0 ≤ C' := by rw [hC'def]; linarith
  have hC'2 : C' / k < ρ' := by
    rw [div_lt_iff₀ hkr, hC'def]
    linarith
  set η := ρ' - C' / k with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have htail := tendsto_log_poly_div (mul_nonneg hC₀ hK0) B
  filter_upwards [(Nat.tendsto_div_const_atTop (show k ≠ 0 by omega)).eventually (hmean C' hC'1),
    htail.eventually (gt_mem_nhds hη), eventually_ge_atTop 1] with M hM1 hM2 hM3
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM3
  -- exact prefix decomposition
  have h7 := floor_pow_mul_eq_head_add_floor_tail (b := 2) (k := k) (le_refl 2) a hsumm M
  simp only [Nat.cast_ofNat] at h7
  set τ : ℝ := ∑' m : ℕ, (a (M / k + 1 + m) : ℝ) * (2 : ℝ) ^ M / (2 : ℝ) ^ (k * (M / k + 1 + m))
    with hτdef
  -- weight splitting
  have hw : signedWeight ⌊(2 : ℝ) ^ M * ∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (k * (n + 1))⌋.natAbs ≤
      ∑ n ∈ Icc 1 (M / k), signedWeight (a n).natAbs + signedWeight ⌊τ⌋.natAbs := by
    rw [h7]
    have h1 := signedWeight_natAbs_add_le (∑ n ∈ Icc 1 (M / k), a n * 2 ^ (M - k * n)) ⌊τ⌋
    have h2 := signedWeight_natAbs_sum_le (Icc 1 (M / k)) a (fun n => M - k * n)
    omega
  -- the head
  have hhead : ∑ n ∈ Icc 1 (M / k), (signedWeight (a n).natAbs : ℝ) ≤ C' / k * M := by
    refine hM1.trans ?_
    have hdiv : ((M / k : ℕ) : ℝ) ≤ (M : ℝ) / k := Nat.cast_div_le
    calc C' * ((M / k : ℕ) : ℝ) ≤ C' * ((M : ℝ) / k) := mul_le_mul_of_nonneg_left hdiv hC'0
      _ = C' / k * M := by ring
  -- the tail
  have hτ := abs_series_tail_le hk a hC₀ hgrowth M
  rw [← hτdef, ← hKdef] at hτ
  have hfl : |(⌊τ⌋ : ℝ)| ≤ |τ| + 1 := by
    have h1 := Int.floor_le τ
    have h2 := Int.lt_floor_add_one τ
    rw [abs_le]
    constructor
    · have := neg_abs_le τ
      linarith
    · have := le_abs_self τ
      linarith
  have hT : ((⌊τ⌋.natAbs : ℕ) : ℝ) ≤ C₀ * K * ((M : ℝ) + 1) ^ B + 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    nlinarith
  have hD : (1 : ℝ) ≤ C₀ * K * ((M : ℝ) + 1) ^ B + 2 := by
    have : 0 ≤ C₀ * K * ((M : ℝ) + 1) ^ B := by positivity
    linarith
  have hwτ := signedWeight_le_real_log hD hT
  have hM2' : Real.log (C₀ * K * ((M : ℝ) + 1) ^ B + 2) / Real.log 2 + 1 < η * M := by
    rwa [div_lt_iff₀ hMr] at hM2
  have hwR : (signedWeight ⌊(2 : ℝ) ^ M * ∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (k * (n + 1))⌋.natAbs : ℝ)
      ≤ ∑ n ∈ Icc 1 (M / k), (signedWeight (a n).natAbs : ℝ) + signedWeight ⌊τ⌋.natAbs := by
    exact_mod_cast hw
  have e : ρ' * M = C' / k * M + η * M := by rw [hηdef]; ring
  rw [e]
  linarith

/-! ### Part 6: the alternating Erdős–Borwein series `E_+(2^k)` -/

/-- `E_+(2^k) = ∑_{m ≥ 1} 1/(2^{km} + 1)`. -/
noncomputable def erdosBorweinPlusPow (k : ℕ) : ℝ := ∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) + 1)

/-- `a_+(n) = (1 - v₂(n)) τ_odd(n)`. -/
def aPlus (n : ℕ) : ℤ := (1 - (n.factorization 2 : ℤ)) * ClassicalBarriers.tauOdd n

/-- `a_+` coincides with `Phase22Cores.erdosBorweinPlusCoeff` (`τ(n) - 2 [2 ∣ n] τ(n/2)`). -/
theorem aPlus_eq_erdosBorweinPlusCoeff (n : ℕ) :
    aPlus n = Phase22Cores.erdosBorweinPlusCoeff n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aPlus, Phase22Cores.erdosBorweinPlusCoeff, ClassicalBarriers.tauOdd]
  · rw [Phase22Cores.erdosBorweinPlusCoeff_eq hn]
    rfl

private theorem summable_tau_div' {k : ℕ} (hk : 1 ≤ k) :
    Summable fun n : ℕ => (n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have h1 : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (k * n) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  calc (n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n) ≤ (n.divisors.card : ℝ) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h2
    _ ≤ (n : ℝ) / (2 : ℝ) ^ n := div_le_div_of_nonneg_right h1 (by positivity)
    _ = (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n := by rw [pow_one, one_div_pow, mul_one_div]

/-- **Lambert expansion:** `E_+(2^k) = ∑_{n ≥ 1} a_+(n) 2^{-kn}`. -/
theorem erdosBorweinPlusPow_eq_signed_series {k : ℕ} (hk : 1 ≤ k) :
    erdosBorweinPlusPow k = ∑' n : ℕ, (aPlus (n + 1) : ℝ) / 2 ^ (k * (n + 1)) := by
  have hb : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h := Phase22Cores.erdosBorweinPlus_eq_sub hb
  have e1 : (∑' n : ℕ, (1 : ℝ) / (((2 ^ k : ℕ) : ℝ) ^ (n + 1) + 1)) = erdosBorweinPlusPow k := by
    unfold erdosBorweinPlusPow
    refine tsum_congr (fun n => ?_)
    push_cast
    rw [← pow_mul]
  have e2 : (∑' n : ℕ, (1 : ℝ) / (((2 ^ k : ℕ) : ℝ) ^ (n + 1) - 1)) = erdosBorweinPow k := by
    unfold erdosBorweinPow
    refine tsum_congr (fun n => ?_)
    push_cast
    rw [← pow_mul]
  have e3 : (∑' n : ℕ, (1 : ℝ) / ((((2 ^ k) ^ 2 : ℕ) : ℝ) ^ (n + 1) - 1)) =
      erdosBorweinPow (2 * k) := by
    unfold erdosBorweinPow
    refine tsum_congr (fun n => ?_)
    push_cast
    rw [← pow_mul, ← pow_mul, show k * (2 * (n + 1)) = 2 * k * (n + 1) by ring]
  rw [e1, e2, e3, erdosBorweinPow_eq_divisor_series hk,
    erdosBorweinPow_eq_divisor_series (show 1 ≤ 2 * k by omega)] at h
  rw [h]
  set f : ℕ → ℝ := fun n => ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (k * (n + 1)) with hfdef
  set g : ℕ → ℝ := fun n => (if 2 ∣ n + 1 then (((n + 1) / 2).divisors.card : ℝ) else 0) /
    (2 : ℝ) ^ (k * (n + 1)) with hgdef
  have hf : Summable f := (summable_tau_div' hk).comp_injective Nat.succ_injective
  have hg_odd : ∀ j : ℕ, g (2 * j + 1) =
      ((j + 1).divisors.card : ℝ) / (2 : ℝ) ^ (2 * k * (j + 1)) := by
    intro j
    simp only [hgdef]
    rw [ite_eq_left (show 2 ∣ 2 * j + 1 + 1 by omega), show (2 * j + 1 + 1) / 2 = j + 1 by omega,
      show k * (2 * j + 1 + 1) = 2 * k * (j + 1) by ring]
  have hg_even : ∀ j : ℕ, g (2 * j) = 0 := by
    intro j
    simp only [hgdef]
    rw [ite_eq_right (show ¬ 2 ∣ 2 * j + 1 by omega), zero_div]
  have hso : Summable fun j : ℕ => g (2 * j + 1) := by
    simp_rw [hg_odd]
    exact (summable_tau_div' (show 1 ≤ 2 * k by omega)).comp_injective Nat.succ_injective
  have hse : Summable fun j : ℕ => g (2 * j) := by
    simp_rw [hg_even]
    exact summable_zero
  have hg : Summable g := Summable.even_add_odd hse hso
  have hgsum : ∑' n : ℕ, g n =
      ∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (2 * k * (n + 1)) := by
    rw [← tsum_even_add_odd hse hso]
    simp_rw [hg_even, hg_odd, tsum_zero, zero_add]
  have hterm : ∀ n : ℕ, (aPlus (n + 1) : ℝ) / 2 ^ (k * (n + 1)) = f n - 2 * g n := by
    intro n
    simp only [hfdef, hgdef]
    rw [aPlus_eq_erdosBorweinPlusCoeff]
    unfold Phase22Cores.erdosBorweinPlusCoeff
    split_ifs <;> push_cast <;> ring
  rw [tsum_congr hterm, hf.tsum_sub (hg.mul_left 2), tsum_mul_left, hgsum]

/-! #### The multiplicative majorant `G₀` -/

/-- The multiplicative arithmetic function with prime-dependent prime-power values `g p e`
(normalised by `g p 0 = 1`): `n ↦ ∏_{p^e ∥ n} g(p, e)`. -/
noncomputable def multOfPrimePowAt (g : ℕ → ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod g, by simp⟩

theorem multOfPrimePowAt_apply (g : ℕ → ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    multOfPrimePowAt g n = n.factorization.prod g := by
  simp [multOfPrimePowAt, hn]

theorem multOfPrimePowAt_isMultiplicative (g : ℕ → ℕ → ℝ) :
    (multOfPrimePowAt g).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn hmn => ?_⟩
  · rw [multOfPrimePowAt_apply g one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  · rw [multOfPrimePowAt_apply g (mul_ne_zero hm hn), multOfPrimePowAt_apply g hm,
      multOfPrimePowAt_apply g hn, Nat.factorization_mul_of_coprime hmn,
      Finsupp.prod_add_index_of_disjoint]
    rw [Nat.support_factorization, Nat.support_factorization]
    exact hmn.disjoint_primeFactors

theorem multOfPrimePowAt_prime_pow {g : ℕ → ℕ → ℝ} (hg : ∀ p, g p 0 = 1) {p : ℕ}
    (hp : p.Prime) (e : ℕ) : multOfPrimePowAt g (p ^ e) = g p e := by
  rw [multOfPrimePowAt_apply g (pow_ne_zero e hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (hg p)]

theorem multOfPrimePowAt_nonneg {g : ℕ → ℕ → ℝ} (hg : ∀ p e, 0 ≤ g p e) (n : ℕ) :
    0 ≤ multOfPrimePowAt g n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [multOfPrimePowAt_apply g hn.ne']
    exact Finset.prod_nonneg (fun p _ => hg _ _)

/-- Prime-power values of `G₀`: `G₀(2^e) = w_±(|1 - e|)`, `G₀(p^e) = w_±(e + 1)` (`p` odd). -/
noncomputable def ePlusLocal (p e : ℕ) : ℝ :=
  if p = 2 then (signedWeight (1 - (e : ℤ)).natAbs : ℝ) else (signedWeight (e + 1) : ℝ)

/-- Prime-power values of the Möbius kernel `G₀ * μ`. -/
noncomputable def ePlusKernelLocal (p e : ℕ) : ℝ :=
  ePlusLocal p e - if e = 0 then 0 else ePlusLocal p (e - 1)

/-- The multiplicative majorant `G₀` of `w_±(|a_+(n)|)` (Theorem B.2(1)). -/
noncomputable def ePlusMajorant : ArithmeticFunction ℝ := multOfPrimePowAt ePlusLocal

/-- The Möbius kernel `h₀ = G₀ * μ`. -/
noncomputable def ePlusKernel : ArithmeticFunction ℝ := multOfPrimePowAt ePlusKernelLocal

/-- The mean value `W_+^{maj} = ∑_n h₀(n)/n` of the majorant. -/
noncomputable def ePlusMean : ℝ := ∑' n : ℕ, ePlusKernel n / n

theorem ePlusLocal_zero (p : ℕ) : ePlusLocal p 0 = 1 := by
  unfold ePlusLocal
  split_ifs <;> simp

theorem ePlusLocal_nonneg (p e : ℕ) : 0 ≤ ePlusLocal p e := by
  unfold ePlusLocal
  split_ifs <;> positivity

theorem abs_ePlusLocal_le (p e : ℕ) : |ePlusLocal p e| ≤ e + 1 := by
  rw [abs_of_nonneg (ePlusLocal_nonneg p e)]
  unfold ePlusLocal
  split_ifs
  · have h1 := signedWeight_le_self (1 - (e : ℤ)).natAbs
    have h2 : (1 - (e : ℤ)).natAbs ≤ e + 1 := by omega
    exact_mod_cast h1.trans h2
  · exact_mod_cast signedWeight_le_self (e + 1)

theorem ePlusKernelLocal_zero (p : ℕ) : ePlusKernelLocal p 0 = 1 := by
  simp [ePlusKernelLocal, ePlusLocal_zero]

theorem ePlusKernelLocal_of_ne_two {p : ℕ} (hp : p ≠ 2) (e : ℕ) :
    ePlusKernelLocal p e = (signedWeight (e + 1) : ℝ) - signedWeight e := by
  unfold ePlusKernelLocal ePlusLocal
  rcases e with _ | e
  · simp [hp]
  · simp [hp]

theorem ePlusKernelLocal_one_of_ne_two {p : ℕ} (hp : p ≠ 2) : ePlusKernelLocal p 1 = 0 := by
  rw [ePlusKernelLocal_of_ne_two hp]
  norm_num [signedWeight]

theorem ePlusKernelLocal_two_one : ePlusKernelLocal 2 1 = -1 := by
  simp [ePlusKernelLocal, ePlusLocal]

theorem abs_ePlusKernelLocal_le (p e : ℕ) : |ePlusKernelLocal p e| ≤ 1 := by
  by_cases hp : p = 2
  · subst hp
    rcases e with _ | _ | e
    · rw [ePlusKernelLocal_zero]
      norm_num
    · rw [ePlusKernelLocal_two_one]
      norm_num
    · have h1 : (1 - ((e + 1 + 1 : ℕ) : ℤ)).natAbs = e + 1 := by omega
      have h2 : (1 - ((e + 1 + 1 - 1 : ℕ) : ℤ)).natAbs = e := by omega
      unfold ePlusKernelLocal ePlusLocal
      rw [ite_eq_right (show e + 1 + 1 ≠ 0 by omega), ite_eq_left (rfl : (2 : ℕ) = 2),
        ite_eq_left (rfl : (2 : ℕ) = 2), h1, h2]
      exact abs_signedWeight_succ_sub_le e
  · rw [ePlusKernelLocal_of_ne_two hp]
    exact abs_signedWeight_succ_sub_le e

theorem ePlusMajorant_isMultiplicative : ePlusMajorant.IsMultiplicative :=
  multOfPrimePowAt_isMultiplicative _

theorem ePlusKernel_isMultiplicative : ePlusKernel.IsMultiplicative :=
  multOfPrimePowAt_isMultiplicative _

theorem ePlusMajorant_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ePlusMajorant (p ^ e) = ePlusLocal p e :=
  multOfPrimePowAt_prime_pow ePlusLocal_zero hp e

theorem ePlusKernel_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ePlusKernel (p ^ e) = ePlusKernelLocal p e :=
  multOfPrimePowAt_prime_pow ePlusKernelLocal_zero hp e

theorem ePlusMajorant_nonneg (n : ℕ) : 0 ≤ ePlusMajorant n :=
  multOfPrimePowAt_nonneg ePlusLocal_nonneg n

theorem ePlusKernel_mul_zeta :
    ePlusKernel * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = ePlusMajorant := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (ePlusKernel_isMultiplicative.mul ArithmeticFunction.isMultiplicative_zeta.natCast) _
    ePlusMajorant_isMultiplicative).2 (fun p e hp => ?_)
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    ePlusMajorant_prime_pow hp]
  simp_rw [ePlusKernel_prime_pow hp]
  have htel : ∀ m : ℕ, ∑ i ∈ range (m + 1), ePlusKernelLocal p i = ePlusLocal p m := by
    intro m
    induction m with
    | zero => simp [ePlusKernelLocal_zero, ePlusLocal_zero]
    | succ m ih =>
      rw [sum_range_succ, ih]
      simp [ePlusKernelLocal]
  exact htel e

/-- The kernel identity `G₀ * μ = h₀`. -/
theorem ePlusMajorant_mul_moebius :
    ePlusMajorant * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = ePlusKernel := by
  rw [← ePlusKernel_mul_zeta, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]

/-! #### `a_+` is multiplicative and dominated by `G₀` -/

theorem aPlus_two_pow (e : ℕ) : aPlus (2 ^ e) = 1 - e := by
  have h := Phase22Cores.card_divisors_eq_succ_fac_two_mul_tauOdd
    (pow_pos (by norm_num : 0 < 2) e)
  have hfac : (2 ^ e).factorization 2 = e := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
  have hcard : ((2 ^ e).divisors.card : ℤ) = e + 1 := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two]
    push_cast
    ring
  rw [hfac, hcard] at h
  have htau : ClassicalBarriers.tauOdd (2 ^ e) = 1 := by
    have hne : ((e : ℤ) + 1) ≠ 0 := by positivity
    exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)
  unfold aPlus
  rw [hfac, htau, mul_one]

theorem aPlus_prime_pow_of_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (e : ℕ) :
    aPlus (p ^ e) = e + 1 := by
  have h := Phase22Cores.card_divisors_eq_succ_fac_two_mul_tauOdd (pow_pos hp.pos e)
  have hfac : (p ^ e).factorization 2 = 0 := by
    rw [hp.factorization_pow, Finsupp.single_apply, ite_eq_right h2]
  have hcard : ((p ^ e).divisors.card : ℤ) = e + 1 := by
    rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    push_cast
    ring
  rw [hfac, hcard] at h
  unfold aPlus
  rw [hfac]
  push_cast at h ⊢
  linarith

theorem aPlus_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    aPlus (m * n) = aPlus m * aPlus n := by
  have hmn0 : 0 < m * n := Nat.mul_pos hm hn
  have hv : (m * n).factorization 2 = m.factorization 2 + n.factorization 2 := by
    rw [Nat.factorization_mul hm.ne' hn.ne', Finsupp.add_apply]
  have hzero : m.factorization 2 = 0 ∨ n.factorization 2 = 0 := by
    by_contra hcon
    push Not at hcon
    have h2m : 2 ∣ m := by
      have := (Nat.prime_two.pow_dvd_iff_le_factorization hm.ne' (k := 1)).2 (by omega)
      simpa using this
    have h2n : 2 ∣ n := by
      have := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne' (k := 1)).2 (by omega)
      simpa using this
    have := Nat.Coprime.coprime_dvd_left h2m (Nat.Coprime.coprime_dvd_right h2n hmn)
    norm_num at this
  have hτ := Phase22Cores.card_divisors_eq_succ_fac_two_mul_tauOdd hmn0
  have hτm := Phase22Cores.card_divisors_eq_succ_fac_two_mul_tauOdd hm
  have hτn := Phase22Cores.card_divisors_eq_succ_fac_two_mul_tauOdd hn
  have hcard : ((m * n).divisors.card : ℤ) = (m.divisors.card : ℤ) * n.divisors.card := by
    rw [Nat.Coprime.card_divisors_mul hmn]
    push_cast
    ring
  rw [hv] at hτ
  have htau : ClassicalBarriers.tauOdd (m * n) =
      ClassicalBarriers.tauOdd m * ClassicalBarriers.tauOdd n := by
    have hne : ((m.factorization 2 : ℤ) + n.factorization 2 + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    have hprod : ((m.factorization 2 : ℤ) + n.factorization 2 + 1) =
        ((m.factorization 2 : ℤ) + 1) * ((n.factorization 2 : ℤ) + 1) := by
      rcases hzero with h | h <;> rw [h] <;> push_cast <;> ring
    push_cast at hτ
    rw [← hτ, hcard, hτm, hτn, hprod]
    ring
  unfold aPlus
  rw [hv, htau]
  push_cast
  rcases hzero with h | h <;> rw [h] <;> push_cast <;> ring

/-- `|a_+(n)| ≤ τ(n) ≤ n`. -/
theorem abs_aPlus_le (n : ℕ) : |(aPlus n : ℝ)| ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aPlus, ClassicalBarriers.tauOdd]
  have h := Phase22Cores.card_divisors_eq_succ_fac_two_mul_tauOdd hn
  have ht : 0 ≤ ClassicalBarriers.tauOdd n := by
    unfold ClassicalBarriers.tauOdd
    positivity
  have hτn : ((n.divisors.card : ℤ)) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have hz : |aPlus n| ≤ n := by
    unfold aPlus
    rw [abs_mul, abs_of_nonneg ht]
    have h1 : |1 - (n.factorization 2 : ℤ)| ≤ (n.factorization 2 : ℤ) + 1 := by
      rw [abs_le]
      constructor <;> omega
    nlinarith
  exact_mod_cast hz

/-- **Theorem B.2(1):** `w_±(|a_+(n)|) ≤ G₀(n)` for every `n`. -/
theorem signedWeight_aPlus_le (n : ℕ) : (signedWeight (aPlus n).natAbs : ℝ) ≤ ePlusMajorant n := by
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun n => (signedWeight (aPlus n).natAbs : ℝ) ≤ ePlusMajorant n) ?_ ?_ ?_ ?_ n
  · intro p e hp _
    rw [ePlusMajorant_prime_pow hp]
    by_cases h2 : p = 2
    · subst h2
      rw [aPlus_two_pow]
      simp [ePlusLocal]
    · rw [aPlus_prime_pow_of_ne_two hp h2]
      simp only [ePlusLocal, ite_eq_right h2]
      have e1 : ((e : ℤ) + 1).natAbs = e + 1 := by omega
      rw [e1]
  · simp [aPlus, ClassicalBarriers.tauOdd]
  · simp [aPlus, ClassicalBarriers.tauOdd, ePlusMajorant_isMultiplicative.map_one,
      Finset.filter_singleton]
  · intro a b ha hb hab iha ihb
    rw [aPlus_mul_of_coprime (by omega) (by omega) hab,
      ePlusMajorant_isMultiplicative.map_mul_of_coprime hab, Int.natAbs_mul]
    calc (signedWeight ((aPlus a).natAbs * (aPlus b).natAbs) : ℝ)
        ≤ (signedWeight (aPlus a).natAbs : ℝ) * signedWeight (aPlus b).natAbs := by
          exact_mod_cast signedWeight_mul_le _ _
      _ ≤ ePlusMajorant a * ePlusMajorant b :=
          mul_le_mul iha ihb (Nat.cast_nonneg _) (ePlusMajorant_nonneg a)

/-! #### Local factors of the Euler product -/

private theorem summable_linear_mul_pow' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {a : ℕ → ℝ}
    (ha : ∀ e, |a e| ≤ e + 1) : Summable fun e => a e * x ^ e := by
  have hn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h2 := summable_geometric_of_lt_one hx0 hx1
  refine Summable.of_norm_bounded (h1.add h2) (fun e => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 e), pow_one]
  calc |a e| * x ^ e ≤ ((e : ℝ) + 1) * x ^ e :=
        mul_le_mul_of_nonneg_right (ha e) (pow_nonneg hx0 e)
    _ = (e : ℝ) * x ^ e + x ^ e := by ring

private theorem summable_bounded_mul_pow' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {a : ℕ → ℝ}
    (ha : ∀ e, |a e| ≤ 1) : Summable fun e => a e * x ^ e :=
  summable_linear_mul_pow' hx0 hx1 (fun e => (ha e).trans (by linarith [(Nat.cast_nonneg e : (0 : ℝ) ≤ e)]))

/-- Head-plus-geometric-tail bound for bounded coefficients. -/
private theorem tsum_le_head_add_geom {c : ℕ → ℝ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hc : ∀ e, |c e| ≤ 1) (E : ℕ) :
    ∑' e : ℕ, c e * x ^ e ≤ ∑ e ∈ range E, c e * x ^ e + x ^ E / (1 - x) := by
  have hs := summable_bounded_mul_pow' hx0 hx1 hc
  have hgeom : Summable fun i : ℕ => x ^ (i + E) := by
    simp_rw [pow_add]
    exact (summable_geometric_of_lt_one hx0 hx1).mul_right _
  rw [← hs.sum_add_tsum_nat_add E]
  have htail : ∑' i : ℕ, c (i + E) * x ^ (i + E) ≤ ∑' i : ℕ, x ^ (i + E) := by
    refine ((summable_nat_add_iff E).2 hs).tsum_le_tsum (fun i => ?_) hgeom
    have := hc (i + E)
    rw [abs_le] at this
    nlinarith [pow_nonneg hx0 (i + E)]
  have hval : ∑' i : ℕ, x ^ (i + E) = x ^ E / (1 - x) := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hx0 hx1]
    ring
  linarith

/-- The kernel's local factor is `(1 - x) ∑ g(e) x^e`. -/
private theorem tsum_kernel_eq {g : ℕ → ℝ} (hg : ∀ e, |g e| ≤ e + 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    ∑' e : ℕ, (g e - if e = 0 then 0 else g (e - 1)) * x ^ e =
      (1 - x) * ∑' e : ℕ, g e * x ^ e := by
  have hs := summable_linear_mul_pow' hx0 hx1 hg
  have hs2 : Summable fun e : ℕ => (if e = 0 then 0 else g (e - 1)) * x ^ e := by
    refine summable_linear_mul_pow' hx0 hx1 (fun e => ?_)
    split_ifs with h
    · rw [abs_zero]
      positivity
    · have := hg (e - 1)
      have he : ((e - 1 : ℕ) : ℝ) ≤ e := by exact_mod_cast Nat.sub_le e 1
      linarith
  simp_rw [sub_mul]
  rw [hs.tsum_sub hs2, hs2.tsum_eq_zero_add]
  simp only [ite_true, zero_mul, zero_add, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
  have : ∑' e : ℕ, g e * x ^ (e + 1) = x * ∑' e : ℕ, g e * x ^ e := by
    rw [← tsum_mul_left]
    congr 1
    ext e
    ring
  rw [this]
  ring

private theorem prime_inv_bounds' {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine ⟨by positivity, ?_⟩
  rw [one_div]
  exact inv_anti₀ (by norm_num) h2

theorem ePlusKernel_div_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ePlusKernel (p ^ e) / ((p ^ e : ℕ) : ℝ) = ePlusKernelLocal p e * ((p : ℝ)⁻¹) ^ e := by
  rw [ePlusKernel_prime_pow hp, Nat.cast_pow, inv_pow, div_eq_mul_inv]

theorem abs_ePlusKernel_div_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    |ePlusKernel (p ^ e)| / ((p ^ e : ℕ) : ℝ) = |ePlusKernelLocal p e| * ((p : ℝ)⁻¹) ^ e := by
  rw [ePlusKernel_prime_pow hp, Nat.cast_pow, inv_pow, div_eq_mul_inv]

/-- The local factor `L(p) = ∑_e h₀(p^e) p^{-e}`. -/
noncomputable def ePlusLocalFactor (p : ℕ) : ℝ :=
  ∑' e : ℕ, ePlusKernelLocal p e * ((p : ℝ)⁻¹) ^ e

theorem ePlusLocalFactor_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ ePlusLocalFactor p := by
  obtain ⟨hx0, hxh⟩ := prime_inv_bounds' hp
  unfold ePlusLocalFactor ePlusKernelLocal
  rw [tsum_kernel_eq (abs_ePlusLocal_le p) hx0 (by linarith)]
  exact mul_nonneg (by linarith) (tsum_nonneg (fun e => mul_nonneg (ePlusLocal_nonneg p e)
    (pow_nonneg hx0 e)))

theorem ePlusLocalFactor_le_head {p : ℕ} (hp : p.Prime) (E : ℕ) :
    ePlusLocalFactor p ≤ ∑ e ∈ range E, ePlusKernelLocal p e * ((p : ℝ)⁻¹) ^ e +
      ((p : ℝ)⁻¹) ^ E / (1 - (p : ℝ)⁻¹) := by
  obtain ⟨hx0, hxh⟩ := prime_inv_bounds' hp
  exact tsum_le_head_add_geom hx0 (by linarith) (abs_ePlusKernelLocal_le p) E

private theorem local_abs_ePlusKernel_le {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, |ePlusKernelLocal p e| * ((p : ℝ)⁻¹) ^ e ≤ 1 + 4 * ((p : ℝ)⁻¹) ^ 2 := by
  obtain ⟨hx0, hxh⟩ := prime_inv_bounds' hp
  have h := tsum_le_head_add_geom (c := fun e => |ePlusKernelLocal p e|) hx0 (by linarith)
    (fun e => by rw [abs_abs]; exact abs_ePlusKernelLocal_le p e) 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, mul_one, pow_one,
    ePlusKernelLocal_zero, abs_one] at h
  have hgeom : ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) ≤ 2 * ((p : ℝ)⁻¹) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  by_cases h2 : p = 2
  · subst h2
    rw [ePlusKernelLocal_two_one] at h
    norm_num at h ⊢
    linarith
  · rw [ePlusKernelLocal_one_of_ne_two h2, abs_zero, zero_mul, add_zero] at h
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]

private theorem prod_one_add_mul_le' {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) : (∏ i ∈ s, (1 + a i)) * (1 - ∑ i ∈ s, a i) ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj]
    have haj : 0 ≤ a j := ha j (mem_insert_self j s)
    have ih' := ih (fun i hi => ha i (mem_insert_of_mem hi))
    have hP : 1 ≤ ∏ i ∈ s, (1 + a i) :=
      Finset.one_le_prod₀ (fun i hi => by linarith [ha i (mem_insert_of_mem hi)])
    have hQ : 1 ≤ (1 + a j) * ∏ i ∈ s, (1 + a i) := by nlinarith
    have hfin := mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 + a j)
    nlinarith [mul_nonneg haj (sub_nonneg.2 hQ)]

/-- **Summability hypothesis of L13 for `G₀`:** `∑ |h₀(n)|/n < ∞`. -/
theorem summable_abs_ePlusKernel_div : Summable fun n : ℕ => |ePlusKernel n| / n := by
  set f : ℕ → ℝ := fun n => |ePlusKernel n| / n with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf00 : f 0 = 0 := by simp [hfdef]
  have hf1 : f 1 = 1 := by simp [hfdef, ePlusKernel_isMultiplicative.map_one]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hfdef, ePlusKernel_isMultiplicative.map_mul_of_coprime hmn, abs_mul,
      Nat.cast_mul]
    rw [mul_div_mul_comm]
  have hloc : ∀ {p : ℕ}, p.Prime → Summable fun e : ℕ => ‖f (p ^ e)‖ := by
    intro p hp
    obtain ⟨hx0, hxh⟩ := prime_inv_bounds' hp
    refine (summable_bounded_mul_pow' hx0 (by linarith)
      (a := fun e => |ePlusKernelLocal p e|)
      (fun e => by rw [abs_abs]; exact abs_ePlusKernelLocal_le p e)).congr (fun e => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _), hfdef]
    exact (abs_ePlusKernel_div_prime_pow hp e).symm
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  refine summable_of_sum_range_le hf0 (c := Real.exp (4 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2))
    (fun N => ?_)
  obtain ⟨hsm, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf1 hmul hloc N
  have hsub : Summable fun m : N.smoothNumbers => f m :=
    hsm.congr (fun m => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)])
  have hsi : Summable (N.smoothNumbers.indicator f) := summable_subtype_iff_indicator.1 hsub
  have h1 : ∑ n ∈ range N, f n ≤ ∑' m : N.smoothNumbers, f m := by
    rw [_root_.tsum_subtype (N.smoothNumbers) f]
    refine le_trans (le_of_eq ?_)
      (hsi.sum_le_tsum (range N) (fun i _ => by
        simp only [Set.indicator_apply]
        split_ifs
        · exact hf0 i
        · exact le_rfl))
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [Set.indicator_apply, hf00]
    · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hn0 (mem_range.mp hn))]
  have h2 : ∏ p ∈ N.primesBelow, ∑' e : ℕ, f (p ^ e) ≤
      ∏ p ∈ N.primesBelow, (1 + 4 * ((p : ℝ)⁻¹) ^ 2) := by
    refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg (fun e => hf0 _)) (fun p hp => ?_)
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have heq : ∑' e : ℕ, f (p ^ e) = ∑' e : ℕ, |ePlusKernelLocal p e| * ((p : ℝ)⁻¹) ^ e :=
      tsum_congr (fun e => abs_ePlusKernel_div_prime_pow hpp e)
    rw [heq]
    exact local_abs_ePlusKernel_le hpp
  have h3 : ∏ p ∈ N.primesBelow, (1 + 4 * ((p : ℝ)⁻¹) ^ 2) ≤
      Real.exp (∑ p ∈ N.primesBelow, 4 * ((p : ℝ)⁻¹) ^ 2) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
    linarith [Real.add_one_le_exp (4 * ((p : ℝ)⁻¹) ^ 2)]
  have h4 : ∑ p ∈ N.primesBelow, 4 * ((p : ℝ)⁻¹) ^ 2 ≤ 4 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc ∑ p ∈ N.primesBelow, ((p : ℝ)⁻¹) ^ 2 = ∑ p ∈ N.primesBelow, 1 / (p : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun p _ => by rw [inv_pow, one_div])
      _ ≤ ∑ n ∈ range N, 1 / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun p hp => mem_range.mpr (Nat.mem_primesBelow.mp hp).1)
            (fun n _ _ => by positivity)
      _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
          hsq.sum_le_tsum (range N) (fun n _ => by positivity)
  calc ∑ n ∈ range N, f n ≤ ∑' m : N.smoothNumbers, f m := h1
    _ = ∏ p ∈ N.primesBelow, ∑' e : ℕ, f (p ^ e) := hhas.tsum_eq
    _ ≤ ∏ p ∈ N.primesBelow, (1 + 4 * ((p : ℝ)⁻¹) ^ 2) := h2
    _ ≤ Real.exp (∑ p ∈ N.primesBelow, 4 * ((p : ℝ)⁻¹) ^ 2) := h3
    _ ≤ Real.exp (4 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := Real.exp_le_exp.mpr h4

/-- `(1/X) ∑_{n ≤ X} G₀(n) → W_+^{maj}`. -/
theorem tendsto_average_ePlusMajorant :
    Tendsto (fun X : ℕ => (∑ n ∈ Icc 1 X, ePlusMajorant n) / (X : ℝ)) atTop (𝓝 ePlusMean) := by
  have := tendsto_average_of_summable_conv_mobius ePlusMajorant (by
    rw [ePlusMajorant_mul_moebius]
    exact summable_abs_ePlusKernel_div)
  rwa [ePlusMajorant_mul_moebius] at this

theorem ePlusMean_nonneg : 0 ≤ ePlusMean := by
  refine ge_of_tendsto tendsto_average_ePlusMajorant (Eventually.of_forall (fun X => ?_))
  exact div_nonneg (sum_nonneg (fun n _ => ePlusMajorant_nonneg n)) (Nat.cast_nonneg X)

/-! #### The explicit Euler-product certificate `W_+^{maj} ≤ 93694/100000` -/

/-- `U₁₅(x) = 1 + x² - x³ + x⁴ - x⁷ + x⁸ + x¹⁰ - x¹¹ + x¹² - x¹³ + x¹⁵/(1 - x)`. -/
noncomputable def nafKernelUpper15 (x : ℝ) : ℝ :=
  1 + x ^ 2 - x ^ 3 + x ^ 4 - x ^ 7 + x ^ 8 + x ^ 10 - x ^ 11 + x ^ 12 - x ^ 13 +
    x ^ 15 / (1 - x)

/-- `U₅(x) = 1 + x² - x³ + x⁴ + x⁵/(1 - x)`. -/
noncomputable def nafKernelUpper5 (x : ℝ) : ℝ := 1 + x ^ 2 - x ^ 3 + x ^ 4 + x ^ 5 / (1 - x)

/-- The certified per-prime upper bounds. -/
noncomputable def ePlusUpper (p : ℕ) : ℝ :=
  if p = 2 then 1 / 2 + nafKernelUpper15 (1 / 2) / 4
  else if p ≤ 19 then nafKernelUpper15 ((p : ℝ)⁻¹) else nafKernelUpper5 ((p : ℝ)⁻¹)

theorem ePlusLocalFactor_two_le : ePlusLocalFactor 2 ≤ ePlusUpper 2 := by
  have h := ePlusLocalFactor_le_head Nat.prime_two 17
  refine h.trans (le_of_eq ?_)
  simp only [ePlusUpper, ite_true, nafKernelUpper15, sum_range_succ, sum_range_zero,
    ePlusKernelLocal, ePlusLocal]
  norm_num [signedWeight]

theorem ePlusLocalFactor_le_upper15 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ePlusLocalFactor p ≤ nafKernelUpper15 ((p : ℝ)⁻¹) := by
  have h := ePlusLocalFactor_le_head hp 15
  refine h.trans (le_of_eq ?_)
  simp only [nafKernelUpper15, sum_range_succ, sum_range_zero, ePlusKernelLocal_of_ne_two h2]
  norm_num [signedWeight]
  ring

theorem ePlusLocalFactor_le_upper5 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ePlusLocalFactor p ≤ nafKernelUpper5 ((p : ℝ)⁻¹) := by
  have h := ePlusLocalFactor_le_head hp 5
  refine h.trans (le_of_eq ?_)
  simp only [nafKernelUpper5, sum_range_succ, sum_range_zero, ePlusKernelLocal_of_ne_two h2]
  norm_num [signedWeight]
  ring

theorem nafKernelUpper5_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    nafKernelUpper5 x ≤ 1 + x ^ 2 := by
  unfold nafKernelUpper5
  have h1 : 0 < 1 - x := by linarith
  have h2 : x ^ 5 / (1 - x) ≤ 2 * x ^ 5 := by
    rw [div_le_iff₀ h1]
    nlinarith [pow_nonneg hx0 5]
  have h3 : x ^ 4 + 2 * x ^ 5 ≤ x ^ 3 := by
    have : x ^ 4 + 2 * x ^ 5 = x ^ 3 * (x + 2 * x ^ 2) := by ring
    rw [this]
    have : x + 2 * x ^ 2 ≤ 1 := by nlinarith
    nlinarith [pow_nonneg hx0 3]
  linarith

theorem ePlusLocalFactor_le_upper {p : ℕ} (hp : p.Prime) : ePlusLocalFactor p ≤ ePlusUpper p := by
  unfold ePlusUpper
  split_ifs with h2 h19
  · subst h2
    exact ePlusLocalFactor_two_le
  · exact ePlusLocalFactor_le_upper15 hp h2
  · exact ePlusLocalFactor_le_upper5 hp h2

theorem ePlusLocalFactor_le_one_add_sq {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ePlusLocalFactor p ≤ 1 + ((p : ℝ)⁻¹) ^ 2 := by
  obtain ⟨hx0, hxh⟩ := prime_inv_bounds' hp
  exact (ePlusLocalFactor_le_upper5 hp h2).trans (nafKernelUpper5_le hx0 hxh)

set_option maxRecDepth 100000 in
private theorem primesBelow_361 : Nat.primesBelow 361 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
    31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127,
    131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
    229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331,
    337, 347, 349, 353, 359} := by
  decide

set_option maxHeartbeats 4000000 in
/-- **Finite certificate:** `(∏_{p < 361} U(p)) · 1074/1073 ≤ 93694/100000` (exact rationals). -/
theorem prod_ePlusUpper_le :
    (∏ p ∈ Nat.primesBelow 361, ePlusUpper p) * (1074 / 1073) ≤ 93694 / 100000 := by
  rw [primesBelow_361]
  simp only [ePlusUpper, nafKernelUpper15, nafKernelUpper5]
  norm_num

private theorem prime_mod_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  omega

private theorem sum_Ico_mod_six_le {M : ℕ} (hM : 1 ≤ M) (M' : ℕ) :
    ∑ m ∈ Ico M M', ((((6 * m + 1 : ℕ) : ℝ))⁻¹ ^ 2 + (((6 * m + 5 : ℕ) : ℝ))⁻¹ ^ 2) ≤
      1 / (18 * (M : ℝ) - 6) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  suffices H : ∀ M', M ≤ M' →
      ∑ m ∈ Ico M M', ((((6 * m + 1 : ℕ) : ℝ))⁻¹ ^ 2 + (((6 * m + 5 : ℕ) : ℝ))⁻¹ ^ 2) +
        1 / (18 * (M' : ℝ) - 6) ≤ 1 / (18 * (M : ℝ) - 6) by
    rcases le_or_gt M' M with h | h
    · rw [Ico_eq_empty_of_le h, sum_empty]
      exact div_nonneg zero_le_one (by linarith)
    · have h1 := H M' h.le
      have hM'' : (1 : ℝ) ≤ M' := by exact_mod_cast (hM.trans h.le)
      have : 0 ≤ 1 / (18 * (M' : ℝ) - 6) := div_nonneg zero_le_one (by linarith)
      linarith
  intro M' hMM'
  induction M', hMM' using Nat.le_induction with
  | base => simp
  | succ m hMm ih =>
    rw [sum_Ico_succ_top hMm]
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast (hM.trans hMm)
    have key : (((6 * m + 1 : ℕ) : ℝ))⁻¹ ^ 2 + (((6 * m + 5 : ℕ) : ℝ))⁻¹ ^ 2 +
        1 / (18 * ((m + 1 : ℕ) : ℝ) - 6) ≤ 1 / (18 * (m : ℝ) - 6) := by
      push_cast
      have h1 : ((6 * (m : ℝ) + 5))⁻¹ ^ 2 ≤ ((6 * (m : ℝ) + 1))⁻¹ ^ 2 := by
        gcongr
        linarith
      have h2 : 2 * ((6 * (m : ℝ) + 1))⁻¹ ^ 2 + 1 / (18 * ((m : ℝ) + 1) - 6) ≤
          1 / (18 * (m : ℝ) - 6) := by
        have ha : (0 : ℝ) < 6 * m + 1 := by linarith
        have hb : (0 : ℝ) < 18 * ((m : ℝ) + 1) - 6 := by linarith
        have hc : (0 : ℝ) < 18 * (m : ℝ) - 6 := by linarith
        rw [inv_pow, ← div_eq_mul_inv, div_add_div _ _ (by positivity) hb.ne',
          div_le_div_iff₀ (by positivity) hc]
        nlinarith
      linarith
    linarith

/-- **Elementary prime tail:** for primes `p ≥ 6M + 1`, `∑ p^{-2} ≤ 1/(18M - 6)`. -/
private theorem sum_inv_sq_primes_tail_le (S : Finset ℕ) {M : ℕ} (hM : 1 ≤ M)
    (hS : ∀ p ∈ S, p.Prime ∧ 6 * M + 1 ≤ p) :
    ∑ p ∈ S, ((p : ℝ)⁻¹) ^ 2 ≤ 1 / (18 * (M : ℝ) - 6) := by
  obtain ⟨M', hM'⟩ : ∃ M', ∀ p ∈ S, p < 6 * M' :=
    ⟨S.sup id + 1, fun p hp => by
      have := Finset.le_sup (f := id) hp
      simp only [id] at this
      omega⟩
  set I : Finset (ℕ × ℕ) := Ico M M' ×ˢ ({1, 5} : Finset ℕ) with hIdef
  set φ : ℕ × ℕ → ℕ := fun q => 6 * q.1 + q.2 with hφdef
  have hsub : S ⊆ I.image φ := by
    intro p hp
    obtain ⟨hpp, h1⟩ := hS p hp
    have h3 := hM' p hp
    have h6 := prime_mod_six hpp (by omega)
    rw [mem_image]
    refine ⟨(p / 6, p % 6), ?_, by simp only [hφdef]; omega⟩
    simp only [hIdef, mem_product, mem_Ico, mem_insert, mem_singleton]
    omega
  have hinj : Set.InjOn φ I := by
    rintro ⟨a, b⟩ ha ⟨c, d⟩ hc h
    simp only [hIdef, coe_product, Set.mem_prod, mem_coe, mem_Ico, mem_insert,
      mem_singleton] at ha hc
    simp only [hφdef, Prod.mk.injEq] at h ⊢
    omega
  calc ∑ p ∈ S, ((p : ℝ)⁻¹) ^ 2
      ≤ ∑ p ∈ I.image φ, ((p : ℝ)⁻¹) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ q ∈ I, ((φ q : ℝ)⁻¹) ^ 2 := sum_image hinj
    _ = ∑ m ∈ Ico M M', ((((6 * m + 1 : ℕ) : ℝ))⁻¹ ^ 2 + (((6 * m + 5 : ℕ) : ℝ))⁻¹ ^ 2) := by
        rw [hIdef, sum_product]
        refine sum_congr rfl (fun m _ => ?_)
        rw [sum_pair (by norm_num)]
    _ ≤ 1 / (18 * (M : ℝ) - 6) := sum_Ico_mod_six_le hM M'

/-- **Theorem B.2(1), Euler-product certificate:** `W_+^{maj} = ∑ h₀(n)/n ≤ 93694/100000`. -/
theorem ePlusMean_le : ePlusMean ≤ 93694 / 100000 := by
  unfold ePlusMean
  set f : ℕ → ℝ := fun n => ePlusKernel n / n with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hf1 : f 1 = 1 := by simp [hfdef, ePlusKernel_isMultiplicative.map_one]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hfdef, ePlusKernel_isMultiplicative.map_mul_of_coprime hmn, Nat.cast_mul]
    rw [mul_div_mul_comm]
  have hsum : Summable fun n : ℕ => ‖f n‖ := by
    refine summable_abs_ePlusKernel_div.congr (fun n => ?_)
    simp only [hfdef, Real.norm_eq_abs, abs_div, Nat.abs_cast]
  have hE := EulerProduct.eulerProduct hf1 hmul hsum hf0
  refine le_of_tendsto hE ?_
  filter_upwards [eventually_ge_atTop 361] with P hP
  have hloc : ∀ p, p.Prime → ∑' e : ℕ, f (p ^ e) = ePlusLocalFactor p := fun p hp =>
    tsum_congr (fun e => ePlusKernel_div_prime_pow hp e)
  have hT : Nat.primesBelow 361 ⊆ P.primesBelow := fun p hp => by
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  rw [← prod_sdiff hT]
  have hA : ∏ p ∈ Nat.primesBelow 361, ∑' e : ℕ, f (p ^ e) ≤
      ∏ p ∈ Nat.primesBelow 361, ePlusUpper p := by
    refine prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have hpp := (Nat.mem_primesBelow.mp hp).2
      rw [hloc p hpp]
      exact ePlusLocalFactor_nonneg hpp
    · have hpp := (Nat.mem_primesBelow.mp hp).2
      rw [hloc p hpp]
      exact ePlusLocalFactor_le_upper hpp
  have hmemT : ∀ p ∈ P.primesBelow \ Nat.primesBelow 361, p.Prime ∧ 361 ≤ p := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_sdiff.mp hp
    have hpp := (Nat.mem_primesBelow.mp h1).2
    refine ⟨hpp, ?_⟩
    by_contra hlt
    exact h2 (Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩)
  have hB : ∏ p ∈ P.primesBelow \ Nat.primesBelow 361, ∑' e : ℕ, f (p ^ e) ≤
      ∏ p ∈ P.primesBelow \ Nat.primesBelow 361, (1 + ((p : ℝ)⁻¹) ^ 2) := by
    refine prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨hpp, _⟩ := hmemT p hp
      rw [hloc p hpp]
      exact ePlusLocalFactor_nonneg hpp
    · obtain ⟨hpp, h361⟩ := hmemT p hp
      rw [hloc p hpp]
      exact ePlusLocalFactor_le_one_add_sq hpp (by omega)
  have hsumT : ∑ p ∈ P.primesBelow \ Nat.primesBelow 361, ((p : ℝ)⁻¹) ^ 2 ≤ 1 / 1074 := by
    have := sum_inv_sq_primes_tail_le (P.primesBelow \ Nat.primesBelow 361) (M := 60)
      (by norm_num) (fun p hp => ⟨(hmemT p hp).1, by have := (hmemT p hp).2; omega⟩)
    norm_num at this ⊢
    linarith
  have hC : ∏ p ∈ P.primesBelow \ Nat.primesBelow 361, (1 + ((p : ℝ)⁻¹) ^ 2) ≤ 1074 / 1073 := by
    have h := prod_one_add_mul_le' (P.primesBelow \ Nat.primesBelow 361)
      (fun p => ((p : ℝ)⁻¹) ^ 2) (fun p _ => by positivity)
    have hP0 : 0 ≤ ∏ p ∈ P.primesBelow \ Nat.primesBelow 361, (1 + ((p : ℝ)⁻¹) ^ 2) :=
      Finset.prod_nonneg (fun p _ => by positivity)
    have h' : (∏ p ∈ P.primesBelow \ Nat.primesBelow 361, (1 + ((p : ℝ)⁻¹) ^ 2)) *
        (1073 / 1074) ≤ 1 := by
      calc (∏ p ∈ P.primesBelow \ Nat.primesBelow 361, (1 + ((p : ℝ)⁻¹) ^ 2)) * (1073 / 1074)
          ≤ (∏ p ∈ P.primesBelow \ Nat.primesBelow 361, (1 + ((p : ℝ)⁻¹) ^ 2)) *
              (1 - ∑ p ∈ P.primesBelow \ Nat.primesBelow 361, ((p : ℝ)⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hP0
        _ ≤ 1 := h
    linarith
  have hD := prod_ePlusUpper_le
  have hA0 : 0 ≤ ∏ p ∈ Nat.primesBelow 361, ∑' e : ℕ, f (p ^ e) :=
    prod_nonneg (fun p hp => by
      have hpp := (Nat.mem_primesBelow.mp hp).2
      rw [hloc p hpp]
      exact ePlusLocalFactor_nonneg hpp)
  have hU0 : 0 ≤ ∏ p ∈ Nat.primesBelow 361, ePlusUpper p := hA0.trans hA
  calc (∏ p ∈ P.primesBelow \ Nat.primesBelow 361, ∑' e : ℕ, f (p ^ e)) *
        ∏ p ∈ Nat.primesBelow 361, ∑' e : ℕ, f (p ^ e)
      ≤ (1074 / 1073) * ∏ p ∈ Nat.primesBelow 361, ePlusUpper p :=
        mul_le_mul (hB.trans hC) hA hA0 (by norm_num)
    _ ≤ 93694 / 100000 := by linarith

/-! ### Part 7: headline theorems for `E_+(2^k)`, `k ≥ 3` (including `E_+(8)`) -/

/-- `E_+(2^k)` has upper prefix NAF density at most `W_+^{maj}/k`. -/
theorem erdosBorweinPlusPow_nafDensityLE {k : ℕ} (hk : 1 ≤ k) :
    NafDensityLE (erdosBorweinPlusPow k) (ePlusMean / k) := by
  rw [erdosBorweinPlusPow_eq_signed_series hk]
  refine nafDensityLE_of_series hk aPlus (C₀ := 1) (B := 1) (fun n _ => ?_) ePlusMean_nonneg
    (fun C' hC' => ?_)
  · rw [one_mul, pow_one]
    exact abs_aPlus_le n
  · filter_upwards [tendsto_average_ePlusMajorant.eventually (gt_mem_nhds hC'),
      eventually_ge_atTop 1] with X hX hX1
    have hXr : (0 : ℝ) < X := by exact_mod_cast hX1
    have h1 : ∑ n ∈ Icc 1 X, (signedWeight (aPlus n).natAbs : ℝ) ≤
        ∑ n ∈ Icc 1 X, ePlusMajorant n := sum_le_sum (fun n _ => signedWeight_aPlus_le n)
    have h2 : ∑ n ∈ Icc 1 X, ePlusMajorant n < C' * X := by rwa [div_lt_iff₀ hXr] at hX
    linarith

private theorem ePlusDensity_le (k : ℕ) :
    ePlusMean / k ≤ 93694 / 100000 / k :=
  div_le_div_of_nonneg_right ePlusMean_le (Nat.cast_nonneg k)

private theorem ePlusDensity_le_three {k : ℕ} (hk : 3 ≤ k) :
    ePlusMean / k ≤ 93694 / 300000 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  calc ePlusMean / k ≤ ePlusMean / 3 :=
        div_le_div_of_nonneg_left ePlusMean_nonneg (by norm_num) hk'
    _ ≤ 93694 / 100000 / 3 := div_le_div_of_nonneg_right ePlusMean_le (by norm_num)
    _ = 93694 / 300000 := by norm_num

/-- **Theorem B.1, base `2`:** for every `k ≥ 1` and `ε > 0`, eventually
`D_N(E_+(2^k); 2) ≥ 2/3 - 2 · (937/1000)/k - ε`. -/
theorem erdosBorweinPlus_two_pow_radixDiscrepancy_eventually_ge (k : ℕ) (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, 2 / 3 - 2 * (937 / 1000) / k - ε ≤
      radixDiscrepancy 2 (erdosBorweinPlusPow k) N := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  filter_upwards [binary_radixDiscrepancy_eventually_ge_two_thirds
    (erdosBorweinPlusPow_nafDensityLE hk) hε] with N hN
  have h1 := ePlusDensity_le k
  have h2 : 2 * (ePlusMean / k) ≤ 2 * (937 / 1000) / k := by
    rw [mul_div_assoc]
    have : (93694 / 100000 : ℝ) / k ≤ 937 / 1000 / k :=
      div_le_div_of_nonneg_right (by norm_num) hkr.le
    linarith
  linarith

/-- **Theorem B.1, base `4`:** for every `k ≥ 1` and `ε > 0`, eventually
`D_N(E_+(2^k); 4) ≥ 2/3 - 2 · (937/1000)/k - ε`. -/
theorem erdosBorweinPlus_two_pow_radixDiscrepancy_base4_eventually_ge (k : ℕ) (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, 2 / 3 - 2 * (937 / 1000) / k - ε ≤
      radixDiscrepancy 4 (erdosBorweinPlusPow k) N := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  filter_upwards [base4_radixDiscrepancy_eventually_ge_two_thirds
    (erdosBorweinPlusPow_nafDensityLE hk) hε] with N hN
  have h1 := ePlusDensity_le k
  have h2 : 2 * (ePlusMean / k) ≤ 2 * (937 / 1000) / k := by
    rw [mul_div_assoc]
    have : (93694 / 100000 : ℝ) / k ≤ 937 / 1000 / k :=
      div_le_div_of_nonneg_right (by norm_num) hkr.le
    linarith
  linarith

/-- **Theorem B.1(1):** for every `k ≥ 3`, `D_N(E_+(2^k); 2) ≥ 21/500` for all large `N`. -/
theorem erdosBorweinPlus_two_pow_lowerDiscrepancy_ge (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ N in atTop, (21 : ℝ) / 500 ≤ radixDiscrepancy 2 (erdosBorweinPlusPow k) N := by
  filter_upwards [binary_radixDiscrepancy_eventually_ge_two_thirds
    (erdosBorweinPlusPow_nafDensityLE (by omega : 1 ≤ k)) (ε := 1 / 50000) (by norm_num)]
    with N hN
  have := ePlusDensity_le_three hk
  linarith

/-- **Theorem B.1(1):** for every `k ≥ 3`, `E_+(2^k)` has positive lower discrepancy in base `2`:
`∃ c > 0` (explicitly `c = 21/500`) with `c ≤ D_N(E_+(2^k); 2)` for all large `N`. -/
theorem erdosBorweinPlus_two_pow_lowerDiscrepancy_pos (k : ℕ) (hk : 3 ≤ k) :
    ∃ c > 0, ∀ᶠ N in atTop, c ≤ radixDiscrepancy 2 (erdosBorweinPlusPow k) N :=
  ⟨21 / 500, by norm_num, erdosBorweinPlus_two_pow_lowerDiscrepancy_ge k hk⟩

/-- **Theorem B.1(1), base `4`:** for every `k ≥ 3`, `D_N(E_+(2^k); 4) ≥ 21/500` eventually. -/
theorem erdosBorweinPlus_two_pow_lowerDiscrepancy_base4_ge (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ N in atTop, (21 : ℝ) / 500 ≤ radixDiscrepancy 4 (erdosBorweinPlusPow k) N := by
  filter_upwards [base4_radixDiscrepancy_eventually_ge_two_thirds
    (erdosBorweinPlusPow_nafDensityLE (by omega : 1 ≤ k)) (ε := 1 / 50000) (by norm_num)]
    with N hN
  have := ePlusDensity_le_three hk
  linarith

/-- **Theorem B.1(2):** for every `k ≥ 3` (in particular `E_+(8)`), `E_+(2^k)` is **not**
`4`-normal in base `2`. -/
theorem erdosBorweinPlus_two_pow_not_orderNormal_four (k : ℕ) (hk : 3 ≤ k) :
    ¬ OrderNormal 2 4 (erdosBorweinPlusPow k) :=
  not_orderNormal_two_four_of_nafDensity (erdosBorweinPlusPow_nafDensityLE (by omega))
    (by have := ePlusDensity_le_three hk; linarith)

/-- **Theorem B.1(2):** for every `k ≥ 3` (in particular `E_+(8)`), `E_+(2^k)` is **not**
`2`-normal in base `4`. -/
theorem erdosBorweinPlus_two_pow_not_orderNormal_base4_two (k : ℕ) (hk : 3 ≤ k) :
    ¬ OrderNormal 4 2 (erdosBorweinPlusPow k) :=
  not_orderNormal_four_two_of_nafDensity (erdosBorweinPlusPow_nafDensityLE (by omega))
    (by have := ePlusDensity_le_three hk; linarith)

/-- For every `k ≥ 3`, `E_+(2^k)` is not normal in base `2`. -/
theorem erdosBorweinPlus_two_pow_not_normalIn_two (k : ℕ) (hk : 3 ≤ k) :
    ¬ NormalIn 2 (erdosBorweinPlusPow k) := fun h =>
  erdosBorweinPlus_two_pow_not_orderNormal_four k hk (orderNormal_of_normalIn h (by norm_num))

/-- For every `k ≥ 3`, `E_+(2^k)` is not normal in base `4`. -/
theorem erdosBorweinPlus_two_pow_not_normalIn_four (k : ℕ) (hk : 3 ≤ k) :
    ¬ NormalIn 4 (erdosBorweinPlusPow k) := fun h =>
  erdosBorweinPlus_two_pow_not_orderNormal_base4_two k hk (orderNormal_of_normalIn h (by norm_num))

/-- **`E_+(8)`:** not `4`-normal in base `2`. -/
theorem erdosBorweinPlus_eight_not_orderNormal_four : ¬ OrderNormal 2 4 (erdosBorweinPlusPow 3) :=
  erdosBorweinPlus_two_pow_not_orderNormal_four 3 le_rfl

/-- **`E_+(8)`:** not `2`-normal in base `4`. -/
theorem erdosBorweinPlus_eight_not_orderNormal_base4_two :
    ¬ OrderNormal 4 2 (erdosBorweinPlusPow 3) :=
  erdosBorweinPlus_two_pow_not_orderNormal_base4_two 3 le_rfl

end NormalityChecker.NafGeometricTransfer
