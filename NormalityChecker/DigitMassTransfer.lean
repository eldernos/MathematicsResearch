module

public import NormalityChecker.HigherOrderTower
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.PSeries

/-! # Phase 24 Track A: dense digit-mass transfer (Lean 4 Module 2)

Kernel-checked theorems for `notes/phase24/dense-digit-mass-and-lambert.md` (§13 blueprint
L1–L15, with the `List.filter (· != 0)` and `moebius`-coercion fixes of
`notes/phase24/reviews/track-a-review.md`, items m8–m9).

1. **Digit sums, nonzero digits and carries (L1–L4):**
   - `digitSum`, `nonzeroDigits`, `carries`; `digitSum_add_add_carries` (Kummer:
     `s_b(a + c) + (b - 1) κ_b(a, c) = s_b(a) + s_b(c)`).
   - `digitSum_add_le`, `digitSum_mul_le`, `digitSum_mul_pow`, `nonzeroDigits_add_le`,
     `nonzeroDigits_mul_le` (`w_b(ac) ≤ min(s_b(a) w_b(c), 2 w_b(a) w_b(c))`).
   - `nonzeroDigits_pred_sq` (`w_b((b - 1)²) = 2`, `w_b(b - 1) = 1` for `b ≥ 3`) and
     `digitSum_two_succ` (`s₂(m + 1) + v₂(m + 1) = s₂(m) + 1`).
2. **Signed weight and two's-complement transitions (L5–L6):**
   - `signedWeight` (NAF weight, defining recursion); `signedWeight_le_digitSum`,
     `signedWeight_two_mul`, `signedWeight_add_le`, `signedWeight_sub_le`, `signedWeight_mul_le`.
   - `transitions`; `transitions_rec`, `transitions_add_two_pow` (`|T(A ± 2^m) - T(A)| ≤ 2`),
     `transitions_add_le` (`T(A + c) ≤ T(A) + 2 w_±(|c|)`).
3. **Prefix decomposition and prefix mass (L7–L9):** `floor_pow_mul_eq_head_add_floor_tail`
   (exact `⌊b^N x⌋ = A_N + ⌊τ_N⌋`), `digitSum_prefix_le`, `transitions_prefix_le`.
4. **Discrepancy criteria (L10–L12):** `interval_le_radixDiscrepancy`,
   `radixDiscrepancy_ge_nonzero_freq`, `binaryDiscrepancy_ge_half_sub_transition`,
   `radixDiscrepancy_descent` (`D_{kN}(x; b) ≤ (b^k - 1)/(k(b - 1)) · D_N(x; b^k)`),
   `radixDiscrepancy_ge_zero_run`.
5. **Elementary analytic core (L13–L14):** `tendsto_average_of_summable_conv_mobius`
   (Lemma 3.1, by dominated convergence; no Tauberian input, no multiplicativity) and
   `local_factor_digitSum_two` (`(1 - p⁻¹) ∑ s₂(e + 1)/p^e = ∑_j p/(p^{2^j} + 1)`).
6. **Multiplicative majorant and its Euler product:** `multOfPrimePow`, `tauDigitMajorant`
   (`G(n) = ∏_{p^e ∥ n} s₂(e + 1)`), `tauDigitKernel` (`h = G * μ`), `digitSum_card_divisors_le`
   (`s₂(τ(n)) ≤ G(n)`), `tauDigitMajorant_mul_moebius`, `summable_abs_tauDigitKernel_div`, and
   `tsum_tauDigitKernel_div_le` (`C = ∑ h(n)/n ≤ 29/20`, from local bounds
   `L(p) ≤ (1 - p⁻²)⁻¹ - p⁻³ - 2p⁻⁷`, exact factors for `p < 37` and `∑_{n ≥ 37} n⁻² ≤ 1/36`).
7. **Unconditional headline (L15):** for `E(2^k) = ∑_{m ≥ 1} 1/(2^{km} - 1)`,
   - `erdosBorweinPow_eq_divisor_series` (`E(2^k) = ∑ τ(n) 2^{-kn}`);
   - `erdosBorwein_two_pow_digitFreq_limsup_le`: `limsup f₁(N; E(2^k), 2) ≤ 29/(20k)` (`k ≥ 1`);
   - `erdosBorwein_two_pow_radixDiscrepancy_eventually_ge`: `D_N ≥ 1/2 - 29/(20k) - ε`
     eventually;
   - `erdosBorwein_two_pow_lowerDiscrepancy_pos`: `D_N(E(2^k); 2) ≥ 1/120` eventually (`k ≥ 3`);
   - `erdosBorwein_two_pow_not_simplyNormal`, `erdosBorwein_two_pow_not_simplyNormal_pow`:
     for every `k ≥ 3` and `j ≥ 1`, `E(2^k)` is not simply normal in base `2^j`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.DigitMassTransfer

open HigherOrderTower SimpleNormalityKernel

/-! ### Part 1 (L1–L4): base-`b` digit sums, nonzero digits and carries -/

/-- Base-`b` digit sum `s_b(n)`. -/
def digitSum (b n : ℕ) : ℕ := (Nat.digits b n).sum

/-- Number of nonzero base-`b` digits `w_b(n)`. -/
def nonzeroDigits (b n : ℕ) : ℕ := ((Nat.digits b n).filter (· != 0)).length

@[simp] theorem digitSum_zero (b : ℕ) : digitSum b 0 = 0 := by simp [digitSum]

@[simp] theorem nonzeroDigits_zero (b : ℕ) : nonzeroDigits b 0 = 0 := by simp [nonzeroDigits]

/-- The defining digit recursion `s_b(n) = (n mod b) + s_b(⌊n / b⌋)`. -/
theorem digitSum_eq {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    digitSum b n = n % b + digitSum b (n / b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [digitSum, Nat.digits_def' (by omega) hn, List.sum_cons]; rfl

/-- The defining digit recursion `w_b(n) = [n mod b ≠ 0] + w_b(⌊n / b⌋)`. -/
theorem nonzeroDigits_eq {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    nonzeroDigits b n = (if n % b = 0 then 0 else 1) + nonzeroDigits b (n / b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [nonzeroDigits, Nat.digits_def' (by omega) hn, List.filter_cons]
    by_cases h : n % b = 0
    · simp [h, nonzeroDigits]
    · simp [h, nonzeroDigits, add_comm]

private theorem div_mod_of_mul_add {b q r : ℕ} (hb : 2 ≤ b) (hr : r < b) :
    (b * q + r) / b = q ∧ (b * q + r) % b = r :=
  (Nat.div_mod_unique (show 0 < b by omega)).2 ⟨by ring, hr⟩

theorem digitSum_mul_add {b : ℕ} (hb : 2 ≤ b) (q r : ℕ) (hr : r < b) :
    digitSum b (b * q + r) = r + digitSum b q := by
  obtain ⟨h1, h2⟩ := div_mod_of_mul_add (q := q) hb hr
  rw [digitSum_eq hb, h1, h2]

theorem nonzeroDigits_mul_add {b : ℕ} (hb : 2 ≤ b) (q r : ℕ) (hr : r < b) :
    nonzeroDigits b (b * q + r) = (if r = 0 then 0 else 1) + nonzeroDigits b q := by
  obtain ⟨h1, h2⟩ := div_mod_of_mul_add (q := q) hb hr
  rw [nonzeroDigits_eq hb, h1, h2]

theorem digitSum_mul_base {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : digitSum b (b * n) = digitSum b n := by
  simpa using digitSum_mul_add hb n 0 (by omega)

theorem nonzeroDigits_mul_base {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    nonzeroDigits b (b * n) = nonzeroDigits b n := by
  simpa using nonzeroDigits_mul_add hb n 0 (by omega)

theorem digitSum_of_lt {b n : ℕ} (hb : 2 ≤ b) (hn : n < b) : digitSum b n = n := by
  simpa using digitSum_mul_add hb 0 n hn

theorem digitSum_le_self {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : digitSum b n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hlt : n / b < n := Nat.div_lt_self hn (by omega)
    have h1 := ih _ hlt
    have h2 := Nat.div_add_mod n b
    have h3 : n / b ≤ b * (n / b) := Nat.le_mul_of_pos_left _ (by omega)
    rw [digitSum_eq hb]
    omega

private theorem div_add_div_lt {b a c : ℕ} (hb : 2 ≤ b) (h : 0 < a + c) :
    a / b + c / b < a + c := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.zero_div, zero_add] at h ⊢
    exact Nat.div_lt_self h (by omega)
  · have h1 := Nat.div_lt_self ha (show 1 < b by omega)
    have h2 := Nat.div_le_self c b
    omega

/-- Carries produced when adding `a` and `c` in base `b` with incoming carry `cin`
(once `a = c = 0` no further carry can occur, since `0 + 0 + 1 < b`). -/
def carries (b cin a c : ℕ) : ℕ :=
  if b ≤ 1 ∨ (a = 0 ∧ c = 0) then 0 else
    let o := if b ≤ a % b + c % b + cin then 1 else 0
    o + carries b o (a / b) (c / b)
termination_by a + c
decreasing_by
  exact div_add_div_lt (by omega) (by omega)

private theorem digitSum_add_add_carries_aux {b : ℕ} (hb : 2 ≤ b) :
    ∀ s a c cin, a + c = s → cin ≤ 1 →
      digitSum b (a + c + cin) + (b - 1) * carries b cin a c =
        digitSum b a + digitSum b c + cin := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro a c cin hs hcin
  rw [carries]
  by_cases hz : a = 0 ∧ c = 0
  · obtain ⟨rfl, rfl⟩ := hz
    rw [ite_eq_left (Or.inr ⟨rfl, rfl⟩)]
    simp [digitSum_of_lt hb (show cin < b by omega)]
  · rw [ite_eq_right (by omega)]
    have ha := Nat.div_add_mod a b
    have hc := Nat.div_add_mod c b
    have ha0 := Nat.mod_lt a (show b > 0 by omega)
    have hc0 := Nat.mod_lt c (show b > 0 by omega)
    have hlt : a / b + c / b < s := hs ▸ div_add_div_lt hb (by omega)
    have hda := digitSum_eq hb a
    have hdc := digitSum_eq hb c
    by_cases hcar : b ≤ a % b + c % b + cin
    · simp only [hcar, ↓reduceIte]
      have hsum : a + c + cin = b * (a / b + c / b + 1) + (a % b + c % b + cin - b) := by
        have : b * (a / b + c / b + 1) = b * (a / b) + b * (c / b) + b := by ring
        omega
      rw [hsum, digitSum_mul_add hb _ _ (by omega)]
      have := ih _ hlt (a / b) (c / b) 1 rfl le_rfl
      rw [mul_add, mul_one]
      generalize (b - 1) * carries b 1 (a / b) (c / b) = Y at this ⊢
      have hb1 : b - 1 + 1 = b := by omega
      omega
    · simp only [hcar, ↓reduceIte]
      have hsum : a + c + cin = b * (a / b + c / b) + (a % b + c % b + cin) := by
        have : b * (a / b + c / b) = b * (a / b) + b * (c / b) := by ring
        omega
      rw [hsum, digitSum_mul_add hb _ _ (by omega)]
      have := ih _ hlt (a / b) (c / b) 0 rfl (by omega)
      simp only [add_zero, zero_add] at this ⊢
      generalize (b - 1) * carries b 0 (a / b) (c / b) = Y at this ⊢
      omega

/-- **L1 (Kummer).** `s_b(a + c) + (b - 1) · κ_b(a, c) = s_b(a) + s_b(c)`, where `κ_b(a, c)`
is the number of carries in the base-`b` addition of `a` and `c`. -/
theorem digitSum_add_add_carries (b a c : ℕ) (hb : 2 ≤ b) :
    digitSum b (a + c) + (b - 1) * carries b 0 a c = digitSum b a + digitSum b c := by
  simpa using digitSum_add_add_carries_aux hb _ a c 0 rfl (Nat.zero_le 1)

/-- **L2.** Subadditivity of the digit sum. -/
theorem digitSum_add_le (b a c : ℕ) (hb : 2 ≤ b) :
    digitSum b (a + c) ≤ digitSum b a + digitSum b c := by
  have := digitSum_add_add_carries b a c hb
  omega

/-- **L2.** Shifting by a power of the radix preserves the digit sum. -/
theorem digitSum_mul_pow (b a t : ℕ) (hb : 2 ≤ b) : digitSum b (a * b ^ t) = digitSum b a := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← mul_assoc, mul_comm _ b, digitSum_mul_base hb, ih]

private theorem digitSum_mul_le_mul {b : ℕ} (hb : 2 ≤ b) (a d : ℕ) :
    digitSum b (a * d) ≤ d * digitSum b a := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [mul_add, mul_one, add_mul, one_mul]
    exact (digitSum_add_le b _ _ hb).trans (by omega)

/-- **L2.** Submultiplicativity of the digit sum. -/
theorem digitSum_mul_le (b a c : ℕ) (hb : 2 ≤ b) :
    digitSum b (a * c) ≤ digitSum b a * digitSum b c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · have hcdiv := Nat.div_add_mod c b
    have hlt : c / b < c := Nat.div_lt_self hc (by omega)
    have h1 : a * c = b * (a * (c / b)) + a * (c % b) := by
      conv_lhs => rw [← hcdiv]
      ring
    rw [h1, digitSum_eq hb c, mul_add]
    calc digitSum b (b * (a * (c / b)) + a * (c % b))
        ≤ digitSum b (b * (a * (c / b))) + digitSum b (a * (c % b)) := digitSum_add_le b _ _ hb
      _ = digitSum b (a * (c / b)) + digitSum b (a * (c % b)) := by rw [digitSum_mul_base hb]
      _ ≤ digitSum b a * digitSum b (c / b) + c % b * digitSum b a :=
          add_le_add (ih _ hlt) (digitSum_mul_le_mul hb a _)
      _ = digitSum b a * (c % b) + digitSum b a * digitSum b (c / b) := by ring

private theorem nonzeroDigits_succ_le {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    nonzeroDigits b (n + 1) ≤ nonzeroDigits b n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hn := Nat.div_add_mod n b
  have hr := Nat.mod_lt n (show b > 0 by omega)
  have hw := nonzeroDigits_eq hb n
  by_cases h : n % b + 1 < b
  · have e : n + 1 = b * (n / b) + (n % b + 1) := by omega
    rw [e, nonzeroDigits_mul_add hb _ _ h, hw]
    split_ifs <;> omega
  · have e : n + 1 = b * (n / b + 1) + 0 := by
      have : b * (n / b + 1) = b * (n / b) + b := by ring
      omega
    have hpos : 0 < n := by
      have := Nat.mod_le n b
      omega
    have hlt : n / b < n := Nat.div_lt_self hpos (by omega)
    rw [e, nonzeroDigits_mul_add hb _ _ (by omega), hw]
    have := ih _ hlt
    split_ifs <;> omega

/-- **L2.** Subadditivity of the number of nonzero digits. -/
theorem nonzeroDigits_add_le (b a c : ℕ) (hb : 2 ≤ b) :
    nonzeroDigits b (a + c) ≤ nonzeroDigits b a + nonzeroDigits b c := by
  suffices H : ∀ s a c, a + c = s →
      nonzeroDigits b (a + c) ≤ nonzeroDigits b a + nonzeroDigits b c from H _ a c rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro a c hs
  rcases Nat.eq_zero_or_pos (a + c) with h0 | hpos
  · have ha : a = 0 := by omega
    have hc : c = 0 := by omega
    subst ha hc
    simp
  · have ha := Nat.div_add_mod a b
    have hc := Nat.div_add_mod c b
    have ha0 := Nat.mod_lt a (show b > 0 by omega)
    have hc0 := Nat.mod_lt c (show b > 0 by omega)
    have hlt : a / b + c / b < s := hs ▸ div_add_div_lt hb hpos
    have hwa := nonzeroDigits_eq hb a
    have hwc := nonzeroDigits_eq hb c
    by_cases hcar : a % b + c % b < b
    · have e : a + c = b * (a / b + c / b) + (a % b + c % b) := by
        have : b * (a / b + c / b) = b * (a / b) + b * (c / b) := by ring
        omega
      rw [e, nonzeroDigits_mul_add hb _ _ hcar, hwa, hwc]
      have := ih _ hlt (a / b) (c / b) rfl
      split_ifs <;> omega
    · have e : a + c = b * (a / b + c / b + 1) + (a % b + c % b - b) := by
        have : b * (a / b + c / b + 1) = b * (a / b) + b * (c / b) + b := by ring
        omega
      rw [e, nonzeroDigits_mul_add hb _ _ (by omega), hwa, hwc]
      have h1 := ih _ hlt (a / b) (c / b) rfl
      have h2 := nonzeroDigits_succ_le hb (a / b + c / b)
      split_ifs <;> omega

private theorem nonzeroDigits_mul_le_mul {b : ℕ} (hb : 2 ≤ b) (c d : ℕ) :
    nonzeroDigits b (d * c) ≤ d * nonzeroDigits b c := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [add_mul, one_mul, add_mul, one_mul]
    exact (nonzeroDigits_add_le b _ _ hb).trans (by omega)

private theorem nonzeroDigits_mul_digit_le {b : ℕ} (hb : 2 ≤ b) (a d : ℕ) (hd : d < b) :
    nonzeroDigits b (a * d) ≤ 2 * nonzeroDigits b a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have hlt : a / b < a := Nat.div_lt_self ha (by omega)
    have hadiv := Nat.div_add_mod a b
    have ha0 := Nat.mod_lt a (show b > 0 by omega)
    obtain ⟨q, r, hqr, hq, hr, hz⟩ : ∃ q r, a % b * d = b * q + r ∧ q < b ∧ r < b ∧
        (a % b = 0 → q = 0 ∧ r = 0) := by
      refine ⟨a % b * d / b, a % b * d % b, (Nat.div_add_mod _ _).symm, ?_,
        Nat.mod_lt _ (by omega), ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (by omega)]
        nlinarith
      · intro h0
        simp [h0]
    have e : a * d = b * (a / b * d + q) + r := by
      calc a * d = (b * (a / b) + a % b) * d := by rw [hadiv]
        _ = b * (a / b * d) + a % b * d := by ring
        _ = b * (a / b * d) + (b * q + r) := by rw [hqr]
        _ = b * (a / b * d + q) + r := by ring
    have hwq : nonzeroDigits b q ≤ 1 := by
      have := nonzeroDigits_mul_add hb 0 q hq
      simp only [mul_zero, zero_add, nonzeroDigits_zero, add_zero] at this
      rw [this]
      split_ifs <;> omega
    rw [e, nonzeroDigits_mul_add hb _ _ hr, nonzeroDigits_eq hb a]
    have h1 := nonzeroDigits_add_le b (a / b * d) q hb
    have h2 := ih _ hlt
    by_cases ha0' : a % b = 0
    · obtain ⟨rfl, rfl⟩ := hz ha0'
      simp only [ha0', ↓reduceIte, zero_add, add_zero] at h1 ⊢
      omega
    · split_ifs <;> omega

/-- **L2.** `w_b(ac) ≤ min(s_b(a) w_b(c), 2 w_b(a) w_b(c))`. -/
theorem nonzeroDigits_mul_le (b a c : ℕ) (hb : 2 ≤ b) :
    nonzeroDigits b (a * c) ≤ min (digitSum b a * nonzeroDigits b c)
      (2 * nonzeroDigits b a * nonzeroDigits b c) := by
  refine le_min ?_ ?_
  · induction a using Nat.strong_induction_on with
    | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have hlt : a / b < a := Nat.div_lt_self ha (by omega)
      have hadiv := Nat.div_add_mod a b
      have e : a * c = b * (a / b * c) + a % b * c := by
        conv_lhs => rw [← hadiv]
        ring
      rw [e, digitSum_eq hb a, add_mul]
      calc nonzeroDigits b (b * (a / b * c) + a % b * c)
          ≤ nonzeroDigits b (b * (a / b * c)) + nonzeroDigits b (a % b * c) :=
            nonzeroDigits_add_le b _ _ hb
        _ = nonzeroDigits b (a / b * c) + nonzeroDigits b (a % b * c) := by
            rw [nonzeroDigits_mul_base hb]
        _ ≤ digitSum b (a / b) * nonzeroDigits b c + a % b * nonzeroDigits b c :=
            add_le_add (ih _ hlt) (nonzeroDigits_mul_le_mul hb c _)
        _ = a % b * nonzeroDigits b c + digitSum b (a / b) * nonzeroDigits b c := by ring
  · induction c using Nat.strong_induction_on with
    | _ c ih =>
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · have hlt : c / b < c := Nat.div_lt_self hc (by omega)
      have hcdiv := Nat.div_add_mod c b
      have hc0 := Nat.mod_lt c (show b > 0 by omega)
      have e : a * c = b * (a * (c / b)) + a * (c % b) := by
        conv_lhs => rw [← hcdiv]
        ring
      have h1 := nonzeroDigits_add_le b (b * (a * (c / b))) (a * (c % b)) hb
      rw [nonzeroDigits_mul_base hb] at h1
      have h2 := ih _ hlt
      have h3 : nonzeroDigits b (a * (c % b)) ≤
          (if c % b = 0 then 0 else 1) * (2 * nonzeroDigits b a) := by
        split_ifs with h
        · simp [h]
        · simpa using nonzeroDigits_mul_digit_le hb a _ hc0
      rw [e, nonzeroDigits_eq hb c]
      calc nonzeroDigits b (b * (a * (c / b)) + a * (c % b))
          ≤ 2 * nonzeroDigits b a * nonzeroDigits b (c / b) +
              (if c % b = 0 then 0 else 1) * (2 * nonzeroDigits b a) := by omega
        _ = 2 * nonzeroDigits b a *
              ((if c % b = 0 then 0 else 1) + nonzeroDigits b (c / b)) := by ring

/-- **L3.** Naive submultiplicativity of `w_b` fails for every `b ≥ 3`:
`w_b((b - 1)²) = 2 > 1 = w_b(b - 1)²`. -/
theorem nonzeroDigits_pred_sq (b : ℕ) (hb : 3 ≤ b) :
    nonzeroDigits b ((b - 1) * (b - 1)) = 2 ∧ nonzeroDigits b (b - 1) = 1 := by
  have hb2 : 2 ≤ b := by omega
  have e : (b - 1) * (b - 1) = b * (b - 2) + 1 := by
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 3 := ⟨b - 3, by omega⟩
    simp only [show c + 3 - 1 = c + 2 by omega, show c + 3 - 2 = c + 1 by omega]
    ring
  have hsingle : ∀ r, r < b → r ≠ 0 → nonzeroDigits b r = 1 := by
    intro r hr hr0
    have := nonzeroDigits_mul_add hb2 0 r hr
    simp only [mul_zero, zero_add, nonzeroDigits_zero, add_zero] at this
    rw [this, ite_eq_right hr0]
  refine ⟨?_, hsingle _ (by omega) (by omega)⟩
  rw [e, nonzeroDigits_mul_add hb2 _ 1 (by omega), hsingle _ (by omega) (by omega)]
  simp

/-- **L4.** Binary successor law `s₂(m + 1) + v₂(m + 1) = s₂(m) + 1`, i.e.
`h(p^e) = 1 - v₂(e + 1)` for the squarefull kernel of `s₂(τ(n))`. -/
theorem digitSum_two_succ (m : ℕ) :
    digitSum 2 (m + 1) + padicValNat 2 (m + 1) = digitSum 2 m + 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hv : padicValNat 2 (2 * j + 1) = 0 := by
      rw [Nat.padicValNat_def]
      exact multiplicity_eq_zero_of_not_dvd (by omega)
    rw [hv, digitSum_mul_add (le_refl 2) j 1 (by norm_num), digitSum_mul_base (le_refl 2)]
    omega
  · have hv : padicValNat 2 (2 * j + 1 + 1) = 1 + padicValNat 2 (j + 1) := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, Nat.padicValNat_def, Nat.padicValNat_def,
        multiplicity_base_mul (by norm_num : 1 < 2) (Nat.succ_ne_zero j), add_comm]
    have := ih j (by omega)
    rw [hv, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, digitSum_mul_base (le_refl 2),
      digitSum_mul_add (le_refl 2) j 1 (by norm_num)]
    omega

/-! ### Part 2 (L5): the signed binary (NAF) weight -/

/-- Minimal signed binary weight (NAF weight), by the defining recursion. -/
def signedWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then signedWeight ((n + 2) / 2)
    else 1 + min (signedWeight ((n + 1) / 2)) (signedWeight ((n + 3) / 2))
decreasing_by all_goals omega

@[simp] theorem signedWeight_zero : signedWeight 0 = 0 := signedWeight.eq_1

@[simp] theorem signedWeight_one : signedWeight 1 = 1 := signedWeight.eq_2

private theorem signedWeight_add_two (n : ℕ) : signedWeight (n + 2) =
    if (n + 2) % 2 = 0 then signedWeight ((n + 2) / 2)
    else 1 + min (signedWeight ((n + 1) / 2)) (signedWeight ((n + 3) / 2)) :=
  signedWeight.eq_3 n

/-- **L5.** `w_±(2n) = w_±(n)`. -/
theorem signedWeight_two_mul (n : ℕ) : signedWeight (2 * n) = signedWeight n := by
  rcases n with _ | m
  · simp
  · rw [show 2 * (m + 1) = 2 * m + 2 by ring, signedWeight_add_two, ite_eq_left (by omega),
      show (2 * m + 2) / 2 = m + 1 by omega]

/-- The odd-step recursion `w_±(2n + 1) = 1 + min(w_±(n), w_±(n + 1))`. -/
theorem signedWeight_two_mul_add_one (n : ℕ) :
    signedWeight (2 * n + 1) = 1 + min (signedWeight n) (signedWeight (n + 1)) := by
  rcases n with _ | m
  · simp
  · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, signedWeight_add_two,
      ite_eq_right (by omega), show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      show (2 * m + 1 + 3) / 2 = m + 1 + 1 by omega]

theorem signedWeight_mul_two_pow (n e : ℕ) : signedWeight (n * 2 ^ e) = signedWeight n := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, ← mul_assoc, mul_comm _ 2, signedWeight_two_mul, ih]

/-- **L5.** The signed weight never exceeds the binary digit sum. -/
theorem signedWeight_le_digitSum (n : ℕ) : signedWeight n ≤ digitSum 2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [signedWeight_two_mul, digitSum_mul_base (le_refl 2)]
      exact ih k (by omega)
  · rw [signedWeight_two_mul_add_one, digitSum_mul_add (le_refl 2) k 1 (by norm_num)]
    have := ih k (by omega)
    have := min_le_left (signedWeight k) (signedWeight (k + 1))
    omega

private theorem signedWeight_succ_le (n : ℕ) :
    signedWeight (n + 1) ≤ signedWeight n + 1 ∧ signedWeight n ≤ signedWeight (n + 1) + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [signedWeight_two_mul_add_one, signedWeight_two_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h := ih k (by omega)
      constructor <;> omega
  · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, signedWeight_two_mul,
      signedWeight_two_mul_add_one]
    have h := ih k (by omega)
    constructor <;> omega

private theorem signedWeight_add_aux : ∀ s a c, a + c = s →
    signedWeight (a + c) ≤ signedWeight a + signedWeight c ∧
    signedWeight a ≤ signedWeight (a + c) + signedWeight c := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro a c hs
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' a <;> obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' c
  · rw [show 2 * i + 2 * j = 2 * (i + j) by ring, signedWeight_two_mul, signedWeight_two_mul,
      signedWeight_two_mul]
    exact ih (i + j) (by omega) i j rfl
  · rw [show 2 * i + (2 * j + 1) = 2 * (i + j) + 1 by ring, signedWeight_two_mul_add_one,
      signedWeight_two_mul, signedWeight_two_mul_add_one]
    have h1 := ih (i + j) (by omega) i j rfl
    have h2 := ih (i + (j + 1)) (by omega) i (j + 1) rfl
    have h3 := signedWeight_succ_le j
    rw [show i + (j + 1) = i + j + 1 by ring] at h2
    constructor <;> omega
  · rw [show 2 * i + 1 + 2 * j = 2 * (i + j) + 1 by ring, signedWeight_two_mul_add_one,
      signedWeight_two_mul_add_one, signedWeight_two_mul]
    have h1 := ih (i + j) (by omega) i j rfl
    have h2 := ih (i + 1 + j) (by omega) (i + 1) j rfl
    rw [show i + 1 + j = i + j + 1 by ring] at h2
    constructor <;> omega
  · rw [show 2 * i + 1 + (2 * j + 1) = 2 * (i + j + 1) by ring, signedWeight_two_mul,
      signedWeight_two_mul_add_one, signedWeight_two_mul_add_one]
    rcases Nat.eq_zero_or_pos (i + j) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
      simp
    · have h1 := ih (i + j) (by omega) i j rfl
      have h2 := ih (i + (j + 1)) (by omega) i (j + 1) rfl
      have h3 := ih (i + 1 + j) (by omega) (i + 1) j rfl
      have h4 := ih (i + 1 + (j + 1)) (by omega) (i + 1) (j + 1) rfl
      have h5 := signedWeight_succ_le (i + j)
      have h6 := signedWeight_succ_le (i + j + 1)
      rw [show i + (j + 1) = i + j + 1 by ring] at h2
      rw [show i + 1 + j = i + j + 1 by ring] at h3
      rw [show i + 1 + (j + 1) = i + j + 1 + 1 by ring] at h4
      constructor <;> omega

/-- **L5.** Subadditivity of the signed weight. -/
theorem signedWeight_add_le (m n : ℕ) :
    signedWeight (m + n) ≤ signedWeight m + signedWeight n :=
  (signedWeight_add_aux _ m n rfl).1

/-- **L5.** `w_±(m - n) ≤ w_±(m) + w_±(n)` for `n ≤ m`. -/
theorem signedWeight_sub_le (m n : ℕ) (h : n ≤ m) :
    signedWeight (m - n) ≤ signedWeight m + signedWeight n := by
  have := (signedWeight_add_aux _ (m - n) n rfl).2
  rwa [Nat.sub_add_cancel h] at this

/-- **L5.** Submultiplicativity of the signed weight. -/
theorem signedWeight_mul_le (m n : ℕ) :
    signedWeight (m * n) ≤ signedWeight m * signedWeight n := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [mul_assoc, signedWeight_two_mul, signedWeight_two_mul]
      exact ih k (by omega)
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [signedWeight_two_mul_add_one]
      rcases le_total (signedWeight k) (signedWeight (k + 1)) with hle | hle
      · rw [min_eq_left hle, show (2 * k + 1) * n = 2 * (k * n) + n by ring]
        have h1 := signedWeight_add_le (2 * (k * n)) n
        rw [signedWeight_two_mul] at h1
        have h2 := ih k (by omega)
        calc signedWeight (2 * (k * n) + n)
            ≤ signedWeight k * signedWeight n + signedWeight n := by omega
          _ = (1 + signedWeight k) * signedWeight n := by ring
      · have e : (2 * k + 1) * n = 2 * ((k + 1) * n) - n := by
          have : 2 * ((k + 1) * n) = (2 * k + 1) * n + n := by ring
          omega
        have hle' : n ≤ 2 * ((k + 1) * n) := by nlinarith
        rw [min_eq_right hle, e]
        have h1 := signedWeight_sub_le (2 * ((k + 1) * n)) n hle'
        rw [signedWeight_two_mul] at h1
        have h2 := ih (k + 1) (by omega)
        calc signedWeight (2 * ((k + 1) * n) - n)
            ≤ signedWeight (k + 1) * signedWeight n + signedWeight n := by omega
          _ = (1 + signedWeight (k + 1)) * signedWeight n := by ring

/-! ### Part 3 (L6): two's-complement transitions -/

/-- Adjacent unequal bits of the two's-complement expansion of `A`. -/
def transitions (A : ℤ) : ℕ :=
  let B : ℕ := if 0 ≤ A then A.toNat else (-A - 1).toNat
  digitSum 2 (B ^^^ (B / 2))

/-- The nonnegative magnitude whose binary expansion encodes the two's complement of `A`. -/
private def twosMag (A : ℤ) : ℕ := if 0 ≤ A then A.toNat else (-A - 1).toNat

private theorem transitions_eq_mag (A : ℤ) :
    transitions A = digitSum 2 (twosMag A ^^^ (twosMag A / 2)) := rfl

private theorem twosMag_cast (A : ℤ) : (twosMag A : ℤ) = if 0 ≤ A then A else -A - 1 := by
  unfold twosMag
  split_ifs <;> omega

private theorem xor_half_rec (B : ℕ) :
    digitSum 2 (B ^^^ (B / 2)) =
      (if B % 2 = B / 2 % 2 then 0 else 1) + digitSum 2 (B / 2 ^^^ (B / 2 / 2)) := by
  rw [digitSum_eq (le_refl 2), Nat.xor_div_two]
  congr 1
  have key := @Nat.xor_mod_two_eq_one B (B / 2)
  rcases Nat.mod_two_eq_zero_or_one B with h2 | h2 <;>
  rcases Nat.mod_two_eq_zero_or_one (B / 2) with h3 | h3 <;>
  rcases Nat.mod_two_eq_zero_or_one (B ^^^ (B / 2)) with h1 | h1 <;>
  simp_all

/-- The transition count obeys `T(A) = [A₀ ≠ A₁] + T(⌊A / 2⌋)` on two's-complement bits. -/
theorem transitions_rec (A : ℤ) :
    transitions A = (if A % 2 = A / 2 % 2 then 0 else 1) + transitions (A / 2) := by
  rw [transitions_eq_mag, transitions_eq_mag, xor_half_rec]
  have h := twosMag_cast A
  have h' := twosMag_cast (A / 2)
  have hB : twosMag A / 2 = twosMag (A / 2) := by
    split_ifs at h h' <;> omega
  rw [hB]
  congr 1
  have hiff : twosMag A % 2 = twosMag (A / 2) % 2 ↔ A % 2 = A / 2 % 2 := by
    constructor <;> intro hh <;> split_ifs at h h' <;> omega
  by_cases hc : A % 2 = A / 2 % 2
  · rw [ite_eq_left (hiff.2 hc), ite_eq_left hc]
  · rw [ite_eq_right (mt hiff.1 hc), ite_eq_right hc]

@[simp] theorem transitions_zero : transitions 0 = 0 := by simp [transitions]

@[simp] theorem transitions_neg_one : transitions (-1) = 0 := by simp [transitions]

private theorem transitions_add_one (A : ℤ) :
    transitions (A + 1) ≤ transitions A + 1 ∧ transitions A ≤ transitions (A + 1) + 1 := by
  suffices H : ∀ n : ℕ, ∀ A : ℤ, A.natAbs = n →
      transitions (A + 1) ≤ transitions A + 1 ∧ transitions A ≤ transitions (A + 1) + 1 from
    H _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA
  by_cases hm : A = -1
  · subst hm
    simp
  rw [transitions_rec (A + 1), transitions_rec A]
  rcases Int.emod_two_eq_zero_or_one A with h | h
  · have e1 : (A + 1) / 2 = A / 2 := by omega
    have e2 : (A + 1) % 2 = 1 := by omega
    rw [e1, e2, h]
    split_ifs <;> omega
  · have e1 : (A + 1) / 2 = A / 2 + 1 := by omega
    have e2 : (A + 1) % 2 = 0 := by omega
    have hlt : (A / 2).natAbs < n := by omega
    have := ih _ hlt (A / 2) rfl
    rw [e1, e2, h]
    split_ifs <;> omega

private theorem transitions_add_two_pow_nat (m : ℕ) : ∀ A : ℤ,
    transitions (A + 2 ^ m) ≤ transitions A + 2 ∧
      transitions A ≤ transitions (A + 2 ^ m) + 2 := by
  induction m with
  | zero =>
    intro A
    have := transitions_add_one A
    simp only [pow_zero]
    omega
  | succ m ih =>
    intro A
    rw [transitions_rec (A + 2 ^ (m + 1)), transitions_rec A]
    have e1 : (A + 2 ^ (m + 1)) / 2 = A / 2 + 2 ^ m := by rw [pow_succ]; omega
    have e2 : (A + 2 ^ (m + 1)) % 2 = A % 2 := by rw [pow_succ]; omega
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have := transitions_add_one (A / 2)
      simp only [pow_zero]
      split_ifs <;> omega
    · have e3 : (A / 2 + 2 ^ m) % 2 = A / 2 % 2 := by
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        rw [pow_succ]
        omega
      rw [e3]
      have := ih (A / 2)
      split_ifs <;> omega

/-- **L6.** Adding a signed power of two changes the transition count by at most `2`. -/
theorem transitions_add_two_pow (A : ℤ) (m : ℕ) :
    (transitions (A + 2 ^ m) : ℤ) ≤ transitions A + 2 ∧
    (transitions A : ℤ) ≤ transitions (A + 2 ^ m) + 2 := by
  have := transitions_add_two_pow_nat m A
  omega

private theorem transitions_sub_two_pow_le (A : ℤ) (m : ℕ) :
    transitions (A - 2 ^ m) ≤ transitions A + 2 := by
  have := (transitions_add_two_pow_nat m (A - 2 ^ m)).2
  rwa [sub_add_cancel] at this

private theorem transitions_add_pow_mul_le : ∀ (n j : ℕ) (A : ℤ),
    transitions (A + 2 ^ j * (n : ℤ)) ≤ transitions A + 2 * signedWeight n ∧
    transitions (A - 2 ^ j * (n : ℤ)) ≤ transitions A + 2 * signedWeight n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j A
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [signedWeight_two_mul]
      have e : (2 : ℤ) ^ j * ((2 * k : ℕ) : ℤ) = 2 ^ (j + 1) * (k : ℤ) := by push_cast; ring
      rw [e]
      exact ih k (by omega) (j + 1) A
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [mul_zero, zero_add, signedWeight_one, Nat.cast_one, mul_one]
      exact ⟨(transitions_add_two_pow_nat j A).1, transitions_sub_two_pow_le A j⟩
    · rw [signedWeight_two_mul_add_one]
      rcases le_total (signedWeight k) (signedWeight (k + 1)) with hle | hle
      · rw [min_eq_left hle]
        have e : (2 : ℤ) ^ j * ((2 * k + 1 : ℕ) : ℤ) = 2 ^ (j + 1) * (k : ℤ) + 2 ^ j := by
          push_cast; ring
        have h1 := ih k (by omega) (j + 1) A
        have h2 := (transitions_add_two_pow_nat j (A + 2 ^ (j + 1) * (k : ℤ))).1
        have h3 := transitions_sub_two_pow_le (A - 2 ^ (j + 1) * (k : ℤ)) j
        have e1 : A + 2 ^ j * ((2 * k + 1 : ℕ) : ℤ) = A + 2 ^ (j + 1) * (k : ℤ) + 2 ^ j := by
          rw [e]; ring
        have e2 : A - 2 ^ j * ((2 * k + 1 : ℕ) : ℤ) = A - 2 ^ (j + 1) * (k : ℤ) - 2 ^ j := by
          rw [e]; ring
        rw [e1, e2]
        constructor <;> omega
      · rw [min_eq_right hle]
        have e : (2 : ℤ) ^ j * ((2 * k + 1 : ℕ) : ℤ) = 2 ^ (j + 1) * ((k + 1 : ℕ) : ℤ) - 2 ^ j := by
          push_cast; ring
        have h1 := ih (k + 1) (by omega) (j + 1) A
        have h2 := transitions_sub_two_pow_le (A + 2 ^ (j + 1) * ((k + 1 : ℕ) : ℤ)) j
        have h3 := (transitions_add_two_pow_nat j (A - 2 ^ (j + 1) * ((k + 1 : ℕ) : ℤ))).1
        have e1 : A + 2 ^ j * ((2 * k + 1 : ℕ) : ℤ) =
            A + 2 ^ (j + 1) * ((k + 1 : ℕ) : ℤ) - 2 ^ j := by rw [e]; ring
        have e2 : A - 2 ^ j * ((2 * k + 1 : ℕ) : ℤ) =
            A - 2 ^ (j + 1) * ((k + 1 : ℕ) : ℤ) + 2 ^ j := by rw [e]; ring
        rw [e1, e2]
        constructor <;> omega

/-- **L6.** `T(A + c) ≤ T(A) + 2 w_±(|c|)`. -/
theorem transitions_add_le (A c : ℤ) :
    transitions (A + c) ≤ transitions A + 2 * signedWeight c.natAbs := by
  rcases le_or_gt 0 c with hc | hc
  · have := (transitions_add_pow_mul_le c.natAbs 0 A).1
    rwa [pow_zero, one_mul, Int.natAbs_of_nonneg hc] at this
  · have := (transitions_add_pow_mul_le c.natAbs 0 A).2
    rwa [pow_zero, one_mul, show A - (c.natAbs : ℤ) = A + c by omega] at this

/-! ### Part 4 (L7–L9): exact prefix decomposition and prefix mass bounds -/

private theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ i ∈ range n, g (i + 1) = ∑ i ∈ Icc 1 n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- **L7 (Theorem 2.1).** Exact prefix decomposition of `x = ∑_{n ≥ 1} a(n) b^{-kn}`:
`⌊b^N x⌋ = ∑_{1 ≤ n ≤ N/k} a(n) b^{N - kn} + ⌊τ_N⌋`. -/
theorem floor_pow_mul_eq_head_add_floor_tail {b k : ℕ} (hb : 2 ≤ b)
    (a : ℕ → ℤ) (hs : Summable fun n : ℕ => |(a (n + 1) : ℝ)| / (b : ℝ) ^ (k * (n + 1)))
    (N : ℕ) :
    ⌊(b : ℝ) ^ N * ∑' n : ℕ, (a (n + 1) : ℝ) / (b : ℝ) ^ (k * (n + 1))⌋ =
      (∑ n ∈ Icc 1 (N / k), a n * (b : ℤ) ^ (N - k * n)) +
      ⌊∑' m : ℕ, (a (N / k + 1 + m) : ℝ) * (b : ℝ) ^ N / (b : ℝ) ^ (k * (N / k + 1 + m))⌋ := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hsum : Summable fun n : ℕ => (a (n + 1) : ℝ) / (b : ℝ) ^ (k * (n + 1)) := by
    refine Summable.of_norm (hs.congr fun n => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 _)]
  rw [← hsum.sum_add_tsum_nat_add (N / k), mul_add, Finset.mul_sum, ← tsum_mul_left]
  have hhead : ∑ i ∈ range (N / k), (b : ℝ) ^ N * ((a (i + 1) : ℝ) / (b : ℝ) ^ (k * (i + 1))) =
      ((∑ n ∈ Icc 1 (N / k), a n * (b : ℤ) ^ (N - k * n) : ℤ) : ℝ) := by
    rw [← sum_range_succ_eq_sum_Icc]
    push_cast
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : k * (i + 1) ≤ N :=
      (Nat.mul_le_mul_left k (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).trans
        (Nat.mul_div_le N k)
    have hpow : (b : ℝ) ^ N = (b : ℝ) ^ (N - k * (i + 1)) * (b : ℝ) ^ (k * (i + 1)) := by
      rw [← pow_add, Nat.sub_add_cancel hi']
    have hne : (b : ℝ) ^ (k * (i + 1)) ≠ 0 := (pow_pos hb0 _).ne'
    rw [hpow]
    field_simp
  have htail : ∑' i, (b : ℝ) ^ N * ((a (i + N / k + 1) : ℝ) / (b : ℝ) ^ (k * (i + N / k + 1))) =
      ∑' m : ℕ, (a (N / k + 1 + m) : ℝ) * (b : ℝ) ^ N / (b : ℝ) ^ (k * (N / k + 1 + m)) := by
    refine tsum_congr (fun i => ?_)
    rw [show i + N / k + 1 = N / k + 1 + i by ring]
    ring
  rw [hhead, htail, Int.floor_intCast_add]

private theorem digitSum_sum_le {b : ℕ} (hb : 2 ≤ b) (S : Finset ℕ) (a e : ℕ → ℕ) (t : ℕ) :
    digitSum b (∑ n ∈ S, a n * b ^ e n + t) ≤ ∑ n ∈ S, digitSum b (a n) + digitSum b t := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih =>
    rw [sum_insert hi, sum_insert hi, add_assoc]
    have h1 := digitSum_add_le b (a i * b ^ e i) (∑ n ∈ S, a n * b ^ e n + t) hb
    rw [digitSum_mul_pow b _ _ hb] at h1
    omega

/-- **L8 (Theorem 2.2).** Unsigned prefix digit-sum bound for the integer prefix. -/
theorem digitSum_prefix_le {b k : ℕ} (hb : 2 ≤ b) (a : ℕ → ℕ) (N t : ℕ) :
    digitSum b ((∑ n ∈ Icc 1 (N / k), a n * b ^ (N - k * n)) + t) ≤
      (∑ n ∈ Icc 1 (N / k), digitSum b (a n)) + digitSum b t :=
  digitSum_sum_le hb _ a (fun n => N - k * n) t

private theorem transitions_sum_le (S : Finset ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ) (t : ℤ) :
    transitions (∑ n ∈ S, a n * 2 ^ e n + t) ≤
      2 * ∑ n ∈ S, signedWeight (a n).natAbs + 2 * signedWeight t.natAbs := by
  induction S using Finset.induction with
  | empty => simpa using transitions_add_le 0 t
  | insert i S hi ih =>
    rw [sum_insert hi, sum_insert hi, add_assoc, add_comm (a i * 2 ^ e i)]
    have h1 := transitions_add_le (∑ n ∈ S, a n * 2 ^ e n + t) (a i * 2 ^ e i)
    have h2 : signedWeight (a i * 2 ^ e i).natAbs = signedWeight (a i).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      exact signedWeight_mul_two_pow _ _
    rw [h2] at h1
    rw [mul_add]
    omega

/-- **L9 (Theorem 7.1).** Signed prefix transition bound. -/
theorem transitions_prefix_le {k : ℕ} (a : ℕ → ℤ) (N : ℕ) (t : ℤ) :
    transitions ((∑ n ∈ Icc 1 (N / k), a n * 2 ^ (N - k * n)) + t) ≤
      2 * (∑ n ∈ Icc 1 (N / k), signedWeight (a n).natAbs) + 2 * signedWeight t.natAbs :=
  transitions_sum_le _ a (fun n => N - k * n) t

/-! ### Part 5 (L10–L12): frequency, transition and zero-run discrepancy criteria -/

/-- Every interval deviation is bounded by the extreme radix discrepancy. -/
theorem interval_le_radixDiscrepancy (b : ℕ) (x : ℝ) (N : ℕ) {a c : ℝ} (ha : 0 ≤ a)
    (hac : a < c) (hc : c ≤ 1) :
    |frequency (shift b x) a c N - (c - a)| ≤ radixDiscrepancy b x N := by
  refine le_csSup ⟨1, ?_⟩ ⟨a, c, ha, hac, hc, rfl⟩
  rintro d ⟨a', c', ha', hac', hc', rfl⟩
  obtain ⟨h1, h2⟩ := frequency_bounds (shift b x) a' c' N
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem radixDiscrepancy_le_of {b : ℕ} {x : ℝ} {N : ℕ} {D : ℝ}
    (H : ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 → |frequency (shift b x) a c N - (c - a)| ≤ D) :
    radixDiscrepancy b x N ≤ D := by
  unfold radixDiscrepancy
  refine csSup_le ⟨_, 0, 1, le_rfl, zero_lt_one, le_rfl, rfl⟩ ?_
  rintro _ ⟨a, c, ha, hac, hc, rfl⟩
  exact H a c ha hac hc

private theorem shift_mem (b : ℕ) (x : ℝ) (i : ℕ) : 0 ≤ shift b x i ∧ shift b x i < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private theorem frequency_zero_right (u : ℕ → ℝ) (a c : ℝ) : frequency u a c 0 = 0 := by
  simp [frequency]

private theorem frequency_split {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i < 1) (a : ℝ) {N : ℕ}
    (hN : 0 < N) : frequency u 0 a N + frequency u a 1 N = 1 := by
  unfold frequency
  have h1 : (range N).filter (fun i => 0 ≤ u i ∧ u i < a) =
      (range N).filter (fun i => u i < a) :=
    Finset.filter_congr (fun i _ => ⟨fun h => h.2, fun h => ⟨(hu i).1, h⟩⟩)
  have h2 : (range N).filter (fun i => a ≤ u i ∧ u i < 1) =
      (range N).filter (fun i => ¬ u i < a) :=
    Finset.filter_congr (fun i _ => ⟨fun h => not_lt.mpr h.1, fun h => ⟨not_lt.mp h, (hu i).2⟩⟩)
  rw [h1, h2, ← add_div, ← Nat.cast_add, Finset.card_filter_add_card_filter_not,
    card_range, div_self (Nat.cast_ne_zero.mpr hN.ne')]

/-- **L10 (Proposition 2.4(2)).** `D_N(x; b) ≥ (b - 1)/b - f_{≠0}(N)`, where the frequency of
nonzero leading digits is the frequency of `[1/b, 1)`. -/
theorem radixDiscrepancy_ge_nonzero_freq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (N : ℕ) :
    ((b - 1 : ℝ) / b) - frequency (shift b x) (1 / b) 1 N ≤ radixDiscrepancy b x N := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hfrac : ((b - 1 : ℝ) / b) = 1 - 1 / b := by field_simp
  have hinv : (0 : ℝ) < 1 / b := by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h := interval_le_radixDiscrepancy b x 0 (le_refl 0) zero_lt_one le_rfl
    rw [frequency_zero_right] at h ⊢
    rw [hfrac]
    norm_num at h
    linarith
  · have hsplit := frequency_split (shift_mem b x) (1 / b) hN
    have h := interval_le_radixDiscrepancy b x N (le_refl 0) hinv
      (by rw [div_le_one hb0]; linarith)
    have := le_abs_self (frequency (shift b x) 0 (1 / b) N - (1 / b - 0))
    rw [hfrac]
    linarith

/-- **L10 (Proposition 2.4(4)).** `D_N(x; 2) ≥ 1/2 - (f₀₁ + f₁₀)(N)`. -/
theorem binaryDiscrepancy_ge_half_sub_transition (x : ℝ) (N : ℕ) :
    1 / 2 - transitionFrequency x N ≤ radixDiscrepancy 2 x N := by
  have h := interval_le_radixDiscrepancy 2 x N (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 3 / 4) (by norm_num)
  have := neg_abs_le (frequency (shift 2 x) (1 / 4) (3 / 4) N - (3 / 4 - 1 / 4))
  unfold transitionFrequency
  linarith

private theorem shift_two_succ_of_lt_half (x : ℝ) (n : ℕ) (h : shift 2 x n < 1 / 2) :
    shift 2 x (n + 1) = 2 * shift 2 x n := by
  unfold shift at h ⊢
  have e : (2 : ℝ) ^ (n + 1) * x =
      2 * Int.fract ((2 : ℝ) ^ n * x) + ((2 * ⌊(2 : ℝ) ^ n * x⌋ : ℤ) : ℝ) := by
    rw [pow_succ]
    push_cast
    rw [Int.fract]
    ring
  simp only [Nat.cast_ofNat]
  rw [e, Int.fract_add_intCast, Int.fract_eq_self]
  exact ⟨by linarith [Int.fract_nonneg ((2 : ℝ) ^ n * x)], by linarith⟩

private theorem exists_half_of_ge_pow (x : ℝ) : ∀ (m n : ℕ), (2⁻¹ : ℝ) ^ m ≤ shift 2 x n →
    ∃ i < m, 1 / 2 ≤ shift 2 x (n + i) := by
  intro m
  induction m with
  | zero =>
    intro n h
    exfalso
    have := (shift_mem 2 x n).2
    rw [pow_zero] at h
    linarith
  | succ m ih =>
    intro n h
    by_cases hn : 1 / 2 ≤ shift 2 x n
    · exact ⟨0, by omega, by simpa using hn⟩
    · have hs := shift_two_succ_of_lt_half x n (not_le.mp hn)
      have h' : (2⁻¹ : ℝ) ^ m ≤ shift 2 x (n + 1) := by
        rw [hs]
        rw [pow_succ] at h
        linarith
      obtain ⟨i, hi, hi'⟩ := ih (n + 1) h'
      exact ⟨i + 1, by omega, by rwa [show n + (i + 1) = n + 1 + i by ring]⟩

private theorem zero_run_count (x : ℝ) (m N : ℕ) :
    ((range N).filter (fun n => ¬ (0 ≤ shift 2 x n ∧ shift 2 x n < 2⁻¹ ^ m))).card ≤
      m * ((range (N + m)).filter (fun t => 1 / 2 ≤ shift 2 x t ∧ shift 2 x t < 1)).card := by
  have hsub : (range N).filter (fun n => ¬ (0 ≤ shift 2 x n ∧ shift 2 x n < 2⁻¹ ^ m)) ⊆
      (range m).biUnion (fun i => (range N).filter
        (fun n => 1 / 2 ≤ shift 2 x (n + i) ∧ shift 2 x (n + i) < 1)) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    obtain ⟨hnN, hn⟩ := hn
    have hge : (2⁻¹ : ℝ) ^ m ≤ shift 2 x n := by
      by_contra hlt
      exact hn ⟨(shift_mem 2 x n).1, not_le.mp hlt⟩
    obtain ⟨i, hi, hi'⟩ := exists_half_of_ge_pow x m n hge
    simp only [mem_biUnion, mem_range, mem_filter]
    exact ⟨i, hi, hnN, hi', (shift_mem 2 x _).2⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ i ∈ range m, ((range N).filter
          (fun n => 1 / 2 ≤ shift 2 x (n + i) ∧ shift 2 x (n + i) < 1)).card
      ≤ ∑ _i ∈ range m,
          ((range (N + m)).filter (fun t => 1 / 2 ≤ shift 2 x t ∧ shift 2 x t < 1)).card := by
        refine sum_le_sum (fun i hi => ?_)
        refine card_le_card_of_injOn (fun n => n + i) ?_ ?_
        · intro n hn
          simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hn ⊢
          have := mem_range.mp hi
          exact ⟨by omega, hn.2⟩
        · intro a _ c _ h
          simpa using h
    _ = m * ((range (N + m)).filter (fun t => 1 / 2 ≤ shift 2 x t ∧ shift 2 x t < 1)).card := by
        simp

/-- **L12 (Proposition 2.4(3)).** Zero-run bound in base `2`:
`D_N(x; 2) ≥ 1 - m ((N + m)/N) f₁(N + m) - 2^{-m}`. -/
theorem radixDiscrepancy_ge_zero_run (x : ℝ) (m N : ℕ) (hN : 0 < N) :
    1 - (m : ℝ) * ((N + m : ℝ) / N) * frequency (shift 2 x) (1 / 2) 1 (N + m) - 2⁻¹ ^ m ≤
      radixDiscrepancy 2 x N := by
  have hpos : (0 : ℝ) < 2⁻¹ ^ m := by positivity
  have hle1 : (2⁻¹ : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h := interval_le_radixDiscrepancy 2 x N (le_refl 0) hpos hle1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := zero_run_count x m N
  have hsplit := Finset.card_filter_add_card_filter_not (s := range N)
    (fun n => 0 ≤ shift 2 x n ∧ shift 2 x n < 2⁻¹ ^ m)
  rw [card_range] at hsplit
  unfold frequency at h ⊢
  generalize ((range N).filter
    (fun n => ¬ (0 ≤ shift 2 x n ∧ shift 2 x n < 2⁻¹ ^ m))).card = B at hc hsplit
  generalize ((range N).filter
    (fun n => 0 ≤ shift 2 x n ∧ shift 2 x n < 2⁻¹ ^ m)).card = Z at hsplit h
  generalize ((range (N + m)).filter
    (fun t => 1 / 2 ≤ shift 2 x t ∧ shift 2 x t < 1)).card = G at hc ⊢
  have habs := le_abs_self ((Z : ℝ) / N - (2⁻¹ ^ m - 0))
  have hNm : (0 : ℝ) < ((N + m : ℕ) : ℝ) := by positivity
  have e1 : (m : ℝ) * ((N + m : ℝ) / N) * ((G : ℝ) / ((N + m : ℕ) : ℝ)) = m * G / N := by
    push_cast at hNm ⊢
    field_simp
  have e2 : (Z : ℝ) / N = 1 - B / N := by
    have : (Z : ℝ) + B = N := by exact_mod_cast hsplit
    field_simp
    linarith
  have hB : (B : ℝ) ≤ m * G := by exact_mod_cast hc
  have hB' : (B : ℝ) / N ≤ m * G / N := div_le_div_of_nonneg_right hB hNr.le
  rw [e1]
  linarith

/-! ### Part 6 (L13–L14): the elementary analytic core -/

private theorem natDiv_div_tendsto {n : ℕ} (hn : 0 < n) :
    Tendsto (fun X : ℕ => ((X / n : ℕ) : ℝ) / X) atTop (𝓝 (1 / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlow : Tendsto (fun X : ℕ => (1 : ℝ) / n - 1 / X) atTop (𝓝 (1 / n)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_sub ((1 : ℝ) / n)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hX' : (0 : ℝ) < X := by exact_mod_cast hX
    have h1 : ((X : ℝ) / n) - 1 < ((X / n : ℕ) : ℝ) := by
      have h2 : X < n * (X / n + 1) := Nat.lt_mul_div_succ X hn
      have h3 : (X : ℝ) < n * (((X / n : ℕ) : ℝ) + 1) := by exact_mod_cast h2
      rw [div_sub_one hn'.ne', div_lt_iff₀ hn']
      linarith
    rw [le_div_iff₀ hX']
    have : ((1 : ℝ) / n - 1 / X) * X = X / n - 1 := by field_simp
    rw [this]
    linarith
  · refine Eventually.of_forall (fun X => ?_)
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp
    · have hX' : (0 : ℝ) < X := by exact_mod_cast hX
      rw [div_le_iff₀ hX', one_div_mul_eq_div]
      exact Nat.cast_div_le

/-- **L13 (Lemma 3.1).** Elementary Dirichlet-convolution mean value: if the squarefull
kernel `h = G * μ` satisfies `∑ |h(n)|/n < ∞`, then `X⁻¹ ∑_{n ≤ X} G(n) → ∑ h(n)/n`.
No Tauberian input and no multiplicativity is needed. -/
theorem tendsto_average_of_summable_conv_mobius (G : ArithmeticFunction ℝ)
    (hs : Summable fun n : ℕ =>
      |((G * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) n)| / n) :
    Tendsto (fun X : ℕ => (∑ n ∈ Icc 1 X, G n) / (X : ℝ)) atTop
      (𝓝 (∑' n : ℕ, (G * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) n / n)) := by
  set h := G * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) with hh
  have hG : G = h * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    rw [hh, mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  have hrepr : ∀ X : ℕ, (∑ n ∈ Icc 1 X, G n) / (X : ℝ) =
      ∑' n : ℕ, h n * (((X / n : ℕ) : ℝ) / X) := by
    intro X
    have hIcc : Icc 1 X = Ioc 0 X := by
      ext n
      simp only [mem_Icc, mem_Ioc]
      omega
    have h1 : ∑ n ∈ Icc 1 X, G n = ∑ n ∈ Ioc 0 X, h n * ((X / n : ℕ) : ℝ) := by
      rw [hIcc, ← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum, ← hG]
    rw [h1, Finset.sum_div]
    simp_rw [mul_div_assoc]
    symm
    refine tsum_eq_sum (fun n hn => ?_)
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hn
    rcases hn with hn | hn
    · obtain rfl : n = 0 := by omega
      simp
    · simp [Nat.div_eq_of_lt hn]
  have hlim : Tendsto (fun X : ℕ => ∑' n : ℕ, h n * (((X / n : ℕ) : ℝ) / X)) atTop
      (𝓝 (∑' n : ℕ, h n / n)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => |h n| / n) hs
      (fun n => ?_) (Eventually.of_forall (fun X n => ?_))
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [div_eq_mul_one_div (h n) (n : ℝ)]
        exact (natDiv_div_tendsto hn).const_mul (h n)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((X / n : ℕ) : ℝ) / X),
        div_eq_mul_one_div |h n|]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rcases Nat.eq_zero_or_pos X with rfl | hX
      · simp
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hX' : (0 : ℝ) < X := by exact_mod_cast hX
          rw [div_le_iff₀ hX', one_div_mul_eq_div]
          exact Nat.cast_div_le
  simp_rw [hrepr]
  exact hlim

private theorem summable_digitSum_mul_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun m : ℕ => (digitSum 2 m : ℝ) * x ^ m := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖x‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hx0])
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
  rw [pow_one]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast digitSum_le_self (le_refl 2) m)
    (pow_nonneg hx0 m)

/-- The binary digit-sum generating function `T(x) = ∑_m s₂(m) x^m`. -/
private noncomputable def binGF (x : ℝ) : ℝ := ∑' m : ℕ, (digitSum 2 m : ℝ) * x ^ m

private theorem binGF_functional {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    binGF x = (1 + x) * binGF (x ^ 2) + x / (1 - x ^ 2) := by
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hs := summable_digitSum_mul_pow hx0 hx1
  have hs2 := summable_digitSum_mul_pow (by positivity : 0 ≤ x ^ 2) hx2
  have hg := summable_geometric_of_lt_one (by positivity : 0 ≤ x ^ 2) hx2
  have he : Summable fun k : ℕ => (digitSum 2 (2 * k) : ℝ) * x ^ (2 * k) :=
    hs.comp_injective (fun a b h => by simpa using h)
  have ho : Summable fun k : ℕ => (digitSum 2 (2 * k + 1) : ℝ) * x ^ (2 * k + 1) :=
    hs.comp_injective (fun a b h => by simpa using h)
  unfold binGF
  rw [← tsum_even_add_odd (f := fun m : ℕ => (digitSum 2 m : ℝ) * x ^ m) he ho]
  have e1 : ∀ k : ℕ, (digitSum 2 (2 * k) : ℝ) * x ^ (2 * k) = (digitSum 2 k : ℝ) * (x ^ 2) ^ k := by
    intro k
    rw [digitSum_mul_base (le_refl 2), pow_mul x 2 k]
  have e2 : ∀ k : ℕ, (digitSum 2 (2 * k + 1) : ℝ) * x ^ (2 * k + 1) =
      x * ((digitSum 2 k : ℝ) * (x ^ 2) ^ k) + x * (x ^ 2) ^ k := by
    intro k
    rw [digitSum_mul_add (le_refl 2) k 1 (by norm_num), pow_succ x (2 * k), pow_mul x 2 k]
    push_cast
    ring
  simp_rw [e1, e2]
  rw [(hs2.mul_left x).tsum_add (hg.mul_left x), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one (by positivity) hx2]
  rw [div_eq_mul_inv]
  ring

private theorem binGF_iter {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (J : ℕ) :
    (1 - x) * binGF x = ∑ j ∈ range J, x ^ 2 ^ j / (1 + x ^ 2 ^ j) +
      (1 - x ^ 2 ^ J) * binGF (x ^ 2 ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [ih, sum_range_succ]
    have hy0 : 0 ≤ x ^ 2 ^ J := by positivity
    have hy1 : x ^ 2 ^ J < 1 := pow_lt_one₀ hx0 hx1 (by positivity)
    have hf := binGF_functional hy0 hy1
    have hsq : (x ^ 2 ^ J) ^ 2 = x ^ 2 ^ (J + 1) := by rw [← pow_mul, pow_succ]
    rw [hsq] at hf
    have hd1 : (1 : ℝ) - (x ^ 2 ^ J) ^ 2 ≠ 0 := by nlinarith
    have hd2 : (1 : ℝ) + x ^ 2 ^ J ≠ 0 := by linarith
    rw [hf, ← hsq]
    field_simp
    ring

private theorem binGF_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) : binGF y ≤ 4 * y := by
  have hy1 : y < 1 := by linarith
  have hny : ‖y‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hy0]
  have hle : binGF y ≤ ∑' m : ℕ, (m : ℝ) * y ^ m := by
    refine (summable_digitSum_mul_pow hy0 hy1).tsum_le_tsum (fun m => ?_) ?_
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast digitSum_le_self (le_refl 2) m)
        (pow_nonneg hy0 m)
    · simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hny
  rw [tsum_coe_mul_geometric_of_norm_lt_one hny] at hle
  have h1 : (1 / 4 : ℝ) ≤ (1 - y) ^ 2 := by nlinarith
  have h2 : y / (1 - y) ^ 2 ≤ 4 * y := by
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    nlinarith
  linarith

/-- **L14 (Corollary 3.3(3)).** Exact local Euler factor of the digit-sum majorant:
`(1 - p⁻¹) ∑_{e ≥ 0} s₂(e + 1) / p^e = ∑_{j ≥ 0} p / (p^{2^j} + 1)`. -/
theorem local_factor_digitSum_two (p : ℕ) (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹) * ∑' e : ℕ, (digitSum 2 (e + 1) : ℝ) / (p : ℝ) ^ e =
      ∑' j : ℕ, (p : ℝ) / ((p : ℝ) ^ (2 ^ j) + 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ)⁻¹ with hxdef
  have hx0 : 0 < x := by positivity
  have hxh : x ≤ 1 / 2 := by
    rw [hxdef, one_div]
    exact inv_anti₀ (by norm_num) hp'
  have hx1 : x < 1 := by linarith
  have hpx : (p : ℝ) = x⁻¹ := by rw [hxdef, inv_inv]
  have hxne : x ≠ 0 := hx0.ne'
  -- the shifted series equals `T(x) / x`
  have hs := summable_digitSum_mul_pow hx0.le hx1
  have hshift : ∑' e : ℕ, (digitSum 2 (e + 1) : ℝ) / (p : ℝ) ^ e = binGF x / x := by
    unfold binGF
    rw [hs.tsum_eq_zero_add]
    simp only [digitSum_zero, Nat.cast_zero, zero_mul, zero_add]
    rw [eq_div_iff hx0.ne', ← tsum_mul_right]
    refine tsum_congr (fun e => ?_)
    rw [hpx, inv_pow, div_inv_eq_mul, pow_succ]
    ring
  -- the series of local terms is summable and its partial sums converge to `(1 - x) T(x)`
  have hterm_le : ∀ j : ℕ, x ^ 2 ^ j / (1 + x ^ 2 ^ j) ≤ x ^ j := by
    intro j
    have h1 : x ^ 2 ^ j ≤ x ^ j := pow_le_pow_of_le_one hx0.le hx1.le Nat.lt_two_pow_self.le
    have h2 : x ^ 2 ^ j / (1 + x ^ 2 ^ j) ≤ x ^ 2 ^ j := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_nonneg hx0.le (2 ^ j)]
    linarith
  have hsum : Summable fun j : ℕ => x ^ 2 ^ j / (1 + x ^ 2 ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm_le
      (summable_geometric_of_lt_one hx0.le hx1)
  have hrem : Tendsto (fun J : ℕ => (1 - x ^ 2 ^ J) * binGF (x ^ 2 ^ J)) atTop (𝓝 0) := by
    have hbound : ∀ J : ℕ, |(1 - x ^ 2 ^ J) * binGF (x ^ 2 ^ J)| ≤ 4 * x ^ J := by
      intro J
      have hy0 : 0 ≤ x ^ 2 ^ J := by positivity
      have hyJ : x ^ 2 ^ J ≤ x ^ J := pow_le_pow_of_le_one hx0.le hx1.le Nat.lt_two_pow_self.le
      have hy : x ^ 2 ^ J ≤ 1 / 2 := by
        have : x ^ 2 ^ J ≤ x := by
          simpa using pow_le_pow_of_le_one hx0.le hx1.le (Nat.one_le_two_pow (n := J))
        linarith
      have hy1 : x ^ 2 ^ J < 1 := by linarith
      have hT0 : 0 ≤ binGF (x ^ 2 ^ J) := by
        unfold binGF
        exact tsum_nonneg (fun m => by positivity)
      have hT := binGF_le hy0 hy
      rw [abs_of_nonneg (mul_nonneg (by linarith) hT0)]
      have : (1 - x ^ 2 ^ J) * binGF (x ^ 2 ^ J) ≤ binGF (x ^ 2 ^ J) := by nlinarith
      linarith
    have h4 : Tendsto (fun J : ℕ => 4 * x ^ J) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1).const_mul 4
    exact squeeze_zero_norm (fun J => by rw [Real.norm_eq_abs]; exact hbound J) h4
  have hpartial : Tendsto (fun J : ℕ => ∑ j ∈ range J, x ^ 2 ^ j / (1 + x ^ 2 ^ j)) atTop
      (𝓝 ((1 - x) * binGF x)) := by
    have : Tendsto (fun J : ℕ => (1 - x) * binGF x - (1 - x ^ 2 ^ J) * binGF (x ^ 2 ^ J))
        atTop (𝓝 ((1 - x) * binGF x - 0)) := tendsto_const_nhds.sub hrem
    rw [sub_zero] at this
    refine this.congr (fun J => ?_)
    rw [binGF_iter hx0.le hx1 J]
    ring
  have htsum : ∑' j : ℕ, x ^ 2 ^ j / (1 + x ^ 2 ^ j) = (1 - x) * binGF x :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpartial
  have hrhs : ∑' j : ℕ, (p : ℝ) / ((p : ℝ) ^ (2 ^ j) + 1) =
      x⁻¹ * ∑' j : ℕ, x ^ 2 ^ j / (1 + x ^ 2 ^ j) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    have hxj : x ^ 2 ^ j ≠ 0 := (pow_pos hx0 _).ne'
    have hxj1 : 1 + x ^ 2 ^ j ≠ 0 := by have := pow_pos hx0 (2 ^ j); linarith
    rw [hpx, inv_pow]
    field_simp
  rw [hshift, hrhs, htsum]
  field_simp

/-! ### Part 7: the multiplicative digit-sum majorant of `s₂(τ(n))` and its Euler product -/

/-- The multiplicative arithmetic function with prescribed prime-power values `g e`
(normalised by `g 0 = 1`): `n ↦ ∏_{p^e ∥ n} g(e)`. -/
noncomputable def multOfPrimePow (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod fun _ e => g e, by simp⟩

theorem multOfPrimePow_apply (g : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    multOfPrimePow g n = n.factorization.prod fun _ e => g e := by
  simp [multOfPrimePow, hn]

theorem multOfPrimePow_isMultiplicative (g : ℕ → ℝ) :
    (multOfPrimePow g).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn hmn => ?_⟩
  · rw [multOfPrimePow_apply g one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  · rw [multOfPrimePow_apply g (mul_ne_zero hm hn), multOfPrimePow_apply g hm,
      multOfPrimePow_apply g hn, Nat.factorization_mul_of_coprime hmn,
      Finsupp.prod_add_index_of_disjoint]
    rw [Nat.support_factorization, Nat.support_factorization]
    exact hmn.disjoint_primeFactors

theorem multOfPrimePow_prime_pow {g : ℕ → ℝ} (hg : g 0 = 1) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    multOfPrimePow g (p ^ e) = g e := by
  rw [multOfPrimePow_apply g (pow_ne_zero e hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index hg]

theorem multOfPrimePow_nonneg {g : ℕ → ℝ} (hg : ∀ e, 0 ≤ g e) (n : ℕ) :
    0 ≤ multOfPrimePow g n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [multOfPrimePow_apply g hn.ne']
    exact Finset.prod_nonneg (fun p _ => hg _)

private theorem digitSum_two_one : digitSum 2 1 = 1 := digitSum_of_lt (le_refl 2) (by norm_num)

private theorem digitSum_two_two : digitSum 2 2 = 1 := by
  have := digitSum_mul_base (le_refl 2) 1
  rwa [digitSum_two_one] at this

private theorem digitSum_two_three : digitSum 2 3 = 2 := by
  have := digitSum_mul_add (le_refl 2) 1 1 (by norm_num)
  rwa [digitSum_two_one] at this

private theorem digitSum_two_four : digitSum 2 4 = 1 := by
  have := digitSum_mul_base (le_refl 2) 2
  rwa [digitSum_two_two] at this

/-- The multiplicative majorant `G(n) = ∏_{p^e ∥ n} s₂(e + 1)` of `s₂(τ(n))`. -/
noncomputable def tauDigitMajorant : ArithmeticFunction ℝ :=
  multOfPrimePow fun e => (digitSum 2 (e + 1) : ℝ)

/-- The squarefull kernel `h = G * μ`, with `h(p^e) = s₂(e + 1) - s₂(e) = 1 - v₂(e + 1)`. -/
noncomputable def tauDigitKernel : ArithmeticFunction ℝ :=
  multOfPrimePow fun e => (digitSum 2 (e + 1) : ℝ) - digitSum 2 e

theorem tauDigitMajorant_isMultiplicative : tauDigitMajorant.IsMultiplicative :=
  multOfPrimePow_isMultiplicative _

theorem tauDigitKernel_isMultiplicative : tauDigitKernel.IsMultiplicative :=
  multOfPrimePow_isMultiplicative _

theorem tauDigitMajorant_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    tauDigitMajorant (p ^ e) = digitSum 2 (e + 1) :=
  multOfPrimePow_prime_pow (g := fun e => (digitSum 2 (e + 1) : ℝ))
    (by simp [digitSum_two_one]) hp e

theorem tauDigitKernel_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    tauDigitKernel (p ^ e) = (digitSum 2 (e + 1) : ℝ) - digitSum 2 e :=
  multOfPrimePow_prime_pow (g := fun e => (digitSum 2 (e + 1) : ℝ) - digitSum 2 e)
    (by simp [digitSum_two_one]) hp e

theorem tauDigitMajorant_nonneg (n : ℕ) : 0 ≤ tauDigitMajorant n :=
  multOfPrimePow_nonneg (fun _ => Nat.cast_nonneg _) n

theorem tauDigitKernel_mul_zeta :
    tauDigitKernel * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = tauDigitMajorant := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (tauDigitKernel_isMultiplicative.mul ArithmeticFunction.isMultiplicative_zeta.natCast) _
    tauDigitMajorant_isMultiplicative).2 (fun p e hp => ?_)
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    tauDigitMajorant_prime_pow hp]
  simp_rw [tauDigitKernel_prime_pow hp]
  have htel : ∀ m : ℕ, ∑ x ∈ range m, ((digitSum 2 (x + 1) : ℝ) - digitSum 2 x) =
      digitSum 2 m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; ring
  rw [htel]

/-- The kernel identity `G * μ = h`. -/
theorem tauDigitMajorant_mul_moebius :
    tauDigitMajorant * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = tauDigitKernel := by
  rw [← tauDigitKernel_mul_zeta, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]

/-- `s₂(τ(n)) ≤ G(n)`, from the submultiplicativity of `s₂` (L2). -/
theorem digitSum_card_divisors_le (n : ℕ) :
    (digitSum 2 n.divisors.card : ℝ) ≤ tauDigitMajorant n := by
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun n => (digitSum 2 n.divisors.card : ℝ) ≤ tauDigitMajorant n) ?_ ?_ ?_ ?_ n
  · intro p k hp _
    rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      tauDigitMajorant_prime_pow hp]
  · simp
  · simp [tauDigitMajorant_isMultiplicative.map_one, digitSum_two_one]
  · intro a b _ _ hab iha ihb
    rw [Nat.Coprime.card_divisors_mul hab, tauDigitMajorant_isMultiplicative.map_mul_of_coprime hab]
    calc (digitSum 2 (a.divisors.card * b.divisors.card) : ℝ)
        ≤ (digitSum 2 a.divisors.card : ℝ) * digitSum 2 b.divisors.card := by
          exact_mod_cast digitSum_mul_le 2 _ _ (le_refl 2)
      _ ≤ tauDigitMajorant a * tauDigitMajorant b :=
          mul_le_mul iha ihb (Nat.cast_nonneg _) (tauDigitMajorant_nonneg a)

private theorem kernel_abs_le (e : ℕ) : |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e| ≤ e + 1 := by
  have h1 : (digitSum 2 (e + 1) : ℝ) ≤ e + 1 := by
    exact_mod_cast digitSum_le_self (le_refl 2) (e + 1)
  have h2 : (digitSum 2 e : ℝ) ≤ e := by exact_mod_cast digitSum_le_self (le_refl 2) e
  have h3 : (0 : ℝ) ≤ digitSum 2 e := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ digitSum 2 (e + 1) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

private theorem kernel_value_le (e : ℕ) :
    (digitSum 2 (e + 1) : ℝ) - digitSum 2 e ≤
      (if Even e then 1 else 0) - (if e = 3 then 1 else 0) - (if e = 7 then 2 else 0) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' e
  · rw [digitSum_mul_add (le_refl 2) j 1 (by norm_num), digitSum_mul_base (le_refl 2),
      ite_eq_left (even_two_mul j), ite_eq_right (by omega), ite_eq_right (by omega)]
    push_cast
    linarith
  · have hodd : ¬ Even (2 * j + 1) := Nat.not_even_two_mul_add_one j
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, digitSum_mul_base (le_refl 2),
      digitSum_mul_add (le_refl 2) j 1 (by norm_num), ite_eq_right hodd]
    by_cases h3 : j = 1
    · subst h3
      norm_num [digitSum_two_one, digitSum_two_two]
    · by_cases h7 : j = 3
      · subst h7
        norm_num [digitSum_two_three, digitSum_two_four]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        have h := digitSum_add_le 2 j 1 (le_refl 2)
        rw [digitSum_two_one] at h
        have h' : (digitSum 2 (j + 1) : ℝ) ≤ digitSum 2 j + 1 := by exact_mod_cast h
        push_cast
        linarith

private theorem summable_bounded_mul_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {a : ℕ → ℝ}
    {K : ℝ} (ha : ∀ e, |a e| ≤ K) : Summable fun e => a e * x ^ e := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hx0 hx1).mul_left K)
    (fun e => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 e)]
  exact mul_le_mul_of_nonneg_right (ha e) (pow_nonneg hx0 e)

private theorem summable_linear_mul_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {a : ℕ → ℝ}
    (ha : ∀ e, |a e| ≤ e + 1) : Summable fun e => a e * x ^ e := by
  have hn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h2 := summable_geometric_of_lt_one hx0 hx1
  refine Summable.of_norm_bounded (h1.add h2) (fun e => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 e), pow_one]
  calc |a e| * x ^ e ≤ ((e : ℝ) + 1) * x ^ e :=
        mul_le_mul_of_nonneg_right (ha e) (pow_nonneg hx0 e)
    _ = (e : ℝ) * x ^ e + x ^ e := by ring

private theorem tsum_even_indicator {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' e : ℕ, (if Even e then (1 : ℝ) else 0) * x ^ e = (1 - x ^ 2)⁻¹ := by
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hs : Summable fun e : ℕ => (if Even e then (1 : ℝ) else 0) * x ^ e :=
    summable_bounded_mul_pow hx0 hx1 (K := 1) (fun e => by split_ifs <;> simp)
  rw [← tsum_even_add_odd (f := fun e : ℕ => (if Even e then (1 : ℝ) else 0) * x ^ e)
    (hs.comp_injective (fun a b h => by simpa using h))
    (hs.comp_injective (fun a b h => by simpa using h))]
  have h1 : ∀ k : ℕ, (if Even (2 * k) then (1 : ℝ) else 0) * x ^ (2 * k) = (x ^ 2) ^ k := by
    intro k
    rw [ite_eq_left (even_two_mul k), one_mul, pow_mul]
  have h2 : ∀ k : ℕ, (if Even (2 * k + 1) then (1 : ℝ) else 0) * x ^ (2 * k + 1) = 0 := by
    intro k
    rw [ite_eq_right (Nat.not_even_two_mul_add_one k), zero_mul]
  simp_rw [h1, h2, tsum_zero, add_zero]
  exact tsum_geometric_of_lt_one (by positivity) hx2

/-- Local upper bound `L(p) ≤ (1 - p⁻²)⁻¹ - p⁻³ - 2 p⁻⁷` for the kernel's local factor. -/
private theorem local_kernel_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' e : ℕ, ((digitSum 2 (e + 1) : ℝ) - digitSum 2 e) * x ^ e ≤
      (1 - x ^ 2)⁻¹ - x ^ 3 - 2 * x ^ 7 := by
  have hsA : Summable fun e : ℕ => ((digitSum 2 (e + 1) : ℝ) - digitSum 2 e) * x ^ e :=
    summable_linear_mul_pow hx0 hx1 kernel_abs_le
  have hsE : Summable fun e : ℕ => (if Even e then (1 : ℝ) else 0) * x ^ e :=
    summable_bounded_mul_pow hx0 hx1 (K := 1) (fun e => by split_ifs <;> simp)
  have hs3 : Summable fun e : ℕ => (if e = 3 then (1 : ℝ) else 0) * x ^ e :=
    summable_bounded_mul_pow hx0 hx1 (K := 1) (fun e => by split_ifs <;> simp)
  have hs7 : Summable fun e : ℕ => (if e = 7 then (2 : ℝ) else 0) * x ^ e :=
    summable_bounded_mul_pow hx0 hx1 (K := 2) (fun e => by split_ifs <;> simp)
  have h3 : ∑' e : ℕ, (if e = 3 then (1 : ℝ) else 0) * x ^ e = x ^ 3 := by
    simp_rw [ite_mul, one_mul, zero_mul]
    exact tsum_ite_eq 3 (fun e => x ^ e)
  have h7 : ∑' e : ℕ, (if e = 7 then (2 : ℝ) else 0) * x ^ e = 2 * x ^ 7 := by
    simp_rw [ite_mul, zero_mul]
    exact tsum_ite_eq 7 (fun e => 2 * x ^ e)
  calc ∑' e : ℕ, ((digitSum 2 (e + 1) : ℝ) - digitSum 2 e) * x ^ e
      ≤ ∑' e : ℕ, ((if Even e then (1 : ℝ) else 0) * x ^ e -
          (if e = 3 then (1 : ℝ) else 0) * x ^ e - (if e = 7 then (2 : ℝ) else 0) * x ^ e) := by
        refine hsA.tsum_le_tsum (fun e => ?_) ((hsE.sub hs3).sub hs7)
        rw [← sub_mul, ← sub_mul]
        exact mul_le_mul_of_nonneg_right (kernel_value_le e) (pow_nonneg hx0 e)
    _ = (1 - x ^ 2)⁻¹ - x ^ 3 - 2 * x ^ 7 := by
        rw [(hsE.sub hs3).tsum_sub hs7, hsE.tsum_sub hs3, tsum_even_indicator hx0 hx1, h3, h7]

/-- The kernel's local factor equals `(1 - x) ∑ s₂(e + 1) x^e`; in particular it is `≥ 0`. -/
private theorem local_kernel_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ ∑' e : ℕ, ((digitSum 2 (e + 1) : ℝ) - digitSum 2 e) * x ^ e := by
  have hs := summable_digitSum_mul_pow hx0 hx1
  have hs1 : Summable fun e : ℕ => (digitSum 2 (e + 1) : ℝ) * x ^ e :=
    summable_linear_mul_pow hx0 hx1 (fun e => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast digitSum_le_self (le_refl 2) (e + 1))
  have hA : 0 ≤ ∑' e : ℕ, (digitSum 2 (e + 1) : ℝ) * x ^ e :=
    tsum_nonneg (fun e => by positivity)
  have heq : ∑' e : ℕ, ((digitSum 2 (e + 1) : ℝ) - digitSum 2 e) * x ^ e =
      (1 - x) * ∑' e : ℕ, (digitSum 2 (e + 1) : ℝ) * x ^ e := by
    simp_rw [sub_mul]
    rw [hs1.tsum_sub hs, hs.tsum_eq_zero_add]
    simp only [digitSum_zero, Nat.cast_zero, zero_mul, zero_add]
    have : ∑' e : ℕ, (digitSum 2 (e + 1) : ℝ) * x ^ (e + 1) =
        x * ∑' e : ℕ, (digitSum 2 (e + 1) : ℝ) * x ^ e := by
      rw [← tsum_mul_left]
      congr 1
      ext e
      ring
    rw [this]
    ring
  rw [heq]
  exact mul_nonneg (by linarith) hA

private theorem local_abs_kernel_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    ∑' e : ℕ, |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e| * x ^ e ≤ 1 + 16 * x ^ 2 := by
  have hx1 : x < 1 := by linarith
  have hs : Summable fun e : ℕ => |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e| * x ^ e :=
    summable_linear_mul_pow hx0 hx1 (fun e => by rw [abs_abs]; exact kernel_abs_le e)
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hg1 : Summable fun e : ℕ => (e : ℝ) * (1 / 2 : ℝ) ^ e := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hhalf
  have hg2 : Summable fun e : ℕ => (1 / 2 : ℝ) ^ e :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hd0 : Summable fun e : ℕ => (if e = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq 0 1).summable
  have hd : Summable fun e : ℕ => (if e = 0 then (1 : ℝ) else 0) +
      4 * x ^ 2 * ((e : ℝ) * (1 / 2 : ℝ) ^ e + (1 / 2 : ℝ) ^ e) :=
    hd0.add ((hg1.add hg2).mul_left (4 * x ^ 2))
  have hle : ∀ e : ℕ, |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e| * x ^ e ≤
      (if e = 0 then (1 : ℝ) else 0) + 4 * x ^ 2 * ((e : ℝ) * (1 / 2 : ℝ) ^ e + (1 / 2 : ℝ) ^ e) := by
    intro e
    by_cases he : 2 ≤ e
    · obtain ⟨e, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
      have hk := kernel_abs_le (e + 2)
      have hxe : x ^ e ≤ (1 / 2 : ℝ) ^ e := pow_le_pow_left₀ hx0 hx e
      have hpow : x ^ (e + 2) ≤ 4 * x ^ 2 * (1 / 2 : ℝ) ^ (e + 2) := by
        have e1 : x ^ (e + 2) = x ^ 2 * x ^ e := by ring
        have e2 : 4 * x ^ 2 * (1 / 2 : ℝ) ^ (e + 2) = x ^ 2 * (1 / 2 : ℝ) ^ e := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left hxe (by positivity)
      rw [ite_eq_right (by omega), zero_add]
      calc |(digitSum 2 (e + 2 + 1) : ℝ) - digitSum 2 (e + 2)| * x ^ (e + 2)
          ≤ (((e + 2 : ℕ) : ℝ) + 1) * (4 * x ^ 2 * (1 / 2 : ℝ) ^ (e + 2)) :=
            mul_le_mul hk hpow (pow_nonneg hx0 _) (by positivity)
        _ = 4 * x ^ 2 * (((e + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (e + 2) + (1 / 2 : ℝ) ^ (e + 2)) := by
            ring
    · have he' : e < 2 := by omega
      interval_cases e
      · norm_num [digitSum_two_one]
        nlinarith [sq_nonneg x]
      · norm_num [digitSum_two_one, digitSum_two_two]
        nlinarith [sq_nonneg x]
  calc ∑' e : ℕ, |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e| * x ^ e
      ≤ ∑' e : ℕ, ((if e = 0 then (1 : ℝ) else 0) +
          4 * x ^ 2 * ((e : ℝ) * (1 / 2 : ℝ) ^ e + (1 / 2 : ℝ) ^ e)) := hs.tsum_le_tsum hle hd
    _ = 1 + 16 * x ^ 2 := by
        rw [hd0.tsum_add ((hg1.add hg2).mul_left (4 * x ^ 2)), (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq,
          tsum_mul_left, hg1.tsum_add hg2, tsum_coe_mul_geometric_of_norm_lt_one hhalf,
          tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
        ring

private theorem kernel_div_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    tauDigitKernel (p ^ e) / ((p ^ e : ℕ) : ℝ) =
      ((digitSum 2 (e + 1) : ℝ) - digitSum 2 e) * ((p : ℝ)⁻¹) ^ e := by
  rw [tauDigitKernel_prime_pow hp, Nat.cast_pow, inv_pow, div_eq_mul_inv]

private theorem abs_kernel_div_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    |tauDigitKernel (p ^ e)| / ((p ^ e : ℕ) : ℝ) =
      |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e| * ((p : ℝ)⁻¹) ^ e := by
  rw [tauDigitKernel_prime_pow hp, Nat.cast_pow, inv_pow, div_eq_mul_inv]

private theorem prime_inv_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine ⟨by positivity, ?_⟩
  rw [one_div]
  exact inv_anti₀ (by norm_num) h2

/-- **Summability hypothesis of L13 for the digit-sum majorant:** `∑ |h(n)|/n < ∞`. -/
theorem summable_abs_tauDigitKernel_div :
    Summable fun n : ℕ => |tauDigitKernel n| / n := by
  set f : ℕ → ℝ := fun n => |tauDigitKernel n| / n with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf00 : f 0 = 0 := by simp [hfdef]
  have hf1 : f 1 = 1 := by simp [hfdef, tauDigitKernel_isMultiplicative.map_one]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hfdef, tauDigitKernel_isMultiplicative.map_mul_of_coprime hmn, abs_mul,
      Nat.cast_mul]
    rw [mul_div_mul_comm]
  have hloc : ∀ {p : ℕ}, p.Prime → Summable fun e : ℕ => ‖f (p ^ e)‖ := by
    intro p hp
    obtain ⟨hx0, hxh⟩ := prime_inv_bounds hp
    refine (summable_linear_mul_pow hx0 (by linarith)
      (a := fun e => |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e|)
      (fun e => by rw [abs_abs]; exact kernel_abs_le e)).congr (fun e => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _), hfdef]
    exact (abs_kernel_div_prime_pow hp e).symm
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 (by norm_num)
  refine summable_of_sum_range_le hf0 (c := Real.exp (16 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2))
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
      ∏ p ∈ N.primesBelow, (1 + 16 * ((p : ℝ)⁻¹) ^ 2) := by
    refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg (fun e => hf0 _)) (fun p hp => ?_)
    have hpp := (Nat.mem_primesBelow.mp hp).2
    obtain ⟨hx0, hxh⟩ := prime_inv_bounds hpp
    have heq : ∑' e : ℕ, f (p ^ e) =
        ∑' e : ℕ, |(digitSum 2 (e + 1) : ℝ) - digitSum 2 e| * ((p : ℝ)⁻¹) ^ e :=
      tsum_congr (fun e => abs_kernel_div_prime_pow hpp e)
    rw [heq]
    exact local_abs_kernel_le hx0 hxh
  have h3 : ∏ p ∈ N.primesBelow, (1 + 16 * ((p : ℝ)⁻¹) ^ 2) ≤
      Real.exp (∑ p ∈ N.primesBelow, 16 * ((p : ℝ)⁻¹) ^ 2) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
    linarith [Real.add_one_le_exp (16 * ((p : ℝ)⁻¹) ^ 2)]
  have h4 : ∑ p ∈ N.primesBelow, 16 * ((p : ℝ)⁻¹) ^ 2 ≤ 16 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
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
    _ ≤ ∏ p ∈ N.primesBelow, (1 + 16 * ((p : ℝ)⁻¹) ^ 2) := h2
    _ ≤ Real.exp (∑ p ∈ N.primesBelow, 16 * ((p : ℝ)⁻¹) ^ 2) := h3
    _ ≤ Real.exp (16 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := Real.exp_le_exp.mpr h4

private theorem prod_one_add_mul_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
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

private theorem sum_Ico_inv_sq_le (M P : ℕ) (hM : 2 ≤ M) :
    ∑ n ∈ Ico M P, 1 / (n : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  suffices H : ∀ P, M ≤ P →
      ∑ n ∈ Ico M P, 1 / (n : ℝ) ^ 2 + 1 / ((P : ℝ) - 1) ≤ 1 / ((M : ℝ) - 1) by
    rcases le_or_gt P M with hPM | hMP
    · rw [Finset.Ico_eq_empty_of_le hPM, sum_empty]
      exact div_nonneg zero_le_one (by linarith)
    · have h := H P hMP.le
      have hP : (2 : ℝ) ≤ P := by exact_mod_cast (hM.trans hMP.le)
      have : 0 ≤ 1 / ((P : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
      linarith
  intro P hP
  induction P, hP using Nat.le_induction with
  | base => simp
  | succ P hMP ih =>
    rw [Finset.sum_Ico_succ_top hMP]
    have hP2 : (2 : ℝ) ≤ P := le_trans hM' (by exact_mod_cast hMP)
    have hP0 : (P : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < P).ne'
    have hPpos : (0 : ℝ) < P := by linarith
    have key : 1 / (P : ℝ) ^ 2 + 1 / (((P + 1 : ℕ) : ℝ) - 1) ≤ 1 / ((P : ℝ) - 1) := by
      rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, div_add_div _ _ (pow_ne_zero 2 hP0) hP0,
        div_le_div_iff₀ (mul_pos (pow_pos hPpos 2) hPpos) (by linarith)]
      nlinarith
    linarith

/-- The explicit local bound `B(p) = (1 - p⁻²)⁻¹ - p⁻³ - 2p⁻⁷`. -/
private noncomputable def localBound (p : ℕ) : ℝ :=
  (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹ - ((p : ℝ)⁻¹) ^ 3 - 2 * ((p : ℝ)⁻¹) ^ 7

private theorem localBound_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    1 ≤ (1 - x ^ 2)⁻¹ - x ^ 3 - 2 * x ^ 7 ∧ (1 - x ^ 2)⁻¹ - x ^ 3 - 2 * x ^ 7 ≤ 1 + x ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hq0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hpos : 0 < 1 - x ^ 2 := by linarith
  have hinv1 : 1 + x ^ 2 ≤ (1 - x ^ 2)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpos]
    nlinarith [mul_nonneg hq0 hq0]
  have hx3 : x ^ 3 ≤ x ^ 2 / 2 := by
    have : x ^ 3 = x ^ 2 * x := by ring
    rw [this]
    nlinarith
  have hx5 : x ^ 5 ≤ 1 / 32 := by
    have := pow_le_pow_left₀ hx0 hx 5
    norm_num at this
    linarith
  have hx7 : x ^ 7 ≤ x ^ 2 / 32 := by
    have : x ^ 7 = x ^ 2 * x ^ 5 := by ring
    rw [this]
    nlinarith
  have hinv2 : (1 - x ^ 2)⁻¹ ≤ 1 + x ^ 2 + x ^ 3 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    have h1 : 0 ≤ 1 - x - x ^ 2 := by nlinarith
    have h2 : 0 ≤ x ^ 3 * (1 - x - x ^ 2) := mul_nonneg (pow_nonneg hx0 3) h1
    nlinarith
  have h7 : 0 ≤ x ^ 7 := pow_nonneg hx0 7
  constructor <;> linarith

/-- **The mean of the majorant:** `C = ∑ h(n)/n ≤ 29/20`, from the Euler product
`C = ∏_p L(p)`, the local bounds `0 ≤ L(p) ≤ (1 - p⁻²)⁻¹ - p⁻³ - 2p⁻⁷` and
`∑_{n ≥ 37} n⁻² ≤ 1/36`. -/
theorem tsum_tauDigitKernel_div_le : ∑' n : ℕ, tauDigitKernel n / n ≤ 29 / 20 := by
  set f : ℕ → ℝ := fun n => tauDigitKernel n / n with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hf1 : f 1 = 1 := by simp [hfdef, tauDigitKernel_isMultiplicative.map_one]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hfdef, tauDigitKernel_isMultiplicative.map_mul_of_coprime hmn, Nat.cast_mul]
    rw [mul_div_mul_comm]
  have hsum : Summable fun n : ℕ => ‖f n‖ := by
    refine summable_abs_tauDigitKernel_div.congr (fun n => ?_)
    simp only [hfdef, Real.norm_eq_abs, abs_div, Nat.abs_cast]
  have hE := EulerProduct.eulerProduct hf1 hmul hsum hf0
  refine le_of_tendsto' hE (fun P => ?_)
  set T : Finset ℕ := Nat.primesBelow 37 with hT
  have hloc : ∀ p ∈ P.primesBelow ∪ T, 0 ≤ ∑' e : ℕ, f (p ^ e) ∧
      ∑' e : ℕ, f (p ^ e) ≤ localBound p ∧ 1 ≤ localBound p ∧
      localBound p ≤ 1 + ((p : ℝ)⁻¹) ^ 2 := by
    intro p hp
    have hpp : p.Prime := by
      rcases mem_union.mp hp with h | h
      · exact (Nat.mem_primesBelow.mp h).2
      · exact (Nat.mem_primesBelow.mp h).2
    obtain ⟨hx0, hxh⟩ := prime_inv_bounds hpp
    have heq : ∑' e : ℕ, f (p ^ e) =
        ∑' e : ℕ, ((digitSum 2 (e + 1) : ℝ) - digitSum 2 e) * ((p : ℝ)⁻¹) ^ e :=
      tsum_congr (fun e => kernel_div_prime_pow hpp e)
    rw [heq]
    exact ⟨local_kernel_nonneg hx0 (by linarith), local_kernel_le hx0 (by linarith),
      localBound_bounds hx0 hxh⟩
  have hTval : ∏ p ∈ T, localBound p ≤ 1.3958 := by
    rw [hT, show Nat.primesBelow 37 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} by decide]
    simp only [localBound]
    norm_num
  have hsplit : ∏ p ∈ P.primesBelow, ∑' e : ℕ, f (p ^ e) ≤
      (∏ p ∈ T, localBound p) * ∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2) := by
    calc ∏ p ∈ P.primesBelow, ∑' e : ℕ, f (p ^ e)
        ≤ ∏ p ∈ P.primesBelow, localBound p :=
          Finset.prod_le_prod₀ (fun p hp => (hloc p (mem_union_left _ hp)).1)
            (fun p hp => (hloc p (mem_union_left _ hp)).2.1)
      _ ≤ ∏ p ∈ T ∪ P.primesBelow \ T, localBound p := by
          rw [Finset.union_sdiff_self_eq_union]
          refine Finset.prod_le_prod_of_subset_of_one_le₀ Finset.subset_union_right
            (fun p hp => le_trans zero_le_one (hloc p (mem_union_left _ hp)).2.2.1)
            (fun p hp _ => (hloc p (by rwa [Finset.union_comm])).2.2.1)
      _ = (∏ p ∈ T, localBound p) * ∏ p ∈ P.primesBelow \ T, localBound p :=
          Finset.prod_union Finset.disjoint_sdiff
      _ ≤ (∏ p ∈ T, localBound p) * ∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
            (fun p hp => le_trans zero_le_one
              (hloc p (mem_union_left _ (mem_sdiff.mp hp).1)).2.2.1)
            (fun p hp => (hloc p (mem_union_left _ (mem_sdiff.mp hp).1)).2.2.2)) ?_
          exact Finset.prod_nonneg (fun p hp => le_trans zero_le_one
            (hloc p (mem_union_right _ hp)).2.2.1)
  have hsub : P.primesBelow \ T ⊆ Ico 37 P := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_sdiff.mp hp
    obtain ⟨hpP, hpp⟩ := Nat.mem_primesBelow.mp hp1
    have h37 : 37 ≤ p := by
      by_contra hlt
      exact hp2 (Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩)
    exact mem_Ico.mpr ⟨h37, hpP⟩
  have hsum_tail : ∑ p ∈ P.primesBelow \ T, ((p : ℝ)⁻¹) ^ 2 ≤ 1 / 36 := by
    calc ∑ p ∈ P.primesBelow \ T, ((p : ℝ)⁻¹) ^ 2
        = ∑ p ∈ P.primesBelow \ T, 1 / (p : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun p _ => by rw [inv_pow, one_div])
      _ ≤ ∑ n ∈ Ico 37 P, 1 / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      _ ≤ 1 / ((37 : ℕ) - 1 : ℝ) := sum_Ico_inv_sq_le 37 P (by norm_num)
      _ = 1 / 36 := by norm_num
  have htail : ∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2) ≤ 36 / 35 := by
    have h := prod_one_add_mul_le (P.primesBelow \ T) (fun p => ((p : ℝ)⁻¹) ^ 2)
      (fun p _ => by positivity)
    have hpos : (0 : ℝ) < 1 - ∑ p ∈ P.primesBelow \ T, ((p : ℝ)⁻¹) ^ 2 := by linarith
    have hP0 : 0 ≤ ∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2) :=
      Finset.prod_nonneg (fun p _ => by positivity)
    have h' : (∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2)) * (35 / 36) ≤ 1 := by
      calc (∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2)) * (35 / 36)
          ≤ (∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2)) *
              (1 - ∑ p ∈ P.primesBelow \ T, ((p : ℝ)⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hP0
        _ ≤ 1 := h
    linarith
  have hT0 : 0 ≤ ∏ p ∈ T, localBound p :=
    Finset.prod_nonneg (fun p hp => le_trans zero_le_one (hloc p (mem_union_right _ hp)).2.2.1)
  calc ∏ p ∈ P.primesBelow, ∑' e : ℕ, f (p ^ e)
      ≤ (∏ p ∈ T, localBound p) * ∏ p ∈ P.primesBelow \ T, (1 + ((p : ℝ)⁻¹) ^ 2) := hsplit
    _ ≤ 1.3958 * (36 / 35) := mul_le_mul hTval htail (Finset.prod_nonneg (fun p _ => by positivity))
        (by norm_num)
    _ ≤ 29 / 20 := by norm_num

/-! ### Part 8 (L15): unconditional simple nonnormality of `E(2^k)` for `k ≥ 3` -/

/-- The Erdős–Borwein-type Lambert sum `E(2^k) = ∑_{m ≥ 1} 1/(2^{km} - 1)`. -/
noncomputable def erdosBorweinPow (k : ℕ) : ℝ := ∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) - 1)

private theorem summable_tau_div {k : ℕ} (hk : 1 ≤ k) :
    Summable fun n : ℕ => (n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have h1 : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (k * n) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  calc (n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n) ≤ (n.divisors.card : ℝ) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h2
    _ ≤ (n : ℝ) / (2 : ℝ) ^ n := div_le_div_of_nonneg_right h1 (by positivity)
    _ = (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n := by rw [pow_one, one_div_pow, mul_one_div]

/-- Lambert-to-divisor expansion `E(2^k) = ∑_{n ≥ 1} τ(n) 2^{-kn}`. -/
theorem erdosBorweinPow_eq_divisor_series {k : ℕ} (hk : 1 ≤ k) :
    erdosBorweinPow k = ∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (k * (n + 1)) := by
  have hterm : ∀ m : ℕ, (1 : ℝ) / (2 ^ (k * (m + 1)) - 1) =
      ∑' j : ℕ, (1 : ℝ) / (2 : ℝ) ^ (k * ((m + 1) * (j + 1))) := by
    intro m
    set r : ℝ := ((2 : ℝ) ^ (k * (m + 1)))⁻¹ with hr
    have hbig : (1 : ℝ) < (2 : ℝ) ^ (k * (m + 1)) := one_lt_pow₀ (by norm_num) (by positivity)
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hbig
    have hts : ∑' j : ℕ, (1 : ℝ) / (2 : ℝ) ^ (k * ((m + 1) * (j + 1))) = r * ∑' j : ℕ, r ^ j := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun j => ?_)
      have e : (2 : ℝ) ^ (k * ((m + 1) * (j + 1))) = ((2 : ℝ) ^ (k * (m + 1))) ^ (j + 1) := by
        rw [← pow_mul]
        congr 1
        ring
      rw [e, hr, ← pow_succ', inv_pow, one_div]
    rw [hts, tsum_geometric_of_lt_one hr0 hr1, hr]
    have hne : (2 : ℝ) ^ (k * (m + 1)) ≠ 0 := by positivity
    have hsub : (2 : ℝ) ^ (k * (m + 1)) - 1 ≠ 0 := by linarith
    field_simp
  let g : ℕ × ℕ → ℝ := fun p => (1 : ℝ) / (2 : ℝ) ^ (k * ((p.1 + 1) * (p.2 + 1)))
  let φ : ℕ × ℕ → ℕ := fun p => (p.1 + 1) * (p.2 + 1)
  have hfiber_fin : ∀ n : ℕ, ∃ s : Finset (ℕ × ℕ), (∀ p, p ∈ s ↔ φ p = n) ∧
      s.card = n.divisors.card := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨∅, fun p => ?_, by simp⟩
      simp only [Finset.notMem_empty, false_iff, φ]
      exact (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)).ne'
    · refine ⟨n.divisors.image (fun d => (d - 1, n / d - 1)), fun p => ?_, ?_⟩
      · constructor
        · intro hp
          obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
          obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hd
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
          have hq_pos : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd_pos
          simp only [φ, Nat.sub_add_cancel hd_pos, Nat.sub_add_cancel hq_pos]
          exact Nat.mul_div_cancel' hdn
        · intro hφ
          have hφ' : (p.1 + 1) * (p.2 + 1) = n := hφ
          refine mem_image.mpr ⟨p.1 + 1, Nat.mem_divisors.mpr ⟨⟨p.2 + 1, hφ'.symm⟩, hn.ne'⟩, ?_⟩
          have : n / (p.1 + 1) = p.2 + 1 := by
            rw [← hφ']
            exact Nat.mul_div_cancel_left _ (Nat.succ_pos _)
          ext <;> simp [this]
      · refine Finset.card_image_of_injOn (fun d₁ hd₁ d₂ hd₂ heq => ?_)
        have h1 : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
        have h2 : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
        have := congrArg Prod.fst heq
        simp only at this
        omega
  have hfiber_sum : ∀ n : ℕ, HasSum (fun p : {p : ℕ × ℕ // φ p = n} => g p.1)
      ((n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n)) := by
    intro n
    obtain ⟨s, hs_iff, hs_card⟩ := hfiber_fin n
    have hconst : ∀ p : {p : ℕ × ℕ // φ p = n}, g p.1 = (1 : ℝ) / (2 : ℝ) ^ (k * n) := by
      intro p
      simp only [g, ← p.2, φ]
    have hsub : {p : ℕ × ℕ // φ p = n} ≃ {p : ℕ × ℕ // p ∈ s} :=
      Equiv.subtypeEquivRight (fun p => (hs_iff p).symm)
    let _ : Fintype {p : ℕ × ℕ // φ p = n} := Fintype.ofEquiv _ hsub.symm
    have hcard : Fintype.card {p : ℕ × ℕ // φ p = n} = s.card := by
      rw [Fintype.card_congr hsub, Fintype.card_coe]
    have hval : ∑ p : {p : ℕ × ℕ // φ p = n}, g p.1 =
        (n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n) := by
      calc ∑ p : {p : ℕ × ℕ // φ p = n}, g p.1
          = ∑ _p : {p : ℕ × ℕ // φ p = n}, (1 : ℝ) / (2 : ℝ) ^ (k * n) :=
            Finset.sum_congr rfl (fun p _ => hconst p)
        _ = (s.card : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ (k * n)) := by simp [hcard]
        _ = (n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n) := by rw [hs_card, mul_one_div]
    rw [← hval]
    exact hasSum_fintype _
  have hsum_g : Summable g := by
    have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hprod : Summable (fun p : ℕ × ℕ => (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2) :=
      hgeom.mul_of_nonneg hgeom (fun _ => by positivity) (fun _ => by positivity)
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hprod
    have hge : p.1 + p.2 ≤ k * ((p.1 + 1) * (p.2 + 1)) := by
      have h1 : (p.1 + 1) * (p.2 + 1) ≤ k * ((p.1 + 1) * (p.2 + 1)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have h2 : p.1 + p.2 ≤ (p.1 + 1) * (p.2 + 1) := by ring_nf; omega
      omega
    simp only [g]
    rw [← pow_add, ← one_div_pow]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hge
  have hL : erdosBorweinPow k = ∑' p : ℕ × ℕ, g p := by
    unfold erdosBorweinPow
    simp_rw [hterm]
    have hrow : ∀ m : ℕ, Summable (fun j : ℕ => g (m, j)) := fun m =>
      hsum_g.comp_injective (fun j₁ j₂ h => congrArg Prod.snd h)
    exact (hsum_g.tsum_prod' hrow).symm
  have hR : ∑' p : ℕ × ℕ, g p = ∑' n : ℕ, (n.divisors.card : ℝ) / (2 : ℝ) ^ (k * n) := by
    have hcomp : Summable (g ∘ Equiv.sigmaFiberEquiv φ) :=
      (Equiv.sigmaFiberEquiv φ).summable_iff.mpr hsum_g
    rw [← (Equiv.sigmaFiberEquiv φ).tsum_eq g]
    change ∑' p : (n : ℕ) × {x : ℕ × ℕ // φ x = n}, (g ∘ Equiv.sigmaFiberEquiv φ) p = _
    rw [hcomp.tsum_sigma' (fun n => (hfiber_sum n).summable)]
    exact tsum_congr (fun n => (hfiber_sum n).tsum_eq)
  rw [hL, hR, (summable_tau_div hk).tsum_eq_zero_add]
  simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, zero_div, zero_add]

private theorem summable_divisor_series {k : ℕ} (hk : 1 ≤ k) :
    Summable fun n : ℕ => ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (k * (n + 1)) :=
  (summable_tau_div hk).comp_injective Nat.succ_injective

private theorem erdosBorweinPow_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ erdosBorweinPow k := by
  rw [erdosBorweinPow_eq_divisor_series hk]
  exact tsum_nonneg (fun n => by positivity)

private theorem floor_two_pow_succ {y : ℝ} (hy : 0 ≤ y) (i : ℕ) :
    ⌊(2 : ℝ) ^ (i + 1) * y⌋₊ =
      2 * ⌊(2 : ℝ) ^ i * y⌋₊ + (if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ i * y) then 1 else 0) := by
  have hz0 : 0 ≤ (2 : ℝ) ^ i * y := by positivity
  have hfl : ((⌊(2 : ℝ) ^ i * y⌋₊ : ℕ) : ℝ) = (⌊(2 : ℝ) ^ i * y⌋ : ℝ) := by
    have := Int.natCast_floor_eq_floor hz0
    exact_mod_cast this
  have hf0 := Int.fract_nonneg ((2 : ℝ) ^ i * y)
  have hf1 := Int.fract_lt_one ((2 : ℝ) ^ i * y)
  have hdecomp : (2 : ℝ) ^ (i + 1) * y =
      2 * Int.fract ((2 : ℝ) ^ i * y) + ((2 * ⌊(2 : ℝ) ^ i * y⌋₊ : ℕ) : ℝ) := by
    have h2z : (2 : ℝ) ^ (i + 1) * y = 2 * ((2 : ℝ) ^ i * y) := by rw [pow_succ]; ring
    rw [h2z, Nat.cast_mul, hfl]
    have := Int.fract_add_floor ((2 : ℝ) ^ i * y)
    push_cast
    linarith
  rw [hdecomp, Nat.floor_add_natCast (by linarith)]
  split_ifs with h
  · have : ⌊2 * Int.fract ((2 : ℝ) ^ i * y)⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      push_cast
      constructor <;> linarith
    rw [this]
    ring
  · have : ⌊2 * Int.fract ((2 : ℝ) ^ i * y)⌋₊ = 0 := by
      rw [Nat.floor_eq_zero]
      linarith [not_le.mp h]
    rw [this]
    ring

private theorem digitSum_floor_pow_eq {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    digitSum 2 ⌊(2 : ℝ) ^ N * y⌋₊ = digitSum 2 ⌊y⌋₊ +
      ∑ i ∈ range N, (if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ i * y) then 1 else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [floor_two_pow_succ hy N, digitSum_mul_add (le_refl 2) _ _ (by split_ifs <;> norm_num),
      ih, sum_range_succ]
    ring

private theorem frequency_half_eq (x : ℝ) (N : ℕ) :
    frequency (shift 2 x) (1 / 2) 1 N =
      ((∑ t ∈ range N, if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * x) then 1 else 0 : ℕ) : ℝ) / N := by
  unfold frequency
  congr 2
  rw [card_filter]
  refine sum_congr rfl (fun t _ => ?_)
  have h1 : shift 2 x t = Int.fract ((2 : ℝ) ^ t * x) := by simp [shift]
  have h2 := (shift_mem 2 x t).2
  rw [h1] at h2 ⊢
  by_cases h : 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * x)
  · rw [ite_eq_left ⟨h, h2⟩, ite_eq_left h]
  · rw [ite_eq_right (fun hh => h hh.1), ite_eq_right h]

private theorem digitSum_two_le_log (T : ℕ) : digitSum 2 T ≤ Nat.log 2 T + 1 := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  rcases Nat.lt_or_ge T 2 with hT | hT
  · interval_cases T <;> simp [digitSum_two_one]
  · rw [digitSum_eq (le_refl 2)]
    have h1 := ih (T / 2) (Nat.div_lt_self (by omega) (by norm_num))
    have h2 : Nat.log 2 (T / 2) = Nat.log 2 T - 1 := Nat.log_div_base 2 T
    have h3 : 0 < Nat.log 2 T := Nat.log_pos (by norm_num) hT
    have h4 := Nat.mod_lt T (show 2 > 0 by norm_num)
    omega

/-- The carry tail `τ_N = ∑_{m ≥ 0} τ(M + 1 + m) 2^N / 2^{k(M + 1 + m)}`, `M = ⌊N/k⌋`. -/
private noncomputable def ebTail (k N : ℕ) : ℝ :=
  ∑' m : ℕ, ((N / k + 1 + m).divisors.card : ℝ) * (2 : ℝ) ^ N / (2 : ℝ) ^ (k * (N / k + 1 + m))

private theorem ebTail_bounds {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    0 ≤ ebTail k N ∧ ebTail k N ≤ N + 2 := by
  unfold ebTail
  set M := N / k with hM
  have hkn : ∀ m : ℕ, N + (m + 1) ≤ k * (M + 1 + m) := by
    intro m
    have h1 : N < k * (M + 1) := Nat.lt_mul_div_succ N (by omega)
    have h2 : m ≤ k * m := Nat.le_mul_of_pos_left m (by omega)
    have : k * (M + 1 + m) = k * (M + 1) + k * m := by ring
    omega
  have hterm : ∀ m : ℕ, ((M + 1 + m).divisors.card : ℝ) * (2 : ℝ) ^ N /
      (2 : ℝ) ^ (k * (M + 1 + m)) ≤ ((M : ℝ) + 1 + m) * (1 / 2 : ℝ) ^ (m + 1) := by
    intro m
    have hτ : ((M + 1 + m).divisors.card : ℝ) ≤ (M : ℝ) + 1 + m := by
      exact_mod_cast Nat.card_divisors_le_self (M + 1 + m)
    have hpow : (2 : ℝ) ^ N / (2 : ℝ) ^ (k * (M + 1 + m)) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
      have hE : (2 : ℝ) ^ (N + (m + 1)) ≤ (2 : ℝ) ^ (k * (M + 1 + m)) :=
        pow_le_pow_right₀ (by norm_num) (hkn m)
      have h2 : (2 : ℝ) ^ (N + (m + 1)) = (2 : ℝ) ^ N * (2 : ℝ) ^ (m + 1) := pow_add _ _ _
      rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    rw [mul_div_assoc]
    exact mul_le_mul hτ hpow (by positivity) (by positivity)
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hg1 := summable_pow_mul_geometric_of_norm_lt_one 1 hhalf
  have hg2 : Summable fun m : ℕ => (1 / 2 : ℝ) ^ m :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hfun : (fun m : ℕ => ((M : ℝ) + 1 + m) * (1 / 2 : ℝ) ^ (m + 1)) =
      fun m : ℕ => ((M : ℝ) + 1) / 2 * (1 / 2 : ℝ) ^ m + 1 / 2 * ((m : ℝ) ^ 1 * (1 / 2 : ℝ) ^ m) := by
    ext m
    ring
  have hb : Summable fun m : ℕ => ((M : ℝ) + 1 + m) * (1 / 2 : ℝ) ^ (m + 1) := by
    rw [hfun]
    exact (hg2.mul_left _).add (hg1.mul_left _)
  have hbsum : ∑' m : ℕ, ((M : ℝ) + 1 + m) * (1 / 2 : ℝ) ^ (m + 1) = (M : ℝ) + 2 := by
    rw [hfun, (hg2.mul_left _).tsum_add (hg1.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    simp only [pow_one]
    rw [tsum_coe_mul_geometric_of_norm_lt_one hhalf]
    have e1 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have e2 : (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 := by norm_num
    rw [e1, e2]
    ring
  have hs : Summable fun m : ℕ => ((M + 1 + m).divisors.card : ℝ) * (2 : ℝ) ^ N /
      (2 : ℝ) ^ (k * (M + 1 + m)) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hterm hb
  refine ⟨tsum_nonneg (fun m => by positivity), ?_⟩
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N k
  calc ∑' m : ℕ, ((M + 1 + m).divisors.card : ℝ) * (2 : ℝ) ^ N / (2 : ℝ) ^ (k * (M + 1 + m))
      ≤ ∑' m : ℕ, ((M : ℝ) + 1 + m) * (1 / 2 : ℝ) ^ (m + 1) := hs.tsum_le_tsum hterm hb
    _ = (M : ℝ) + 2 := hbsum
    _ ≤ N + 2 := by linarith

private theorem erdosBorwein_floor_eq {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ⌊(2 : ℝ) ^ N * erdosBorweinPow k⌋₊ =
      (∑ n ∈ Icc 1 (N / k), n.divisors.card * 2 ^ (N - k * n)) + ⌊ebTail k N⌋₊ := by
  have hs : Summable fun n : ℕ =>
      |((((n + 1).divisors.card : ℕ) : ℤ) : ℝ)| / ((2 : ℕ) : ℝ) ^ (k * (n + 1)) :=
    (summable_divisor_series hk).congr (fun n => by simp)
  have h7 := floor_pow_mul_eq_head_add_floor_tail (b := 2) (k := k) (le_refl 2)
    (fun n => ((n.divisors.card : ℕ) : ℤ)) hs N
  simp only [Nat.cast_ofNat, Int.cast_natCast] at h7
  rw [← erdosBorweinPow_eq_divisor_series hk] at h7
  have hx0 : 0 ≤ (2 : ℝ) ^ N * erdosBorweinPow k :=
    mul_nonneg (by positivity) (erdosBorweinPow_nonneg hk)
  have htail0 := (ebTail_bounds hk N).1
  unfold ebTail at htail0 ⊢
  have key : ((⌊(2 : ℝ) ^ N * erdosBorweinPow k⌋₊ : ℕ) : ℤ) =
      (((∑ n ∈ Icc 1 (N / k), n.divisors.card * 2 ^ (N - k * n)) +
        ⌊∑' m : ℕ, ((N / k + 1 + m).divisors.card : ℝ) * (2 : ℝ) ^ N /
          (2 : ℝ) ^ (k * (N / k + 1 + m))⌋₊ : ℕ) : ℤ) := by
    rw [Int.natCast_floor_eq_floor hx0, h7]
    push_cast
    rw [Int.natCast_floor_eq_floor htail0]
  exact_mod_cast key

/-- Finite transfer: `N f₁(N) ≤ ∑_{n ≤ N/k} s₂(τ(n)) + ⌊log₂(N + 2)⌋ + 1`. -/
private theorem erdosBorwein_count_le {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    (∑ t ∈ range N, if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * erdosBorweinPow k) then 1 else 0) ≤
      ∑ n ∈ Icc 1 (N / k), digitSum 2 n.divisors.card + (Nat.log 2 (N + 2) + 1) := by
  have h1 := digitSum_floor_pow_eq (erdosBorweinPow_nonneg hk) N
  rw [erdosBorwein_floor_eq hk N] at h1
  have h2 : digitSum 2 ((∑ n ∈ Icc 1 (N / k), n.divisors.card * 2 ^ (N - k * n)) +
      ⌊ebTail k N⌋₊) ≤
      (∑ n ∈ Icc 1 (N / k), digitSum 2 n.divisors.card) + digitSum 2 ⌊ebTail k N⌋₊ :=
    digitSum_prefix_le (le_refl 2) (fun n => n.divisors.card) N _
  have hT : ⌊ebTail k N⌋₊ ≤ N + 2 :=
    Nat.floor_le_of_le (by push_cast; exact (ebTail_bounds hk N).2)
  have h3 := digitSum_two_le_log ⌊ebTail k N⌋₊
  have h4 : Nat.log 2 ⌊ebTail k N⌋₊ ≤ Nat.log 2 (N + 2) := Nat.log_mono_right hT
  omega

/-- The explicit upper envelope `(1/k) · avg_G(⌊N/k⌋) + (⌊log₂(N + 2)⌋ + 1)/N` of `f₁(N)`. -/
private noncomputable def ebEnvelope (k N : ℕ) : ℝ :=
  (1 / k) * ((∑ n ∈ Icc 1 (N / k), tauDigitMajorant n) / ((N / k : ℕ) : ℝ)) +
    ((Nat.log 2 (N + 2) + 1 : ℕ) : ℝ) / N

private theorem erdosBorwein_freq_le_envelope {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    frequency (shift 2 (erdosBorweinPow k)) (1 / 2) 1 N ≤ ebEnvelope k N := by
  rw [frequency_half_eq]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [ebEnvelope]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hc := erdosBorwein_count_le hk N
  have hS : 0 ≤ ∑ n ∈ Icc 1 (N / k), tauDigitMajorant n :=
    Finset.sum_nonneg (fun n _ => tauDigitMajorant_nonneg n)
  have hcR : ((∑ t ∈ range N,
      if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * erdosBorweinPow k) then 1 else 0 : ℕ) : ℝ) ≤
      ∑ n ∈ Icc 1 (N / k), tauDigitMajorant n + ((Nat.log 2 (N + 2) + 1 : ℕ) : ℝ) := by
    calc ((∑ t ∈ range N,
          if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * erdosBorweinPow k) then 1 else 0 : ℕ) : ℝ)
        ≤ ((∑ n ∈ Icc 1 (N / k), digitSum 2 n.divisors.card + (Nat.log 2 (N + 2) + 1) : ℕ) : ℝ) := by
          exact_mod_cast hc
      _ = ∑ n ∈ Icc 1 (N / k), (digitSum 2 n.divisors.card : ℝ) +
            ((Nat.log 2 (N + 2) + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ∑ n ∈ Icc 1 (N / k), tauDigitMajorant n + ((Nat.log 2 (N + 2) + 1 : ℕ) : ℝ) := by
          gcongr with n hn
          exact digitSum_card_divisors_le n
  have hmean : (∑ n ∈ Icc 1 (N / k), tauDigitMajorant n) / N ≤
      (1 / k) * ((∑ n ∈ Icc 1 (N / k), tauDigitMajorant n) / ((N / k : ℕ) : ℝ)) := by
    rcases Nat.eq_zero_or_pos (N / k) with h0 | hpos
    · rw [h0]
      simp
    · have hM : (0 : ℝ) < ((N / k : ℕ) : ℝ) := by exact_mod_cast hpos
      have hkM : ((N / k : ℕ) : ℝ) * k ≤ N := by
        have := Nat.mul_div_le N k
        rw [mul_comm] at this
        exact_mod_cast this
      have e : (1 / (k : ℝ)) * ((∑ n ∈ Icc 1 (N / k), tauDigitMajorant n) / ((N / k : ℕ) : ℝ)) =
          (∑ n ∈ Icc 1 (N / k), tauDigitMajorant n) / (((N / k : ℕ) : ℝ) * k) := by
        rw [one_div_mul_eq_div, div_div]
      rw [e]
      exact div_le_div_of_nonneg_left hS (mul_pos hM hkr) hkM
  have hstep := div_le_div_of_nonneg_right hcR hNr.le
  rw [add_div] at hstep
  unfold ebEnvelope
  linarith

private theorem tendsto_log_div :
    Tendsto (fun N : ℕ => ((Nat.log 2 (N + 2) + 1 : ℕ) : ℝ) / N) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hreal : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2) / N) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero
    have hg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    refine (h.comp hg).congr' (Eventually.of_forall (fun N => ?_))
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hup : Tendsto (fun N : ℕ => 1 / Real.log 2 * (Real.log ((N : ℝ) + 2) / N) + 1 / (N : ℝ))
      atTop (𝓝 0) := by
    have := (hreal.const_mul (1 / Real.log 2)).add hinv
    rwa [mul_zero, add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall (fun N => by positivity)) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : (Nat.log 2 (N + 2) : ℝ) ≤ Real.log ((N : ℝ) + 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    have h2 : (2 : ℝ) ^ Nat.log 2 (N + 2) ≤ (N : ℝ) + 2 := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N + 2 ≠ 0)
    have := (Real.pow_le_iff_le_log (by norm_num) (by positivity)).1 h2
    linarith
  have hstep : ((Nat.log 2 (N + 2) + 1 : ℕ) : ℝ) / N ≤
      (Real.log ((N : ℝ) + 2) / Real.log 2 + 1) / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    push_cast
    linarith
  have e : (Real.log ((N : ℝ) + 2) / Real.log 2 + 1) / N =
      1 / Real.log 2 * (Real.log ((N : ℝ) + 2) / N) + 1 / (N : ℝ) := by
    field_simp
  linarith

private theorem tendsto_ebEnvelope {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (ebEnvelope k) atTop (𝓝 ((1 / k) * ∑' n : ℕ, tauDigitKernel n / n)) := by
  have hmeanG : Tendsto (fun X : ℕ => (∑ n ∈ Icc 1 X, tauDigitMajorant n) / (X : ℝ)) atTop
      (𝓝 (∑' n : ℕ, tauDigitKernel n / n)) := by
    have := tendsto_average_of_summable_conv_mobius tauDigitMajorant (by
      rw [tauDigitMajorant_mul_moebius]
      exact summable_abs_tauDigitKernel_div)
    rwa [tauDigitMajorant_mul_moebius] at this
  have h1 := (hmeanG.comp (Nat.tendsto_div_const_atTop (show k ≠ 0 by omega))).const_mul
    (1 / (k : ℝ))
  have := h1.add tendsto_log_div
  rw [add_zero] at this
  exact this

/-- **L15 (Theorem 4.1(1)), unconditional.** For every `k ≥ 1`,
`limsup_N f₁(N; E(2^k), 2) ≤ 29/(20k)`, where `E(2^k) = ∑_{m ≥ 1} 1/(2^{km} - 1)`. -/
theorem erdosBorwein_two_pow_digitFreq_limsup_le (k : ℕ) (hk : 1 ≤ k) :
    Filter.limsup (fun N => frequency (shift 2 (∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) - 1)))
      (1 / 2) 1 N) Filter.atTop ≤ 29 / (20 * k) := by
  change Filter.limsup (fun N => frequency (shift 2 (erdosBorweinPow k)) (1 / 2) 1 N) atTop ≤ _
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hlim := tendsto_ebEnvelope hk
  calc Filter.limsup (fun N => frequency (shift 2 (erdosBorweinPow k)) (1 / 2) 1 N) atTop
      ≤ Filter.limsup (ebEnvelope k) atTop :=
        Filter.limsup_le_limsup (Eventually.of_forall (erdosBorwein_freq_le_envelope hk))
          (Filter.isCoboundedUnder_le_of_le atTop (fun N => (frequency_bounds _ _ _ N).1))
          hlim.isBoundedUnder_le
    _ = (1 / k) * ∑' n : ℕ, tauDigitKernel n / n := hlim.limsup_eq
    _ ≤ (1 / k) * (29 / 20) :=
        mul_le_mul_of_nonneg_left tsum_tauDigitKernel_div_le (by positivity)
    _ = 29 / (20 * k) := by field_simp

/-- Eventual lower bound for the binary discrepancy:
`D_N(E(2^k); 2) ≥ 1/2 - 29/(20k) - ε` for all large `N`. -/
theorem erdosBorwein_two_pow_radixDiscrepancy_eventually_ge (k : ℕ) (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, 1 / 2 - 29 / (20 * k) - ε ≤
      radixDiscrepancy 2 (∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) - 1)) N := by
  change ∀ᶠ N in atTop, 1 / 2 - 29 / (20 * k) - ε ≤ radixDiscrepancy 2 (erdosBorweinPow k) N
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hlim := tendsto_ebEnvelope hk
  have hval : (1 / k) * ∑' n : ℕ, tauDigitKernel n / n < 29 / (20 * k) + ε := by
    have h1 : (1 / (k : ℝ)) * ∑' n : ℕ, tauDigitKernel n / n ≤ (1 / k) * (29 / 20) :=
      mul_le_mul_of_nonneg_left tsum_tauDigitKernel_div_le (by positivity)
    have h2 : (1 / (k : ℝ)) * (29 / 20) = 29 / (20 * k) := by field_simp
    linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hval)] with N hN
  have h := radixDiscrepancy_ge_nonzero_freq 2 (le_refl 2) (erdosBorweinPow k) N
  simp only [Nat.cast_ofNat] at h
  have hf := erdosBorwein_freq_le_envelope hk N
  linarith

private theorem erdosBorwein_eventually_lt {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N in atTop, frequency (shift 2 (erdosBorweinPow k)) (1 / 2) 1 N < 59 / 120 := by
  have hk1 : 1 ≤ k := by omega
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hlim := tendsto_ebEnvelope hk1
  have hval : (1 / (k : ℝ)) * ∑' n : ℕ, tauDigitKernel n / n < 59 / 120 := by
    have h1 : (1 / (k : ℝ)) * ∑' n : ℕ, tauDigitKernel n / n ≤ (1 / k) * (29 / 20) :=
      mul_le_mul_of_nonneg_left tsum_tauDigitKernel_div_le (by positivity)
    have h2 : (1 / (k : ℝ)) * (29 / 20) ≤ (1 / 3) * (29 / 20) :=
      mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hk') (by norm_num)
    linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hval)] with N hN
  exact lt_of_le_of_lt (erdosBorwein_freq_le_envelope hk1 N) hN

/-- **L15′.** For every `k ≥ 3`, `E(2^k)` has positive lower discrepancy in base `2`:
`D_N(E(2^k); 2) ≥ 1/120` for all large `N`. -/
theorem erdosBorwein_two_pow_lowerDiscrepancy_pos (k : ℕ) (hk : 3 ≤ k) :
    ∃ δ > 0, ∀ᶠ N in atTop,
      δ ≤ radixDiscrepancy 2 (∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) - 1)) N := by
  refine ⟨1 / 120, by norm_num, ?_⟩
  change ∀ᶠ N in atTop, 1 / 120 ≤ radixDiscrepancy 2 (erdosBorweinPow k) N
  filter_upwards [erdosBorwein_eventually_lt hk] with N hN
  have h := radixDiscrepancy_ge_nonzero_freq 2 (le_refl 2) (erdosBorweinPow k) N
  simp only [Nat.cast_ofNat] at h
  linarith

private theorem sum_range_mul_eq {β : Type*} [AddCommMonoid β] (f : ℕ → β) (j M : ℕ) :
    ∑ t ∈ range (j * M), f t = ∑ n ∈ range M, ∑ i ∈ range j, f (j * n + i) := by
  induction M with
  | zero => simp
  | succ M ih => rw [mul_add, mul_one, sum_range_add, ih, sum_range_succ]

private theorem sum_digitSum_range_two_pow (j : ℕ) :
    2 * ∑ v ∈ range (2 ^ j), digitSum 2 v = j * 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsplit : ∀ m : ℕ, ∑ v ∈ range (2 * m), digitSum 2 v =
        ∑ v ∈ range m, (digitSum 2 (2 * v) + digitSum 2 (2 * v + 1)) := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ihm,
          sum_range_succ]
        ring
    have h2 : ∑ v ∈ range (2 ^ j), (digitSum 2 (2 * v) + digitSum 2 (2 * v + 1)) =
        2 * ∑ v ∈ range (2 ^ j), digitSum 2 v + 2 ^ j := by
      calc ∑ v ∈ range (2 ^ j), (digitSum 2 (2 * v) + digitSum 2 (2 * v + 1))
          = ∑ v ∈ range (2 ^ j), (2 * digitSum 2 v + 1) := by
            refine sum_congr rfl (fun v _ => ?_)
            rw [digitSum_mul_base (le_refl 2), digitSum_mul_add (le_refl 2) v 1 (by norm_num)]
            ring
        _ = 2 * ∑ v ∈ range (2 ^ j), digitSum 2 v + 2 ^ j := by
            rw [sum_add_distrib, ← mul_sum, sum_const, card_range, smul_eq_mul, mul_one]
    rw [pow_succ, mul_comm (2 ^ j) 2, hsplit, h2, mul_add, ih]
    ring

/-- Popcount identity: the base-`2^j` digits of `x` carry exactly the binary `1`s of `x`. -/
private theorem popcount_word_identity (j M : ℕ) (x : ℝ) :
    ∑ v ∈ range (2 ^ j), digitSum 2 v * wordCount (2 ^ j) 1 x v M =
      ∑ t ∈ range (j * M), if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * x) then 1 else 0 := by
  have hw : ∀ n, ⌊((2 ^ j : ℕ) : ℝ) ^ 1 * shift (2 ^ j) x n⌋₊ < 2 ^ j := fun n => by
    have := wordAt_lt (b := 2 ^ j) Nat.one_le_two_pow 1 x n
    rw [pow_one] at this
    exact this
  have hbits : ∀ n, digitSum 2 ⌊((2 ^ j : ℕ) : ℝ) ^ 1 * shift (2 ^ j) x n⌋₊ =
      ∑ i ∈ range j, if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ (j * n + i) * x) then 1 else 0 := by
    intro n
    have hy0 : 0 ≤ shift (2 ^ j) x n := (shift_mem _ x n).1
    have hy1 : shift (2 ^ j) x n < 1 := (shift_mem _ x n).2
    have hpush : ((2 ^ j : ℕ) : ℝ) ^ 1 = (2 : ℝ) ^ j := by push_cast; ring
    rw [hpush, digitSum_floor_pow_eq hy0 j, Nat.floor_eq_zero.mpr hy1, digitSum_zero, zero_add]
    refine sum_congr rfl (fun i _ => ?_)
    have hfr : Int.fract ((2 : ℝ) ^ i * shift (2 ^ j) x n) =
        Int.fract ((2 : ℝ) ^ (j * n + i) * x) := by
      unfold shift
      have e : (2 : ℝ) ^ i * Int.fract (((2 ^ j : ℕ) : ℝ) ^ n * x) =
          (2 : ℝ) ^ (j * n + i) * x - ((2 ^ i * ⌊((2 ^ j : ℕ) : ℝ) ^ n * x⌋ : ℤ) : ℝ) := by
        rw [Int.fract]
        push_cast
        ring
      rw [e, Int.fract_sub_intCast]
    rw [hfr]
  calc ∑ v ∈ range (2 ^ j), digitSum 2 v * wordCount (2 ^ j) 1 x v M
      = ∑ n ∈ range M, digitSum 2 ⌊((2 ^ j : ℕ) : ℝ) ^ 1 * shift (2 ^ j) x n⌋₊ := by
        unfold wordCount
        simp_rw [card_filter, mul_sum, mul_ite, mul_one, mul_zero]
        rw [sum_comm]
        refine sum_congr rfl (fun n _ => ?_)
        rw [sum_ite_eq, ite_eq_left (mem_range.mpr (hw n))]
    _ = ∑ n ∈ range M,
          ∑ i ∈ range j, if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ (j * n + i) * x) then 1 else 0 :=
        sum_congr rfl (fun n _ => hbits n)
    _ = ∑ t ∈ range (j * M), if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * x) then 1 else 0 :=
        (sum_range_mul_eq (fun t => if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * x) then 1 else 0) j M).symm

/-- **L15′ (descent to every base `2^j`).** For every `k ≥ 3` and `j ≥ 1`,
`E(2^k) = ∑_{m ≥ 1} 1/(2^{km} - 1)` is not simply normal in base `2^j`. -/
theorem erdosBorwein_two_pow_not_simplyNormal_pow (k j : ℕ) (hk : 3 ≤ k) (hj : 1 ≤ j) :
    ¬ OrderNormal (2 ^ j) 1 (∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) - 1)) := by
  change ¬ OrderNormal (2 ^ j) 1 (erdosBorweinPow k)
  intro hON
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hlimF : Tendsto (fun M : ℕ => ∑ v ∈ range (2 ^ j),
      (digitSum 2 v : ℝ) * wordFreq (2 ^ j) 1 (erdosBorweinPow k) v M) atTop
      (𝓝 (∑ v ∈ range (2 ^ j), (digitSum 2 v : ℝ) * (1 / ((2 ^ j : ℕ) : ℝ) ^ 1))) :=
    tendsto_finsetSum _ (fun v hv => (hON v (by rw [pow_one]; exact mem_range.mp hv)).const_mul _)
  have hval : ∑ v ∈ range (2 ^ j), (digitSum 2 v : ℝ) * (1 / ((2 ^ j : ℕ) : ℝ) ^ 1) =
      (j : ℝ) / 2 := by
    rw [← Finset.sum_mul (range (2 ^ j)) (fun v => (digitSum 2 v : ℝ))]
    have hR : (2 : ℝ) * ∑ v ∈ range (2 ^ j), (digitSum 2 v : ℝ) = j * 2 ^ j := by
      exact_mod_cast sum_digitSum_range_two_pow j
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    push_cast
    rw [pow_one]
    field_simp
    linarith
  have hF : ∀ M : ℕ, 0 < M → ∑ v ∈ range (2 ^ j),
      (digitSum 2 v : ℝ) * wordFreq (2 ^ j) 1 (erdosBorweinPow k) v M =
      j * frequency (shift 2 (erdosBorweinPow k)) (1 / 2) 1 (j * M) := by
    intro M hM
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hj0 : (j : ℝ) ≠ 0 := hjr.ne'
    have hid := popcount_word_identity j M (erdosBorweinPow k)
    rw [frequency_half_eq]
    unfold wordFreq
    simp_rw [mul_div_assoc']
    rw [← Finset.sum_div]
    have hcast : ∑ v ∈ range (2 ^ j), (digitSum 2 v : ℝ) *
        (wordCount (2 ^ j) 1 (erdosBorweinPow k) v M : ℝ) =
        ((∑ t ∈ range (j * M),
          if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * erdosBorweinPow k) then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast hid
    rw [hcast]
    generalize ((∑ t ∈ range (j * M),
      if 1 / 2 ≤ Int.fract ((2 : ℝ) ^ t * erdosBorweinPow k) then 1 else 0 : ℕ) : ℝ) = S
    rw [Nat.cast_mul]
    field_simp
  have hsub : Tendsto (fun M : ℕ => frequency (shift 2 (erdosBorweinPow k)) (1 / 2) 1 (j * M))
      atTop (𝓝 (1 / 2)) := by
    have h := hlimF.const_mul (1 / (j : ℝ))
    rw [hval, show (1 / (j : ℝ)) * ((j : ℝ) / 2) = 1 / 2 by field_simp] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    rw [hF M hM]
    field_simp
  have hmul : Tendsto (fun M : ℕ => j * M) atTop atTop :=
    tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M hj) tendsto_id
  have hlt := hmul.eventually (erdosBorwein_eventually_lt hk)
  have hgt := hsub.eventually (lt_mem_nhds (by norm_num : (59 / 120 : ℝ) < 1 / 2))
  obtain ⟨M, hM1, hM2⟩ := (hlt.and hgt).exists
  linarith

/-- **L15′.** For every `k ≥ 3`, `E(2^k) = ∑_{m ≥ 1} 1/(2^{km} - 1)` is not simply normal in
base `2`. -/
theorem erdosBorwein_two_pow_not_simplyNormal (k : ℕ) (hk : 3 ≤ k) :
    ¬ OrderNormal 2 1 (∑' n : ℕ, (1 : ℝ) / (2 ^ (k * (n + 1)) - 1)) := by
  have := erdosBorwein_two_pow_not_simplyNormal_pow k 1 hk le_rfl
  rwa [pow_one] at this

/-! ### Part 9 (L11): radix descent of the extreme discrepancy -/

private theorem radixDiscrepancy_le_one (b : ℕ) (x : ℝ) (N : ℕ) : radixDiscrepancy b x N ≤ 1 :=
  radixDiscrepancy_le_of (fun a c _ _ _ => by
    obtain ⟨h1, h2⟩ := frequency_bounds (shift b x) a c N
    exact abs_le.mpr ⟨by linarith, by linarith⟩)

private theorem shift_mul_add (b k m r : ℕ) (x : ℝ) :
    shift b x (k * m + r) = Int.fract ((b : ℝ) ^ r * shift (b ^ k) x m) := by
  unfold shift
  have e : (b : ℝ) ^ r * Int.fract (((b ^ k : ℕ) : ℝ) ^ m * x) =
      (b : ℝ) ^ (k * m + r) * x - (((b : ℤ) ^ r * ⌊((b ^ k : ℕ) : ℝ) ^ m * x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [e, Int.fract_sub_intCast]

private theorem indicator_fract_eq_sum {b r : ℕ} (hb : 2 ≤ b) {y a c : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y < 1) (ha : 0 ≤ a) (hc : c ≤ 1) :
    (if a ≤ Int.fract ((b : ℝ) ^ r * y) ∧ Int.fract ((b : ℝ) ^ r * y) < c then 1 else 0 : ℕ) =
      ∑ j ∈ range (b ^ r), if ((j : ℝ) + a) / (b : ℝ) ^ r ≤ y ∧ y < ((j : ℝ) + c) / (b : ℝ) ^ r
        then 1 else 0 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbr : (0 : ℝ) < (b : ℝ) ^ r := pow_pos hb0 r
  have ht0 : 0 ≤ (b : ℝ) ^ r * y := mul_nonneg hbr.le hy0
  have htlt : (b : ℝ) ^ r * y < (b : ℝ) ^ r := by nlinarith
  have hj0lt : ⌊(b : ℝ) ^ r * y⌋₊ < b ^ r := by
    rw [Nat.floor_lt ht0]
    push_cast
    exact htlt
  have hcond : ∀ j : ℕ, (((j : ℝ) + a) / (b : ℝ) ^ r ≤ y ∧ y < ((j : ℝ) + c) / (b : ℝ) ^ r) ↔
      ((j : ℝ) + a ≤ (b : ℝ) ^ r * y ∧ (b : ℝ) ^ r * y < j + c) := by
    intro j
    rw [div_le_iff₀ hbr, lt_div_iff₀ hbr, mul_comm y]
  have hfloor : ((⌊(b : ℝ) ^ r * y⌋₊ : ℕ) : ℝ) = (⌊(b : ℝ) ^ r * y⌋ : ℝ) := by
    have := Int.natCast_floor_eq_floor ht0
    exact_mod_cast this
  have hfr : Int.fract ((b : ℝ) ^ r * y) = (b : ℝ) ^ r * y - (⌊(b : ℝ) ^ r * y⌋₊ : ℝ) := by
    rw [hfloor]
    rfl
  rw [Finset.sum_eq_single_of_mem _ (mem_range.mpr hj0lt)]
  · by_cases h : a ≤ Int.fract ((b : ℝ) ^ r * y) ∧ Int.fract ((b : ℝ) ^ r * y) < c
    · rw [ite_eq_left h, ite_eq_left ((hcond _).2 ⟨by rw [hfr] at h; linarith [h.1],
        by rw [hfr] at h; linarith [h.2]⟩)]
    · rw [ite_eq_right h, ite_eq_right]
      intro h'
      rw [hcond] at h'
      exact h ⟨by rw [hfr]; linarith [h'.1], by rw [hfr]; linarith [h'.2]⟩
  · intro j _ hj
    rw [ite_eq_right]
    intro hcj
    rw [hcond] at hcj
    apply hj
    symm
    rw [Nat.floor_eq_iff ht0]
    constructor <;> linarith [hcj.1, hcj.2]

/-- Number of `m < N` whose base-`b^k` shift lies in `[(j + a)/b^r, (j + c)/b^r)`. -/
private noncomputable def descentCount (b k : ℕ) (x a c : ℝ) (N r j : ℕ) : ℕ :=
  ((range N).filter (fun m => ((j : ℝ) + a) / (b : ℝ) ^ r ≤ shift (b ^ k) x m ∧
    shift (b ^ k) x m < ((j : ℝ) + c) / (b : ℝ) ^ r)).card

private theorem count_descent {b k N : ℕ} (hb : 2 ≤ b) (x : ℝ) {a c : ℝ} (ha : 0 ≤ a)
    (hc : c ≤ 1) :
    ((range (k * N)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card =
      ∑ r ∈ range k, ∑ j ∈ range (b ^ r), descentCount b k x a c N r j := by
  rw [card_filter, sum_range_mul_eq (fun n => if a ≤ shift b x n ∧ shift b x n < c then 1 else 0)
    k N, sum_comm]
  refine sum_congr rfl (fun r _ => ?_)
  unfold descentCount
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun m _ => ?_)
  rw [shift_mul_add]
  exact indicator_fract_eq_sum hb (shift_mem _ x m).1 (shift_mem _ x m).2 ha hc

/-- **L11 (Proposition 2.4(5)).** Radix descent:
`D_{kN}(x; b) ≤ (b^k - 1)/(k (b - 1)) · D_N(x; b^k)`. -/
theorem radixDiscrepancy_descent (b k N : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) (x : ℝ) :
    radixDiscrepancy b x (k * N) ≤
      ((b : ℝ) ^ k - 1) / (k * ((b : ℝ) - 1)) * radixDiscrepancy (b ^ k) x N := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hgeom : ∑ r ∈ range k, (b : ℝ) ^ r = ((b : ℝ) ^ k - 1) / ((b : ℝ) - 1) :=
    geom_sum_eq (by linarith) k
  have hcoef : ((b : ℝ) ^ k - 1) / (k * ((b : ℝ) - 1)) = (∑ r ∈ range k, (b : ℝ) ^ r) / k := by
    rw [hgeom, div_div, mul_comm (k : ℝ)]
  have hD0 : 0 ≤ radixDiscrepancy (b ^ k) x N :=
    (abs_nonneg _).trans (interval_le_radixDiscrepancy _ x N le_rfl zero_lt_one le_rfl)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hD1 : 1 ≤ radixDiscrepancy (b ^ k) x 0 := by
      have := interval_le_radixDiscrepancy (b ^ k) x 0 (le_refl 0) zero_lt_one le_rfl
      rw [frequency_zero_right] at this
      norm_num at this
      exact this
    have hc1 : 1 ≤ ((b : ℝ) ^ k - 1) / (k * ((b : ℝ) - 1)) := by
      rw [hcoef, le_div_iff₀ hkr, one_mul]
      calc (k : ℝ) = ∑ _r ∈ range k, (1 : ℝ) := by simp
        _ ≤ ∑ r ∈ range k, (b : ℝ) ^ r :=
            sum_le_sum (fun r _ => one_le_pow₀ (by linarith))
    calc radixDiscrepancy b x (k * 0) ≤ 1 := radixDiscrepancy_le_one b x _
      _ = 1 * 1 := by norm_num
      _ ≤ ((b : ℝ) ^ k - 1) / (k * ((b : ℝ) - 1)) * radixDiscrepancy (b ^ k) x 0 :=
          mul_le_mul hc1 hD1 zero_le_one (by linarith)
  · apply radixDiscrepancy_le_of
    intro a c ha hac hc
    set D := radixDiscrepancy (b ^ k) x N with hDdef
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hb0 : (0 : ℝ) < b := by linarith
    have hbne : (b : ℝ) ≠ 0 := hb0.ne'
    have hk0 : (k : ℝ) ≠ 0 := hkr.ne'
    have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
    have hpiece : ∀ r ∈ range k, ∀ j ∈ range (b ^ r),
        |(descentCount b k x a c N r j : ℝ) / N - (c - a) / (b : ℝ) ^ r| ≤ D := by
      intro r _ j hj
      have hbr : (0 : ℝ) < (b : ℝ) ^ r := pow_pos hb0 r
      have hj1 : (j : ℝ) + 1 ≤ (b : ℝ) ^ r := by
        have : j + 1 ≤ b ^ r := mem_range.mp hj
        exact_mod_cast this
      have hlo : 0 ≤ ((j : ℝ) + a) / (b : ℝ) ^ r := by positivity
      have hlohi : ((j : ℝ) + a) / (b : ℝ) ^ r < ((j : ℝ) + c) / (b : ℝ) ^ r :=
        div_lt_div_of_pos_right (by linarith) hbr
      have hhi : ((j : ℝ) + c) / (b : ℝ) ^ r ≤ 1 := by
        rw [div_le_one hbr]
        linarith
      have h := interval_le_radixDiscrepancy (b ^ k) x N hlo hlohi hhi
      have hlen : ((j : ℝ) + c) / (b : ℝ) ^ r - ((j : ℝ) + a) / (b : ℝ) ^ r =
          (c - a) / (b : ℝ) ^ r := by ring
      rw [hlen] at h
      exact h
    have hcount := count_descent (k := k) (N := N) hb x ha hc
    have hsum_len : ∑ r ∈ range k, ∑ _j ∈ range (b ^ r), (c - a) / (b : ℝ) ^ r = k * (c - a) := by
      have : ∀ r ∈ range k, ∑ _j ∈ range (b ^ r), (c - a) / (b : ℝ) ^ r = c - a := by
        intro r _
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        field_simp
      rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
    set S : ℝ := ∑ r ∈ range k, ∑ j ∈ range (b ^ r), (descentCount b k x a c N r j : ℝ) with hS
    set T : ℝ := ∑ r ∈ range k, ∑ j ∈ range (b ^ r),
      ((descentCount b k x a c N r j : ℝ) / N - (c - a) / (b : ℝ) ^ r) with hT
    have hTS : T = S / N - k * (c - a) := by
      rw [hT, hS, ← hsum_len]
      simp_rw [sum_sub_distrib, sum_div]
    have hfreq : frequency (shift b x) a c (k * N) - (c - a) = T / k := by
      unfold frequency
      rw [hcount, hTS]
      push_cast
      rw [← hS]
      field_simp
    have habsT : |T| ≤ ∑ r ∈ range k, (b : ℝ) ^ r * D := by
      calc |T| ≤ ∑ r ∈ range k, |∑ j ∈ range (b ^ r),
            ((descentCount b k x a c N r j : ℝ) / N - (c - a) / (b : ℝ) ^ r)| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ range k, ∑ j ∈ range (b ^ r),
            |(descentCount b k x a c N r j : ℝ) / N - (c - a) / (b : ℝ) ^ r| :=
            sum_le_sum (fun r _ => abs_sum_le_sum_abs _ _)
        _ ≤ ∑ r ∈ range k, ∑ _j ∈ range (b ^ r), D :=
            sum_le_sum (fun r hr => sum_le_sum (fun j hj => hpiece r hr j hj))
        _ = ∑ r ∈ range k, (b : ℝ) ^ r * D := by
            refine sum_congr rfl (fun r _ => ?_)
            rw [sum_const, card_range, nsmul_eq_mul]
            push_cast
            ring
    rw [hfreq, abs_div, abs_of_pos hkr, hcoef, div_mul_eq_mul_div, Finset.sum_mul]
    exact div_le_div_of_nonneg_right habsT hkr.le

end NormalityChecker.DigitMassTransfer
