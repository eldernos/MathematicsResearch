module

public import NormalityChecker.SharpTranslation

/-! # Phase 18: radix retirement, programmed rational states and discrepancy transfer

Kernel-checked elementary cores of the Phase 18 synthesis programme.

1. **Geometric retirement.** A complete group of `h` consecutive radix powers weighted by
   `(b-1)/(b^h-1)`, the reciprocal of the repunit `1+b+⋯+b^(h-1)`, collapses to the single
   power `b^-(m+h)` (`geometric_retirement_weight`). Arbitrary signed multipliers and variable
   group lengths give the finite identity `grouped_retirement` and, for bounded real
   multipliers, the absolutely convergent identity `grouped_retirement_hasSum`, in which the
   dense raw series and the sparse grouped series have the same sum.
2. **Raw denominators.** Each raw summand `1/(R_h b^m)` has reduced denominator `R_h b^m` with
   `R_h` coprime to `b`, and is never a `b`-adic rational for `h ≥ 2`. Every prime not dividing
   `b` divides the repunit of every gap divisible by `r(r-1)`; schedules whose gaps are
   eventually divisible by every integer (for example `t·k!`) therefore have infinite raw
   denominator prime support (`raw_prime_support_infinite`).
3. **Rational state programming.** The recursion `R_k = b^(g_k) R_(k-1) + c_k` with
   `c_k = {u_k - b^(g_k) R_(k-1)}` (zero replaced by one) has `{R_k} = u_k` exactly, positive
   coefficients at most one, `den c_k ∣ den u_k · den u_(k-1)`, and coefficients supported on
   `p` when every target is. The state is the shifted prefix of `∑ c_k b^-n_k`; it keeps the
   target's denominator on active indices and is an integer on retired ones. Replacing every
   programmed term by its geometric group gives a dense positive series with the same sum
   (`programmed_dense_hasSum`).
4. **Discrepancy transfer.** For every `ε ≥ 0`, the extreme interval discrepancies of `x+z`
   and `x` differ by at most `2ε + E_N(ε)/N`, where `E_N(ε)` counts the positions `n < N` at
   which `b^n z` is farther than `ε` from every integer (`discrepancy_transfer`). Circular
   intervals are handled through complementary arcs. Corollaries: integer and `b`-adic
   translations and every eventually integral perturbation (`|ΔD_N| ≤ min(1, K/N)`), and
   asymptotic equality of discrepancies (`discrepancy_transfer_tendsto`).
   For a sparse integer perturbation `z = ∑ A_k b^-m_k` with `|A_k| ≤ B`, every far position
   lies in a window of length `w` before an insertion once `2B b^-w ≤ ε`
   (`sparse_farCount_le`). For `Z = ∑_{k≥1} 2^-(k(k+1))` this gives
   `|D_N(x+Z;2) - D_N(x;2)| ≤ 4·2^-w + w⌊√(N+w)⌋/N` for every `x` and `w`
   (`quadratic_sparse_transfer`), hence `O(log N/√N)`.

Exact shifted-prefix denominators are proved in NormalityChecker.RetirementDenominator.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.Phase18Synthetic

/-! ### 1. Geometric retirement -/

/-- The base-`b` repunit `1 + b + ⋯ + b^(h-1)`. -/
def repunit (b h : ℕ) : ℕ := ∑ i ∈ range h, b ^ i

theorem repunit_mul_sub_one (b h : ℕ) :
    (repunit b h : ℤ) * ((b : ℤ) - 1) = (b : ℤ) ^ h - 1 := by
  unfold repunit; push_cast; exact geom_sum_mul (b : ℤ) h

theorem repunit_succ (b h : ℕ) : repunit b (h + 1) = 1 + b * repunit b h := by
  unfold repunit
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ', pow_zero]
  ring

/-- A complete group of `h` consecutive powers after position `m`, in any field. -/
theorem geometric_retirement {K : Type*} [Field K] (b : K) (hb : b ≠ 0) (m h : ℕ) :
    ∑ r ∈ range h, (b ^ (m + r + 1))⁻¹ = (∑ i ∈ range h, b ^ i) * (b ^ (m + h))⁻¹ := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih, geom_sum_succ]
    have hm : b ^ (m + (h + 1)) = b ^ (m + h) * b := by rw [← add_assoc, pow_succ]
    rw [hm, pow_succ]
    field_simp

/-- **Geometric retirement identity.** `(b-1)/(b^h-1) · ∑_{r=1}^h b^-(m+r) = b^-(m+h)`. -/
theorem geometric_retirement_weight {K : Type*} [Field K] {b : K} (hb : b ≠ 0) {h : ℕ}
    (hh : b ^ h ≠ 1) (m : ℕ) :
    (b - 1) / (b ^ h - 1) * ∑ r ∈ range h, (b ^ (m + r + 1))⁻¹ = (b ^ (m + h))⁻¹ := by
  rw [geometric_retirement b hb m h, ← mul_assoc]
  have hs : (∑ i ∈ range h, b ^ i) * (b - 1) = b ^ h - 1 := geom_sum_mul b h
  have hd : b ^ h - 1 ≠ 0 := sub_ne_zero.mpr hh
  have key : (b - 1) / (b ^ h - 1) * (∑ i ∈ range h, b ^ i) = 1 := by
    rw [div_mul_eq_mul_div, mul_comm, hs, div_self hd]
  rw [key, one_mul]

/-- One complete block `(s, s+h]` with constant raw coefficient `c·(b-1)/(b^h-1)` retires to
the single term `c·b^-(s+h)`. -/
theorem block_retirement {K : Type*} [Field K] {b : K} (hb : b ≠ 0) {h : ℕ} (hh : b ^ h ≠ 1)
    (c : K) (s : ℕ) (a : ℕ → K)
    (compat : ∀ m ∈ Ioc s (s + h), a m = c * ((b - 1) / (b ^ h - 1))) :
    ∑ m ∈ Ioc s (s + h), a m * (b ^ m)⁻¹ = c * (b ^ (s + h))⁻¹ := by
  rw [Finset.sum_congr rfl (fun m hm => by rw [compat m hm]),
    ← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
  have hlen : s + h + 1 - (s + 1) = h := by omega
  rw [hlen, ← geometric_retirement_weight hb hh s, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [show s + 1 + r = s + r + 1 by omega]
  ring

/-- **Grouped retirement, finite form.** Along a strictly increasing schedule `n`, any raw
coefficient sequence that equals `c_k (b-1)/(b^(n_(k+1)-n_k)-1)` on the block
`(n_k, n_(k+1)]` has prefix sums equal to the grouped sums `∑ c_k b^-n_(k+1)`. The multipliers
`c_k` are arbitrary, so signs and zero coefficients are allowed. -/
theorem grouped_retirement {K : Type*} [Field K] {b : K} (hb : b ≠ 0)
    (hpow : ∀ h, 0 < h → b ^ h ≠ 1) (n : ℕ → ℕ) (mono : StrictMono n) (c a : ℕ → K)
    (compat : ∀ k, ∀ m ∈ Ioc (n k) (n (k + 1)),
      a m = c k * ((b - 1) / (b ^ (n (k + 1) - n k) - 1))) (L : ℕ) :
    ∑ m ∈ Ioc (n 0) (n L), a m * (b ^ m)⁻¹ = ∑ k ∈ range L, c k * (b ^ n (k + 1))⁻¹ := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hlt : n L < n (L + 1) := mono (Nat.lt_succ_self L)
    rw [← Finset.sum_Ioc_consecutive _ (mono.monotone (Nat.zero_le L)) hlt.le, ih,
      Finset.sum_range_succ]
    congr 1
    have he : n (L + 1) = n L + (n (L + 1) - n L) := by omega
    have hblock := block_retirement hb (hpow (n (L + 1) - n L) (by omega)) (c L) (n L) a
      (by rw [← he]; exact compat L)
    rw [← he] at hblock
    exact hblock

/-- The retirement weight of a nonempty group lies in `(0, 1]` for a real radix `b > 1`. -/
theorem retirement_weight_mem {b : ℝ} (hb : 1 < b) {h : ℕ} (hh : 0 < h) :
    0 < (b - 1) / (b ^ h - 1) ∧ (b - 1) / (b ^ h - 1) ≤ 1 := by
  have hbh : b ≤ b ^ h := le_self_pow₀ hb.le hh.ne'
  have hpos : 0 < b ^ h - 1 := by linarith
  exact ⟨div_pos (by linarith) hpos, (div_le_one hpos).mpr (by linarith)⟩

private lemma exists_block (n : ℕ → ℕ) (mono : StrictMono n) (h0 : n 0 = 0) {m : ℕ}
    (hm : 0 < m) : ∃ k, n k < m ∧ m ≤ n (k + 1) := by
  classical
  have ex : ∃ j, m ≤ n j := ⟨m, mono.id_le m⟩
  set j := Nat.find ex with hj
  have hjm : m ≤ n j := Nat.find_spec ex
  have hj0 : j ≠ 0 := by
    intro h; rw [h, h0] at hjm; omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  rw [hk] at hjm
  refine ⟨k, ?_, hjm⟩
  have := Nat.find_min ex (show k < Nat.find ex by omega)
  omega

/-- **Grouped retirement, infinite form.** For a real radix `b > 1`, a schedule starting at
zero and bounded real multipliers, the dense raw series converges absolutely and its sum is the
sum of the sparse grouped series. -/
theorem grouped_retirement_hasSum {b : ℝ} (hb : 1 < b) (n : ℕ → ℕ) (mono : StrictMono n)
    (h0 : n 0 = 0) (c a : ℕ → ℝ) {C : ℝ} (hc : ∀ k, |c k| ≤ C) (ha0 : a 0 = 0)
    (compat : ∀ k, ∀ m ∈ Ioc (n k) (n (k + 1)),
      a m = c k * ((b - 1) / (b ^ (n (k + 1) - n k) - 1))) :
    HasSum (fun m => a m * (b ^ m)⁻¹) (∑' k, c k * (b ^ n (k + 1))⁻¹) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hC : 0 ≤ C := (abs_nonneg _).trans (hc 0)
  have hr : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  have geo : Summable (fun m : ℕ => C * (b⁻¹) ^ m) :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left C
  -- raw coefficients are bounded by `C`
  have abound : ∀ m, |a m| ≤ C := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa [ha0] using hC
    obtain ⟨k, hk1, hk2⟩ := exists_block n mono h0 hm
    rw [compat k m (Finset.mem_Ioc.mpr ⟨hk1, hk2⟩), abs_mul]
    have hw := retirement_weight_mem hb (show 0 < n (k + 1) - n k by omega)
    rw [abs_of_pos hw.1]
    calc |c k| * ((b - 1) / (b ^ (n (k + 1) - n k) - 1)) ≤ C * 1 :=
          mul_le_mul (hc k) hw.2 hw.1.le hC
      _ = C := mul_one C
  have rawSum : Summable (fun m => a m * (b ^ m)⁻¹) := by
    refine Summable.of_norm_bounded geo (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hb0 m)), inv_pow]
    exact mul_le_mul_of_nonneg_right (abound m) (by positivity)
  have grpSum : Summable (fun k => c k * (b ^ n (k + 1))⁻¹) := by
    refine Summable.of_norm_bounded geo (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hb0 _)), ← inv_pow]
    refine mul_le_mul (hc k) ?_ (by positivity) hC
    exact pow_le_pow_of_le_one (by positivity) hr.le
      ((mono.id_le (k + 1)).trans' (Nat.le_succ k))
  -- compare partial sums along the subsequence of completed groups
  have hpart : ∀ L, ∑ m ∈ range (n L + 1), a m * (b ^ m)⁻¹ =
      ∑ k ∈ range L, c k * (b ^ n (k + 1))⁻¹ := by
    intro L
    rw [Finset.sum_range_succ', ha0, zero_mul, add_zero]
    rw [← grouped_retirement (ne_of_gt hb0)
      (fun h hh => ne_of_gt (one_lt_pow₀ hb hh.ne')) n mono c a compat L, h0,
      ← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr (by simp) (fun i _ => by rw [zero_add, add_comm 1 i])
  have sub : Tendsto (fun L => n L + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp mono.tendsto_atTop
  have t1 := (rawSum.hasSum.tendsto_sum_nat).comp sub
  have t2 := grpSum.hasSum.tendsto_sum_nat
  have heq : (fun L => ∑ m ∈ range (n L + 1), a m * (b ^ m)⁻¹) =
      fun L => ∑ k ∈ range L, c k * (b ^ n (k + 1))⁻¹ := funext hpart
  have : ∑' m, a m * (b ^ m)⁻¹ = ∑' k, c k * (b ^ n (k + 1))⁻¹ := by
    refine tendsto_nhds_unique ?_ t2
    have : (fun L => ∑ m ∈ range (n L + 1), a m * (b ^ m)⁻¹) =
        (fun N => ∑ m ∈ range N, a m * (b ^ m)⁻¹) ∘ (fun L => n L + 1) := rfl
    rw [← heq, this]; exact t1
  rw [← this]; exact rawSum.hasSum

/-! ### 2. Raw denominators -/

/-- The retirement weight is the reciprocal of the repunit. -/
theorem retirement_weight_eq_inv_repunit {b : ℕ} (hb : 2 ≤ b) (h : ℕ) :
    ((b : ℚ) - 1) / ((b : ℚ) ^ h - 1) = ((repunit b h : ℕ) : ℚ)⁻¹ := by
  have hq : ((repunit b h : ℕ) : ℚ) * ((b : ℚ) - 1) = (b : ℚ) ^ h - 1 := by
    exact_mod_cast repunit_mul_sub_one b h
  have hb1 : (b : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ b := by exact_mod_cast hb
    linarith
  rw [← hq, div_mul_eq_div_div_swap, div_self hb1, one_div]

theorem repunit_coprime {b h : ℕ} (hh : 0 < h) : Nat.Coprime (repunit b h) b := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_lt hh
  rw [show 0 + h + 1 = h + 1 by omega, repunit_succ, Nat.coprime_comm,
    Nat.coprime_add_mul_left_right]
  exact Nat.coprime_one_right b

theorem repunit_ge_two {b h : ℕ} (hb : 1 ≤ b) (hh : 2 ≤ h) : 2 ≤ repunit b h := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [show 2 + h = (h + 1) + 1 by omega, repunit_succ, repunit_succ]
  have : 0 < b * (1 + b * repunit b h) := Nat.mul_pos (by omega) (by omega)
  omega

/-- Each raw summand `1/(R_h b^m)` has reduced denominator exactly `R_h b^m`. -/
theorem raw_term_den {b : ℕ} (h m : ℕ) (hb : 1 ≤ b) (hh : 0 < h) :
    ((((repunit b h * b ^ m : ℕ) : ℚ))⁻¹).den = repunit b h * b ^ m := by
  have hpos : repunit b h * b ^ m ≠ 0 := by
    have : 1 ≤ repunit b h := by
      obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_lt hh
      rw [show 0 + h + 1 = h + 1 by omega, repunit_succ]; omega
    positivity
  simp only [Rat.inv_natCast_den, hpos, ↓reduceIte]

/-- A raw summand of a group of length at least two is never a `b`-adic rational: no radix
shift of it is an integer. -/
theorem raw_term_not_radix {b : ℕ} (hb : 2 ≤ b) {h : ℕ} (hh : 2 ≤ h) (m N : ℕ) (z : ℤ) :
    (b : ℚ) ^ N * (((repunit b h : ℕ) : ℚ) * (b : ℚ) ^ m)⁻¹ ≠ z := by
  intro heq
  have hR := repunit_ge_two (show 1 ≤ b by omega) hh
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hRq : ((repunit b h : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show repunit b h ≠ 0 by omega)
  have key : ((b ^ N : ℕ) : ℤ) = z * ((repunit b h * b ^ m : ℕ) : ℤ) := by
    have : (b : ℚ) ^ N = z * (((repunit b h : ℕ) : ℚ) * (b : ℚ) ^ m) := by
      rw [← heq, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hRq (pow_ne_zero _ hbq)), mul_one]
    exact_mod_cast this
  have hdvd : (repunit b h : ℤ) ∣ ((b ^ N : ℕ) : ℤ) := by
    rw [key]; push_cast; exact ⟨z * (b : ℤ) ^ m, by ring⟩
  have hdvd' : repunit b h ∣ b ^ N := Int.natCast_dvd_natCast.mp hdvd
  have hcop : Nat.Coprime (repunit b h) (b ^ N) :=
    Nat.Coprime.pow_right N (repunit_coprime (by omega))
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd'
  omega

/-- Repunits divide repunits of multiple length. -/
theorem repunit_dvd_of_dvd {b a h : ℕ} (hb : 2 ≤ b) (hah : a ∣ h) : repunit b a ∣ repunit b h := by
  obtain ⟨c, rfl⟩ := hah
  have hb1 : (b : ℤ) - 1 ≠ 0 := by omega
  have key : (repunit b (a * c) : ℤ) =
      (repunit b a : ℤ) * ∑ j ∈ range c, ((b : ℤ) ^ a) ^ j := by
    apply mul_right_cancel₀ hb1
    rw [repunit_mul_sub_one, mul_comm (repunit b a : ℤ), mul_assoc, repunit_mul_sub_one,
      geom_sum_mul, pow_mul]
  have : (repunit b a : ℤ) ∣ (repunit b (a * c) : ℤ) := ⟨_, key⟩
  exact Int.natCast_dvd_natCast.mp this

/-- Every prime `r ∤ b` divides the repunit of length `r(r-1)`. -/
theorem prime_dvd_repunit {b r : ℕ} (hb : 2 ≤ b) (hr : r.Prime) (hrb : ¬ r ∣ b) :
    r ∣ repunit b (r * (r - 1)) := by
  have := Fact.mk hr
  have hbz : (b : ZMod r) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  by_cases h1 : (b : ZMod r) = 1
  · -- `r ∣ b - 1`: the repunit of length `r` is `r` modulo `r`
    have hr0 : r ∣ repunit b r := by
      rw [← ZMod.natCast_eq_zero_iff]
      unfold repunit; push_cast; rw [h1]; simp
    exact hr0.trans (repunit_dvd_of_dvd hb (Dvd.intro _ rfl))
  · -- otherwise Fermat's little theorem kills the repunit of length `r - 1`
    have hr0 : r ∣ repunit b (r - 1) := by
      rw [← ZMod.natCast_eq_zero_iff]
      have hf : (b : ZMod r) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one hbz
      have hm : ((repunit b (r - 1) : ℕ) : ZMod r) * ((b : ZMod r) - 1) = 0 := by
        unfold repunit; push_cast; rw [geom_sum_mul, hf, sub_self]
      exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr h1)
    exact hr0.trans (repunit_dvd_of_dvd hb (Dvd.intro_left _ rfl))

/-- **Infinite raw prime support.** If for every `M > 0` some gap of the schedule is divisible
by `M`, every prime not dividing `b` divides some raw denominator, and the set of primes in raw
denominators is infinite. -/
theorem raw_prime_support_infinite {b : ℕ} (hb : 2 ≤ b) (n : ℕ → ℕ)
    (gaps : ∀ M, 0 < M → ∃ k, n k < n (k + 1) ∧ M ∣ n (k + 1) - n k) :
    (∀ r, r.Prime → ¬ r ∣ b → ∃ k, n k < n (k + 1) ∧ r ∣ repunit b (n (k + 1) - n k)) ∧
      {r : ℕ | r.Prime ∧ ∃ k, n k < n (k + 1) ∧ r ∣ repunit b (n (k + 1) - n k)}.Infinite := by
  have each : ∀ r, r.Prime → ¬ r ∣ b → ∃ k, n k < n (k + 1) ∧ r ∣ repunit b (n (k + 1) - n k) := by
    intro r hr hrb
    have hpos : 0 < r * (r - 1) := Nat.mul_pos hr.pos (by have := hr.two_le; omega)
    obtain ⟨k, hgap, hk⟩ := gaps _ hpos
    exact ⟨k, hgap, (prime_dvd_repunit hb hr hrb).trans (repunit_dvd_of_dvd hb hk)⟩
  refine ⟨each, Set.infinite_of_not_bddAbove ?_⟩
  rintro ⟨M, hM⟩
  obtain ⟨r, hr1, hr⟩ := Nat.exists_infinite_primes (M + b + 1)
  have hrb : ¬ r ∣ b := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have := hM ⟨hr, each r hr hrb⟩
  omega

/-- Factorial schedules `t·k!` have a gap divisible by every positive integer. -/
theorem factorial_gaps {t : ℕ} (ht : 0 < t) : ∀ M, 0 < M → ∃ k,
    t * k.factorial < t * (k + 1).factorial ∧ M ∣ t * (k + 1).factorial - t * k.factorial := by
  intro M hM
  refine ⟨M, Nat.mul_lt_mul_of_pos_left ?_ ht, Nat.dvd_sub ?_ ?_⟩
  · rw [Nat.factorial_succ]
    simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right (show 1 < M+1 by omega) (Nat.factorial_pos M)
  · exact Dvd.dvd.mul_left ((Nat.dvd_factorial hM le_rfl).trans
      (Nat.factorial_dvd_factorial (Nat.le_succ M))) t
  · exact Dvd.dvd.mul_left (Nat.dvd_factorial hM le_rfl) t

/-- A fraction over `p^e` whose numerator is prime to `p` has reduced denominator `p^e`. -/
theorem den_of_unit_numerator {p e : ℕ} (hp : p.Prime) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M) :
    ((M : ℚ) / ((p ^ e : ℕ) : ℚ)).den = p ^ e := by
  have h := Rat.den_div_eq_of_coprime (a := M) (b := ((p ^ e : ℕ) : ℤ))
    (by exact_mod_cast pow_pos hp.pos e) (by
      simp only [Int.natAbs_natCast]
      refine Nat.Coprime.pow_right _ ?_
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd; exact hM (Int.natCast_dvd.mpr hd))
  exact_mod_cast h

/-- After enough shifts a grouped term with a retained off-radix prime power keeps exactly that
denominator: `b^N/(p^e b^n)` has denominator `p^e` for `N ≥ n`. -/
theorem retained_term_den {b p e n N : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) (hN : n ≤ N) :
    ((b : ℚ) ^ N * ((p : ℚ) ^ e * (b : ℚ) ^ n)⁻¹).den = p ^ e := by
  have hb : (b : ℚ) ≠ 0 := by
    intro h; apply hpb; rw [Nat.cast_eq_zero.mp h]; exact dvd_zero p
  have eq : (b : ℚ) ^ N * ((p : ℚ) ^ e * (b : ℚ) ^ n)⁻¹ =
      (((b ^ (N - n) : ℕ) : ℤ) : ℚ) / ((p ^ e : ℕ) : ℚ) := by
    push_cast
    rw [show N = (N - n) + n by omega, pow_add]
    field_simp
    simp
  rw [eq]
  push_cast
  have h := den_of_unit_numerator (e := e) hp (M := ((b ^ (N - n) : ℕ) : ℤ)) (by
    intro hd; exact hpb (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.mp hd)))
  push_cast at h
  exact h

/-! ### 3. Rational state programming -/

/-- The coefficient moving state `R` to target `u` across a gap `g`: the fractional part of
`u - b^g R`, with zero replaced by one. -/
def programCoeff (b g : ℕ) (R u : ℚ) : ℚ :=
  if Int.fract (u - (b : ℚ) ^ g * R) = 0 then 1 else Int.fract (u - (b : ℚ) ^ g * R)

/-- The programmed states: `R_0 = 0` and `R_(k+1) = b^(g_(k+1)) R_k + c_(k+1)`. -/
def programState (b : ℕ) (g : ℕ → ℕ) (u : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => (b : ℚ) ^ g (k + 1) * programState b g u k +
      programCoeff b (g (k + 1)) (programState b g u k) (u (k + 1))

/-- The programmed coefficients `c_(k+1)`. -/
def programCoeffs (b : ℕ) (g : ℕ → ℕ) (u : ℕ → ℚ) (k : ℕ) : ℚ :=
  programCoeff b (g (k + 1)) (programState b g u k) (u (k + 1))

theorem programCoeff_mem (b g : ℕ) (R u : ℚ) :
    0 < programCoeff b g R u ∧ programCoeff b g R u ≤ 1 := by
  unfold programCoeff
  split_ifs with h
  · exact ⟨one_pos, le_rfl⟩
  · exact ⟨lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h), (Int.fract_lt_one _).le⟩

/-- The coefficient differs from `u - b^g R` by an integer. -/
theorem programCoeff_sub (b g : ℕ) (R u : ℚ) :
    ∃ z : ℤ, programCoeff b g R u = u - (b : ℚ) ^ g * R + z := by
  unfold programCoeff
  split_ifs with h
  · refine ⟨1 - ⌊u - (b : ℚ) ^ g * R⌋, ?_⟩
    have := Int.fract_add_floor (u - (b : ℚ) ^ g * R)
    rw [h] at this; push_cast; linarith
  · exact ⟨-⌊u - (b : ℚ) ^ g * R⌋, by rw [Int.fract]; push_cast; ring⟩

/-- **Exact state programming.** Every completed state has fractional part equal to its
target. -/
theorem programState_fract (b : ℕ) (g : ℕ → ℕ) (u : ℕ → ℚ) (k : ℕ)
    (hu : 0 ≤ u (k + 1) ∧ u (k + 1) < 1) :
    Int.fract (programState b g u (k + 1)) = u (k + 1) := by
  obtain ⟨z, hz⟩ := programCoeff_sub b (g (k + 1)) (programState b g u k) (u (k + 1))
  rw [Int.fract_eq_iff]
  refine ⟨hu.1, hu.2, z, ?_⟩
  simp only [programState]; rw [hz]; ring

private lemma den_add_int_dvd (q : ℚ) (z : ℤ) : (q + z).den ∣ q.den := by
  simp

/-- **Coefficient denominators.** If the previous state has fractional part `u_k`, the next
coefficient has denominator dividing `den u_(k+1) · den u_k`. -/
theorem programCoeff_den_dvd (b : ℕ) (g : ℕ → ℕ) (u : ℕ → ℚ) (k : ℕ)
    (prev : Int.fract (programState b g u k) = u k) :
    (programCoeffs b g u k).den ∣ (u (k + 1)).den * (u k).den := by
  obtain ⟨z, hz⟩ := programCoeff_sub b (g (k + 1)) (programState b g u k) (u (k + 1))
  have hR := Int.fract_add_floor (programState b g u k)
  rw [prev] at hR
  set w := ⌊programState b g u k⌋
  have expr : programCoeffs b g u k =
      (u (k + 1) + -((b : ℚ) ^ g (k + 1) * u k)) + ((z - (b : ℤ) ^ g (k + 1) * w : ℤ) : ℚ) := by
    unfold programCoeffs; rw [hz, ← hR]; push_cast; ring
  rw [expr]
  refine (den_add_int_dvd _ _).trans ((Rat.add_den_dvd _ _).trans ?_)
  rw [Rat.neg_den]
  refine Nat.mul_dvd_mul_left _ ((Rat.mul_den_dvd _ _).trans ?_)
  have : ((b : ℚ) ^ g (k + 1)).den = 1 := by
    rw [show (b : ℚ) ^ g (k + 1) = ((b ^ g (k + 1) : ℕ) : ℚ) by push_cast; rfl]
    exact Rat.den_natCast _
  rw [this, one_mul]

/-- With `u_0 = 0` and every target in `[0,1)`, all coefficient denominators obey the bound. -/
theorem programCoeffs_den_dvd (b : ℕ) (g : ℕ → ℕ) (u : ℕ → ℚ) (u0 : u 0 = 0)
    (hu : ∀ k, 0 ≤ u k ∧ u k < 1) (k : ℕ) :
    (programCoeffs b g u k).den ∣ (u (k + 1)).den * (u k).den := by
  apply programCoeff_den_dvd
  cases k with
  | zero => simp [programState, u0]
  | succ k => exact programState_fract b g u k (hu _)

/-- **Off-radix programming.** If every target denominator is a power of a prime `p`, so is
every coefficient denominator. -/
theorem programCoeffs_prime_power {b p : ℕ} (hp : p.Prime) (g : ℕ → ℕ) (u : ℕ → ℚ)
    (u0 : u 0 = 0) (hu : ∀ k, 0 ≤ u k ∧ u k < 1) (pow : ∀ k, ∃ e, (u k).den = p ^ e) (k : ℕ) :
    ∃ e, (programCoeffs b g u k).den = p ^ e := by
  obtain ⟨e1, h1⟩ := pow (k + 1)
  obtain ⟨e0, h0⟩ := pow k
  have := programCoeffs_den_dvd b g u u0 hu k
  rw [h1, h0, ← pow_add] at this
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).mp this
  exact ⟨e, he⟩

/-- **The state is the shifted prefix.** With gaps `g_(k+1) = n_(k+1) - n_k` of a monotone
schedule with `n_0 = 0`, the state `R_L` equals `b^(n_L) ∑_{k<L} c_(k+1) b^-n_(k+1)`. -/
theorem programState_eq_prefix {b : ℕ} (hb : 0 < b) (n g : ℕ → ℕ) (mono : Monotone n)
    (h0 : n 0 = 0) (hg : ∀ k, g (k + 1) = n (k + 1) - n k) (u : ℕ → ℚ) (L : ℕ) :
    programState b g u L =
      (b : ℚ) ^ n L * ∑ k ∈ range L, programCoeffs b g u k * ((b : ℚ) ^ n (k + 1))⁻¹ := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  induction L with
  | zero => simp [programState, h0]
  | succ L ih =>
    have step : programState b g u (L + 1) =
        (b : ℚ) ^ g (L + 1) * programState b g u L + programCoeffs b g u L := rfl
    have hle : n L ≤ n (L + 1) := mono (Nat.le_succ L)
    set S := ∑ k ∈ range L, programCoeffs b g u k * ((b : ℚ) ^ n (k + 1))⁻¹
    have hpow : (b : ℚ) ^ g (L + 1) * ((b : ℚ) ^ n L * S) = (b : ℚ) ^ n (L + 1) * S := by
      rw [← mul_assoc, ← pow_add, hg, Nat.sub_add_cancel hle]
    rw [step, ih, hpow, Finset.sum_range_succ, mul_add]
    congr 1
    rw [mul_comm (programCoeffs b g u L), ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hbq),
      one_mul]

/-- **Programmed orbit states.** The radix shift of the `L`-th prefix by its own last
insertion exponent has fractional part `u_L`. -/
theorem programmed_prefix_fract {b : ℕ} (hb : 0 < b) (n g : ℕ → ℕ) (mono : Monotone n)
    (h0 : n 0 = 0) (hg : ∀ k, g (k + 1) = n (k + 1) - n k) (u : ℕ → ℚ) (L : ℕ)
    (hu : 0 ≤ u (L + 1) ∧ u (L + 1) < 1) :
    Int.fract ((b : ℚ) ^ n (L + 1) * ∑ k ∈ range (L + 1),
        programCoeffs b g u k * ((b : ℚ) ^ n (k + 1))⁻¹) = u (L + 1) := by
  rw [← programState_eq_prefix hb n g mono h0 hg u (L + 1)]
  exact programState_fract b g u L hu

/-- **Retained denominator.** A completed state has the same reduced denominator as its
target; on an active interval with `u_k = 1/p^(e_k)` the state keeps exactly `p^(e_k)`. -/
theorem programState_den (b : ℕ) (g : ℕ → ℕ) (u : ℕ → ℚ) (k : ℕ)
    (hu : 0 ≤ u (k + 1) ∧ u (k + 1) < 1) :
    (programState b g u (k + 1)).den = (u (k + 1)).den := by
  have hf := programState_fract b g u k hu
  have h := Int.fract_add_floor (programState b g u (k + 1))
  rw [hf] at h
  apply Nat.dvd_antisymm
  · rw [← h]; exact den_add_int_dvd _ _
  · have : u (k + 1) = programState b g u (k + 1) + ((-⌊programState b g u (k + 1)⌋ : ℤ) : ℚ) := by
      push_cast; linarith
    rw [this]; exact den_add_int_dvd _ _

/-- **Retired states.** A zero target makes the completed state an integer, so the programmed
prefix contributes nothing modulo one at that insertion. -/
theorem programState_retired (b : ℕ) (g : ℕ → ℕ) (u : ℕ → ℚ) (k : ℕ) (hu : u (k + 1) = 0) :
    ∃ z : ℤ, programState b g u (k + 1) = z := by
  have hf := programState_fract b g u k ⟨hu.ge, by rw [hu]; exact one_pos⟩
  refine ⟨⌊programState b g u (k + 1)⌋, ?_⟩
  have h := Int.fract_add_floor (programState b g u (k + 1))
  rw [hf, hu, zero_add] at h
  exact h.symm

/-- **Programmed dense series.** Replacing each programmed term `c_(k+1) b^-n_(k+1)` by its
complete geometric group gives a dense, absolutely convergent series with positive raw
coefficients whose sum is the programmed number. -/
theorem programmed_dense_hasSum {b : ℕ} (hb : 2 ≤ b) (n g : ℕ → ℕ) (mono : StrictMono n)
    (h0 : n 0 = 0) (u : ℕ → ℚ) (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (compat : ∀ k, ∀ m ∈ Ioc (n k) (n (k + 1)),
      a m = (programCoeffs b g u k : ℝ) * (((b : ℝ) - 1) / ((b : ℝ) ^ (n (k + 1) - n k) - 1))) :
    HasSum (fun m => a m * ((b : ℝ) ^ m)⁻¹)
      (∑' k, (programCoeffs b g u k : ℝ) * ((b : ℝ) ^ n (k + 1))⁻¹) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  refine grouped_retirement_hasSum hb1 n mono h0 _ a (C := 1) (fun k => ?_) ha0 compat
  have h := programCoeff_mem b (g (k + 1)) (programState b g u k) (u (k + 1))
  have h1 : (0 : ℝ) < (programCoeffs b g u k : ℝ) := by exact_mod_cast h.1
  have h2 : (programCoeffs b g u k : ℝ) ≤ 1 := by exact_mod_cast h.2
  rw [abs_of_pos h1]; exact h2

/-! ### 4. Discrepancy transfer -/

/-- `y` lies within `ε` of some integer. -/
def Near (y ε : ℝ) : Prop := ∃ j : ℤ, |y - j| ≤ ε

open Classical in
/-- `E_N(ε)`: the number of positions `n < N` at which `b^n z` is farther than `ε` from every
integer. -/
noncomputable def farCount (b : ℕ) (z ε : ℝ) (N : ℕ) : ℕ :=
  ((range N).filter (fun n => ¬ Near ((b : ℝ) ^ n * z) ε)).card

theorem radixDiscrepancy_mem (b : ℕ) (x : ℝ) (N : ℕ) :
    0 ≤ radixDiscrepancy b x N ∧ radixDiscrepancy b x N ≤ 1 :=
  ⟨SharpTranslation.sampleDisc_nonneg _ _, SharpTranslation.sampleDisc_le_one _ _⟩

/-- Concentration near integers bounds the discrepancy deficit. The interior arc
avoids all good points, including samples at either end of the closed neighborhood. -/
theorem discrepancy_deficit_le (b : ℕ) (z : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) :
    1 - radixDiscrepancy b z N ≤ 2 * ε + (farCount b z ε N : ℝ) / N := by
  classical
  let E := (farCount b z ε N : ℝ) / N
  let D := radixDiscrepancy b z N
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 ≤ D := (radixDiscrepancy_mem b z N).1
  change 1 - D ≤ 2 * ε + E
  by_contra! h
  let η := (1 - D - 2 * ε - E) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have ordered : ε + η < 1 - ε := by dsimp [η]; linarith
  have disc := SharpTranslation.interval_le_sampleDisc (shift b z) N
    (add_nonneg hε hη.le) ordered (show 1 - ε ≤ 1 by linarith)
  change |frequency (shift b z) (ε+η) (1-ε) N - ((1-ε)-(ε+η))| ≤ D at disc
  have count : frequency (shift b z) (ε+η) (1-ε) N ≤ E := by
    unfold frequency E farCount
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro n hn
    obtain ⟨hnN, hmem⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnN, ?_⟩
    rintro ⟨j, hj⟩
    let y := (b : ℝ)^n * z
    change ε + η ≤ y - ↑⌊y⌋ ∧ y - ↑⌊y⌋ < 1 - ε at hmem
    change |y - ↑j| ≤ ε at hj
    rcases abs_le.mp hj with ⟨lo,hi⟩
    by_cases hfloor : j ≤ ⌊y⌋
    · have : (j : ℝ) ≤ (⌊y⌋ : ℤ) := by exact_mod_cast hfloor
      linarith [hmem.1]
    · have : (⌊y⌋ : ℝ) + 1 ≤ j := by exact_mod_cast (show ⌊y⌋+1 ≤ j by omega)
      linarith [hmem.2]
  have low := (abs_le.mp disc).1
  dsimp [η] at low
  change frequency (shift b z) (ε + (1-D-2*ε-E)/2) (1-ε) N ≤ E at count
  linarith

/-- One-sided finite comparison obtained from the sharp translation law. -/
theorem discrepancy_add_le (b : ℕ) (x z : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) :
    radixDiscrepancy b (x + z) N ≤
      radixDiscrepancy b x N + 2 * ε + (farCount b z ε N : ℝ) / N := by
  have h := (abs_le.mp (SharpTranslation.sharp_translation b x z hN)).2
  linarith [discrepancy_deficit_le b z hε N]

theorem near_neg {y ε : ℝ} : Near (-y) ε ↔ Near y ε := by
  constructor <;> rintro ⟨j, hj⟩ <;> refine ⟨-j, ?_⟩ <;> push_cast <;>
    [rw [show y - -(j : ℝ) = -(-y - j) by ring, abs_neg]; rw [show -y - -(j : ℝ) = -(y - j) by ring, abs_neg]] <;> exact hj

theorem farCount_neg (b : ℕ) (z ε : ℝ) (N : ℕ) : farCount b (-z) ε N = farCount b z ε N := by
  unfold farCount
  congr 1
  ext n
  simp only [mem_filter, mul_neg, near_neg]

/-- **Discrepancy transfer theorem.** For every real `x`, `z`, every `ε ≥ 0` and `N > 0`,
`|D_N(x+z) - D_N(x)| ≤ 2ε + E_N(ε)/N`, with `D_N` the extreme interval discrepancy over
half-open subintervals of `[0,1)` and `E_N(ε)` the number of positions `n < N` at which
`b^n z` is farther than `ε` from every integer. -/
theorem discrepancy_transfer (b : ℕ) (x z : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy b (x + z) N - radixDiscrepancy b x N| ≤
      2 * ε + (farCount b z ε N : ℝ) / N := by
  exact (SharpTranslation.sharp_translation b x z hN).trans (discrepancy_deficit_le b z hε N)

/-- **Asymptotic transfer.** If `E_N(ε)/N → 0` for every `ε > 0`, the discrepancies of `x+z`
and `x` differ by `o(1)`; in particular their upper and lower limits coincide. -/
theorem discrepancy_transfer_tendsto (b : ℕ) (x z : ℝ)
    (sparse : ∀ ε > 0, Tendsto (fun N => (farCount b z ε N : ℝ) / N) atTop (𝓝 0)) :
    Tendsto (fun N => radixDiscrepancy b (x + z) N - radixDiscrepancy b x N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (sparse (η / 4) (by positivity)) (η / 2)
    (by positivity)
  refine ⟨M + 1, fun N hN => ?_⟩
  have hb := discrepancy_transfer b x z (ε := η / 4) (by positivity) (show 0 < N by omega)
  have hf := hM N (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hf
  rw [Real.dist_eq, sub_zero]
  linarith

/-- Integer translation leaves every radix shift unchanged. -/
theorem shift_add_int (b : ℕ) (x : ℝ) (k : ℤ) (n : ℕ) : shift b (x + k) n = shift b x n := by
  unfold shift
  rw [mul_add, show (b : ℝ) ^ n * (k : ℝ) = ((b ^ n * k : ℤ) : ℝ) by push_cast; ring,
    Int.fract_add_intCast]

/-- A `b`-adic rational `A/b^K` leaves every shift from position `K` onward unchanged. -/
theorem shift_add_radix_rat {b : ℕ} (hb : 0 < b) (x : ℝ) (A : ℤ) {K n : ℕ} (hn : K ≤ n) :
    shift b (x + A / (b : ℝ) ^ K) n = shift b x n := by
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold shift
  have : (b : ℝ) ^ n * (x + A / (b : ℝ) ^ K) = (b : ℝ) ^ n * x + ((A * b ^ (n - K) : ℤ) : ℝ) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_sub_cancel_left]
    push_cast
    rw [pow_add]
    field_simp
  rw [this, Int.fract_add_intCast]

/-- `E_N(0) ≤ K` whenever every shift `b^n z` with `n ≥ K` is an integer. -/
theorem farCount_le_of_eventually_int (b : ℕ) {z : ℝ} {K : ℕ}
    (hz : ∀ n, K ≤ n → ∃ j : ℤ, (b : ℝ) ^ n * z = j) (N : ℕ) :
    farCount b z 0 N ≤ K := by
  classical
  unfold farCount
  refine (card_le_card (t := range K) ?_).trans_eq (card_range K)
  intro n hn
  rw [mem_filter] at hn
  rw [mem_range]
  by_contra hK
  push Not at hK
  apply hn.2
  obtain ⟨j, hj⟩ := hz n hK
  exact ⟨j, by rw [hj, sub_self, abs_zero]⟩

/-- **Eventually integral transfer.** If `b^n z ∈ ℤ` for all `n ≥ K`, then
`|D_N(x+z) - D_N(x)| ≤ min(1, K/N)`. This covers every `b`-adic rational and every finite sum
of eventually integral contributions. -/
theorem discrepancy_eventually_int (b : ℕ) (x : ℝ) {z : ℝ} {K : ℕ}
    (hz : ∀ n, K ≤ n → ∃ j : ℤ, (b : ℝ) ^ n * z = j) {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy b (x + z) N - radixDiscrepancy b x N| ≤ min 1 ((K : ℝ) / N) := by
  refine le_min ?_ ?_
  · have h1 := radixDiscrepancy_mem b (x + z) N
    have h2 := radixDiscrepancy_mem b x N
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have h := discrepancy_transfer b x z (ε := 0) le_rfl hN
    have hK : (farCount b z 0 N : ℝ) ≤ K := by
      exact_mod_cast farCount_le_of_eventually_int b hz N
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    calc _ ≤ 2 * 0 + (farCount b z 0 N : ℝ) / N := h
      _ ≤ (K : ℝ) / N := by rw [mul_zero, zero_add]; exact div_le_div_of_nonneg_right hK hNr.le

/-- `E_N(0) ≤ K` for the `b`-adic rational `A/b^K`. -/
theorem farCount_radix_rat_le {b : ℕ} (hb : 0 < b) (A : ℤ) (K N : ℕ) :
    farCount b (A / (b : ℝ) ^ K) 0 N ≤ K := by
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  refine farCount_le_of_eventually_int b (fun n hn => ⟨A * b ^ (n - K), ?_⟩) N
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left]
  push_cast
  rw [pow_add]
  field_simp

/-- **Finite `b`-adic transfer.** `|D_N(x + A/b^K) - D_N(x)| ≤ min(1, K/N)`. -/
theorem discrepancy_radix_rat {b : ℕ} (hb : 0 < b) (x : ℝ) (A : ℤ) (K : ℕ) {N : ℕ}
    (hN : 0 < N) :
    |radixDiscrepancy b (x + A / (b : ℝ) ^ K) N - radixDiscrepancy b x N| ≤
      min 1 ((K : ℝ) / N) := by
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  refine discrepancy_eventually_int b x (fun n hn => ⟨A * b ^ (n - K), ?_⟩) hN
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left]
  push_cast
  rw [pow_add]
  field_simp

/-- Integer translations preserve the discrepancy at every cutoff. -/
theorem discrepancy_add_int (b : ℕ) (x : ℝ) (k : ℤ) (N : ℕ) :
    radixDiscrepancy b (x + k) N = radixDiscrepancy b x N := by
  unfold radixDiscrepancy frequency
  simp_rw [shift_add_int]

/-! ### 4b. Sparse integer perturbations -/

/-- The sparse perturbation `∑_k A_k b^-m_k`. -/
noncomputable def sparseValue (b : ℕ) (m : ℕ → ℕ) (A : ℕ → ℤ) : ℝ :=
  ∑' k, (A k : ℝ) * ((b : ℝ) ^ m k)⁻¹

/-- **Integer head, small tail.** If the insertions with index below `K` lie at or before `n`
and the next lies at `m_K > n`, then `b^n ∑ A_k b^-m_k` is within `2B b^-(m_K-n)` of an
integer, where `|A_k| ≤ B`. -/
theorem sparse_near {b : ℕ} (hb : 2 ≤ b) {m : ℕ → ℕ} (mono : StrictMono m) {A : ℕ → ℤ}
    {B : ℝ} (hA : ∀ k, |(A k : ℝ)| ≤ B) {n K : ℕ} (hK1 : ∀ k < K, m k ≤ n) (hK2 : n < m K) :
    Near ((b : ℝ) ^ n * sparseValue b m A) (2 * B * ((b : ℝ)⁻¹) ^ (m K - n)) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hr : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have hB : 0 ≤ B := (abs_nonneg _).trans (hA 0)
  set f : ℕ → ℝ := fun k => (A k : ℝ) * ((b : ℝ) ^ m k)⁻¹ with hf
  have hz : sparseValue b m A = ∑' k, f k := rfl
  have fbound : ∀ k, |f k| ≤ B * ((b : ℝ)⁻¹) ^ m k := by
    intro k
    rw [hf, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hb0 _)), inv_pow]
    exact mul_le_mul_of_nonneg_right (hA k) (by positivity)
  have hsum : Summable f := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr).mul_left B)
      (fun k => ?_)
    rw [Real.norm_eq_abs]
    exact (fbound k).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr.le (mono.id_le k)) hB)
  have head : ∃ j : ℤ, (b : ℝ) ^ n * ∑ k ∈ range K, f k = j := by
    refine ⟨∑ k ∈ range K, A k * (b : ℤ) ^ (n - m k), ?_⟩
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hle := hK1 k (mem_range.mp hk)
    have hpow : (b : ℝ) ^ n = (b : ℝ) ^ (n - m k) * (b : ℝ) ^ m k := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hf, hpow]
    field_simp
  obtain ⟨j, hj⟩ := head
  refine ⟨j, ?_⟩
  have split := hsum.sum_add_tsum_nat_add K
  have hrest : (b : ℝ) ^ n * sparseValue b m A - j = (b : ℝ) ^ n * ∑' i, f (i + K) := by
    rw [← hj, hz, ← split]; ring
  rw [hrest]
  set r : ℝ := (b : ℝ)⁻¹
  have tailb : ∀ i, |(b : ℝ) ^ n * f (i + K)| ≤ B * r ^ (m K - n) * r ^ i := by
    intro i
    rw [abs_mul, abs_of_pos (pow_pos hb0 n)]
    have hexp : n + (m K - n) + i ≤ m (i + K) := by have := mono.add_le_nat i K; omega
    calc (b : ℝ) ^ n * |f (i + K)| ≤ (b : ℝ) ^ n * (B * r ^ m (i + K)) :=
          mul_le_mul_of_nonneg_left (fbound _) (by positivity)
      _ ≤ (b : ℝ) ^ n * (B * r ^ (n + (m K - n) + i)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr0 hr.le hexp) hB) (by positivity)
      _ = B * r ^ (m K - n) * r ^ i := by
          rw [pow_add, pow_add]
          have : (b : ℝ) ^ n * r ^ n = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hb0.ne', one_pow]
          linear_combination (B * r ^ (m K - n) * r ^ i) * this
  have gsum : Summable (fun i => B * r ^ (m K - n) * r ^ i) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have nsum : Summable (fun i => ‖(b : ℝ) ^ n * f (i + K)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => by rw [Real.norm_eq_abs]; exact tailb i) gsum
  have hhalf : (1 - r)⁻¹ ≤ 2 := by
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have : r ≤ 2⁻¹ := inv_anti₀ (by norm_num) hb2
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  rw [← tsum_mul_left]
  calc |∑' i, (b : ℝ) ^ n * f (i + K)| = ‖∑' i, (b : ℝ) ^ n * f (i + K)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' i, ‖(b : ℝ) ^ n * f (i + K)‖ := norm_tsum_le_tsum_norm nsum
    _ ≤ ∑' i, B * r ^ (m K - n) * r ^ i :=
        Summable.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact tailb i) nsum gsum
    _ = B * r ^ (m K - n) * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
    _ ≤ B * r ^ (m K - n) * 2 := mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = 2 * B * r ^ (m K - n) := by ring

/-- **Counting far positions.** If `2B b^-w ≤ ε`, every position at which a sparse
perturbation is farther than `ε` from an integer lies in one of the windows of length `w`
before an insertion, so `E_N(ε) ≤ w · #{k : m_k < N + w}`. -/
theorem sparse_farCount_le {b : ℕ} (hb : 2 ≤ b) {m : ℕ → ℕ} (mono : StrictMono m)
    {A : ℕ → ℤ} {B ε : ℝ} (hA : ∀ k, |(A k : ℝ)| ≤ B) {w : ℕ}
    (hw : 2 * B * ((b : ℝ)⁻¹) ^ w ≤ ε) (N : ℕ) :
    farCount b (sparseValue b m A) ε N ≤
      w * ((range (N + w)).filter (fun k => m k < N + w)).card := by
  classical
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hr : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have hB : 0 ≤ B := (abs_nonneg _).trans (hA 0)
  set S := (range (N + w)).filter (fun k => m k < N + w)
  have ex : ∀ n, ∃ K, n < m K :=
    fun n => ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (mono.id_le _)⟩
  let nxt : ℕ → ℕ := fun n => Nat.find (ex n)
  have nxt_spec : ∀ n, n < m (nxt n) := fun n => Nat.find_spec (ex n)
  have nxt_min : ∀ n, ∀ k < nxt n, m k ≤ n := fun n k hk => not_lt.mp (Nat.find_min (ex n) hk)
  unfold farCount
  calc _ ≤ (S ×ˢ range w).card := by
        refine card_le_card_of_injOn (fun n => (nxt n, m (nxt n) - n)) ?_ ?_
        · intro n hn
          obtain ⟨hnN, hfar⟩ := mem_filter.mp (mem_coe.mp hn)
          have hd : m (nxt n) - n < w := by
            by_contra h
            push Not at h
            apply hfar
            obtain ⟨j, hj⟩ := sparse_near hb mono hA (nxt_min n) (nxt_spec n)
            refine ⟨j, hj.trans (hw.trans' ?_)⟩
            exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr.le h) (by positivity)
          have hN : n < N := mem_range.mp hnN
          have hmK : m (nxt n) < N + w := by have := nxt_spec n; omega
          rw [mem_coe, mem_product, mem_filter, mem_range, mem_range]
          exact ⟨⟨lt_of_le_of_lt (mono.id_le _) hmK, hmK⟩, hd⟩
        · intro n1 _ n2 _ heq
          simp only [Prod.mk.injEq] at heq
          obtain ⟨h1, h2⟩ := heq
          have s1 := nxt_spec n1
          have s2 := nxt_spec n2
          rw [h1] at s1 h2
          omega
    _ = w * S.card := by rw [card_product, card_range, mul_comm]

/-- **Sparse discrepancy transfer.** For a sparse integer perturbation with `|A_k| ≤ B` and any
`w` with `2B b^-w ≤ ε`, `|D_N(x+z) - D_N(x)| ≤ 2ε + w · #{k : m_k < N+w} / N`. -/
theorem sparse_discrepancy_transfer {b : ℕ} (hb : 2 ≤ b) {m : ℕ → ℕ} (mono : StrictMono m)
    {A : ℕ → ℤ} {B ε : ℝ} (hA : ∀ k, |(A k : ℝ)| ≤ B) (hε : 0 ≤ ε) {w : ℕ}
    (hw : 2 * B * ((b : ℝ)⁻¹) ^ w ≤ ε) (x : ℝ) {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy b (x + sparseValue b m A) N - radixDiscrepancy b x N| ≤
      2 * ε + ((w * ((range (N + w)).filter (fun k => m k < N + w)).card : ℕ) : ℝ) / N := by
  have h := discrepancy_transfer b x (sparseValue b m A) hε hN
  have hc := sparse_farCount_le hb mono hA hw N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' : (farCount b (sparseValue b m A) ε N : ℝ) ≤
      ((w * ((range (N + w)).filter (fun k => m k < N + w)).card : ℕ) : ℝ) := by
    exact_mod_cast hc
  linarith [div_le_div_of_nonneg_right hc' hNr.le]

/-- Quadratic insertion positions `(k+1)(k+2)` below `M` number at most `⌊√M⌋`. -/
theorem quadratic_insertions_le (M : ℕ) :
    ((range M).filter (fun k => (k + 1) * (k + 2) < M)).card ≤ Nat.sqrt M := by
  refine (card_le_card (t := range (Nat.sqrt M)) ?_).trans_eq (card_range _)
  intro k hk
  rw [mem_filter] at hk
  rw [mem_range, ← Nat.succ_le_iff, Nat.le_sqrt]
  nlinarith [hk.2]

/-- **The flagship sparse perturbation** `Z = ∑_{k≥1} 2^-(k(k+1))`. For every real `x`,
cutoff `N > 0` and window `w`,
`|D_N(x+Z;2) - D_N(x;2)| ≤ 4·2^-w + w·⌊√(N+w)⌋/N`; the choice `w ≍ log₂ N` gives
`O(log N/√N)`. -/
theorem quadratic_sparse_transfer (x : ℝ) {N : ℕ} (hN : 0 < N) (w : ℕ) :
    |radixDiscrepancy 2 (x + sparseValue 2 (fun k => (k + 1) * (k + 2)) (fun _ => 1)) N -
        radixDiscrepancy 2 x N| ≤
      4 * (2⁻¹ : ℝ) ^ w + ((w * Nat.sqrt (N + w) : ℕ) : ℝ) / N := by
  have mono : StrictMono (fun k : ℕ => (k + 1) * (k + 2)) := by
    intro i j hij; dsimp only; nlinarith
  have h := sparse_discrepancy_transfer (b := 2) le_rfl mono (A := fun _ => 1) (B := 1)
    (ε := 2 * (2⁻¹ : ℝ) ^ w) (fun _ => by simp) (by positivity) (w := w)
    (by push_cast; linarith) x hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ((w * ((range (N + w)).filter (fun k => (k + 1) * (k + 2) < N + w)).card : ℕ) : ℝ)
      ≤ ((w * Nat.sqrt (N + w) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left w (quadratic_insertions_le (N + w))
  calc _ ≤ 2 * (2 * (2⁻¹ : ℝ) ^ w) +
        ((w * ((range (N + w)).filter (fun k => (k + 1) * (k + 2) < N + w)).card : ℕ) : ℝ) / N := h
    _ ≤ 4 * (2⁻¹ : ℝ) ^ w + ((w * Nat.sqrt (N + w) : ℕ) : ℝ) / N := by
        have := div_le_div_of_nonneg_right hc hNr.le
        linarith

end NormalityChecker.Phase18Synthetic
