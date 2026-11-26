module

public import NormalityChecker.CoefficientTransfer
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Nat.Factorization.PrimePow

/-! # Finite arithmetic and combinatorial core for the sub-threshold width law (Track A)

Kernel-checked finite lemmas supporting Phase 21 Track A (exact base-`b` discrepancy constants
across all radices `b ≥ 2` for multiplicative Lambert series, Euler's square `E_b²`, and
binary quadratic forms):

1. **Circle-distance lower bounds for isolated displaced sources (`dist0_div_pow_ge`,
   `dist0_div_pow_eq`, `card_far_in_gap_ge`).**
   For any radix `b ≥ 2`, any integer `C` not divisible by `b` with `b^(u - 1) ≤ |C| < b^u`,
   any small perturbation `|A| ≤ 1/2`, and any `η > 0` with `2 * η * b^lam ≤ 1`:
   - For every `1 ≤ j ≤ lam`, `dist0 ((C + A) / b^j) ≥ 1 / (2 * b^j) ≥ η`.
   - For every `j ≥ u + 1`, `dist0 ((C + A) / b^j) = |C + A| / b^j`, which is `≥ η` for
     `u + 1 ≤ j ≤ u + lam - 1`.
   - Consequently, inside `Icc 1 (u + lam - 1)` at least `min u lam + lam - 1` shifts `j`
     satisfy `η ≤ dist0 ((C + A) / b^j)`. (Note that for `u > lam` the two guaranteed bands
     `[1, lam]` and `[u + 1, u + lam - 1]` are disjoint inside `[1, u + lam - 1]`.)

2. **Isolated-tail Markov bound (`card_large_tail_le`).**
   If right-isolation at radius `R` scales `A t = A (t + R) / b^R` on a finite set `T` of
   sources with `t + R < M`, then the number of `t ∈ T` with `|A t| > 1/2` is at most
   `(2 / b^R) * ∑_{s < M} |A s|`.

3. **Exact first-moment prime-power identity (`sum_log_eq_sum_primePow`).**
   For any multiplicative `c : ℕ → ℕ` (`c 1 = 1` and `c (m * n) = c m * c n` for coprime `m, n`),
   `∑_{n ≤ N, c n ≠ 0} log (c n) = ∑_{q = p^e ≤ N, c q ≠ 0} log (c q) · #{m ≤ N/q : c m ≠ 0, p ∤ m}`,
   providing the exact algebraic identity behind uniform integrability of `log c(n)` (Track A1).

4. **Finite width-law upper bound (`width_law_upper`) and odd-prime valuation lower bound
   (`padicVal_succ_pos_imp`).**
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.RadixWidthLaw

open CoefficientTransfer SharpTranslation Phase18Synthetic

/-! ### Part 1: Distance to the nearest integer and guaranteed far shifts in a gap -/

/-- Distance from a real number to the nearest integer. -/
noncomputable def dist0 (y : ℝ) : ℝ := |y - (round y : ℝ)|

theorem dist0_le_abs_sub_int (y : ℝ) (k : ℤ) : dist0 y ≤ |y - (k : ℝ)| := by
  unfold dist0
  have h1 := abs_sub_round y
  have h2 : |y - (round y : ℝ)| ≤ |y - (k : ℝ)| := by
    by_cases hle : |y - (k : ℝ)| < 1 / 2
    · have hk : round y = k := by
        rw [round_eq_iff]
        rw [abs_lt] at hle
        constructor <;> linarith
      rw [hk]
    · push Not at hle
      exact h1.trans hle
  exact h2

/-- **Lower-band circle-distance bound (Track A, Lemma 3.2(1)).**
For any radix `b ≥ 2`, integer `C` with `b ∤ C`, perturbation `|A| ≤ 1/2`, and `j ≥ 1`,
`dist0 ((C + A) / b^j) ≥ 1 / (2 * b^j)`. -/
theorem dist0_div_pow_ge {b : ℕ} (hb : 2 ≤ b) {C : ℤ} (hC : ¬ (b : ℤ) ∣ C)
    {A : ℝ} (hA : |A| ≤ 1 / 2) {j : ℕ} (hj : 1 ≤ j) :
    ((b : ℝ) ^ j)⁻¹ / 2 ≤ dist0 ((C + A) / (b : ℝ) ^ j) := by
  unfold dist0
  set k : ℤ := round ((C + A) / (b : ℝ) ^ j)
  have hb_pos : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  have hne : C - k * (b : ℤ) ^ j ≠ 0 := by
    intro h0
    have hC_eq : C = k * (b : ℤ) ^ j := sub_eq_zero.mp h0
    apply hC
    have hpow : (b : ℤ) ∣ (b : ℤ) ^ j := dvd_pow_self (b : ℤ) (by omega)
    rw [hC_eq]
    exact dvd_mul_of_dvd_right hpow k
  have hge1 : (1 : ℝ) ≤ |((C - k * (b : ℤ) ^ j : ℤ) : ℝ)| := by
    have : 1 ≤ (C - k * (b : ℤ) ^ j).natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne)
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast this
  have hrew : (C + A) / (b : ℝ) ^ j - (k : ℝ) =
      (((C - k * (b : ℤ) ^ j : ℤ) : ℝ) + A) / (b : ℝ) ^ j := by
    push_cast
    field_simp [hb_pos.ne']
    ring
  rw [hrew, abs_div, abs_of_pos hb_pos]
  have htri : (1 / 2 : ℝ) ≤ |((C - k * (b : ℤ) ^ j : ℤ) : ℝ) + A| := by
    have hrev := abs_sub_abs_le_abs_add ((C - k * (b : ℤ) ^ j : ℤ) : ℝ) A
    linarith
  have hdiv := div_le_div_of_nonneg_right htri hb_pos.le
  have heq : (1 / 2 : ℝ) / (b : ℝ) ^ j = ((b : ℝ) ^ j)⁻¹ / 2 := by ring
  linarith

/-- **Upper-band exact circle distance (Track A, Lemma 3.2(2)).**
If `b ≥ 2`, `|C| < b^u`, `j ≥ u + 1`, and `|A| ≤ 1/2`, then
`dist0 ((C + A) / b^j) = |C + A| / b^j`. -/
theorem dist0_div_pow_eq {b : ℕ} (hb : 2 ≤ b) {C : ℤ} {u j : ℕ}
    (hu : |(C : ℝ)| < (b : ℝ) ^ u) (hj : u + 1 ≤ j) {A : ℝ} (hA : |A| ≤ 1 / 2) :
    dist0 ((C + A) / (b : ℝ) ^ j) = |C + A| / (b : ℝ) ^ j := by
  have hb_pos : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  have habs_eq : (C.natAbs : ℝ) = |(C : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    simp
  have hC_int : C.natAbs < b ^ u := by
    have h1 : (C.natAbs : ℝ) < ((b ^ u : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h1
  have hC_le : |(C : ℝ)| ≤ (b : ℝ) ^ u - 1 := by
    have h1 : C.natAbs + 1 ≤ b ^ u := hC_int
    have h2 : (C.natAbs : ℝ) + 1 ≤ (b : ℝ) ^ u := by exact_mod_cast h1
    linarith
  have hpow_ge : 2 * (b : ℝ) ^ u ≤ (b : ℝ) ^ j := by
    have h1 : 2 * b ^ u ≤ b ^ (u + 1) := by
      rw [pow_succ']
      exact Nat.mul_le_mul_right (b ^ u) hb
    have h2 : b ^ (u + 1) ≤ b ^ j := Nat.pow_le_pow_right (by omega) hj
    exact_mod_cast (h1.trans h2)
  have hlt_half : |(C + A) / (b : ℝ) ^ j| < 1 / 2 := by
    rw [abs_div, abs_of_pos hb_pos, div_lt_iff₀ hb_pos]
    have h1 : |C + A| ≤ |(C : ℝ)| + |A| := abs_add_le _ _
    linarith
  have hround : round ((C + A) / (b : ℝ) ^ j) = 0 := by
    rw [round_eq_iff]
    rw [abs_lt] at hlt_half
    simp only [Int.cast_zero]
    exact ⟨by linarith [hlt_half.1], by linarith [hlt_half.2]⟩
  unfold dist0
  rw [hround, Int.cast_zero, sub_zero, abs_div, abs_of_pos hb_pos]

/-- **Guaranteed far shifts per isolated source (Track A, Lemma 3.2(3)).**
If `b ≥ 2`, `b ∤ C`, `1 ≤ u`, `1 ≤ lam`, `b^(u - 1) ≤ |C| < b^u`, `|A| ≤ 1/2`, and
`2 * η * b^lam ≤ 1`, then at least `min u lam + lam - 1` shifts `j ∈ Icc 1 (u + lam - 1)`
satisfy `η ≤ dist0 ((C + A) / b^j)`. -/
theorem card_far_in_gap_ge {b : ℕ} (hb : 2 ≤ b) {C : ℤ} (hC : ¬ (b : ℤ) ∣ C) {u lam : ℕ}
    (hu1 : 1 ≤ u) (hlam1 : 1 ≤ lam)
    (hu : (b : ℝ) ^ (u - 1) ≤ |(C : ℝ)|) (hu' : |(C : ℝ)| < (b : ℝ) ^ u)
    {A η : ℝ} (hA : |A| ≤ 1 / 2) (hη : 2 * η * (b : ℝ) ^ lam ≤ 1) :
    min u lam + lam - 1 ≤
      ((Icc 1 (u + lam - 1)).filter
        (fun j => η ≤ dist0 ((C + A) / (b : ℝ) ^ j))).card := by
  let S₁ := Icc 1 (min lam (u + lam - 1))
  let S₂ := Icc (u + 1) (u + lam - 1)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hη_le : η ≤ ((b : ℝ) ^ lam)⁻¹ / 2 := by
    have hrew : ((b : ℝ) ^ lam)⁻¹ / 2 = 1 / (2 * (b : ℝ) ^ lam) := by ring
    rw [hrew, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (b : ℝ) ^ lam)]
    linarith
  have hsub1 : S₁ ⊆ (Icc 1 (u + lam - 1)).filter (fun j => η ≤ dist0 ((C + A) / (b : ℝ) ^ j)) := by
    intro j hj
    obtain ⟨hj1, hjmax⟩ := mem_Icc.mp hj
    have hj_lam : j ≤ lam := hjmax.trans (min_le_left _ _)
    have hj_top : j ≤ u + lam - 1 := hjmax.trans (min_le_right _ _)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hj1, hj_top⟩, ?_⟩
    have hpow_le : (b : ℝ) ^ j ≤ (b : ℝ) ^ lam := pow_le_pow_right₀ hb1 hj_lam
    have hinv_ge : ((b : ℝ) ^ lam)⁻¹ ≤ ((b : ℝ) ^ j)⁻¹ :=
      inv_anti₀ (by positivity) hpow_le
    have hdist := dist0_div_pow_ge hb hC hA hj1
    linarith
  have hsub2 : S₂ ⊆ (Icc 1 (u + lam - 1)).filter (fun j => η ≤ dist0 ((C + A) / (b : ℝ) ^ j)) := by
    intro j hj
    obtain ⟨hju, hj_top⟩ := mem_Icc.mp hj
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hj_top⟩, ?_⟩
    rw [dist0_div_pow_eq hb hu' hju hA]
    have hbu1_ge1 : (1 : ℝ) ≤ (b : ℝ) ^ (u - 1) := one_le_pow₀ hb1
    have hCA : (b : ℝ) ^ (u - 1) / 2 ≤ |C + A| := by
      have hrev := abs_sub_abs_le_abs_add (C : ℝ) A
      linarith
    have hpow_le : (b : ℝ) ^ j ≤ (b : ℝ) ^ (u - 1) * (b : ℝ) ^ lam := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hb1 (by omega)
    have hdiv_ge : ((b : ℝ) ^ lam)⁻¹ / 2 ≤ |C + A| / (b : ℝ) ^ j := by
      have hbj_pos : (0 : ℝ) < (b : ℝ) ^ j := by positivity
      have hbu_pos : (0 : ℝ) < (b : ℝ) ^ (u - 1) := by positivity
      have hbl_pos : (0 : ℝ) < (b : ℝ) ^ lam := by positivity
      calc ((b : ℝ) ^ lam)⁻¹ / 2
          = ((b : ℝ) ^ (u - 1) / 2) / ((b : ℝ) ^ (u - 1) * (b : ℝ) ^ lam) := by
            field_simp [hbu_pos.ne', hbl_pos.ne']
        _ ≤ |C + A| / (b : ℝ) ^ j := by
            exact div_le_div₀ (by positivity) hCA hbj_pos hpow_le
    linarith
  have hunion_sub : S₁ ∪ S₂ ⊆
      (Icc 1 (u + lam - 1)).filter (fun j => η ≤ dist0 ((C + A) / (b : ℝ) ^ j)) :=
    union_subset hsub1 hsub2
  have hcard_union : min u lam + lam - 1 ≤ (S₁ ∪ S₂).card := by
    by_cases hle : u ≤ lam
    · have hmin : min u lam = u := min_eq_left hle
      have hcov : Icc 1 (u + lam - 1) ⊆ S₁ ∪ S₂ := by
        intro j hj
        obtain ⟨hj1, hj_top⟩ := mem_Icc.mp hj
        rw [mem_union]
        by_cases hjL : j ≤ lam
        · left; exact mem_Icc.mpr ⟨hj1, le_min hjL hj_top⟩
        · right; exact mem_Icc.mpr ⟨by omega, hj_top⟩
      calc min u lam + lam - 1 = u + lam - 1 := by rw [hmin]
        _ = (Icc 1 (u + lam - 1)).card := by rw [Nat.card_Icc]; omega
        _ ≤ (S₁ ∪ S₂).card := card_le_card hcov
    · push Not at hle
      have hmin : min u lam = lam := min_eq_right hle.le
      have hdisj : Disjoint S₁ S₂ := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        have h1 : j ≤ lam := (mem_Icc.mp hj1).2.trans (min_le_left _ _)
        have h2 : u + 1 ≤ j := (mem_Icc.mp hj2).1
        omega
      rw [card_union_of_disjoint hdisj]
      have hc1 : S₁.card = lam := by
        simp only [S₁, Nat.card_Icc]
        have : min lam (u + lam - 1) = lam := min_eq_left (by omega)
        rw [this]; omega
      have hc2 : S₂.card = lam - 1 := by
        simp only [S₂, Nat.card_Icc]; omega
      omega
  exact hcard_union.trans (card_le_card hunion_sub)

/-! ### Part 2: Isolated-tail Markov bound (Track A, step E4) -/

/-- **Isolated-tail Markov bound (Track A, step E4).**
If `A t = A (t + R) / b^R` on a finite set `T` with `t + R < M`, then
`#{t ∈ T : |A t| > 1/2} ≤ (2 / b^R) * ∑_{s < M} |A s|`. -/
theorem card_large_tail_le {b : ℕ} (hb : 2 ≤ b) (T : Finset ℕ) (R : ℕ)
    (A : ℕ → ℝ) (hscale : ∀ t ∈ T, A t = A (t + R) / (b : ℝ) ^ R) (M : ℕ)
    (hT : ∀ t ∈ T, t + R < M) :
    ((T.filter fun t => (1 / 2 : ℝ) < |A t|).card : ℝ) ≤
      2 / (b : ℝ) ^ R * ∑ s ∈ range M, |A s| := by
  have hbR_pos : (0 : ℝ) < (b : ℝ) ^ R := by positivity
  let F := T.filter (fun t => (1 / 2 : ℝ) < |A t|)
  have h1 : (F.card : ℝ) * (1 / 2 : ℝ) ≤ ∑ t ∈ F, |A t| := by
    calc (F.card : ℝ) * (1 / 2 : ℝ)
        = ∑ _t ∈ F, (1 / 2 : ℝ) := by simp
      _ ≤ ∑ t ∈ F, |A t| := Finset.sum_le_sum (fun t ht => (mem_filter.mp ht).2.le)
  have h2 : ∑ t ∈ F, |A t| ≤ (∑ s ∈ range M, |A s|) / (b : ℝ) ^ R := by
    have hrew : ∑ t ∈ F, |A t| = (∑ t ∈ F, |A (t + R)|) / (b : ℝ) ^ R := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [hscale t (mem_filter.mp ht).1, abs_div, abs_of_pos hbR_pos]
    rw [hrew]
    refine div_le_div_of_nonneg_right ?_ hbR_pos.le
    have hinj : Set.InjOn (fun t : ℕ => t + R) (F : Set ℕ) :=
      fun x _ y _ h => by simp only at h; omega
    rw [← Finset.sum_image (f := fun s => |A s|) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    exact mem_range.mpr (hT t (mem_filter.mp ht).1)
  have h3 : (F.card : ℝ) ≤ 2 * ((∑ s ∈ range M, |A s|) / (b : ℝ) ^ R) := by linarith
  have h4 : 2 * ((∑ s ∈ range M, |A s|) / (b : ℝ) ^ R) =
      2 / (b : ℝ) ^ R * ∑ s ∈ range M, |A s| := by ring
  linarith

/-! ### Part 3: Exact first-moment identity for multiplicative functions (Track A1, Lemma 2.1) -/

/-- The least prime factor of a prime power `p^e` (`e > 0`) is `p`. -/
private lemma minFac_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    (p ^ e).minFac = p := by
  have hne1 : p ^ e ≠ 1 := (one_lt_pow₀ hp.one_lt he).ne'
  have hpr : (p ^ e).minFac.Prime := Nat.minFac_prime hne1
  have hdvd : (p ^ e).minFac ∣ p := hpr.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ e))
  exact (Nat.prime_dvd_prime_iff_eq hpr hp).mp hdvd

/-- For a multiplicative `c : ℕ → ℕ`, `c n` factors over exact prime-power divisors of `n`. -/
private lemma mul_prod_primePow {c : ℕ → ℕ} (h1 : c 1 = 1)
    (hmul : ∀ m n, Nat.Coprime m n → c (m * n) = c m * c n) {n : ℕ} (hn : n ≠ 0) :
    c n = ∏ p ∈ n.primeFactors, c (p ^ n.factorization p) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · simp [h1]
    · set p : ℕ := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      set e : ℕ := n.factorization p
      have he_pos : 0 < e := hp.factorization_pos_of_dvd hn (Nat.minFac_dvd n)
      set m : ℕ := n / p ^ e
      have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
      have hn_eq : p ^ e * m = n := Nat.mul_div_cancel' hpe_dvd
      have hm_ne : m ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hn_eq; exact hn hn_eq.symm
      have hpm : ¬ p ∣ m := by
        intro hdvd
        have h1 : p ^ (e + 1) ∣ n := by
          rw [← hn_eq, pow_succ]; exact mul_dvd_mul_left (p ^ e) hdvd
        have hle := (hp.pow_dvd_iff_le_factorization hn).mp h1
        omega
      have hcop : Nat.Coprime (p ^ e) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left e
      have hmlt : m < n := by
        have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt he_pos.ne'
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
        nlinarith
      have hpf_split : n.primeFactors = insert p m.primeFactors := by
        ext q
        rw [mem_insert, Nat.mem_primeFactors, Nat.mem_primeFactors]
        constructor
        · rintro ⟨hq, hqn, _⟩
          by_cases hqp : q = p
          · left; exact hqp
          · right
            refine ⟨hq, ?_, hm_ne⟩
            rw [← hn_eq] at hqn
            rcases hq.dvd_mul.mp hqn with hqpe | hqm
            · have hqp' := hq.dvd_of_dvd_pow hqpe
              have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp'
              exact absurd this hqp
            · exact hqm
        · rintro (rfl | ⟨hq, hqm, _⟩)
          · exact ⟨hp, Nat.minFac_dvd n, hn⟩
          · exact ⟨hq, hqm.trans (by rw [← hn_eq]; exact dvd_mul_left m _), hn⟩
      have hp_not_mem : p ∉ m.primeFactors := by
        rw [Nat.mem_primeFactors]; rintro ⟨_, h, _⟩; exact hpm h
      have hfac_eq : ∀ q ∈ m.primeFactors, n.factorization q = m.factorization q := by
        intro q hq
        have hqp : q ≠ p := fun h => hp_not_mem (h ▸ hq)
        have hq' := (Nat.mem_primeFactors.mp hq).1
        rw [← hn_eq, Nat.factorization_mul (pow_pos hp.pos e).ne' hm_ne, Finsupp.add_apply,
          hp.factorization_pow, Finsupp.single_eq_of_ne hqp, zero_add]
      rw [← hn_eq, hmul (p ^ e) m hcop, ih m hmlt hm_ne, hn_eq, hpf_split,
        Finset.prod_insert hp_not_mem]
      congr 1
      exact Finset.prod_congr rfl (fun q hq => by rw [hfac_eq q hq])

/-- **Exact first-moment identity for multiplicative functions (Track A1, Lemma 2.1).**
For any multiplicative `c : ℕ → ℕ` (`c 1 = 1` and `c (m * n) = c m * c n` for coprime `m, n`),
`∑_{n ≤ N, c n ≠ 0} log (c n) = ∑_{q = p^e ≤ N, c q ≠ 0} log (c q) · #{m ≤ N/q : c m ≠ 0, p ∤ m}`. -/
theorem sum_log_eq_sum_primePow (c : ℕ → ℕ) (h1 : c 1 = 1)
    (hmul : ∀ m n, Nat.Coprime m n → c (m * n) = c m * c n) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => c n ≠ 0), Real.log (c n : ℝ) =
      ∑ q ∈ (Icc 2 N).filter (fun q => IsPrimePow q ∧ c q ≠ 0),
        Real.log (c q : ℝ) *
          (((Icc 1 (N / q)).filter (fun m => c m ≠ 0 ∧ ¬ q.minFac ∣ m)).card : ℝ) := by
  classical
  -- Step 1: Expand `log (c n)` as `∑_{p ∈ n.primeFactors} log (c (p^{v_p(n)}))`.
  have hlog_expand : ∀ n ∈ (Icc 1 N).filter (fun n => c n ≠ 0),
      Real.log (c n : ℝ) =
        ∑ p ∈ n.primeFactors, Real.log (c (p ^ n.factorization p) : ℝ) := by
    intro n hn
    obtain ⟨hnI, hcn⟩ := mem_filter.mp hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hnI).1; omega
    have hfac := mul_prod_primePow h1 hmul hn0
    have hne_each : ∀ p ∈ n.primeFactors, (c (p ^ n.factorization p) : ℝ) ≠ 0 := by
      intro p hp
      have : c (p ^ n.factorization p) ≠ 0 := by
        intro h0
        apply hcn
        rw [hfac, Finset.prod_eq_zero hp h0]
      exact_mod_cast this
    rw [hfac, Nat.cast_prod, Real.log_prod hne_each]
  rw [Finset.sum_congr rfl hlog_expand, Finset.sum_sigma']
  -- Step 2: Rewrite the RHS as a sigma sum over `(q, m)`.
  have hrhs_sig :
      ∑ q ∈ (Icc 2 N).filter (fun q => IsPrimePow q ∧ c q ≠ 0),
        Real.log (c q : ℝ) *
          (((Icc 1 (N / q)).filter (fun m => c m ≠ 0 ∧ ¬ q.minFac ∣ m)).card : ℝ) =
      ∑ x ∈ ((Icc 2 N).filter (fun q => IsPrimePow q ∧ c q ≠ 0)).sigma
          (fun q => (Icc 1 (N / q)).filter (fun m => c m ≠ 0 ∧ ¬ q.minFac ∣ m)),
        Real.log (c x.1 : ℝ) := by
    calc ∑ q ∈ (Icc 2 N).filter (fun q => IsPrimePow q ∧ c q ≠ 0),
            Real.log (c q : ℝ) *
              (((Icc 1 (N / q)).filter (fun m => c m ≠ 0 ∧ ¬ q.minFac ∣ m)).card : ℝ)
        = ∑ q ∈ (Icc 2 N).filter (fun q => IsPrimePow q ∧ c q ≠ 0),
            ∑ _m ∈ (Icc 1 (N / q)).filter (fun m => c m ≠ 0 ∧ ¬ q.minFac ∣ m),
              Real.log (c q : ℝ) :=
          Finset.sum_congr rfl (fun q _ => by simp [mul_comm])
      _ = ∑ x ∈ ((Icc 2 N).filter (fun q => IsPrimePow q ∧ c q ≠ 0)).sigma
              (fun q => (Icc 1 (N / q)).filter (fun m => c m ≠ 0 ∧ ¬ q.minFac ∣ m)),
            Real.log (c x.1 : ℝ) :=
          Finset.sum_sigma' _ _ (fun q _ => Real.log (c q : ℝ))
  rw [hrhs_sig]
  -- Step 3: Biject `(n, p)` with `(q, m) = (p^{v_p(n)}, n / p^{v_p(n)})`.
  refine Finset.sum_nbij
    (fun x : (n : ℕ) × ℕ => (⟨x.2 ^ x.1.factorization x.2, x.1 / x.2 ^ x.1.factorization x.2⟩ : (q : ℕ) × ℕ))
    ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := mem_sigma.mp hx
    obtain ⟨hnI, hcn⟩ := mem_filter.mp hx1
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
    obtain ⟨hp, hpn, hn0⟩ := Nat.mem_primeFactors.mp hx2
    set q : ℕ := x.2 ^ x.1.factorization x.2
    set m : ℕ := x.1 / q
    have he_pos : 0 < x.1.factorization x.2 := hp.factorization_pos_of_dvd hn0 hpn
    have hq_pp : IsPrimePow q := hp.isPrimePow.pow he_pos.ne'
    have hq_minFac : q.minFac = x.2 := minFac_prime_pow hp he_pos.ne'
    have hq_dvd : q ∣ x.1 := Nat.ordProj_dvd x.1 x.2
    have hqm : q * m = x.1 := Nat.mul_div_cancel' hq_dvd
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hq_dvd) (pow_pos hp.pos _)
    have hq_ge2 : 2 ≤ q := by
      have : 2 ≤ x.2 := hp.two_le
      have : x.2 ≤ x.2 ^ x.1.factorization x.2 := Nat.le_self_pow he_pos.ne' x.2
      omega
    have hq_leN : q ≤ N := (Nat.le_of_dvd (by omega) hq_dvd).trans hnN
    have hpm : ¬ x.2 ∣ m := by
      intro hdvd
      have h1 : q * x.2 ∣ x.1 := by rw [← hqm]; exact mul_dvd_mul_left q hdvd
      have h2 : x.2 ^ (x.1.factorization x.2 + 1) ∣ x.1 := by
        simpa only [q, pow_succ] using h1
      have hle := (hp.pow_dvd_iff_le_factorization hn0).mp h2
      omega
    have hcop : Nat.Coprime q m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left _
    have hcm_eq : c x.1 = c q * c m := by rw [← hqm, hmul q m hcop]
    have hcq : c q ≠ 0 := fun h0 => hcn (by rw [hcm_eq, h0, zero_mul])
    have hcm : c m ≠ 0 := fun h0 => hcn (by rw [hcm_eq, h0, mul_zero])
    refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hq_ge2, hq_leN⟩, hq_pp, hcq⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hm_pos, Nat.div_le_div_right hnN⟩, hcm, ?_⟩⟩
    rwa [hq_minFac]
  · intro x₁ hx₁ x₂ hx₂ heq
    dsimp only at heq
    obtain ⟨hx₁1, hx₁2⟩ := mem_sigma.mp hx₁
    obtain ⟨hx₂1, hx₂2⟩ := mem_sigma.mp hx₂
    obtain ⟨hp₁, hp₁n, hn₁0⟩ := Nat.mem_primeFactors.mp hx₁2
    obtain ⟨hp₂, hp₂n, hn₂0⟩ := Nat.mem_primeFactors.mp hx₂2
    have hq_eq : x₁.2 ^ x₁.1.factorization x₁.2 = x₂.2 ^ x₂.1.factorization x₂.2 := congrArg Sigma.fst heq
    have hm_eq : x₁.1 / x₁.2 ^ x₁.1.factorization x₁.2 = x₂.1 / x₂.2 ^ x₂.1.factorization x₂.2 := by
      have := congrArg Sigma.snd heq; simpa using this
    have hn_eq : x₁.1 = x₂.1 := by
      have e1 := Nat.mul_div_cancel' (Nat.ordProj_dvd x₁.1 x₁.2)
      have e2 := Nat.mul_div_cancel' (Nat.ordProj_dvd x₂.1 x₂.2)
      rw [← e1, ← e2, hm_eq, hq_eq]
    have hp_eq : x₁.2 = x₂.2 := by
      have he₁ : 0 < x₁.1.factorization x₁.2 := hp₁.factorization_pos_of_dvd hn₁0 hp₁n
      have he₂ : 0 < x₂.1.factorization x₂.2 := hp₂.factorization_pos_of_dvd hn₂0 hp₂n
      have h1 : (x₁.2 ^ x₁.1.factorization x₁.2).minFac = x₁.2 := minFac_prime_pow hp₁ he₁.ne'
      have h2 : (x₂.2 ^ x₂.1.factorization x₂.2).minFac = x₂.2 := minFac_prime_pow hp₂ he₂.ne'
      rw [← h1, hq_eq, h2]
    exact Sigma.ext hn_eq (by simp [hp_eq])
  · intro y hy
    obtain ⟨hy1, hy2⟩ := mem_sigma.mp (mem_coe.mp hy)
    obtain ⟨hqI, hq_pp, hcq⟩ := mem_filter.mp hy1
    obtain ⟨hmI, hcm, hpm⟩ := mem_filter.mp hy2
    obtain ⟨hq2, hqN⟩ := mem_Icc.mp hqI
    obtain ⟨hm1, hmNq⟩ := mem_Icc.mp hmI
    obtain ⟨p, e, hp_prime, he_pos, hpe⟩ := (isPrimePow_nat_iff y.1).mp hq_pp
    have hp_minFac : y.1.minFac = p := by
      rw [← hpe]; exact minFac_prime_pow hp_prime he_pos.ne'
    rw [hp_minFac] at hpm
    set n : ℕ := y.1 * y.2
    have hcop : Nat.Coprime y.1 y.2 := by
      rw [← hpe]; exact (hp_prime.coprime_iff_not_dvd.mpr hpm).pow_left e
    have hn_le : n ≤ N := (Nat.mul_le_mul_left y.1 hmNq).trans (Nat.mul_div_le N y.1)
    have hn_pos : 1 ≤ n := Nat.mul_pos (by omega) hm1
    have hcn : c n ≠ 0 := by rw [hmul y.1 y.2 hcop]; exact Nat.mul_ne_zero hcq hcm
    have hpn : p ∣ n := by
      have : p ∣ y.1 := by rw [← hpe]; exact dvd_pow_self p he_pos.ne'
      exact this.trans (dvd_mul_right y.1 y.2)
    have hy2_ne : y.2 ≠ 0 := by omega
    have hfac_n : n.factorization p = e := by
      change (y.1 * y.2).factorization p = e
      rw [← hpe, Nat.factorization_mul (pow_pos hp_prime.pos e).ne' hy2_ne, Finsupp.add_apply,
        hp_prime.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]
    refine ⟨⟨n, p⟩, mem_coe.mpr (mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hn_pos, hn_le⟩, hcn⟩,
      Nat.mem_primeFactors.mpr ⟨hp_prime, hpn, Nat.ne_of_gt hn_pos⟩⟩), ?_⟩
    dsimp only
    rw [hfac_n, hpe]
    exact Sigma.ext rfl (by simp [n, Nat.mul_div_cancel_left y.2 (by omega : 0 < y.1)])

/-! ### Part 4: Odd-prime valuation lower bound and finite width-law upper bound -/

/-- Valuation mechanism of Track A1 Lemma 2.3(2): if `q` is prime and `q ∣ e + 1`, then `q - 1 ≤ e`. -/
theorem padicVal_succ_pos_imp {q e : ℕ} (_hq : q.Prime) (h : q ∣ e + 1) : q - 1 ≤ e := by
  have hle : q ≤ e + 1 := Nat.le_of_dvd (Nat.succ_pos e) h
  omega

/-- **Finite sub-threshold width-law upper bound (Track A, Theorem 1 upper half).** -/
theorem width_law_upper {b : ℕ} (_hb : 2 ≤ b) {a : ℕ → ℤ}
    {N L : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (W P Λ : ℕ) (Phat : ℝ)
    (hunion : (farCount b (coeffSeries b a) ε N : ℝ) ≤
      (W : ℝ) + (L : ℝ) * (1 + (P : ℝ)) + (Λ : ℝ) +
        Phat / (((b : ℝ) - 1) * (b : ℝ) ^ L * ε)) :
    1 - radixDiscrepancy b (coeffSeries b a) N ≤
      2 * ε + ((W : ℝ) + (L : ℝ) * (1 + (P : ℝ)) + (Λ : ℝ)) / (N : ℝ) +
        Phat / (((b : ℝ) - 1) * (b : ℝ) ^ L * ε * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdef := discrepancy_deficit_le b (coeffSeries b a) hε.le N
  have hdiv := div_le_div_of_nonneg_right hunion hNr.le
  rw [add_div, div_div] at hdiv
  linarith

end NormalityChecker.RadixWidthLaw
