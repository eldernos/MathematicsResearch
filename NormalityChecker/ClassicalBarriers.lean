module

public import NormalityChecker.AntisymmetricLambert
public import Mathlib.NumberTheory.Divisors

/-! # Finite cores for character-sector decompositions and classical barriers (Tracks B1–B3, E1–E2)

Kernel-checked finite algebraic, combinatorial, and discrepancy theorems supporting Phase 21
Tracks B1–B3 and E1–E2:

1. **Complementary-support barrier for mod-`2^k` decompositions of `E_odd` (Track E1, Theorem 1.2):**
   - `complementary_cover`: for every `k ≥ 2`, `r`, and `n ≥ 1`, either `τ_{r, 2^k}(n) ≠ 0` or
     `2^(k - 1) * τ_{r, 2^k}(n) - τ_odd(n) ≠ 0`.
   - `supportCount_complementary_sum_ge`: `S(τ_{r, 2^k}; N) + S(a_{k, r}; N) ≥ N` for every `N`.

2. **Small-number concentration and radix-power inclusion (Tracks E1 Lemma 1.1, E2 Prop. 2.2):**
   - `one_sub_radixDiscrepancy_le_of_small`: if `0 ≤ x` and `b^(N - 1) * x < 1`, then
     `1 - D_N(x; b) ≤ b^(N - 1) * x`.
   - `one_sub_radixDiscrepancy_pow_le`: for all `b ≥ 1`, `k ≥ 1`, `N ≥ 1`, and `x : ℝ`,
     `1 - D_N(x; b^k) ≤ k * (1 - D_{kN}(x; b))`.
   - `tendsto_radixDiscrepancy_pow_one`: consequently `x ∈ K_b → x ∈ K_{b^k}`.

3. **Character-combination support union, anti-multiplicative vanishing, and gcd strata (Tracks B1, B3):**
   - `sum_pow_eq_zero_of_eq_neg_one`: if `ζ = -1` and `e` is odd, `∑_{i=0}^e ζ^i = 0`.
   - `supportCount_combo_le`: the support count of a finite linear combination is at most the sum
     of the constituent support counts.
   - `dirichletOneConv_eq_zero_of_antiMul`: if `p` is prime, `w (p * x) = - w x` for all `x`,
     `p ∤ m`, and `e` is odd, then `(1 * w)(p^e * m) = 0`.
   - `dirichletOneConv_strata`: exact gcd-strata decomposition
     `(1 * w)(n) = ∑_{g ∣ gcd(n, M)} (1 * w_g)(n / g)` for any `M`-periodic `w`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.ClassicalBarriers

open CoefficientTransfer AntisymmetricLambert SharpTranslation

/-! ### Part 1: Complementary-support barrier for mod-`2^k` decompositions (Track E1) -/

/-- Number of divisors of `n` congruent to `r` modulo `2^k`. -/
def tauModTwoPow (k r n : ℕ) : ℤ :=
  ((n.divisors.filter fun d => d % 2 ^ k = r).card : ℤ)

/-- Number of odd divisors of `n`. -/
def tauOdd (n : ℕ) : ℤ :=
  ((n.divisors.filter Odd).card : ℤ)

/-- Difference coefficient `a_{k, r}(n) = 2^(k - 1) * τ_{r, 2^k}(n) - τ_odd(n)`. -/
def modTwoPowDiffCoeff (k r n : ℕ) : ℤ :=
  (2 ^ (k - 1) : ℤ) * tauModTwoPow k r n - tauOdd n

/-- **Complementary-support barrier (Track E1, Theorem 1.2).**
For every `k`, `r`, and `n ≥ 1`, either `τ_{r, 2^k}(n) ≠ 0` or `a_{k, r}(n) ≠ 0`. -/
theorem complementary_cover (k r : ℕ) {n : ℕ} (hn : 0 < n) :
    tauModTwoPow k r n ≠ 0 ∨ modTwoPowDiffCoeff k r n ≠ 0 := by
  by_cases h : tauModTwoPow k r n = 0
  · right
    unfold modTwoPowDiffCoeff tauOdd
    rw [h, mul_zero, zero_sub, neg_ne_zero]
    have h1mem : 1 ∈ n.divisors.filter Odd :=
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩, odd_one⟩
    have hpos : 0 < (n.divisors.filter Odd).card := Finset.card_pos.mpr ⟨1, h1mem⟩
    exact_mod_cast hpos.ne'
  · left; exact h

/-- **Complementary support-count lower bound (Track E1, Theorem 1.2 consequence 2).**
For every `k`, `r`, and `N`, `supportCount (tauModTwoPow k r) N + supportCount (modTwoPowDiffCoeff k r) N ≥ N`. -/
theorem supportCount_complementary_sum_ge (k r N : ℕ) :
    N ≤ supportCount (tauModTwoPow k r) N + supportCount (modTwoPowDiffCoeff k r) N := by
  unfold supportCount
  let S₁ := (Icc 1 N).filter (fun n => tauModTwoPow k r n ≠ 0)
  let S₂ := (Icc 1 N).filter (fun n => modTwoPowDiffCoeff k r n ≠ 0)
  have hcov : Icc 1 N ⊆ S₁ ∪ S₂ := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    rw [mem_union]
    rcases complementary_cover k r (show 0 < n by omega) with h1 | h2
    · left; exact mem_filter.mpr ⟨hn, h1⟩
    · right; exact mem_filter.mpr ⟨hn, h2⟩
  calc N = (Icc 1 N).card := by rw [Nat.card_Icc]; omega
    _ ≤ (S₁ ∪ S₂).card := card_le_card hcov
    _ ≤ S₁.card + S₂.card := card_union_le S₁ S₂

/-! ### Part 2: Small-number concentration and radix-power inclusion (Tracks E1, E2) -/

/-- **Small-number concentration core (Track E1, Lemma 1.1).**
If `b ≥ 1`, `0 ≤ x`, `N ≥ 1`, and `b^(N - 1) * x < 1`, then `1 - D_N(x; b) ≤ b^(N - 1) * x`. -/
theorem one_sub_radixDiscrepancy_le_of_small {b : ℕ} (hb : 1 ≤ b) {x : ℝ} (hx0 : 0 ≤ x)
    {N : ℕ} (hN : 0 < N) (hx : (b : ℝ) ^ (N - 1) * x < 1) :
    1 - radixDiscrepancy b x N ≤ (b : ℝ) ^ (N - 1) * x := by
  set a : ℝ := (b : ℝ) ^ (N - 1) * x
  have ha0 : 0 ≤ a := by positivity
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  -- Every point `shift b x n` (`n < N`) lies in `[0, a]`.
  have hpts : ∀ n < N, 0 ≤ shift b x n ∧ shift b x n ≤ a := by
    intro n hn
    have hle : (b : ℝ) ^ n ≤ (b : ℝ) ^ (N - 1) := pow_le_pow_right₀ hb1 (by omega)
    have hmul : (b : ℝ) ^ n * x ≤ a := mul_le_mul_of_nonneg_right hle hx0
    have hnonneg : 0 ≤ (b : ℝ) ^ n * x := by positivity
    have hlt1 : (b : ℝ) ^ n * x < 1 := lt_of_le_of_lt hmul hx
    unfold shift
    rw [Int.fract_eq_self.mpr ⟨hnonneg, hlt1⟩]
    exact ⟨hnonneg, hmul⟩
  -- For every `c` with `a < c ≤ 1`, all `N` points lie in `[0, c)`, so `D_N ≥ 1 - c`.
  have hge : ∀ c : ℝ, a < c → c ≤ 1 → 1 - c ≤ radixDiscrepancy b x N := by
    intro c hac hc1
    have hc0 : 0 < c := lt_of_le_of_lt ha0 hac
    have hfreq : frequency (shift b x) 0 c N = 1 := by
      unfold frequency
      have hall : (range N).filter (fun n => (0 : ℝ) ≤ shift b x n ∧ shift b x n < c) = range N := by
        rw [Finset.filter_eq_self]
        intro n hn
        have hp := hpts n (mem_range.mp hn)
        exact ⟨hp.1, lt_of_le_of_lt hp.2 hac⟩
      rw [hall, card_range]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      exact div_self hNr
    have hle := interval_le_sampleDisc (shift b x) N le_rfl hc0 hc1
    rw [hfreq, sub_zero, abs_of_nonneg (by linarith)] at hle
    exact hle
  -- Let `c → a⁺` to conclude `1 - a ≤ D_N`.
  by_contra hlt
  push Not at hlt
  set δ : ℝ := (1 - radixDiscrepancy b x N - a) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  set c : ℝ := min 1 (a + δ)
  have hac : a < c := lt_min hx (by linarith)
  have hc1 : c ≤ 1 := min_le_left _ _
  have h1 := hge c hac hc1
  have hc_le : c ≤ a + δ := min_le_right _ _
  dsimp only [δ] at hc_le
  linarith

/-- **Radix-power discrepancy inequality (Track E2, Proposition 2.2).**
For all `b ≥ 1`, `k ≥ 1`, `N ≥ 1`, and `x : ℝ`,
`1 - D_N(x; b^k) ≤ k * (1 - D_{kN}(x; b))`. -/
theorem one_sub_radixDiscrepancy_pow_le {b k : ℕ} (hk : 0 < k) (x : ℝ) {N : ℕ} (hN : 0 < N) :
    1 - radixDiscrepancy (b ^ k) x N ≤ (k : ℝ) * (1 - radixDiscrepancy b x (k * N)) := by
  classical
  set D : ℝ := radixDiscrepancy (b ^ k) x N
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN_pos : (0 : ℝ) < ((k * N : ℕ) : ℝ) := by positivity
  -- Suffices to show `D_{kN}(x; b) ≤ 1 - (1 - D) / k`.
  have hmain : radixDiscrepancy b x (k * N) ≤ 1 - (1 - D) / (k : ℝ) := by
    rw [radixDiscrepancy_eq_sampleDisc]
    refine sampleDisc_le_of (fun a c ha hac hc => ?_)
    -- Count of indices `m < k * N` in `[a, c)` splits into `m = k * n` (`n < N`) and the rest.
    let P : ℕ → Prop := fun m => a ≤ shift b x m ∧ shift b x m < c
    let S_all := (range (k * N)).filter P
    let S_zero := (range N).filter (fun n => a ≤ shift (b ^ k) x n ∧ shift (b ^ k) x n < c)
    have hshift_eq : ∀ n : ℕ, shift b x (k * n) = shift (b ^ k) x n := by
      intro n; unfold shift; push_cast; rw [pow_mul]
    let img := S_zero.image (fun n => k * n)
    have himg_sub : img ⊆ S_all := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
      obtain ⟨hnN, hPn⟩ := mem_filter.mp hn
      rw [mem_range] at hnN
      refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
      · exact Nat.mul_lt_mul_of_pos_left hnN hk
      · simp only [P, hshift_eq]; exact hPn
    have himg_card : img.card = S_zero.card :=
      Finset.card_image_of_injective _ (fun n₁ n₂ h => Nat.eq_of_mul_eq_mul_left hk h)
    have hcard_ge : S_zero.card ≤ S_all.card := by
      rw [← himg_card]; exact card_le_card himg_sub
    have hcard_le : S_all.card ≤ S_zero.card + (k - 1) * N := by
      -- Elements of `S_all \ img` lie in `(range (k * N)) \ (range N).image (k * ·)`, which has size `(k - 1) * N`.
      let baseImg := (range N).image (fun n => k * n)
      have hbase_sub : baseImg ⊆ range (k * N) := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        exact mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hn) hk)
      have hbase_card : baseImg.card = N := by
        rw [Finset.card_image_of_injective _ (fun n₁ n₂ h => Nat.eq_of_mul_eq_mul_left hk h), card_range]
      have hdiff_sub : S_all \ img ⊆ range (k * N) \ baseImg := by
        intro m hm
        obtain ⟨hm_all, hm_nimg⟩ := mem_sdiff.mp hm
        obtain ⟨hm_rng, hPm⟩ := mem_filter.mp hm_all
        refine mem_sdiff.mpr ⟨hm_rng, fun hmb => hm_nimg ?_⟩
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hmb
        refine mem_image.mpr ⟨n, mem_filter.mpr ⟨hn, ?_⟩, rfl⟩
        simpa only [P, hshift_eq] using hPm
      have hdiff_card : (S_all \ img).card ≤ (k - 1) * N := by
        calc (S_all \ img).card ≤ (range (k * N) \ baseImg).card := card_le_card hdiff_sub
          _ = (range (k * N)).card - baseImg.card := card_sdiff_of_subset hbase_sub
          _ = k * N - N := by rw [card_range, hbase_card]
          _ = (k - 1) * N := by rw [Nat.sub_mul, one_mul]
      have hsplit : S_all.card = (S_all \ img).card + img.card := by
        have := card_sdiff_add_card_eq_card himg_sub
        omega
      omega
    -- Translate card bounds into `frequency` bounds and apply `|f₀ - (c - a)| ≤ D`.
    have hf0 : |frequency (shift (b ^ k) x) a c N - (c - a)| ≤ D :=
      interval_le_sampleDisc (shift (b ^ k) x) N ha hac hc
    have hf0_eq : frequency (shift (b ^ k) x) a c N = (S_zero.card : ℝ) / (N : ℝ) := by
      unfold frequency S_zero; congr 2
    have hf_eq : frequency (shift b x) a c (k * N) = (S_all.card : ℝ) / ((k * N : ℕ) : ℝ) := by
      unfold frequency S_all P; congr 2
    have hge_r : (S_zero.card : ℝ) ≤ (S_all.card : ℝ) := by exact_mod_cast hcard_ge
    have hle_r : (S_all.card : ℝ) ≤ (S_zero.card : ℝ) + ((k - 1 : ℕ) : ℝ) * (N : ℝ) := by
      exact_mod_cast hcard_le
    have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by exact_mod_cast Nat.cast_sub hk
    rw [hkm1] at hle_r
    have hf_ge : frequency (shift (b ^ k) x) a c N / (k : ℝ) ≤ frequency (shift b x) a c (k * N) := by
      rw [hf0_eq, hf_eq, div_div, Nat.cast_mul, mul_comm (N : ℝ) (k : ℝ)]
      exact div_le_div_of_nonneg_right hge_r (by positivity)
    have hf_le : frequency (shift b x) a c (k * N) ≤
        frequency (shift (b ^ k) x) a c N / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) := by
      rw [hf0_eq, hf_eq, Nat.cast_mul]
      have hrew : (S_zero.card : ℝ) / (N : ℝ) / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) =
          ((S_zero.card : ℝ) + ((k : ℝ) - 1) * (N : ℝ)) / ((k : ℝ) * (N : ℝ)) := by
        field_simp [hk_pos.ne', hN_pos.ne']
      rw [hrew]
      exact div_le_div_of_nonneg_right hle_r (by positivity)
    have hlen0 : 0 ≤ c - a := by linarith
    have hlen1 : c - a ≤ 1 := by linarith
    have hkm1_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) / (k : ℝ) := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      exact div_nonneg (by linarith) hk_pos.le
    rw [abs_le] at hf0 ⊢
    constructor
    · -- Lower bound: `-(1 - (1 - D)/k) ≤ f - (c - a)`
      have h1 : -D / (k : ℝ) ≤ (frequency (shift (b ^ k) x) a c N - (c - a)) / (k : ℝ) :=
        div_le_div_of_nonneg_right hf0.1 hk_pos.le
      rw [sub_div, neg_div] at h1
      have h2 : ((k : ℝ) - 1) / (k : ℝ) * (c - a) ≤ ((k : ℝ) - 1) / (k : ℝ) :=
        mul_le_of_le_one_right hkm1_nn hlen1
      have h3 : (c - a) = (c - a) / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) * (c - a) := by
        field_simp [hk_pos.ne']; ring
      have h4 : (1 - (1 - D) / (k : ℝ)) = D / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) := by
        field_simp [hk_pos.ne']; ring
      linarith
    · -- Upper bound: `f - (c - a) ≤ 1 - (1 - D)/k`
      have h1 : (frequency (shift (b ^ k) x) a c N - (c - a)) / (k : ℝ) ≤ D / (k : ℝ) :=
        div_le_div_of_nonneg_right hf0.2 hk_pos.le
      rw [sub_div] at h1
      have h2 : ((k : ℝ) - 1) / (k : ℝ) * (1 - (c - a)) ≤ ((k : ℝ) - 1) / (k : ℝ) :=
        mul_le_of_le_one_right hkm1_nn (by linarith)
      have h3 : ((k : ℝ) - 1) / (k : ℝ) - (c - a) =
          -((c - a) / (k : ℝ)) + ((k : ℝ) - 1) / (k : ℝ) * (1 - (c - a)) := by
        field_simp [hk_pos.ne']; ring
      have h4 : (1 - (1 - D) / (k : ℝ)) = D / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) := by
        field_simp [hk_pos.ne']; ring
      linarith
  have hmul := mul_le_mul_of_nonneg_left (show 1 - (1 - (1 - D) / (k : ℝ)) ≤ 1 - radixDiscrepancy b x (k * N) by linarith) hk_pos.le
  have hsimp : (k : ℝ) * (1 - (1 - (1 - D) / (k : ℝ))) = 1 - D := by
    field_simp [hk_pos.ne']; ring
  linarith

/-- **Kernel inclusion `K_b ⊆ K_{b^k}` (Track E2, Proposition 2.2 corollary).** -/
theorem tendsto_radixDiscrepancy_pow_one {b k : ℕ} (hk : 0 < k) {x : ℝ}
    (hx : Tendsto (fun N : ℕ => radixDiscrepancy b x N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => radixDiscrepancy (b ^ k) x N) atTop (𝓝 1) := by
  have hcomp : Tendsto (fun N : ℕ => (k : ℝ) * (1 - radixDiscrepancy b x (k * N))) atTop (𝓝 0) := by
    have hmul : Tendsto (fun N : ℕ => k * N) atTop atTop :=
      tendsto_atTop_atTop.mpr (fun M => ⟨M, fun N hN => by
        calc M ≤ 1 * N := by omega
          _ ≤ k * N := Nat.mul_le_mul_right N hk⟩)
    have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hx.comp hmul)).const_mul (k : ℝ)
    simpa [Function.comp_def] using h1
  have hgap : Tendsto (fun N : ℕ => 1 - radixDiscrepancy (b ^ k) x N) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hcomp
    · filter_upwards with N
      rw [radixDiscrepancy_eq_sampleDisc]
      linarith [sampleDisc_le_one (shift (b ^ k) x) N]
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact one_sub_radixDiscrepancy_pow_le hk x hN
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub hgap
  simpa using h2

/-! ### Part 3: Character-combination support union, anti-multiplicative vanishing, and gcd strata -/

/-- Local vanishing at `ζ = -1` for odd exponent `e` (Track B1, Lemma 1.1). -/
theorem sum_pow_eq_zero_of_eq_neg_one {R : Type*} [Ring R] {ζ : R} (hζ : ζ = -1)
    {e : ℕ} (he : Odd e) :
    ∑ i ∈ range (e + 1), ζ ^ i = 0 := by
  rcases he with ⟨m, rfl⟩
  subst hζ
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 + 1 = (2 * m + 1 + 1) + 2 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [zero_add, pow_add, pow_mul]
    norm_num

/-- **Support-union bound for finite linear combinations (Track B1, Theorem 1.5(1)).** -/
theorem supportCount_combo_le {ι : Type*} (s : Finset ι) (c : ι → ℕ → ℂ) (coef : ι → ℂ)
    (a : ℕ → ℤ) (ha : ∀ n, (a n : ℂ) = ∑ i ∈ s, coef i * c i n) (X : ℕ) :
    supportCount a X ≤ ∑ i ∈ s, ((Icc 1 X).filter fun n => c i n ≠ 0).card := by
  classical
  unfold supportCount
  have hsub : (Icc 1 X).filter (fun n => a n ≠ 0) ⊆
      s.biUnion (fun i => (Icc 1 X).filter (fun n => c i n ≠ 0)) := by
    intro n hn
    obtain ⟨hnI, hane⟩ := mem_filter.mp hn
    rw [mem_biUnion]
    by_contra hno
    push Not at hno
    have hzero : (a n : ℂ) = 0 := by
      rw [ha n]
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hci : c i n = 0 := by
        by_contra hcne
        exact hno i hi (mem_filter.mpr ⟨hnI, hcne⟩)
      simp [hci]
    exact hane (Int.cast_eq_zero.mp hzero)
  exact (card_le_card hsub).trans Finset.card_biUnion_le

/-- **General anti-multiplicative vanishing theorem (Track B3, Theorem 3.2(2)).**
If `p` is prime, `w (p * x) = - w x` for all `x`, `p ∤ m`, and `e` is odd, then
`(1 * w)(p^e * m) = 0`. -/
theorem dirichletOneConv_eq_zero_of_antiMul {w : ℕ → ℤ} {p m e : ℕ} (hp : p.Prime)
    (hanti : ∀ x, w (p * x) = -w x) (hm : ¬ p ∣ m) (he : Odd e) :
    dirichletOneConv w (p ^ e * m) = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp [dirichletOneConv]
  have hpow_anti : ∀ i x, w (p ^ i * x) = (-1 : ℤ) ^ i * w x := by
    intro i x
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', mul_assoc, hanti, ih, pow_succ']
      ring
  have hne : p ^ e * m ≠ 0 := Nat.mul_ne_zero (pow_pos hp.pos e).ne' hm_pos.ne'
  have hbij : ∑ x ∈ (p ^ e * m).divisors, w x =
      ∑ q ∈ (range (e + 1)) ×ˢ m.divisors, w (p ^ q.1 * q.2) := by
    symm
    refine Finset.sum_nbij (fun q : ℕ × ℕ => p ^ q.1 * q.2) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro q hq
      obtain ⟨hi, hd⟩ := mem_product.mp hq
      have hile : q.1 ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hi)
      obtain ⟨hdm, _⟩ := Nat.mem_divisors.mp hd
      exact Nat.mem_divisors.mpr ⟨mul_dvd_mul (pow_dvd_pow p hile) hdm, hne⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      obtain ⟨_, hd₁⟩ := mem_product.mp hq₁
      obtain ⟨_, hd₂⟩ := mem_product.mp hq₂
      obtain ⟨hd₁m, _⟩ := Nat.mem_divisors.mp hd₁
      obtain ⟨hd₂m, _⟩ := Nat.mem_divisors.mp hd₂
      have hd₁0 : q₁.2 ≠ 0 := ne_zero_of_dvd_ne_zero hm_pos.ne' hd₁m
      have hd₂0 : q₂.2 ≠ 0 := ne_zero_of_dvd_ne_zero hm_pos.ne' hd₂m
      have hpd₁ : ¬ p ∣ q₁.2 := fun h => hm (h.trans hd₁m)
      have hpd₂ : ¬ p ∣ q₂.2 := fun h => hm (h.trans hd₂m)
      have hfac := congrArg (fun n : ℕ => n.factorization p) heq
      rw [Nat.factorization_mul (pow_pos hp.pos _).ne' hd₁0,
        Nat.factorization_mul (pow_pos hp.pos _).ne' hd₂0,
        Finsupp.add_apply, Finsupp.add_apply,
        hp.factorization_pow, hp.factorization_pow,
        Finsupp.single_eq_same, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hpd₁,
        Nat.factorization_eq_zero_of_not_dvd hpd₂, add_zero, add_zero] at hfac
      have hd_eq : q₁.2 = q₂.2 := by
        dsimp only at heq
        rw [hfac] at heq
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos q₂.1) heq
      exact Prod.ext hfac hd_eq
    · intro x hx
      obtain ⟨hxd, _⟩ := Nat.mem_divisors.mp (mem_coe.mp hx)
      have hx0 : x ≠ 0 := ne_zero_of_dvd_ne_zero hne hxd
      set i : ℕ := x.factorization p
      set d : ℕ := x / p ^ i
      have hpi_dvd : p ^ i ∣ x := Nat.ordProj_dvd x p
      have hx_eq : p ^ i * d = x := Nat.mul_div_cancel' hpi_dvd
      have hfac_tot : (p ^ e * m).factorization p = e := by
        rw [Nat.factorization_mul (pow_pos hp.pos e).ne' hm_pos.ne', Finsupp.add_apply,
          hp.factorization_pow, Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
      have hie : i ≤ e := by
        have := (Nat.factorization_le_iff_dvd hx0 hne).mpr hxd p
        omega
      have hpd : ¬ p ∣ d := by
        intro h
        have h1 : p ^ (i + 1) ∣ x := by
          rw [← hx_eq, pow_succ]; exact mul_dvd_mul_left (p ^ i) h
        have hle := (hp.pow_dvd_iff_le_factorization hx0).mp h1
        omega
      have hdm : d ∣ m := by
        have h1 : p ^ i * d ∣ p ^ i * (p ^ (e - i) * m) := by
          rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hie, hx_eq]; exact hxd
        have h2 : d ∣ p ^ (e - i) * m := (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos i)).mp h1
        have hcop : Nat.Coprime d (p ^ (e - i)) :=
          (hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right (e - i)
        exact hcop.dvd_of_dvd_mul_left h2
      refine ⟨(i, d), mem_coe.mpr (mem_product.mpr ⟨mem_range.mpr (by omega),
        Nat.mem_divisors.mpr ⟨hdm, hm_pos.ne'⟩⟩), hx_eq⟩
  unfold dirichletOneConv
  rw [hbij, Finset.sum_product]
  simp_rw [hpow_anti, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_pow_eq_zero_of_eq_neg_one rfl he, zero_mul]

/-- **Exact gcd-strata decomposition (Track B3, Lemma 3.3).**
For any `M > 0`, `n > 0`, and `w : ℕ → ℤ`,
`(1 * w)(n) = ∑_{g ∣ gcd(n, M)} (1 * w_g)(n / g)` where `w_g(x) = w(g * x)` if `Coprime x (M / g)`
and `0` otherwise. -/
theorem dirichletOneConv_strata {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (w : ℕ → ℤ) :
    dirichletOneConv w n =
      ∑ g ∈ (Nat.gcd n M).divisors,
        dirichletOneConv (fun x => if Nat.Coprime x (M / g) then w (g * x) else 0) (n / g) := by
  unfold dirichletOneConv
  have hfilt : ∀ g ∈ (Nat.gcd n M).divisors,
      ∑ x ∈ (n / g).divisors, (if Nat.Coprime x (M / g) then w (g * x) else 0) =
        ∑ x ∈ (n / g).divisors.filter (fun x => Nat.Coprime x (M / g)), w (g * x) := by
    intro g _; rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hfilt]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_nbij (fun p : (g : ℕ) × ℕ => p.1 * p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    obtain ⟨hg, hx⟩ := mem_sigma.mp hp
    obtain ⟨hg_dvd, _⟩ := Nat.mem_divisors.mp hg
    obtain ⟨hx_div, _⟩ := mem_filter.mp hx
    obtain ⟨hx_dvd, _⟩ := Nat.mem_divisors.mp hx_div
    have hgn : p.1 ∣ n := hg_dvd.trans (Nat.gcd_dvd_left n M)
    have hdvd : p.1 * p.2 ∣ n := by
      have := mul_dvd_mul_left p.1 hx_dvd
      rwa [Nat.mul_div_cancel' hgn] at this
    exact Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    dsimp only at heq
    obtain ⟨hg₁, hx₁⟩ := mem_sigma.mp hp₁
    obtain ⟨hg₂, hx₂⟩ := mem_sigma.mp hp₂
    obtain ⟨hg₁_dvd, _⟩ := Nat.mem_divisors.mp hg₁
    obtain ⟨hg₂_dvd, _⟩ := Nat.mem_divisors.mp hg₂
    have hcop₁ : Nat.Coprime p₁.2 (M / p₁.1) := (mem_filter.mp hx₁).2
    have hcop₂ : Nat.Coprime p₂.2 (M / p₂.1) := (mem_filter.mp hx₂).2
    have hg₁M : p₁.1 ∣ M := hg₁_dvd.trans (Nat.gcd_dvd_right n M)
    have hg₂M : p₂.1 ∣ M := hg₂_dvd.trans (Nat.gcd_dvd_right n M)
    have hgcd₁ : Nat.gcd (p₁.1 * p₁.2) M = p₁.1 := by
      conv_lhs => rw [← Nat.mul_div_cancel' hg₁M]
      rw [Nat.gcd_mul_left, hcop₁.gcd_eq_one, mul_one]
    have hgcd₂ : Nat.gcd (p₂.1 * p₂.2) M = p₂.1 := by
      conv_lhs => rw [← Nat.mul_div_cancel' hg₂M]
      rw [Nat.gcd_mul_left, hcop₂.gcd_eq_one, mul_one]
    have hf : p₁.1 = p₂.1 := by rw [← hgcd₁, heq, hgcd₂]
    have hg_pos : 0 < p₁.1 := Nat.pos_of_dvd_of_pos hg₁M hM
    have hs : p₁.2 = p₂.2 := by
      rw [hf] at heq
      exact Nat.eq_of_mul_eq_mul_left (by omega) heq
    exact Sigma.ext hf (by simp [hs])
  · intro d hd
    obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp (mem_coe.mp hd)
    set g : ℕ := Nat.gcd d M
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right d hM
    have hgd : g ∣ d := Nat.gcd_dvd_left d M
    have hgM : g ∣ M := Nat.gcd_dvd_right d M
    have hgn : g ∣ n := hgd.trans hdn
    have hggcd : g ∣ Nat.gcd n M := Nat.dvd_gcd hgn hgM
    have hgcd_ne : Nat.gcd n M ≠ 0 := (Nat.gcd_pos_of_pos_left M hn).ne'
    set x : ℕ := d / g
    have hgx : g * x = d := Nat.mul_div_cancel' hgd
    have hxn : x ∣ n / g := (Nat.mul_dvd_mul_iff_left hg_pos).mp (by rw [hgx, Nat.mul_div_cancel' hgn]; exact hdn)
    have hng_ne : n / g ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hgn) hg_pos).ne'
    have hcop : Nat.Coprime x (M / g) := Nat.coprime_div_gcd_div_gcd hg_pos
    refine ⟨⟨g, x⟩, mem_coe.mpr (mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨hggcd, hgcd_ne⟩,
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hxn, hng_ne⟩, hcop⟩⟩), hgx⟩

end NormalityChecker.ClassicalBarriers
