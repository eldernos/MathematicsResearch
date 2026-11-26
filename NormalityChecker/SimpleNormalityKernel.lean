module

public import NormalityChecker.GeneralMassTransfer

/-! # Digit frequencies in the numerical kernel and oriented-tail coefficient transfer

Kernel-checked finite and asymptotic foundations for Phase 22 (Tracks A1–A2):

1. **Cylinder geometry and finite localization inside `K_b` (Track A1):**
   - `wordAt`, `wordCount`, `wordFreq`, `digitFreq`, `otherWordCount`, `otherWordFreq`:
     length-`L` base-`b` word counts and frequencies via `⌊b^L · shift b x n⌋₊`, bridged to
     `NormalityChecker.frequency` by `wordFreq_eq_frequency`.
   - `interior_fixed_point_margins`, `interior_fixed_point_margin`, `floor_eq_repunit_of_near`
     (Lemma 1.1): every interior fixed point `c_m = m / (b - 1)` (`1 ≤ m ≤ b - 2`) lies strictly
     inside the cylinder `C_{m^L}` with exact radius `η_{m,L} = min(m, b-1-m) / ((b-1) b^L) ≥ 1 / ((b-1) b^L)`.
   - `floor_eq_zero_or_top_of_near` (Lemma 1.2): every point of `[0, 1)` within circle distance
     `< b^(-L)` of `0` reads `0^L` or `(b - 1)^L`.
   - `exists_fixed_center_of_deficit` & `exists_fixed_center_of_deficit_le` (Lemma 2.2):
     whenever `N ≥ 3` and `δ = 1 - D_N(x; b) < 1/2 - 1/N`, at most `δ N` shifts `n < N` lie
     farther than `b δ / (b - 1)` on the circle from some fixed point `j / (b - 1)` (`0 ≤ j ≤ b - 2`).
   - `word_dichotomy_of_deficit` & `finite_digit_dichotomy` (Theorem 3.2):
     whenever `N ≥ 4`, `L ≥ 1`, and `δ = 1 - D_N(x; b) < b^{-(L+1)}`, exclusively either
     all words outside `{0^L, (b - 1)^L}` have total frequency `≤ δ`, or a unique interior
     constant word `m^L` (`1 ≤ m ≤ b - 2`) has frequency `≥ 1 - δ`.
   - `exists_digit_freq_le_of_deficit` (Corollary 3.3), `kernel_eventual_dichotomy` (Theorem 3.4(a–c)),
     `not_simply_normal_of_mem_kernel` (Theorem 3.4(d)): for every `b ≥ 3`, no element of `K_b`
     is simply normal in base `b`.
   - `binary_transitions_tendsto_zero_of_mem_kernel`, `not_two_normal_of_mem_binary_kernel`,
     and `not_normalIn_of_mem_kernel`: for `b = 2` and `x ∈ K_2`, the words `01` and `10` both
     have frequency tending to `0`, so `x` is not 2-normal; for every `b ≥ 2`, `x ∈ K_b` is not
     normal in base `b`.

2. **Signed / oriented-tail coefficient transfer (Track A2):**
   - `orientedTail` (`tailSeries` `T_n = ∑_{m > n} a(m) b^{n - m}`),
     `shift_coeffSeries_eq_fract_tail` (`shift_eq_fract_tail`), `orientedTail_succ` (Lemma 5.1).
   - `floor_fract_eq_zero`, `floor_fract_eq_top`, `wordCount_zeros_sub_posTail_le`,
     `wordCount_maxDigit_sub_negTail_le`, `otherWordCount_le_badTailCount` (Theorem 5.2):
     exact finite transfer between the counts of `0^L`, `(b - 1)^L` and the sign counts of `T_n`
     up to `badTailCount b a L N = #{n < N : |T_n| ≥ b^(-L)}`.
   - `nearSupport_card_le_succ`, `badTail_card_le_of_shiftedTail`, `badTail_card_le_linear_mass`
     (Theorem 5.3): sharp shadow bound `(L + k)(1 + S(N - 1))` plus linear-mass tail control.
   - `orientedTail_of_gap` (Proposition 6.1), `abs_orientedTail_lt`, `sign_of_dominant`
     (Lemma 6.2(b,c)), and `badTail_card_le` (Corollary 6.4 for `|a| ≤ H ≤ b - 1`).
   - `badTailFreq_tendsto_zero_of_linear_mass`, `asymptotic_oriented_tail_transfer` (Theorem 6.7),
     `nonneg_sparse_zeros_tendsto_one`, and `not_simply_normal_of_nonneg_sparse` (Corollary 7.1):
     every nonnegative integer sequence with linear mass and density-zero support has
     `wordFreq b L (coeffSeries b a) 0 N → 1` and is never simply normal in any base `b ≥ 2`
     (including base `2`).
   - `beatty_odd_weight` (Lemma 8.0): exact Abel-summation discrepancy bound for odd-weighted
     Beatty indicators.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.SimpleNormalityKernel

open CoefficientTransfer GeneralMassTransfer Phase18Synthetic SharpTranslation

/-! ### Part 1: Words, cylinders, and circle distance -/

/-- The length-`L` base-`b` word (encoded as an integer in `[0, b^L)`) read at shift `n`. -/
noncomputable def wordAt (b L : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ L * shift b x n⌋₊

/-- Starts `n < N` at which the base-`b` word of length `L` with value `v` occurs. -/
noncomputable def wordCount (b L : ℕ) (x : ℝ) (v N : ℕ) : ℕ :=
  ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = v).card

/-- Frequency of the length-`L` base-`b` word `v` among the first `N` starts. -/
noncomputable def wordFreq (b L : ℕ) (x : ℝ) (v N : ℕ) : ℝ :=
  (wordCount b L x v N : ℝ) / (N : ℝ)

/-- Frequency of the base-`b` digit `d` among the first `N` digits of `x`. -/
noncomputable def digitFreq (b : ℕ) (x : ℝ) (d N : ℕ) : ℝ :=
  wordFreq b 1 x d N

/-- Starts `n < N` reading a length-`L` word other than `0^L` and `(b - 1)^L`. -/
noncomputable def otherWordCount (b L : ℕ) (x : ℝ) (N : ℕ) : ℕ :=
  ((range N).filter fun n =>
    ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ 0 ∧ ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ b ^ L - 1).card

/-- Total frequency of length-`L` words other than `0^L` and `(b - 1)^L`. -/
noncomputable def otherWordFreq (b L : ℕ) (x : ℝ) (N : ℕ) : ℝ :=
  (otherWordCount b L x N : ℝ) / (N : ℝ)

/-- Exact distance from `y` to the nearest integer: `min {y} (1 - {y})`. -/
noncomputable def distInt (y : ℝ) : ℝ :=
  min (Int.fract y) (1 - Int.fract y)

/-- `Near y r` holds if and only if `distInt y ≤ r`. -/
theorem near_iff_distInt_le {y r : ℝ} : Near y r ↔ distInt y ≤ r := by
  constructor
  · rintro ⟨z, hz⟩
    unfold distInt
    rcases le_or_gt z ⌊y⌋ with hle | hgt
    · refine min_le_of_left_le ?_
      have hz' : (z : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hle
      have hfr : 0 ≤ Int.fract y := Int.fract_nonneg y
      have heq : y - (z : ℝ) = Int.fract y + ((⌊y⌋ : ℝ) - (z : ℝ)) := by
        rw [Int.fract]; ring
      have hnn : 0 ≤ y - (z : ℝ) := by linarith
      rw [abs_of_nonneg hnn] at hz
      linarith
    · refine min_le_of_right_le ?_
      have hle' : ⌊y⌋ + 1 ≤ z := by omega
      have hz' : (⌊y⌋ : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hle'
      have hfr : Int.fract y < 1 := Int.fract_lt_one y
      have heq : (z : ℝ) - y = (1 - Int.fract y) + ((z : ℝ) - ((⌊y⌋ : ℝ) + 1)) := by
        rw [Int.fract]; ring
      have hnp : y - (z : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hnp] at hz
      linarith
  · intro h
    unfold distInt at h
    rcases le_total (Int.fract y) (1 - Int.fract y) with hle | hle
    · rw [min_eq_left hle] at h
      refine ⟨⌊y⌋, ?_⟩
      rw [show y - (⌊y⌋ : ℝ) = Int.fract y from rfl, abs_of_nonneg (Int.fract_nonneg y)]
      exact h
    · rw [min_eq_right hle] at h
      refine ⟨⌊y⌋ + 1, ?_⟩
      have hsub : y - ((⌊y⌋ + 1 : ℤ) : ℝ) = -(1 - Int.fract y) := by
        rw [Int.fract]; push_cast; ring
      rw [hsub, abs_neg, abs_of_pos (by linarith [Int.fract_lt_one y])]
      exact h

private lemma near_add_int {y r : ℝ} (k : ℤ) : Near (y + (k : ℝ)) r ↔ Near y r := by
  rw [near_iff_distInt_le, near_iff_distInt_le]
  unfold distInt
  rw [Int.fract_add_intCast]

private lemma near_add {y₁ y₂ r₁ r₂ : ℝ} (h₁ : Near y₁ r₁) (h₂ : Near y₂ r₂) :
    Near (y₁ + y₂) (r₁ + r₂) := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  refine ⟨k₁ + k₂, ?_⟩
  have hrew : y₁ + y₂ - ((k₁ + k₂ : ℤ) : ℝ) = (y₁ - (k₁ : ℝ)) + (y₂ - (k₂ : ℝ)) := by
    push_cast; ring
  rw [hrew]
  exact (abs_add_le _ _).trans (add_le_add hk₁ hk₂)

private lemma near_sub {y₁ y₂ r₁ r₂ : ℝ} (h₁ : Near y₁ r₁) (h₂ : Near y₂ r₂) :
    Near (y₁ - y₂) (r₁ + r₂) := by
  rw [sub_eq_add_neg]
  exact near_add h₁ (near_neg.mpr h₂)

private lemma near_mul_nat {y r : ℝ} (m : ℕ) (h : Near y r) :
    Near ((m : ℝ) * y) ((m : ℝ) * r) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨(m : ℤ) * k, ?_⟩
  have hrew : (m : ℝ) * y - (((m : ℤ) * k : ℤ) : ℝ) = (m : ℝ) * (y - (k : ℝ)) := by
    push_cast; ring
  rw [hrew, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  exact mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg m)

private lemma near_mono {y r₁ r₂ : ℝ} (h : Near y r₁) (hle : r₁ ≤ r₂) : Near y r₂ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.trans hle⟩

private lemma shift_nonneg (b : ℕ) (x : ℝ) (n : ℕ) : 0 ≤ shift b x n :=
  Int.fract_nonneg _

private lemma floor_pow_mul_eq_iff {b L : ℕ} (hb : 1 ≤ b) {t : ℝ} (ht0 : 0 ≤ t) (v : ℕ) :
    ⌊(b : ℝ) ^ L * t⌋₊ = v ↔
      (v : ℝ) / (b : ℝ) ^ L ≤ t ∧ t < ((v : ℝ) + 1) / (b : ℝ) ^ L := by
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by exact_mod_cast hb) L
  rw [Nat.floor_eq_iff (mul_nonneg hbL.le ht0), div_le_iff₀ hbL, lt_div_iff₀ hbL, mul_comm t]

/-- `wordFreq` agrees with `NormalityChecker.frequency` on the corresponding base-`b` cylinder. -/
theorem wordFreq_eq_frequency {b : ℕ} (hb : 1 ≤ b) (L : ℕ) (x : ℝ) (v N : ℕ) :
    wordFreq b L x v N =
      frequency (shift b x) ((v : ℝ) / (b : ℝ) ^ L) (((v : ℝ) + 1) / (b : ℝ) ^ L) N := by
  unfold wordFreq wordCount frequency
  congr 1
  congr 1
  congr 1
  ext n
  simp only [mem_filter, floor_pow_mul_eq_iff hb (shift_nonneg b x n) v]

/-- Every base-`b` word of length `L` has integer value strictly less than `b^L`. -/
theorem wordAt_lt {b : ℕ} (hb : 1 ≤ b) (L : ℕ) (x : ℝ) (n : ℕ) :
    wordAt b L x n < b ^ L := by
  unfold wordAt
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by exact_mod_cast hb) L
  have hlt : (b : ℝ) ^ L * shift b x n < ((b ^ L : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    nlinarith [show shift b x n < 1 from Int.fract_lt_one _]
  exact (Nat.floor_lt (mul_nonneg hbL.le (Int.fract_nonneg _))).mpr hlt

theorem wordCount_bounds (b L : ℕ) (x : ℝ) (v N : ℕ) :
    wordCount b L x v N ≤ N :=
  (card_filter_le _ _).trans_eq (card_range N)

theorem wordFreq_bounds (b L : ℕ) (x : ℝ) (v N : ℕ) :
    0 ≤ wordFreq b L x v N ∧ wordFreq b L x v N ≤ 1 := by
  unfold wordFreq
  constructor
  · positivity
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast wordCount_bounds b L x v N)

theorem wordCount_add_le_of_ne {b L : ℕ} (x : ℝ) {u v : ℕ} (huv : u ≠ v) (N : ℕ) :
    wordCount b L x u N + wordCount b L x v N ≤ N := by
  unfold wordCount
  have hdisj : Disjoint
      ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = u)
      ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = v) := by
    rw [Finset.disjoint_left]
    intro n hu hv
    exact huv ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2)
  calc ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = u).card +
        ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = v).card
      = (((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = u) ∪
          ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = v)).card :=
        (card_union_of_disjoint hdisj).symm
    _ ≤ (range N).card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    _ = N := card_range N

theorem otherWordCount_eq_sub {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) (x : ℝ) (N : ℕ) :
    otherWordCount b L x N = N - wordCount b L x 0 N - wordCount b L x (b ^ L - 1) N := by
  have htop_ne : (0 : ℕ) ≠ b ^ L - 1 := by
    have : 2 ≤ b ^ L := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hL)
    omega
  set A := (range N).filter (fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = 0)
  set B := (range N).filter (fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = b ^ L - 1)
  set C := (range N).filter (fun n =>
    ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ 0 ∧ ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ b ^ L - 1)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro n hA hB
    exact htop_ne ((mem_filter.mp hA).2.symm.trans (mem_filter.mp hB).2)
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    have hC := (mem_filter.mp h2).2
    rcases mem_union.mp h1 with hA | hB
    · exact hC.1 (mem_filter.mp hA).2
    · exact hC.2 (mem_filter.mp hB).2
  have hunion : (A ∪ B) ∪ C = range N := by
    ext n
    simp only [A, B, C, mem_union, mem_filter]
    constructor
    · rintro ((⟨hn, _⟩ | ⟨hn, _⟩) | ⟨hn, _⟩) <;> exact hn
    · intro hn
      by_cases h0 : ⌊(b : ℝ) ^ L * shift b x n⌋₊ = 0
      · exact Or.inl (Or.inl ⟨hn, h0⟩)
      · by_cases h1 : ⌊(b : ℝ) ^ L * shift b x n⌋₊ = b ^ L - 1
        · exact Or.inl (Or.inr ⟨hn, h1⟩)
        · exact Or.inr ⟨hn, h0, h1⟩
  have hcard : A.card + B.card + C.card = N := by
    rw [← card_union_of_disjoint hAB, ← card_union_of_disjoint hABC, hunion, card_range]
  change C.card = N - A.card - B.card
  omega

theorem otherWordCount_cast_eq {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) (x : ℝ) (N : ℕ) :
    (otherWordCount b L x N : ℝ) =
      (N : ℝ) - (wordCount b L x 0 N : ℝ) - (wordCount b L x (b ^ L - 1) N : ℝ) := by
  have htop_ne : (0 : ℕ) ≠ b ^ L - 1 := by
    have : 2 ≤ b ^ L := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hL)
    omega
  have hle : wordCount b L x 0 N + wordCount b L x (b ^ L - 1) N ≤ N :=
    wordCount_add_le_of_ne x htop_ne N
  rw [otherWordCount_eq_sub hb hL x N]
  have hsub : N - wordCount b L x 0 N - wordCount b L x (b ^ L - 1) N =
      N - (wordCount b L x 0 N + wordCount b L x (b ^ L - 1) N) := by omega
  rw [hsub, Nat.cast_sub hle, Nat.cast_add]
  ring

theorem sum_wordCount_eq {b : ℕ} (hb : 1 ≤ b) (L : ℕ) (x : ℝ) (N : ℕ) :
    ∑ v ∈ range (b ^ L), wordCount b L x v N = N := by
  unfold wordCount
  rw [← Finset.card_biUnion]
  · have heq : (range (b ^ L)).biUnion
        (fun v => (range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = v) = range N := by
      ext n
      simp only [mem_biUnion, mem_filter, mem_range]
      constructor
      · rintro ⟨_, _, hn, _⟩; exact hn
      · intro hn
        exact ⟨⌊(b : ℝ) ^ L * shift b x n⌋₊, wordAt_lt hb L x n, hn, rfl⟩
    rw [heq, card_range]
  · intro u _ v _ huv
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hu hv
    exact huv ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2)

theorem otherWordCount_eq_sum {b : ℕ} (hb : 1 ≤ b) (L : ℕ) (x : ℝ) (N : ℕ) :
    otherWordCount b L x N =
      ∑ v ∈ (range (b ^ L)).filter (fun v => v ≠ 0 ∧ v ≠ b ^ L - 1), wordCount b L x v N := by
  unfold otherWordCount wordCount
  rw [← Finset.card_biUnion]
  · congr 1
    ext n
    simp only [mem_biUnion, mem_filter, mem_range]
    constructor
    · rintro ⟨hn, h0, h1⟩
      exact ⟨⌊(b : ℝ) ^ L * shift b x n⌋₊, ⟨wordAt_lt hb L x n, h0, h1⟩, hn, rfl⟩
    · rintro ⟨v, ⟨_, h0, h1⟩, hn, rfl⟩
      exact ⟨hn, h0, h1⟩
  · intro u _ v _ huv
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hu hv
    exact huv ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2)

/-! ### Part 2: Cylinder geometry of fixed points (Lemmas 1.1–1.2) -/

/-- Exact interior cylinder margin `η_{m,L} = min(m, b - 1 - m) / ((b - 1) b^L)`. -/
noncomputable def interiorMargin (b m L : ℕ) : ℝ :=
  min (m : ℝ) ((b : ℝ) - 1 - (m : ℝ)) / (((b : ℝ) - 1) * (b : ℝ) ^ L)

/-- **Lemma 1.1 (exact margins).** For `b ≥ 2`, `1 ≤ m ≤ b - 2`, and any `L`, the interior fixed
point `c_m = m / (b - 1)` lies in the cylinder of `m^L` with exact left and right margins
`m / ((b - 1) b^L)` and `(b - 1 - m) / ((b - 1) b^L)`. -/
theorem interior_fixed_point_margins {b m : ℕ} (hb : 2 ≤ b) (L : ℕ) :
    (m : ℝ) / ((b : ℝ) - 1) - ((m * repunit b L : ℕ) : ℝ) / (b : ℝ) ^ L =
      (m : ℝ) / (((b : ℝ) - 1) * (b : ℝ) ^ L) ∧
    (((m * repunit b L : ℕ) : ℝ) + 1) / (b : ℝ) ^ L - (m : ℝ) / ((b : ℝ) - 1) =
      ((b : ℝ) - 1 - (m : ℝ)) / (((b : ℝ) - 1) * (b : ℝ) ^ L) := by
  have hbm1 : (b : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbL : (b : ℝ) ^ L ≠ 0 := pow_ne_zero L (by exact_mod_cast (show b ≠ 0 by omega))
  have hrep : (repunit b L : ℝ) * ((b : ℝ) - 1) = (b : ℝ) ^ L - 1 := by
    exact_mod_cast repunit_mul_sub_one b L
  constructor
  · push_cast; field_simp [hbm1, hbL]; linear_combination -(m : ℝ) * hrep
  · push_cast; field_simp [hbm1, hbL]; linear_combination (m : ℝ) * hrep

/-- **Lemma 1.1 (interior fixed-point margin).** For `1 ≤ m ≤ b - 2` and any `L`:
1. `1 / ((b - 1) b^L) ≤ η_{m,L}`;
2. every `t ∈ [0, 1)` within circle distance `r < η_{m,L}` of `m / (b - 1)` lies in the
   cylinder of `m^L`, i.e., `⌊b^L t⌋₊ = m * repunit b L`. -/
theorem interior_fixed_point_margin {b m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (hmb : m + 2 ≤ b) :
    1 / (((b : ℝ) - 1) * (b : ℝ) ^ L) ≤ interiorMargin b m L ∧
    ∀ {t r : ℝ}, 0 ≤ t → t < 1 → r < interiorMargin b m L →
      Near (t - (m : ℝ) / ((b : ℝ) - 1)) r → ⌊(b : ℝ) ^ L * t⌋₊ = m * repunit b L := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmb' : (m : ℝ) + 2 ≤ b := by exact_mod_cast hmb
  have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by linarith) L
  have hbL_ge1 : (1 : ℝ) ≤ (b : ℝ) ^ L := one_le_pow₀ (by linarith)
  have hmin_ge1 : (1 : ℝ) ≤ min (m : ℝ) ((b : ℝ) - 1 - (m : ℝ)) := le_min hm1 (by linarith)
  refine ⟨?_, ?_⟩
  · unfold interiorMargin
    exact div_le_div_of_nonneg_right hmin_ge1 (mul_nonneg hbm1_pos.le hbL_pos.le)
  · intro t r ht0 ht1 hr hnear
    set c : ℝ := (m : ℝ) / ((b : ℝ) - 1)
    have hmargin_le_c : interiorMargin b m L ≤ c := by
      unfold interiorMargin
      have h1 : min (m : ℝ) ((b : ℝ) - 1 - (m : ℝ)) ≤ (m : ℝ) := min_le_left _ _
      have h2 : (b : ℝ) - 1 ≤ ((b : ℝ) - 1) * (b : ℝ) ^ L :=
        le_mul_of_one_le_right hbm1_pos.le hbL_ge1
      calc min (m : ℝ) ((b : ℝ) - 1 - (m : ℝ)) / (((b : ℝ) - 1) * (b : ℝ) ^ L)
          ≤ (m : ℝ) / (((b : ℝ) - 1) * (b : ℝ) ^ L) :=
            div_le_div_of_nonneg_right h1 (by positivity)
        _ ≤ (m : ℝ) / ((b : ℝ) - 1) :=
            div_le_div_of_nonneg_left (by positivity) hbm1_pos h2
    have hmargin_le_1c : interiorMargin b m L ≤ 1 - c := by
      unfold interiorMargin
      have h1 : min (m : ℝ) ((b : ℝ) - 1 - (m : ℝ)) ≤ (b : ℝ) - 1 - (m : ℝ) := min_le_right _ _
      have h2 : (b : ℝ) - 1 ≤ ((b : ℝ) - 1) * (b : ℝ) ^ L :=
        le_mul_of_one_le_right hbm1_pos.le hbL_ge1
      have h1c : 1 - c = ((b : ℝ) - 1 - (m : ℝ)) / ((b : ℝ) - 1) := by
        dsimp only [c]; field_simp [hbm1_pos.ne']
      rw [h1c]
      calc min (m : ℝ) ((b : ℝ) - 1 - (m : ℝ)) / (((b : ℝ) - 1) * (b : ℝ) ^ L)
          ≤ ((b : ℝ) - 1 - (m : ℝ)) / (((b : ℝ) - 1) * (b : ℝ) ^ L) :=
            div_le_div_of_nonneg_right h1 (by positivity)
        _ ≤ ((b : ℝ) - 1 - (m : ℝ)) / ((b : ℝ) - 1) :=
            div_le_div_of_nonneg_left (by linarith) hbm1_pos h2
    -- Any integer shift in `Near (t - c) r` must be `0`.
    have hc_pos : 0 < c := div_pos (by linarith) hbm1_pos
    obtain ⟨k, hk⟩ := hnear
    have hk0 : k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        have hpos : 1 - c ≤ t - c - (k : ℝ) := by linarith
        have habs : 1 - c ≤ |t - c - (k : ℝ)| := hpos.trans (le_abs_self _)
        linarith
      · have hk_ge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
        have hneg : t - c - (k : ℝ) < -c := by linarith
        have habs : c < |t - c - (k : ℝ)| := by
          rw [abs_of_neg (by linarith)]; linarith
        linarith
    subst hk0
    simp only [Int.cast_zero, sub_zero] at hk
    have habs : |t - c| < interiorMargin b m L := hk.trans_lt hr
    have hmargins := interior_fixed_point_margins (m := m) hb L
    have hleft_le : interiorMargin b m L ≤ (m : ℝ) / (((b : ℝ) - 1) * (b : ℝ) ^ L) :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
    have hright_le : interiorMargin b m L ≤ ((b : ℝ) - 1 - (m : ℝ)) / (((b : ℝ) - 1) * (b : ℝ) ^ L) :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
    rw [abs_lt] at habs
    rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) ht0]
    constructor <;> linarith [hmargins.1, hmargins.2]

/-- **Lemma 1.1 (interior fixed points).** -/
theorem floor_eq_repunit_of_near {b m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (hmb : m + 2 ≤ b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hnear : |t - (m : ℝ) / ((b : ℝ) - 1)| < 1 / (((b : ℝ) - 1) * (b : ℝ) ^ L)) :
    ⌊(b : ℝ) ^ L * t⌋₊ = m * repunit b L := by
  have h := interior_fixed_point_margin (L := L) hb hm hmb
  exact h.2 ht0 ht1 (hnear.trans_le h.1) ⟨0, by simp⟩

/-- **Lemma 1.2 (the boundary fixed point).** -/
theorem floor_eq_zero_or_top_of_near {b L : ℕ} (hb : 2 ≤ b) {t ε : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : ε < 1 / (b : ℝ) ^ L) (hnear : Near t ε) :
    ⌊(b : ℝ) ^ L * t⌋₊ = 0 ∨ ⌊(b : ℝ) ^ L * t⌋₊ = b ^ L - 1 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by linarith) L
  have hinv_le1 : 1 / (b : ℝ) ^ L ≤ 1 := by
    rw [div_le_one hbL_pos]
    exact one_le_pow₀ hb1
  obtain ⟨j, hj⟩ := hnear
  have hj01 : j = 0 ∨ j = 1 := by
    by_contra hno
    push Not at hno
    rcases lt_or_gt_of_ne hno.1 with hlt | hgt
    · have hj_le : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      have : 1 ≤ t - (j : ℝ) := by linarith
      have : 1 ≤ |t - (j : ℝ)| := this.trans (le_abs_self _)
      linarith
    · have hj_ge : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 2 ≤ j by omega)
      have : t - (j : ℝ) < -1 := by linarith
      have : 1 < |t - (j : ℝ)| := by rw [abs_of_neg (by linarith)]; linarith
      linarith
  rcases hj01 with rfl | rfl
  · left
    simp only [Int.cast_zero, sub_zero, abs_of_nonneg ht0] at hj
    rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) ht0]
    exact ⟨by simp [ht0], by simpa using hj.trans_lt hε⟩
  · right
    simp only [Int.cast_one] at hj
    rw [abs_of_neg (by linarith)] at hj
    rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) ht0]
    have hge1 : 1 ≤ b ^ L := Nat.one_le_pow L b (by omega)
    rw [Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one]
    constructor
    · rw [sub_div, div_self hbL_pos.ne']
      linarith
    · have : ((b : ℝ) ^ L - 1 + 1) / (b : ℝ) ^ L = 1 := by field_simp [hbL_pos.ne']; ring
      rw [this]
      exact ht1

/-! ### Part 3: Finite localization from discrepancy deficit (Lemma 2.2) -/

open Classical in
/-- **Lemma 2.2 (localization; strict form).** If `b ≥ 2`, `N ≥ 3`, and
`1 - D_N(x; b) < δ ≤ 1/2 - 1/N`, then there is a fixed point `c_j = j / (b - 1)` (`0 ≤ j ≤ b - 2`)
such that at most `δ N` shifts `n < N` lie at circle distance `> b δ / (b - 1)` from `c_j`. -/
theorem exists_fixed_center_of_deficit {b N : ℕ} (hb : 2 ≤ b) (hN : 3 ≤ N) (x : ℝ) {δ : ℝ}
    (hδ : 1 - radixDiscrepancy b x N < δ) (hδN : δ ≤ 1 / 2 - 1 / (N : ℝ)) :
    ∃ j : ℕ, j + 2 ≤ b ∧
      (((range N).filter fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * δ / ((b : ℝ) - 1))).card : ℝ) ≤ δ * N := by
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  -- Step 1: Extract an interval achieving excess `> 1 - δ`, and convert it to an arc via complementation.
  have hlt_sup : 1 - δ < sampleDisc (shift b x) N := by
    rw [← radixDiscrepancy_eq_sampleDisc]
    linarith
  have hne : {d | ∃ a c : ℝ, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧
      d = |frequency (shift b x) a c N - (c - a)|}.Nonempty :=
    ⟨_, 0, 1, le_rfl, zero_lt_one, le_rfl, rfl⟩
  have hbdd : BddAbove {d | ∃ a c : ℝ, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧
      d = |frequency (shift b x) a c N - (c - a)|} := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, c, ha, hac, hc, rfl⟩
    have hf := frequency_bounds (shift b x) a c N
    rw [abs_le]; constructor <;> linarith [hf.1, hf.2]
  obtain ⟨_, ⟨a, c, ha, hac, hc, rfl⟩, hgt⟩ := (lt_csSup_iff hbdd hne).mp hlt_sup
  obtain ⟨α, l, hl0, _, harc⟩ :=
    interval_eq_arc_excess (u := shift b x) (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
      hNpos ha hac hc
  rw [← harc] at hgt
  set G := (range N).filter (fun n => Int.fract (shift b x n - α) < l)
  have hG_le : G.card ≤ N := (card_filter_le _ _).trans_eq (card_range N)
  have he_add_l : (1 - (G.card : ℝ) / N) + l < δ := by
    have : (G.card : ℝ) / N = (arcCount (shift b x) α l N : ℝ) / N := rfl
    linarith
  have he_nonneg : 0 ≤ 1 - (G.card : ℝ) / N := by
    have : (G.card : ℝ) / N ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hG_le)
    linarith
  have hl_lt_δ : l < δ := by linarith
  have he_lt_δ : 1 - (G.card : ℝ) / N < δ := by linarith
  -- Step 2: Find a consecutive pair `n, n + 1 ∈ G` with `n < N - 1`.
  have hmiss_lt : ((N - G.card : ℕ) : ℝ) < δ * N := by
    rw [Nat.cast_sub hG_le]
    have hmul := mul_lt_mul_of_pos_right he_lt_δ hNr
    field_simp [hNr.ne'] at hmul ⊢
    linarith
  have hpair : ∃ n < N - 1, n ∈ G ∧ n + 1 ∈ G := by
    set B₁ := (range (N - 1)).filter (fun n => n ∉ G)
    set B₂ := (range (N - 1)).filter (fun n => n + 1 ∉ G)
    have hB₁ : B₁.card ≤ N - G.card := by
      have hsub : B₁ ⊆ range N \ G := by
        intro n hn
        obtain ⟨hn1, hnG⟩ := mem_filter.mp hn
        exact mem_sdiff.mpr ⟨mem_range.mpr (by have := mem_range.mp hn1; omega), hnG⟩
      calc B₁.card ≤ (range N \ G).card := card_le_card hsub
        _ = N - G.card := by rw [card_sdiff_of_subset (filter_subset _ _), card_range]
    have hB₂ : B₂.card ≤ N - G.card := by
      have hinj : B₂.card ≤ (range N \ G).card := by
        refine card_le_card_of_injOn (fun n => n + 1) ?_ ?_
        · intro n hn
          obtain ⟨hn1, hnG⟩ := mem_filter.mp (mem_coe.mp hn)
          dsimp only
          exact mem_coe.mpr (mem_sdiff.mpr ⟨mem_range.mpr (by have := mem_range.mp hn1; omega), hnG⟩)
        · intro x _ y _ h; dsimp only at h; omega
      rwa [card_sdiff_of_subset (filter_subset _ _), card_range] at hinj
    have h2miss : 2 * (N - G.card) < N - 1 := by
      have hδN_mul : δ * (N : ℝ) ≤ (N : ℝ) / 2 - 1 := by
        have h := mul_le_mul_of_nonneg_right hδN hNr.le
        have hrew : (1 / 2 - 1 / (N : ℝ)) * (N : ℝ) = (N : ℝ) / 2 - 1 := by
          field_simp [hNr.ne']
        linarith
      have hr : (2 : ℝ) * ((N - G.card : ℕ) : ℝ) < (N : ℝ) - 1 := by
        have : ((N - G.card : ℕ) : ℝ) < (N : ℝ) / 2 - 1 := hmiss_lt.trans_le hδN_mul
        linarith
      have hr' : ((2 * (N - G.card) : ℕ) : ℝ) < ((N - 1 : ℕ) : ℝ) := by
        have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [Nat.cast_mul, Nat.cast_ofNat, hN1]
        exact hr
      exact_mod_cast hr'
    have hlt_card : (B₁ ∪ B₂).card < (range (N - 1)).card := by
      rw [card_range]
      calc (B₁ ∪ B₂).card ≤ B₁.card + B₂.card := card_union_le B₁ B₂
        _ ≤ (N - G.card) + (N - G.card) := Nat.add_le_add hB₁ hB₂
        _ < N - 1 := by omega
    have hsub : B₁ ∪ B₂ ⊆ range (N - 1) := union_subset (filter_subset _ _) (filter_subset _ _)
    obtain ⟨n, hn_rng, hn_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_card
    refine ⟨n, mem_range.mp hn_rng, ?_, ?_⟩
    · by_contra hno
      exact hn_not (mem_union_left _ (mem_filter.mpr ⟨hn_rng, hno⟩))
    · by_contra hno
      exact hn_not (mem_union_right _ (mem_filter.mpr ⟨hn_rng, hno⟩))
  -- Step 3: Every point in `G` is within `l / 2` of the midpoint `c' = α + l / 2`.
  set c' : ℝ := α + l / 2
  have hnear_mid : ∀ u ∈ G, Near (shift b x u - c') (l / 2) := by
    intro u hu
    have hlt : Int.fract (shift b x u - α) < l := (mem_filter.mp hu).2
    have hnn : 0 ≤ Int.fract (shift b x u - α) := Int.fract_nonneg _
    refine ⟨⌊shift b x u - α⌋, ?_⟩
    have hrew : shift b x u - c' - (⌊shift b x u - α⌋ : ℝ) =
        Int.fract (shift b x u - α) - l / 2 := by
      dsimp only [c']; rw [Int.fract]; ring
    rw [hrew, abs_le]
    constructor <;> linarith
  -- Step 4: Use the consecutive pair `n, n + 1 ∈ G` to bound `‖(b - 1) c'‖ ≤ (b + 1) l / 2`.
  obtain ⟨n₀, _, hn₀G, hn₀1G⟩ := hpair
  have hstep_int : ∃ z : ℤ, (b : ℝ) * shift b x n₀ - shift b x (n₀ + 1) = (z : ℝ) := by
    refine ⟨⌊(b : ℝ) ^ (n₀ + 1) * x⌋ - (b : ℤ) * ⌊(b : ℝ) ^ n₀ * x⌋, ?_⟩
    unfold shift
    rw [Int.fract, Int.fract, pow_succ']
    push_cast
    ring
  obtain ⟨z₀, hz₀⟩ := hstep_int
  have hbc'_near : Near (((b : ℝ) - 1) * c') (((b : ℝ) + 1) * l / 2) := by
    have h1 := near_mul_nat b (hnear_mid n₀ hn₀G)
    have h2 := hnear_mid (n₀ + 1) hn₀1G
    have h3 := near_sub h2 h1
    have hrew : (shift b x (n₀ + 1) - c') - (b : ℝ) * (shift b x n₀ - c') + (z₀ : ℝ) =
        ((b : ℝ) - 1) * c' := by
      rw [← hz₀]; ring
    have hrad : l / 2 + (b : ℝ) * (l / 2) = ((b : ℝ) + 1) * l / 2 := by ring
    rw [hrad] at h3
    rw [← hrew]
    exact (near_add_int z₀).mpr h3
  -- Step 5: Reduce the integer approximation of `(b - 1) c'` modulo `b - 1` to get `j` with `j + 2 ≤ b`.
  obtain ⟨k, hk⟩ := hbc'_near
  set bm1 : ℕ := b - 1
  have hbm1_nat_pos : 0 < bm1 := by omega
  have hbm1_int_pos : (0 : ℤ) < (bm1 : ℤ) := by exact_mod_cast hbm1_nat_pos
  set j : ℕ := (k % (bm1 : ℤ)).toNat
  set q : ℤ := k / (bm1 : ℤ)
  have hj_eq : (j : ℤ) = k % (bm1 : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k hbm1_int_pos.ne')
  have hj_lt : j < bm1 := by
    have h := Int.emod_lt_of_pos k hbm1_int_pos
    rw [← hj_eq] at h
    exact_mod_cast h
  have hj_bd : j + 2 ≤ b := by omega
  have hk_decomp : (k : ℝ) = ((b : ℝ) - 1) * (q : ℝ) + (j : ℝ) := by
    have hz : k = (bm1 : ℤ) * q + (j : ℤ) := by
      rw [hj_eq, add_comm]
      exact (Int.emod_add_mul_ediv k (bm1 : ℤ)).symm
    have hr : (k : ℝ) = ((bm1 : ℕ) : ℝ) * (q : ℝ) + (j : ℝ) := by exact_mod_cast hz
    rw [Nat.cast_sub (show 1 ≤ b by omega), Nat.cast_one] at hr
    exact hr
  have hc'_near_j : Near (c' - (j : ℝ) / ((b : ℝ) - 1)) (((b : ℝ) + 1) * l / (2 * ((b : ℝ) - 1))) := by
    refine ⟨q, ?_⟩
    have hrew : c' - (j : ℝ) / ((b : ℝ) - 1) - (q : ℝ) =
        (((b : ℝ) - 1) * c' - (k : ℝ)) / ((b : ℝ) - 1) := by
      rw [hk_decomp]; field_simp [hbm1_pos.ne']; ring
    rw [hrew, abs_div, abs_of_pos hbm1_pos]
    calc |((b : ℝ) - 1) * c' - (k : ℝ)| / ((b : ℝ) - 1)
        ≤ (((b : ℝ) + 1) * l / 2) / ((b : ℝ) - 1) := div_le_div_of_nonneg_right hk hbm1_pos.le
      _ = ((b : ℝ) + 1) * l / (2 * ((b : ℝ) - 1)) := by rw [div_div]
  -- Step 6: Every shift in `G` is within `b l / (b - 1) ≤ b δ / (b - 1)` of `j / (b - 1)`.
  refine ⟨j, hj_bd, ?_⟩
  have hgood : ∀ u ∈ G,
      Near (shift b x u - (j : ℝ) / ((b : ℝ) - 1)) ((b : ℝ) * δ / ((b : ℝ) - 1)) := by
    intro u hu
    have hsum := near_add (hnear_mid u hu) hc'_near_j
    have hrew : (shift b x u - c') + (c' - (j : ℝ) / ((b : ℝ) - 1)) =
        shift b x u - (j : ℝ) / ((b : ℝ) - 1) := by ring
    have hrad : l / 2 + ((b : ℝ) + 1) * l / (2 * ((b : ℝ) - 1)) = (b : ℝ) * l / ((b : ℝ) - 1) := by
      field_simp [hbm1_pos.ne']; ring
    rw [hrew, hrad] at hsum
    refine near_mono hsum ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl_lt_δ.le (by positivity)) hbm1_pos.le
  have hsub : ((range N).filter fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
      ((b : ℝ) * δ / ((b : ℝ) - 1))) ⊆ range N \ G := by
    intro u hu
    obtain ⟨huN, hfar⟩ := mem_filter.mp hu
    exact mem_sdiff.mpr ⟨huN, fun huG => hfar (hgood u huG)⟩
  have hcard : ((range N).filter fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
      ((b : ℝ) * δ / ((b : ℝ) - 1))).card ≤ N - G.card := by
    calc _ ≤ (range N \ G).card := card_le_card hsub
      _ = N - G.card := by rw [card_sdiff_of_subset (filter_subset _ _), card_range]
  have hcard_r : (((range N).filter fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
      ((b : ℝ) * δ / ((b : ℝ) - 1))).card : ℝ) ≤ ((N - G.card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

open Classical in
/-- **Lemma 2.2 (localization; exact non-strict deficit form).**
For `b ≥ 2`, `N ≥ 3`, and `δ = 1 - D_N(x; b) < 1/2 - 1/N`, there is `j` with `j + 2 ≤ b` such that
at most `δ N` shifts `n < N` lie at circle distance `> b δ / (b - 1)` from `j / (b - 1)`. -/
theorem exists_fixed_center_of_deficit_le {b N : ℕ} (hb : 2 ≤ b) (hN : 3 ≤ N) (x : ℝ)
    (hδN : 1 - radixDiscrepancy b x N < 1 / 2 - 1 / (N : ℝ)) :
    ∃ j : ℕ, j + 2 ≤ b ∧
      (((range N).filter fun n =>
        ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
            ((b : ℝ) * (1 - radixDiscrepancy b x N) / ((b : ℝ) - 1))).card : ℝ) ≤
        (1 - radixDiscrepancy b x N) * N := by
  set δ : ℝ := 1 - radixDiscrepancy b x N
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hb_pos : (0 : ℝ) < b := by linarith
  set r₀ : ℝ := (b : ℝ) * δ / ((b : ℝ) - 1)
  -- Define the exception count at radius `r₀` for each fixed center `j ∈ range (b - 1)`.
  let E : ℕ → ℕ := fun j =>
    ((range N).filter fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1)) r₀).card
  have hne_centers : (range (b - 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨j₀, hj₀_mem, hj₀_min⟩ := Finset.exists_min_image (range (b - 1)) E hne_centers
  have hj₀_bd : j₀ + 2 ≤ b := by have := mem_range.mp hj₀_mem; omega
  refine ⟨j₀, hj₀_bd, ?_⟩
  -- Find a uniform positive margin separating all strictly far pairs `(j, n)` from `r₀`.
  let P := ((range (b - 1)) ×ˢ (range N)).filter fun p =>
    r₀ < distInt (shift b x p.2 - (p.1 : ℝ) / ((b : ℝ) - 1))
  have hgap_exists : ∃ η : ℝ, 0 < η ∧ δ + η ≤ 1 / 2 - 1 / (N : ℝ) ∧
      ∀ p ∈ P, (b : ℝ) * (δ + η) / ((b : ℝ) - 1) <
        distInt (shift b x p.2 - (p.1 : ℝ) / ((b : ℝ) - 1)) := by
    by_cases hP : P.Nonempty
    · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ := Finset.exists_min_image P
        (fun p => distInt (shift b x p.2 - (p.1 : ℝ) / ((b : ℝ) - 1))) hP
      have hdiff_pos : 0 < distInt (shift b x p₀.2 - (p₀.1 : ℝ) / ((b : ℝ) - 1)) - r₀ := by
        have := (mem_filter.mp hp₀_mem).2; linarith
      set η₁ : ℝ := (distInt (shift b x p₀.2 - (p₀.1 : ℝ) / ((b : ℝ) - 1)) - r₀) *
          ((b : ℝ) - 1) / (2 * (b : ℝ))
      have hη₁ : 0 < η₁ := by positivity
      refine ⟨min η₁ (1 / 2 - 1 / (N : ℝ) - δ), lt_min hη₁ (by linarith),
        by linarith [min_le_right η₁ (1 / 2 - 1 / (N : ℝ) - δ)], fun p hp => ?_⟩
      have hle_p : distInt (shift b x p₀.2 - (p₀.1 : ℝ) / ((b : ℝ) - 1)) ≤
          distInt (shift b x p.2 - (p.1 : ℝ) / ((b : ℝ) - 1)) := hp₀_min p hp
      have hη_le : min η₁ (1 / 2 - 1 / (N : ℝ) - δ) ≤ η₁ := min_le_left _ _
      have hstep : (b : ℝ) * (δ + min η₁ (1 / 2 - 1 / (N : ℝ) - δ)) / ((b : ℝ) - 1) ≤
          (b : ℝ) * (δ + η₁) / ((b : ℝ) - 1) := by gcongr
      have hcalc : (b : ℝ) * (δ + η₁) / ((b : ℝ) - 1) =
          r₀ + (distInt (shift b x p₀.2 - (p₀.1 : ℝ) / ((b : ℝ) - 1)) - r₀) / 2 := by
        dsimp only [r₀, η₁]
        field_simp [hbm1_pos.ne', hb_pos.ne']
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hP
      refine ⟨1 / 2 - 1 / (N : ℝ) - δ, by linarith, by linarith, fun p hp => ?_⟩
      rw [hP] at hp; exact absurd hp (notMem_empty p)
  obtain ⟨η, hη_pos, hη_le, hη_sep⟩ := hgap_exists
  -- For every `0 < ε ≤ η`, apply the strict localization theorem to `δ + ε`.
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ η → (E j₀ : ℝ) ≤ (δ + ε) * (N : ℝ) := by
    intro ε hε hεη
    obtain ⟨j, hj_bd, hj_card⟩ := exists_fixed_center_of_deficit hb hN x (δ := δ + ε)
      (by linarith) (by linarith)
    have hj_mem : j ∈ range (b - 1) := mem_range.mpr (by omega)
    have hE_le : E j ≤ ((range N).filter fun n =>
        ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * (δ + ε) / ((b : ℝ) - 1))).card := by
      refine card_le_card (fun n hn => ?_)
      obtain ⟨hnN, hfar⟩ := mem_filter.mp hn
      rw [near_iff_distInt_le, not_le] at hfar
      refine mem_filter.mpr ⟨hnN, ?_⟩
      rw [near_iff_distInt_le, not_le]
      have hp : (j, n) ∈ P := mem_filter.mpr ⟨mem_product.mpr ⟨hj_mem, hnN⟩, hfar⟩
      have hsep := hη_sep (j, n) hp
      have hmono : (b : ℝ) * (δ + ε) / ((b : ℝ) - 1) ≤ (b : ℝ) * (δ + η) / ((b : ℝ) - 1) := by
        gcongr
      exact hmono.trans_lt hsep
    have hmin : (E j₀ : ℝ) ≤ (E j : ℝ) := by exact_mod_cast hj₀_min j hj_mem
    have hE_r : (E j : ℝ) ≤ (((range N).filter fun n =>
        ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * (δ + ε) / ((b : ℝ) - 1))).card : ℝ) := by exact_mod_cast hE_le
    linarith
  -- Let `ε → 0⁺` to conclude `E j₀ ≤ δ * N`.
  by_contra hlt
  push Not at hlt
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set ε : ℝ := min η (((E j₀ : ℝ) - δ * (N : ℝ)) / (2 * (N : ℝ)))
  have hε_pos : 0 < ε := lt_min hη_pos (div_pos (by linarith) (by positivity))
  have hε_le : ε ≤ η := min_le_left _ _
  have hε_small : ε * (N : ℝ) ≤ ((E j₀ : ℝ) - δ * (N : ℝ)) / 2 := by
    have h1 : ε ≤ ((E j₀ : ℝ) - δ * (N : ℝ)) / (2 * (N : ℝ)) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 hNr.le
    have hrew : ((E j₀ : ℝ) - δ * (N : ℝ)) / (2 * (N : ℝ)) * (N : ℝ) =
        ((E j₀ : ℝ) - δ * (N : ℝ)) / 2 := by field_simp [hNr.ne']
    linarith
  have h := hbound ε hε_pos hε_le
  linarith

/-! ### Part 4: Finite digit dichotomy and non-normality in `K_b` (Theorems 3.2–3.4) -/

/-- **Theorem 3.2 (finite dichotomy; strict form).** -/
theorem word_dichotomy_of_deficit {b N L : ℕ} (hb : 2 ≤ b) (hN : 4 ≤ N) (hL : 1 ≤ L)
    (x : ℝ) {δ : ℝ} (hδ : 1 - radixDiscrepancy b x N < δ) (hδL : δ < 1 / (b : ℝ) ^ (L + 1)) :
    (N : ℝ) - wordCount b L x 0 N - wordCount b L x (b ^ L - 1) N ≤ δ * N ∨
    ∃ m, 1 ≤ m ∧ m + 2 ≤ b ∧ (N : ℝ) - wordCount b L x (m * repunit b L) N ≤ δ * N := by
  classical
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hb_pos : (0 : ℝ) < b := by linarith
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos hb_pos L
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hδN : δ ≤ 1 / 2 - 1 / (N : ℝ) := by
    have hpow4 : (4 : ℝ) ≤ (b : ℝ) ^ (L + 1) := by
      have h1 : 4 ≤ b ^ (L + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
          _ ≤ b ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast h1
    have hinv1 : 1 / (b : ℝ) ^ (L + 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hpow4
    have hinv2 : 1 / (N : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hN4
    linarith
  obtain ⟨j, hj_bd, hj_card⟩ := exists_fixed_center_of_deficit hb (by omega) x hδ hδN
  have hr_lt : (b : ℝ) * δ / ((b : ℝ) - 1) < 1 / (((b : ℝ) - 1) * (b : ℝ) ^ L) := by
    have h1 : (b : ℝ) * δ < (b : ℝ) * (1 / (b : ℝ) ^ (L + 1)) :=
      mul_lt_mul_of_pos_left hδL hb_pos
    have h2 : (b : ℝ) * (1 / (b : ℝ) ^ (L + 1)) = 1 / (b : ℝ) ^ L := by
      rw [pow_succ]; field_simp [hb_pos.ne', hbL_pos.ne']
    have h3 : (b : ℝ) * δ / ((b : ℝ) - 1) < (1 / (b : ℝ) ^ L) / ((b : ℝ) - 1) :=
      div_lt_div_of_pos_right (h1.trans_eq h2) hbm1_pos
    have h4 : (1 / (b : ℝ) ^ L) / ((b : ℝ) - 1) = 1 / (((b : ℝ) - 1) * (b : ℝ) ^ L) := by
      rw [div_div, mul_comm]
    exact h3.trans_eq h4
  rcases Nat.eq_zero_or_pos j with rfl | hj_pos
  · left
    have hsub : (range N).filter (fun n =>
        ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ 0 ∧ ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ b ^ L - 1) ⊆
        (range N).filter (fun n => ¬ Near (shift b x n - ((0 : ℕ) : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * δ / ((b : ℝ) - 1))) := by
      intro n hn
      obtain ⟨hnN, h0, htop⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hnN, fun hnear => ?_⟩
      simp only [Nat.cast_zero, zero_div, sub_zero] at hnear
      have hr_lt' : (b : ℝ) * δ / ((b : ℝ) - 1) < 1 / (b : ℝ) ^ L := by
        have hbm1_ge1 : (1 : ℝ) ≤ (b : ℝ) - 1 := by linarith
        have hle : 1 / (((b : ℝ) - 1) * (b : ℝ) ^ L) ≤ 1 / (b : ℝ) ^ L :=
          one_div_le_one_div_of_le hbL_pos (le_mul_of_one_le_left hbL_pos.le hbm1_ge1)
        exact hr_lt.trans_le hle
      rcases floor_eq_zero_or_top_of_near hb (Int.fract_nonneg _) (Int.fract_lt_one _)
          hr_lt' hnear with h | h
      · exact h0 h
      · exact htop h
    have hcard_le : (otherWordCount b L x N : ℝ) ≤
        (((range N).filter fun n => ¬ Near (shift b x n - ((0 : ℕ) : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * δ / ((b : ℝ) - 1))).card : ℝ) := by
      unfold otherWordCount
      exact_mod_cast card_le_card hsub
    rw [otherWordCount_cast_eq hb hL x N] at hcard_le
    linarith
  · right
    refine ⟨j, hj_pos, hj_bd, ?_⟩
    have hm := interior_fixed_point_margin (L := L) hb hj_pos hj_bd
    have hsub : (range N).filter (fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ j * repunit b L) ⊆
        (range N).filter (fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * δ / ((b : ℝ) - 1))) := by
      intro n hn
      obtain ⟨hnN, hne⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hnN, fun hnear => ?_⟩
      exact hne (hm.2 (Int.fract_nonneg _) (Int.fract_lt_one _) (hr_lt.trans_le hm.1) hnear)
    have hcompl : ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ j * repunit b L).card =
        N - wordCount b L x (j * repunit b L) N := by
      have htot := Finset.card_filter_add_card_filter_not (s := range N)
        (fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = j * repunit b L)
      rw [card_range] at htot
      simp only [ne_eq]
      unfold wordCount
      omega
    have hcard_le : ((N - wordCount b L x (j * repunit b L) N : ℕ) : ℝ) ≤
        (((range N).filter fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * δ / ((b : ℝ) - 1))).card : ℝ) := by
      rw [← hcompl]
      exact_mod_cast card_le_card hsub
    rw [Nat.cast_sub (wordCount_bounds b L x (j * repunit b L) N)] at hcard_le
    linarith

/-- Helper: `m * repunit b L` is distinct from `0` and `b^L - 1` when `1 ≤ m ≤ b - 2` and `L ≥ 1`. -/
theorem mul_repunit_ne_boundary {b m L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hmb : m + 2 ≤ b) :
    m * repunit b L ≠ 0 ∧ m * repunit b L ≠ b ^ L - 1 := by
  have hrep_pos : 1 ≤ repunit b L := by
    obtain ⟨L', rfl⟩ := Nat.exists_eq_add_of_le hL
    rw [show 1 + L' = L' + 1 by omega, repunit_succ]
    omega
  have hrep_top : (b - 1) * repunit b L = b ^ L - 1 := by
    have hz := repunit_mul_sub_one b L
    have hge1 : 1 ≤ b ^ L := Nat.one_le_pow L b (by omega)
    have h1 : (((b - 1) * repunit b L : ℕ) : ℤ) = ((b ^ L - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one]
      linarith
    exact_mod_cast h1
  constructor
  · exact Nat.mul_ne_zero (by omega) (by omega)
  · have hlt : m * repunit b L < (b - 1) * repunit b L :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega

/-- **Theorem 3.2 (exact exclusive finite digit dichotomy).**
Let `b ≥ 2`, `L ≥ 1`, `N ≥ 4`, and `δ = 1 - D_N(x; b) < b^{-(L+1)}`. Then exclusively either:
1. **(boundary)** `otherWordFreq b L x N ≤ δ`, and no interior `m` satisfies `1 - wordFreq m^L ≤ δ`;
2. **(interior)** there is a unique `m` with `1 ≤ m` and `m + 2 ≤ b` such that
   `1 - wordFreq b L x (m * repunit b L) N ≤ δ`, and `otherWordFreq b L x N > δ`. -/
theorem finite_digit_dichotomy {b N L : ℕ} (hb : 2 ≤ b) (hN : 4 ≤ N) (hL : 1 ≤ L)
    (x : ℝ) (hδL : 1 - radixDiscrepancy b x N < 1 / (b : ℝ) ^ (L + 1)) :
    let δ := 1 - radixDiscrepancy b x N
    (otherWordFreq b L x N ≤ δ ∧
      ∀ m, 1 ≤ m → m + 2 ≤ b → δ < 1 - wordFreq b L x (m * repunit b L) N) ∨
    (∃! m, 1 ≤ m ∧ m + 2 ≤ b ∧ 1 - wordFreq b L x (m * repunit b L) N ≤ δ) ∧
      δ < otherWordFreq b L x N := by
  intro δ
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ_lt_half : δ < 1 / 2 := by
    have hpow4 : (4 : ℝ) ≤ (b : ℝ) ^ (L + 1) := by
      have : 4 ≤ b ^ (L + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
          _ ≤ b ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast this
    have : 1 / (b : ℝ) ^ (L + 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hpow4
    linarith
  -- Mutual exclusivity lemmas for any threshold `< 1/2`.
  have hexcl_bi : ∀ {r₁ r₂ : ℝ} {m : ℕ}, r₁ + r₂ < 1 → 1 ≤ m → m + 2 ≤ b →
      otherWordFreq b L x N ≤ r₁ → 1 - wordFreq b L x (m * repunit b L) N ≤ r₂ → False := by
    intro r₁ r₂ m hsum hm hmb h1 h2
    have hne := mul_repunit_ne_boundary hb hL hm hmb
    have hle : wordCount b L x (m * repunit b L) N ≤ otherWordCount b L x N := by
      refine card_le_card (fun n hn => ?_)
      obtain ⟨hnN, heq⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hnN, heq.symm ▸ hne.1, heq.symm ▸ hne.2⟩
    have hfreq_le : wordFreq b L x (m * repunit b L) N ≤ otherWordFreq b L x N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hle) hNr.le
    linarith
  have hexcl_ii : ∀ {r₁ r₂ : ℝ} {m₁ m₂ : ℕ}, r₁ + r₂ < 1 → 1 ≤ m₁ → 1 ≤ m₂ → m₁ ≠ m₂ →
      1 - wordFreq b L x (m₁ * repunit b L) N ≤ r₁ →
      1 - wordFreq b L x (m₂ * repunit b L) N ≤ r₂ → False := by
    intro r₁ r₂ m₁ m₂ hsum _ _ hne h1 h2
    have hrep_pos : 0 < repunit b L := by
      obtain ⟨L', rfl⟩ := Nat.exists_eq_add_of_le hL
      rw [show 1 + L' = L' + 1 by omega, repunit_succ]; omega
    have hmul_ne : m₁ * repunit b L ≠ m₂ * repunit b L := fun h =>
      hne (Nat.eq_of_mul_eq_mul_right hrep_pos h)
    have hle : wordCount b L x (m₁ * repunit b L) N + wordCount b L x (m₂ * repunit b L) N ≤ N :=
      wordCount_add_le_of_ne x hmul_ne N
    have hfreq_le : wordFreq b L x (m₁ * repunit b L) N + wordFreq b L x (m₂ * repunit b L) N ≤ 1 := by
      unfold wordFreq
      rw [← add_div, div_le_one hNr]
      exact_mod_cast hle
    linarith
  -- Apply strict dichotomy at the midpoint `δ₁ = (δ + b^{-(L+1)}) / 2` to identify the alternative,
  -- then let `δ' → δ⁺` using mutual exclusivity.
  set δ₁ : ℝ := (δ + 1 / (b : ℝ) ^ (L + 1)) / 2
  have hδ₁_gt : δ < δ₁ := by dsimp only [δ₁]; linarith
  have hδ₁_lt : δ₁ < 1 / (b : ℝ) ^ (L + 1) := by dsimp only [δ₁]; linarith
  have hδ₁_half : δ₁ < 1 / 2 := by
    have hpow4 : (4 : ℝ) ≤ (b : ℝ) ^ (L + 1) := by
      have : 4 ≤ b ^ (L + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
          _ ≤ b ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast this
    have : 1 / (b : ℝ) ^ (L + 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hpow4
    linarith
  have hfreq_form : ∀ {r : ℝ},
      ((N : ℝ) - wordCount b L x 0 N - wordCount b L x (b ^ L - 1) N ≤ r * N ↔
        otherWordFreq b L x N ≤ r) ∧
      (∀ v, (N : ℝ) - wordCount b L x v N ≤ r * N ↔ 1 - wordFreq b L x v N ≤ r) := by
    intro r
    constructor
    · rw [← otherWordCount_cast_eq hb hL x N]
      unfold otherWordFreq
      rw [div_le_iff₀ hNr]
    · intro v
      unfold wordFreq
      have : 1 - (wordCount b L x v N : ℝ) / (N : ℝ) =
          ((N : ℝ) - (wordCount b L x v N : ℝ)) / (N : ℝ) := by
        field_simp [hNr.ne']
      rw [this, div_le_iff₀ hNr]
  rcases word_dichotomy_of_deficit hb hN hL x hδ₁_gt hδ₁_lt with hbd₁ | ⟨m, hm1, hmb, hint₁⟩
  · -- Boundary alternative holds at `δ₁`, hence at every `δ' ∈ (δ, δ₁]`, hence at `δ`.
    rw [(hfreq_form (r := δ₁)).1] at hbd₁
    have hbd_all : ∀ ε : ℝ, 0 < ε → ε ≤ δ₁ - δ → otherWordFreq b L x N ≤ δ + ε := by
      intro ε hε hεle
      rcases word_dichotomy_of_deficit hb hN hL x (δ := δ + ε) (by linarith) (by linarith) with
          hbd | ⟨m', hm'1, hm'b, hint⟩
      · exact (hfreq_form (r := δ + ε)).1.mp hbd
      · exfalso
        exact hexcl_bi (by linarith) hm'1 hm'b hbd₁ ((hfreq_form (r := δ + ε)).2 _ |>.mp hint)
    have hbd_δ : otherWordFreq b L x N ≤ δ := by
      by_contra hgt
      push Not at hgt
      set ε : ℝ := min (δ₁ - δ) ((otherWordFreq b L x N - δ) / 2)
      have hε : 0 < ε := lt_min (by linarith) (by linarith)
      have h := hbd_all ε hε (min_le_left _ _)
      linarith [min_le_right (δ₁ - δ) ((otherWordFreq b L x N - δ) / 2)]
    left
    refine ⟨hbd_δ, fun m' hm'1 hm'b => ?_⟩
    by_contra hle
    push Not at hle
    exact hexcl_bi (by linarith) hm'1 hm'b hbd_δ hle
  · -- Interior alternative holds with `m` at `δ₁`, hence with the same `m` at all `δ' ∈ (δ, δ₁]`.
    rw [(hfreq_form (r := δ₁)).2] at hint₁
    have hint_all : ∀ ε : ℝ, 0 < ε → ε ≤ δ₁ - δ →
        1 - wordFreq b L x (m * repunit b L) N ≤ δ + ε := by
      intro ε hε hεle
      rcases word_dichotomy_of_deficit hb hN hL x (δ := δ + ε) (by linarith) (by linarith) with
          hbd | ⟨m', hm'1, hm'b, hint⟩
      · exfalso
        exact hexcl_bi (by linarith) hm1 hmb ((hfreq_form (r := δ + ε)).1.mp hbd) hint₁
      · rw [(hfreq_form (r := δ + ε)).2] at hint
        have hm_eq : m' = m := by
          by_contra hne
          exact hexcl_ii (by linarith) hm'1 hm1 hne hint hint₁
        rwa [← hm_eq]
    have hint_δ : 1 - wordFreq b L x (m * repunit b L) N ≤ δ := by
      by_contra hgt
      push Not at hgt
      set ε : ℝ := min (δ₁ - δ) ((1 - wordFreq b L x (m * repunit b L) N - δ) / 2)
      have hε : 0 < ε := lt_min (by linarith) (by linarith)
      have h := hint_all ε hε (min_le_left _ _)
      linarith [min_le_right (δ₁ - δ) ((1 - wordFreq b L x (m * repunit b L) N - δ) / 2)]
    right
    refine ⟨⟨m, ⟨hm1, hmb, hint_δ⟩, fun m' ⟨hm'1, _, hint'⟩ => ?_⟩, ?_⟩
    · by_contra hne
      exact hexcl_ii (by linarith) hm'1 hm1 hne hint' hint_δ
    · by_contra hle
      push Not at hle
      exact hexcl_bi (by linarith) hm1 hmb hle hint_δ

/-- **Corollary 3.3 (quantitative finite failure of simple normality).**
For `b ≥ 3`, `N ≥ 4`, and `δ = 1 - D_N(x; b) < b^(-2)`, some base-`b` digit `d < b` has
frequency at most `δ / (b - 2)`, hence deviates from `1 / b` by at least `1/b - δ/(b - 2)`. -/
theorem exists_digit_freq_le_of_deficit {b N : ℕ} (hb : 3 ≤ b) (hN : 4 ≤ N) (x : ℝ)
    (hδ : 1 - radixDiscrepancy b x N < 1 / (b : ℝ) ^ 2) :
    ∃ d < b,
      digitFreq b x d N ≤ (1 - radixDiscrepancy b x N) / ((b : ℝ) - 2) ∧
      1 / (b : ℝ) - (1 - radixDiscrepancy b x N) / ((b : ℝ) - 2) ≤
        |digitFreq b x d N - 1 / (b : ℝ)| := by
  set δ : ℝ := 1 - radixDiscrepancy b x N
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hbm2_pos : (0 : ℝ) < (b : ℝ) - 2 := by linarith
  have hδL : δ < 1 / (b : ℝ) ^ (1 + 1) := by simpa using hδ
  have hgoal : ∃ d < b, digitFreq b x d N ≤ δ / ((b : ℝ) - 2) := by
    rcases finite_digit_dichotomy (show 2 ≤ b by omega) hN le_rfl x hδL with
        ⟨hbd, _⟩ | ⟨⟨m, ⟨hm1, hmb, hint⟩, _⟩, _⟩
    · -- Boundary case: the `b - 2` interior digits `1, ..., b - 2` sum to `otherWordFreq ≤ δ`.
      set S := (range (b ^ 1)).filter (fun v => v ≠ 0 ∧ v ≠ b ^ 1 - 1)
      have hS_eq : S = Icc 1 (b - 2) := by
        ext v
        simp only [S, pow_one, mem_filter, mem_range, mem_Icc]
        omega
      have hS_card : (S.card : ℝ) = (b : ℝ) - 2 := by
        rw [hS_eq, Nat.card_Icc]
        have h1 : b - 2 + 1 - 1 = b - 2 := by omega
        rw [h1, Nat.cast_sub (by omega), Nat.cast_ofNat]
      have hS_ne : S.Nonempty := by
        rw [hS_eq]; exact ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      have hsum : ∑ d ∈ S, digitFreq b x d N = otherWordFreq b 1 x N := by
        unfold digitFreq wordFreq otherWordFreq
        rw [← Finset.sum_div, ← Nat.cast_sum, ← otherWordCount_eq_sum (show 1 ≤ b by omega)]
      obtain ⟨d, hdS, hd_le⟩ := Finset.exists_le_of_sum_le hS_ne (show ∑ d ∈ S, digitFreq b x d N ≤
          ∑ _ ∈ S, (δ / ((b : ℝ) - 2)) by
        rw [Finset.sum_const, nsmul_eq_mul, hS_card, mul_div_cancel₀ _ hbm2_pos.ne', hsum]
        exact hbd)
      have hd_lt : d < b := by
        rw [hS_eq, mem_Icc] at hdS; omega
      exact ⟨d, hd_lt, hd_le⟩
    · -- Interior case: the `b - 1` digits different from `m` sum to `1 - digitFreq m ≤ δ`.
      have hrep1 : repunit b 1 = 1 := by simp [repunit]
      rw [hrep1, mul_one] at hint
      set S := (range b).erase m
      have hm_mem : m ∈ range b := mem_range.mpr (by omega)
      have hS_card : (S.card : ℝ) = (b : ℝ) - 1 := by
        rw [card_erase_of_mem hm_mem, card_range, Nat.cast_sub (by omega), Nat.cast_one]
      have hS_ne : S.Nonempty := ⟨0, mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩⟩
      have hsum : ∑ d ∈ S, digitFreq b x d N = 1 - digitFreq b x m N := by
        have htot := sum_wordCount_eq (show 1 ≤ b by omega) 1 x N
        rw [pow_one] at htot
        have hsplit := Finset.add_sum_erase (range b) (fun d => wordCount b 1 x d N) hm_mem
        unfold digitFreq wordFreq
        rw [← Finset.sum_div, ← Nat.cast_sum]
        have hsub_r : ((∑ d ∈ S, wordCount b 1 x d N : ℕ) : ℝ) =
            (N : ℝ) - (wordCount b 1 x m N : ℝ) := by
          have hadd_eq : wordCount b 1 x m N + ∑ d ∈ S, wordCount b 1 x d N = N := by
            simpa only [S, htot] using hsplit
          have : ∑ d ∈ S, wordCount b 1 x d N = N - wordCount b 1 x m N := by omega
          rw [this, Nat.cast_sub (wordCount_bounds b 1 x m N)]
        rw [hsub_r]
        field_simp [hNr.ne']
      have hδ_nn : 0 ≤ δ := by linarith [(radixDiscrepancy_mem b x N).2]
      have hle_rhs : δ ≤ ((b : ℝ) - 1) * (δ / ((b : ℝ) - 2)) := by
        have h1 : (b : ℝ) - 2 ≤ (b : ℝ) - 1 := by linarith
        calc δ = ((b : ℝ) - 2) * (δ / ((b : ℝ) - 2)) := by field_simp [hbm2_pos.ne']
          _ ≤ ((b : ℝ) - 1) * (δ / ((b : ℝ) - 2)) :=
            mul_le_mul_of_nonneg_right h1 (div_nonneg hδ_nn hbm2_pos.le)
      obtain ⟨d, hdS, hd_le⟩ := Finset.exists_le_of_sum_le hS_ne (show ∑ d ∈ S, digitFreq b x d N ≤
          ∑ _ ∈ S, (δ / ((b : ℝ) - 2)) by
        rw [Finset.sum_const, nsmul_eq_mul, hS_card, hsum]
        exact hint.trans hle_rhs)
      exact ⟨d, mem_range.mp (mem_of_mem_erase hdS), hd_le⟩
  obtain ⟨d, hdb, hle⟩ := hgoal
  refine ⟨d, hdb, hle, ?_⟩
  have h1 : 1 / (b : ℝ) - digitFreq b x d N ≤ |digitFreq b x d N - 1 / (b : ℝ)| := by
    rw [← abs_neg, neg_sub]
    exact le_abs_self _
  linarith

/-- **Theorem 3.4(d) / Corollary 3.3 (no simple normality in `K_b` for `b ≥ 3`).**
For every integer base `b ≥ 3` and every `x ∈ K_b` (`D_N(x; b) → 1`), `x` is NOT simply normal
in base `b`. -/
theorem not_simply_normal_of_mem_kernel {b : ℕ} (hb : 3 ≤ b) {x : ℝ}
    (hx : Tendsto (fun N => radixDiscrepancy b x N) atTop (𝓝 1)) :
    ¬ (∀ d < b, Tendsto (digitFreq b x d) atTop (𝓝 (1 / (b : ℝ)))) := by
  intro hsn
  have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < b := by linarith
  have hbm2_pos : (0 : ℝ) < (b : ℝ) - 2 := by linarith
  have hdef : Tendsto (fun N => 1 - radixDiscrepancy b x N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx
  -- Every digit `d < b` eventually has `|digitFreq b x d N - 1 / b| < 1 / (2 * b)`.
  have hall_ev : ∀ᶠ N in atTop, ∀ d ∈ range b, |digitFreq b x d N - 1 / (b : ℝ)| < 1 / (2 * (b : ℝ)) := by
    rw [Finset.eventually_all]
    intro d hd
    have ht := Metric.tendsto_nhds.mp (hsn d (mem_range.mp hd)) (1 / (2 * (b : ℝ))) (by positivity)
    filter_upwards [ht] with N hN
    simpa [Real.dist_eq] using hN
  -- Meanwhile `1 - D_N(x; b)` eventually drops below `min (1 / b^2) ((b - 2) / (2 * b))`.
  set η : ℝ := min (1 / (b : ℝ) ^ 2) (((b : ℝ) - 2) / (2 * (b : ℝ)))
  have hη_pos : 0 < η := lt_min (by positivity) (by positivity)
  have hdef_ev : ∀ᶠ N in atTop, 1 - radixDiscrepancy b x N < η := by
    filter_upwards [Metric.tendsto_nhds.mp hdef η hη_pos] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    exact (le_abs_self _).trans_lt hN
  obtain ⟨N, hN4, hN_all, hN_def⟩ :=
    ((eventually_ge_atTop 4).and (hall_ev.and hdef_ev)).exists
  have hδ_lt1 : 1 - radixDiscrepancy b x N < 1 / (b : ℝ) ^ 2 :=
    hN_def.trans_le (min_le_left _ _)
  have hδ_lt2 : (1 - radixDiscrepancy b x N) / ((b : ℝ) - 2) < 1 / (2 * (b : ℝ)) := by
    rw [div_lt_iff₀ hbm2_pos]
    have h := hN_def.trans_le (min_le_right _ _)
    have hrew : 1 / (2 * (b : ℝ)) * ((b : ℝ) - 2) = ((b : ℝ) - 2) / (2 * (b : ℝ)) := by ring
    linarith
  obtain ⟨d, hdb, _, hdev⟩ := exists_digit_freq_le_of_deficit hb hN4 x hδ_lt1
  have hclose := hN_all d (mem_range.mpr hdb)
  have hhalf : 1 / (b : ℝ) - 1 / (2 * (b : ℝ)) = 1 / (2 * (b : ℝ)) := by
    field_simp [hb_pos.ne']; ring
  linarith

/-- **Binary kernel transitions vanish.** For every `x ∈ K_2`, the frequencies of the length-2
binary words `01` (`v = 1`) and `10` (`v = 2`) both tend to `0`. -/
theorem binary_transitions_tendsto_zero_of_mem_kernel {x : ℝ}
    (hx : Tendsto (fun N => radixDiscrepancy 2 x N) atTop (𝓝 1)) :
    Tendsto (wordFreq 2 2 x 1) atTop (𝓝 0) ∧ Tendsto (wordFreq 2 2 x 2) atTop (𝓝 0) := by
  have hdef : Tendsto (fun N => 1 - radixDiscrepancy 2 x N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx
  have hother_ev : ∀ᶠ N in atTop, otherWordFreq 2 2 x N ≤ 1 - radixDiscrepancy 2 x N := by
    have hlt : ∀ᶠ N in atTop, 1 - radixDiscrepancy 2 x N < 1 / (2 : ℝ) ^ (2 + 1) := by
      filter_upwards [Metric.tendsto_nhds.mp hdef (1 / (2 : ℝ) ^ (2 + 1)) (by positivity)] with N hN
      rw [Real.dist_eq, sub_zero] at hN
      exact (le_abs_self _).trans_lt hN
    filter_upwards [eventually_ge_atTop 4, hlt] with N hN4 hδ
    rcases finite_digit_dichotomy (b := 2) (L := 2) le_rfl hN4 (by omega) x hδ with
        ⟨hbd, _⟩ | ⟨⟨m, ⟨hm1, hmb, _⟩, _⟩, _⟩
    · exact hbd
    · omega
  have hle_other : ∀ v : ℕ, v = 1 ∨ v = 2 → ∀ N, wordFreq 2 2 x v N ≤ otherWordFreq 2 2 x N := by
    intro v hv N
    have hle : wordCount 2 2 x v N ≤ otherWordCount 2 2 x N := by
      unfold wordCount otherWordCount
      refine card_le_card (fun n hn => ?_)
      obtain ⟨hnN, heq⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hnN, ?_, ?_⟩ <;> rcases hv with rfl | rfl <;> omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg N)
  constructor
  · refine squeeze_zero' (Eventually.of_forall fun N => (wordFreq_bounds 2 2 x 1 N).1) ?_ hdef
    filter_upwards [hother_ev] with N hN
    exact (hle_other 1 (Or.inl rfl) N).trans hN
  · refine squeeze_zero' (Eventually.of_forall fun N => (wordFreq_bounds 2 2 x 2 N).1) ?_ hdef
    filter_upwards [hother_ev] with N hN
    exact (hle_other 2 (Or.inr rfl) N).trans hN

/-- **No 2-normality in the binary kernel `K_2`.** For every `x ∈ K_2`, the length-2 words
`01` and `10` have frequency tending to `0`, so `x` is not 2-normal (and hence not normal in base 2). -/
theorem not_two_normal_of_mem_binary_kernel {x : ℝ}
    (hx : Tendsto (fun N => radixDiscrepancy 2 x N) atTop (𝓝 1)) :
    (Tendsto (wordFreq 2 2 x 1) atTop (𝓝 0) ∧ Tendsto (wordFreq 2 2 x 2) atTop (𝓝 0)) ∧
    ¬ (∀ v < 2 ^ 2, Tendsto (wordFreq 2 2 x v) atTop (𝓝 (1 / (2 : ℝ) ^ 2))) := by
  have htr := binary_transitions_tendsto_zero_of_mem_kernel hx
  refine ⟨htr, fun h2n => ?_⟩
  have hEq : (0 : ℝ) = 1 / (2 : ℝ) ^ 2 := tendsto_nhds_unique htr.1 (h2n 1 (by norm_num))
  norm_num at hEq

/-- For every base `b ≥ 2` and every `x ∈ K_b`, the length-2 non-constant word `0(b - 1)`
(value `b - 1`) has frequency tending to `0`. -/
theorem wordFreq_transition_tendsto_zero_of_mem_kernel {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : Tendsto (fun N => radixDiscrepancy b x N) atTop (𝓝 1)) :
    Tendsto (wordFreq b 2 x (b - 1)) atTop (𝓝 0) := by
  have hdef : Tendsto (fun N => 1 - radixDiscrepancy b x N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx
  have hle_ev : ∀ᶠ N in atTop, wordFreq b 2 x (b - 1) N ≤ 1 - radixDiscrepancy b x N := by
    have hlt : ∀ᶠ N in atTop, 1 - radixDiscrepancy b x N < 1 / (b : ℝ) ^ (2 + 1) := by
      filter_upwards [Metric.tendsto_nhds.mp hdef (1 / (b : ℝ) ^ (2 + 1)) (by positivity)] with N hN
      rw [Real.dist_eq, sub_zero] at hN
      exact (le_abs_self _).trans_lt hN
    filter_upwards [eventually_ge_atTop 4, hlt] with N hN4 hδ
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rcases finite_digit_dichotomy hb hN4 (by omega) x hδ with
        ⟨hbd, _⟩ | ⟨⟨m, ⟨hm1, _, hint⟩, _⟩, _⟩
    · have hsub : wordCount b 2 x (b - 1) N ≤ otherWordCount b 2 x N := by
        refine card_le_card (fun n hn => ?_)
        obtain ⟨hnN, heq⟩ := mem_filter.mp hn
        have hb2 : b < b ^ 2 := by nlinarith
        refine mem_filter.mpr ⟨hnN, by omega, by omega⟩
      exact (div_le_div_of_nonneg_right (by exact_mod_cast hsub) hNr.le).trans hbd
    · have hrep2 : repunit b 2 = b + 1 := by simp [repunit, Finset.sum_range_succ, add_comm]
      have hne : b - 1 ≠ m * repunit b 2 := by
        rw [hrep2]
        have : b + 1 ≤ m * (b + 1) := Nat.le_mul_of_pos_left (b + 1) hm1
        omega
      have hadd := wordCount_add_le_of_ne (b := b) (L := 2) x hne N
      have hfreq : wordFreq b 2 x (b - 1) N + wordFreq b 2 x (m * repunit b 2) N ≤ 1 := by
        unfold wordFreq
        rw [← add_div, div_le_one hNr]
        exact_mod_cast hadd
      linarith
  exact squeeze_zero' (Eventually.of_forall fun N => (wordFreq_bounds b 2 x (b - 1) N).1)
    hle_ev hdef

/-- **No normality in `K_b` (Theorem 3.4(d)).** For every base `b ≥ 2`, no element of `K_b`
is normal in base `b`. -/
theorem not_normalIn_of_mem_kernel {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : Tendsto (fun N => radixDiscrepancy b x N) atTop (𝓝 1)) :
    ¬ NormalIn b x := by
  intro hn
  have h0 := wordFreq_transition_tendsto_zero_of_mem_kernel hb hx
  have hb2 : b < b ^ 2 := by nlinarith
  have h1 := hn.2 2 (b - 1) (by omega) (by omega)
  have hEq_fun : wordFreq b 2 x (b - 1) =
      frequency (shift b x) (((b - 1 : ℕ) : ℝ) / (b : ℝ) ^ 2)
        ((((b - 1 : ℕ) : ℝ) + 1) / (b : ℝ) ^ 2) := by
    funext N
    exact wordFreq_eq_frequency (show 1 ≤ b by omega) 2 x (b - 1) N
  rw [hEq_fun] at h0
  have hzero : (0 : ℝ) = 1 / (b : ℝ) ^ 2 := tendsto_nhds_unique h0 h1
  have hpos : (0 : ℝ) < 1 / (b : ℝ) ^ 2 := by positivity
  linarith

/-- **Theorem 3.4(a–c) (asymptotic classification in `K_b`).**
Every `x ∈ K_b` satisfies a single alternative valid for every word length `L ≥ 1`:
- **(boundary)** `otherWordFreq b L x N → 0` and `wordFreq b L x 0 N - digitFreq b x 0 N → 0`
  for every `L ≥ 1`;
- **(interior)** for a unique `m` with `1 ≤ m` and `m + 2 ≤ b`,
  `wordFreq b L x (m * repunit b L) N → 1` for every `L ≥ 1`. -/
theorem kernel_eventual_dichotomy {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : Tendsto (fun N => radixDiscrepancy b x N) atTop (𝓝 1)) :
    (∀ L ≥ 1, Tendsto (otherWordFreq b L x) atTop (𝓝 0) ∧
      Tendsto (fun N => wordFreq b L x 0 N - digitFreq b x 0 N) atTop (𝓝 0)) ∨
    (∃! m, 1 ≤ m ∧ m + 2 ≤ b ∧ ∀ L ≥ 1,
      Tendsto (wordFreq b L x (m * repunit b L)) atTop (𝓝 1)) := by
  have hdef : Tendsto (fun N => 1 - radixDiscrepancy b x N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx
  -- Step 1: Fix `N₀ ≥ 5` so that for all `N ≥ N₀`, `δ_N < min (1 / b^2) (1 / 8)`.
  set η₁ : ℝ := min (1 / (b : ℝ) ^ (1 + 1)) (1 / 8)
  have hη₁_pos : 0 < η₁ := lt_min (by positivity) (by norm_num)
  have hev₀ : ∀ᶠ N in atTop, 5 ≤ N ∧ 1 - radixDiscrepancy b x N < η₁ := by
    filter_upwards [eventually_ge_atTop 5, Metric.tendsto_nhds.mp hdef η₁ hη₁_pos] with N hN5 hN
    exact ⟨hN5, (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hN)⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev₀
  have hN₀_ge : 5 ≤ N₀ := (hN₀ N₀ le_rfl).1
  have hN₀_def : ∀ N ≥ N₀, 1 - radixDiscrepancy b x N < η₁ := fun N hN => (hN₀ N hN).2
  -- Helper: adjacent-step stability of `wordFreq`.
  have hstep_le : ∀ (L v N : ℕ), 1 ≤ N →
      wordFreq b L x v (N + 1) ≤ wordFreq b L x v N + 1 / ((N + 1 : ℕ) : ℝ) := by
    intro L v N hN1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    have hN1r : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hcnt : wordCount b L x v (N + 1) ≤ wordCount b L x v N + 1 := by
      unfold wordCount
      rw [range_add_one, filter_insert]
      split_ifs <;> simp
    have h1 : (wordCount b L x v (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) ≤
        ((wordCount b L x v N : ℝ) + 1) / ((N + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcnt) hN1r.le
    have h2 : (wordCount b L x v N : ℝ) / ((N + 1 : ℕ) : ℝ) ≤
        (wordCount b L x v N : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hNr (by exact_mod_cast Nat.le_succ N)
    rw [add_div] at h1
    unfold wordFreq
    linarith
  have hstep_ge : ∀ (L v N : ℕ), 5 ≤ N →
      (5 / 6 : ℝ) * wordFreq b L x v N ≤ wordFreq b L x v (N + 1) := by
    intro L v N hN5
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1r : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hcnt : wordCount b L x v N ≤ wordCount b L x v (N + 1) := by
      unfold wordCount
      exact card_le_card (filter_subset_filter _ (range_mono (Nat.le_succ N)))
    have hrat : (5 / 6 : ℝ) ≤ (N : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hN1r]
      have : (5 : ℝ) ≤ N := by exact_mod_cast hN5
      push_cast; linarith
    unfold wordFreq
    calc (5 / 6 : ℝ) * ((wordCount b L x v N : ℝ) / (N : ℝ))
        ≤ ((N : ℝ) / ((N + 1 : ℕ) : ℝ)) * ((wordCount b L x v N : ℝ) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hrat (by positivity)
      _ = (wordCount b L x v N : ℝ) / ((N + 1 : ℕ) : ℝ) := by field_simp [hNr.ne']
      _ ≤ (wordCount b L x v (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hcnt) hN1r.le
  -- Helper: `wordFreq b 1 x m N ≤ otherWordFreq b 1 x N` for any interior digit `1 ≤ m ≤ b - 2`.
  have hdigit_other : ∀ m N, 1 ≤ m → m + 2 ≤ b →
      wordFreq b 1 x m N ≤ otherWordFreq b 1 x N := by
    intro m N hm hmb
    have hle : wordCount b 1 x m N ≤ otherWordCount b 1 x N := by
      unfold wordCount otherWordCount
      refine card_le_card (fun n hn => ?_)
      obtain ⟨hnN, heq⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hnN, by omega, by rw [Nat.pow_one]; omega⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg N)
  -- Helper: `wordCount b L x (m * repunit b L) N ≤ wordCount b 1 x m N`.
  have hlevel_sub : ∀ L ≥ 1, ∀ m, 1 ≤ m → m + 2 ≤ b → ∀ N,
      wordCount b L x (m * repunit b L) N ≤ wordCount b 1 x m N := by
    intro L hL m hm hmb N
    refine card_le_card (fun n hn => ?_)
    obtain ⟨hnN, heq⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnN, ?_⟩
    rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) (shift_nonneg b x n)] at heq ⊢
    have hb_pos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos hb_pos L
    have hrep_lo : (m : ℝ) / (b : ℝ) ≤ ((m * repunit b L : ℕ) : ℝ) / (b : ℝ) ^ L := by
      obtain ⟨L', rfl⟩ := Nat.exists_eq_add_of_le hL
      rw [show 1 + L' = L' + 1 by omega]
      have hge : b ^ L' ≤ repunit b (L' + 1) := by
        unfold repunit
        exact Finset.single_le_sum (f := fun i => b ^ i) (fun _ _ => Nat.zero_le _)
          (mem_range.mpr (Nat.lt_succ_self L'))
      have hmul_ge : m * b ^ L' ≤ m * repunit b (L' + 1) := Nat.mul_le_mul_left m hge
      rw [div_le_div_iff₀ hb_pos (pow_pos hb_pos _), pow_succ']
      have hcast : ((m * b ^ L' : ℕ) : ℝ) ≤ ((m * repunit b (L' + 1) : ℕ) : ℝ) := by
        exact_mod_cast hmul_ge
      rw [Nat.cast_mul, Nat.cast_pow] at hcast
      nlinarith
    have hrep_hi : (((m * repunit b L : ℕ) : ℝ) + 1) / (b : ℝ) ^ L ≤ ((m : ℝ) + 1) / (b : ℝ) := by
      have hm_lt : m * repunit b L + 1 ≤ (m + 1) * b ^ (L - 1) := by
        have hrep_lt : (b - 1) * repunit b L = b ^ L - 1 := by
          have hz := repunit_mul_sub_one b L
          have hge1 : 1 ≤ b ^ L := Nat.one_le_pow L b (by omega)
          have h1 : (((b - 1) * repunit b L : ℕ) : ℤ) = ((b ^ L - 1 : ℕ) : ℤ) := by
            rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one]
            linarith
          exact_mod_cast h1
        have hpow_eq : b ^ L = b * b ^ (L - 1) := by
          obtain ⟨L', rfl⟩ := Nat.exists_eq_add_of_le hL
          rw [show 1 + L' = L' + 1 by omega, Nat.add_sub_cancel, pow_succ']
        -- Exact algebraic bound: `(b - 1) * (m * repunit b L + 1) = m * (b^L - 1) + (b - 1) < (m + 1) * b^(L-1) * (b - 1)`.
        have hmul_lt : (b - 1) * (m * repunit b L + 1) ≤ (b - 1) * ((m + 1) * b ^ (L - 1)) := by
          have hL_eq : (b - 1) * (m * repunit b L + 1) = m * (b ^ L - 1) + (b - 1) := by
            calc (b - 1) * (m * repunit b L + 1)
                = m * ((b - 1) * repunit b L) + (b - 1) := by ring
              _ = m * (b ^ L - 1) + (b - 1) := by rw [hrep_lt]
          have hge1 : 1 ≤ b ^ L := Nat.one_le_pow L b (by omega)
          have h1 : m * (b ^ L - 1) + (b - 1) ≤ m * b ^ L + (b - 1) := by
            have := Nat.mul_le_mul_left m (Nat.sub_le (b ^ L) 1); omega
          have h2 : (b - 1) * ((m + 1) * b ^ (L - 1)) = (m + 1) * (b ^ L - b ^ (L - 1)) := by
            rw [hpow_eq]
            have : b ^ (L - 1) ≤ b * b ^ (L - 1) := Nat.le_mul_of_pos_left _ (by omega)
            zify [show 1 ≤ b by omega, this]; ring
          have h3 : m * (b ^ L - 1) + (b - 1) ≤ (m + 1) * (b ^ L - b ^ (L - 1)) := by
            rw [hpow_eq]
            have hge_pow : 1 ≤ b ^ (L - 1) := Nat.one_le_pow (L - 1) b (by omega)
            have hle_mul : b ^ (L - 1) ≤ b * b ^ (L - 1) := Nat.le_mul_of_pos_left _ (by omega)
            have hge_mul : 1 ≤ b * b ^ (L - 1) := hge_pow.trans hle_mul
            zify [hge_mul, hle_mul, show 1 ≤ b by omega]
            nlinarith [show (b : ℤ) ≥ 2 by omega, show (m : ℤ) + 2 ≤ b by omega,
              show (b ^ (L - 1) : ℤ) ≥ 1 by exact_mod_cast hge_pow]
          omega
        exact Nat.le_of_mul_le_mul_left hmul_lt (by omega)
      rw [div_le_div_iff₀ hbL_pos hb_pos]
      have hpow_eq : (b : ℝ) ^ L = (b : ℝ) * (b : ℝ) ^ (L - 1) := by
        obtain ⟨L', rfl⟩ := Nat.exists_eq_add_of_le hL
        rw [show 1 + L' = L' + 1 by omega, Nat.add_sub_cancel, pow_succ']
      rw [hpow_eq]
      have hcast : (((m * repunit b L : ℕ) : ℝ) + 1) ≤ ((m : ℝ) + 1) * (b : ℝ) ^ (L - 1) := by
        exact_mod_cast hm_lt
      nlinarith
    rw [pow_one]
    exact ⟨hrep_lo.trans heq.1, heq.2.trans_le hrep_hi⟩
  -- Step 2: Check which alternative holds at `L = 1`, `N = N₀`, and propagate by induction to all `N ≥ N₀`.
  have hN₀_lt1 : 1 - radixDiscrepancy b x N₀ < 1 / (b : ℝ) ^ (1 + 1) :=
    (hN₀_def N₀ le_rfl).trans_le (min_le_left _ _)
  rcases finite_digit_dichotomy hb (by omega) le_rfl x hN₀_lt1 with
      ⟨hbd₀, _⟩ | ⟨⟨m, ⟨hm1, hmb, hint₀⟩, _⟩, _⟩
  · -- Case 1: Boundary at `(L = 1, N₀)` persists for all `N ≥ N₀`, and forces boundary for every `L ≥ 1`.
    have hbd_all : ∀ N ≥ N₀, otherWordFreq b 1 x N ≤ 1 - radixDiscrepancy b x N := by
      intro N hN
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
      induction k with
      | zero => simpa using hbd₀
      | succ k ih =>
        have hprev := ih (by omega)
        have hlt_next : 1 - radixDiscrepancy b x (N₀ + k + 1) < 1 / (b : ℝ) ^ (1 + 1) :=
          (hN₀_def (N₀ + k + 1) (by omega)).trans_le (min_le_left _ _)
        rcases finite_digit_dichotomy hb (by omega) le_rfl x hlt_next with
            ⟨hbd, _⟩ | ⟨⟨m', ⟨hm'1, hm'b, hint⟩, _⟩, _⟩
        · exact hbd
        · exfalso
          have hrep1 : repunit b 1 = 1 := by simp [repunit]
          rw [hrep1, mul_one] at hint
          have hm'_le : wordFreq b 1 x m' (N₀ + k) ≤ otherWordFreq b 1 x (N₀ + k) :=
            hdigit_other m' (N₀ + k) hm'1 hm'b
          have hprev_lt : 1 - radixDiscrepancy b x (N₀ + k) < 1 / 8 :=
            (hN₀_def (N₀ + k) (by omega)).trans_le (min_le_right _ _)
          have hnext_lt : 1 - radixDiscrepancy b x (N₀ + k + 1) < 1 / 8 :=
            (hN₀_def (N₀ + k + 1) (by omega)).trans_le (min_le_right _ _)
          have hst := hstep_le 1 m' (N₀ + k) (by omega)
          have hinv : 1 / ((N₀ + k + 1 : ℕ) : ℝ) ≤ 1 / 6 :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 6 ≤ N₀ + k + 1 by omega))
          linarith
    left
    intro L hL
    have hother_ev : ∀ᶠ N in atTop, otherWordFreq b L x N ≤ 1 - radixDiscrepancy b x N := by
      set ηL : ℝ := min (1 / (b : ℝ) ^ (L + 1)) (1 / 4)
      have hηL : 0 < ηL := lt_min (by positivity) (by norm_num)
      have hltL : ∀ᶠ N in atTop, 1 - radixDiscrepancy b x N < ηL := by
        filter_upwards [Metric.tendsto_nhds.mp hdef ηL hηL] with N hN
        exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hN)
      filter_upwards [eventually_ge_atTop N₀, hltL] with N hN hδL
      rcases finite_digit_dichotomy hb (by omega) hL x (hδL.trans_le (min_le_left _ _)) with
          ⟨hbd, _⟩ | ⟨⟨m', ⟨hm'1, hm'b, hint⟩, _⟩, _⟩
      · exact hbd
      · exfalso
        have hsub := hlevel_sub L hL m' hm'1 hm'b N
        have hfreq_le : wordFreq b L x (m' * repunit b L) N ≤ wordFreq b 1 x m' N :=
          div_le_div_of_nonneg_right (by exact_mod_cast hsub) (Nat.cast_nonneg N)
        have hm'_other : wordFreq b 1 x m' N ≤ otherWordFreq b 1 x N :=
          hdigit_other m' N hm'1 hm'b
        have h1 := hbd_all N hN
        have hδ_lt1 : 1 - radixDiscrepancy b x N < 1 / 8 :=
          (hN₀_def N hN).trans_le (min_le_right _ _)
        linarith [hδL.trans_le (min_le_right _ _)]
    have hother_to0 : Tendsto (otherWordFreq b L x) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun N => by unfold otherWordFreq; positivity) hother_ev hdef
    refine ⟨hother_to0, ?_⟩
    -- Show `0 ≤ digitFreq b x 0 N - wordFreq b L x 0 N ≤ otherWordFreq b L x N`.
    have hdiff_bound : ∀ N,
        |wordFreq b L x 0 N - digitFreq b x 0 N| ≤ otherWordFreq b L x N := by
      intro N
      have hsub0 : (range N).filter (fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = 0) ⊆
          (range N).filter (fun n => ⌊(b : ℝ) ^ 1 * shift b x n⌋₊ = 0) := by
        intro n hn
        obtain ⟨hnN, heq⟩ := mem_filter.mp hn
        refine mem_filter.mpr ⟨hnN, ?_⟩
        rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) (shift_nonneg b x n)] at heq ⊢
        have hb_pos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
        have hpow_ge : (b : ℝ) ^ 1 ≤ (b : ℝ) ^ L := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) hL
        have hinv : 1 / (b : ℝ) ^ L ≤ 1 / (b : ℝ) ^ 1 := one_div_le_one_div_of_le (by positivity) hpow_ge
        simp only [Nat.cast_zero, zero_div, zero_add] at heq ⊢
        exact ⟨heq.1, heq.2.trans_le hinv⟩
      have hdiff_sub :
          ((range N).filter fun n => ⌊(b : ℝ) ^ 1 * shift b x n⌋₊ = 0) \
            ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = 0) ⊆
          (range N).filter fun n =>
            ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ 0 ∧ ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ b ^ L - 1 := by
        intro n hn
        obtain ⟨h1, h2⟩ := mem_sdiff.mp hn
        obtain ⟨hnN, heq1⟩ := mem_filter.mp h1
        have hne0 : ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ 0 := fun h => h2 (mem_filter.mpr ⟨hnN, h⟩)
        have hnetop : ⌊(b : ℝ) ^ L * shift b x n⌋₊ ≠ b ^ L - 1 := by
          intro htop
          rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) (shift_nonneg b x n)] at heq1 htop
          have hge1 : 1 ≤ b ^ L := Nat.one_le_pow L b (by omega)
          have hb_pos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
          have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
          have hbL_ge : (b : ℝ) ≤ (b : ℝ) ^ L := by
            simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ b by linarith) hL
          have h1' : shift b x n < 1 / (b : ℝ) := by simpa using heq1.2
          have h2' : 1 - 1 / (b : ℝ) ^ L ≤ shift b x n := by
            have := htop.1
            rw [Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one, sub_div,
              div_self (pow_ne_zero L hb_pos.ne')] at this
            exact this
          have hinv_le : 1 / (b : ℝ) ^ L ≤ 1 / (b : ℝ) := one_div_le_one_div_of_le hb_pos hbL_ge
          have hsum_le : 1 / (b : ℝ) + 1 / (b : ℝ) ≤ 1 := by
            rw [← add_div, div_le_one hb_pos]; linarith
          linarith
        exact mem_filter.mpr ⟨hnN, hne0, hnetop⟩
      have hcard_le : wordCount b L x 0 N ≤ wordCount b 1 x 0 N := card_le_card hsub0
      have hcard_diff : wordCount b 1 x 0 N - wordCount b L x 0 N ≤ otherWordCount b L x N := by
        unfold wordCount otherWordCount
        rw [← card_sdiff_of_subset hsub0]
        exact card_le_card hdiff_sub
      have hfreq_le : wordFreq b L x 0 N ≤ digitFreq b x 0 N :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) (Nat.cast_nonneg N)
      rw [abs_of_nonpos (by linarith), neg_sub]
      unfold digitFreq wordFreq otherWordFreq
      rw [← sub_div, ← Nat.cast_sub hcard_le]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_diff) (Nat.cast_nonneg N)
    exact squeeze_zero_norm (fun N => by simpa [Real.norm_eq_abs] using hdiff_bound N) hother_to0
  · -- Case 2: Interior `m` at `(L = 1, N₀)` persists for all `N ≥ N₀` and forces interior `m` for every `L ≥ 1`.
    have hrep1 : repunit b 1 = 1 := by simp [repunit]
    rw [hrep1, mul_one] at hint₀
    have hint_all : ∀ N ≥ N₀, 1 - wordFreq b 1 x m N ≤ 1 - radixDiscrepancy b x N := by
      intro N hN
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
      induction k with
      | zero => simpa using hint₀
      | succ k ih =>
        have hprev := ih (by omega)
        have hlt_next : 1 - radixDiscrepancy b x (N₀ + k + 1) < 1 / (b : ℝ) ^ (1 + 1) :=
          (hN₀_def (N₀ + k + 1) (by omega)).trans_le (min_le_left _ _)
        have hprev_lt : 1 - radixDiscrepancy b x (N₀ + k) < 1 / 8 :=
          (hN₀_def (N₀ + k) (by omega)).trans_le (min_le_right _ _)
        have hnext_lt : 1 - radixDiscrepancy b x (N₀ + k + 1) < 1 / 8 :=
          (hN₀_def (N₀ + k + 1) (by omega)).trans_le (min_le_right _ _)
        have hst := hstep_ge 1 m (N₀ + k) (by omega)
        rcases finite_digit_dichotomy hb (by omega) le_rfl x hlt_next with
            ⟨hbd, _⟩ | ⟨⟨m', ⟨hm'1, hm'b, hint⟩, _⟩, _⟩
        · exfalso
          have hm_other : wordFreq b 1 x m (N₀ + k + 1) ≤ otherWordFreq b 1 x (N₀ + k + 1) :=
            hdigit_other m (N₀ + k + 1) hm1 hmb
          linarith
        · rw [hrep1, mul_one] at hint
          have hm_eq : m' = m := by
            by_contra hne
            have hadd := wordCount_add_le_of_ne (b := b) (L := 1) x hne (N₀ + k + 1)
            have hNr : (0 : ℝ) < (N₀ + k + 1 : ℕ) := by positivity
            have hsum_le : wordFreq b 1 x m' (N₀ + k + 1) + wordFreq b 1 x m (N₀ + k + 1) ≤ 1 := by
              unfold wordFreq; rw [← add_div, div_le_one hNr]; exact_mod_cast hadd
            linarith
          rwa [← hm_eq]
    right
    refine ⟨m, ⟨hm1, hmb, fun L hL => ?_⟩, fun m' ⟨hm'1, _, hm'lim⟩ => ?_⟩
    · have hgap_ev : ∀ᶠ N in atTop,
          1 - wordFreq b L x (m * repunit b L) N ≤ 1 - radixDiscrepancy b x N := by
        set ηL : ℝ := min (1 / (b : ℝ) ^ (L + 1)) (1 / 4)
        have hηL : 0 < ηL := lt_min (by positivity) (by norm_num)
        have hltL : ∀ᶠ N in atTop, 1 - radixDiscrepancy b x N < ηL := by
          filter_upwards [Metric.tendsto_nhds.mp hdef ηL hηL] with N hN
          exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hN)
        filter_upwards [eventually_ge_atTop N₀, hltL] with N hN hδL
        have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
        have hδ_lt1 : 1 - radixDiscrepancy b x N < 1 / 8 :=
          (hN₀_def N hN).trans_le (min_le_right _ _)
        have hm1_hi := hint_all N hN
        rcases finite_digit_dichotomy hb (by omega) hL x (hδL.trans_le (min_le_left _ _)) with
            ⟨hbd, _⟩ | ⟨⟨m', ⟨hm'1, hm'b, hint⟩, _⟩, _⟩
        · exfalso
          -- Every shift reading digit `m` reads a length-`L` word other than `0^L` and `(b-1)^L`.
          have hm_sub : wordCount b 1 x m N ≤ otherWordCount b L x N := by
            refine card_le_card (fun n hn => ?_)
            obtain ⟨hnN, heq⟩ := mem_filter.mp hn
            rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) (shift_nonneg b x n), pow_one] at heq
            refine mem_filter.mpr ⟨hnN, ?_, ?_⟩
            · intro h0
              rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) (shift_nonneg b x n)] at h0
              have hb_pos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
              have hbL_ge : (b : ℝ) ≤ (b : ℝ) ^ L := by
                simpa using pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) hL
              have hinv : 1 / (b : ℝ) ^ L ≤ 1 / (b : ℝ) := one_div_le_one_div_of_le hb_pos hbL_ge
              have hm_ge1 : (1 : ℝ) / (b : ℝ) ≤ (m : ℝ) / (b : ℝ) :=
                div_le_div_of_nonneg_right (by exact_mod_cast hm1) hb_pos.le
              simp only [Nat.cast_zero, zero_add] at h0
              linarith
            · intro htop
              rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) (shift_nonneg b x n)] at htop
              have hb_pos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
              have hge1 : 1 ≤ b ^ L := Nat.one_le_pow L b (by omega)
              have hbL_ge : (b : ℝ) ≤ (b : ℝ) ^ L := by
                simpa using pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) hL
              have hinv : 1 / (b : ℝ) ^ L ≤ 1 / (b : ℝ) := one_div_le_one_div_of_le hb_pos hbL_ge
              have htop_lo : 1 - 1 / (b : ℝ) ^ L ≤ shift b x n := by
                have := htop.1
                rw [Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one, sub_div,
                  div_self (pow_ne_zero L hb_pos.ne')] at this
                exact this
              have hm_hi : ((m : ℝ) + 1) / (b : ℝ) ≤ 1 - 1 / (b : ℝ) := by
                have hmb' : (m : ℝ) + 2 ≤ (b : ℝ) := by exact_mod_cast hmb
                have : (m : ℝ) + 1 ≤ (b : ℝ) - 1 := by linarith
                rw [show 1 - 1 / (b : ℝ) = ((b : ℝ) - 1) / (b : ℝ) by field_simp [hb_pos.ne']]
                exact div_le_div_of_nonneg_right this hb_pos.le
              linarith
          have hfreq_le : wordFreq b 1 x m N ≤ otherWordFreq b L x N :=
            div_le_div_of_nonneg_right (by exact_mod_cast hm_sub) hNr.le
          linarith [hδL.trans_le (min_le_right _ _)]
        · have hm_eq : m' = m := by
            by_contra hne
            have hsub := hlevel_sub L hL m' hm'1 hm'b N
            have hfreq_le : wordFreq b L x (m' * repunit b L) N ≤ wordFreq b 1 x m' N :=
              div_le_div_of_nonneg_right (by exact_mod_cast hsub) hNr.le
            have hadd := wordCount_add_le_of_ne (b := b) (L := 1) x hne N
            have hsum_le : wordFreq b 1 x m' N + wordFreq b 1 x m N ≤ 1 := by
              unfold wordFreq; rw [← add_div, div_le_one hNr]; exact_mod_cast hadd
            linarith [hδL.trans_le (min_le_right _ _)]
          rwa [← hm_eq]
      have hgap_to0 : Tendsto (fun N => 1 - wordFreq b L x (m * repunit b L) N) atTop (𝓝 0) :=
        squeeze_zero'
          (Eventually.of_forall fun N => by linarith [(wordFreq_bounds b L x (m * repunit b L) N).2])
          hgap_ev hdef
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hgap_to0
    · by_contra hne
      have h1 := hm'lim 1 le_rfl
      rw [hrep1, mul_one] at h1
      have h2 : Tendsto (wordFreq b 1 x m) atTop (𝓝 1) := by
        have hgap_to0 : Tendsto (fun N => 1 - wordFreq b 1 x m N) atTop (𝓝 0) :=
          squeeze_zero'
            (Eventually.of_forall fun N => by linarith [(wordFreq_bounds b 1 x m N).2])
            (eventually_atTop.mpr ⟨N₀, hint_all⟩) hdef
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hgap_to0
      have hsum_lim : Tendsto (fun N => wordFreq b 1 x m' N + wordFreq b 1 x m N) atTop (𝓝 2) := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num]
        exact h1.add h2
      have hsum_le : ∀ᶠ N in atTop, wordFreq b 1 x m' N + wordFreq b 1 x m N ≤ 1 := by
        filter_upwards [eventually_ge_atTop 1] with N hN1
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
        unfold wordFreq
        rw [← add_div, div_le_one hNr]
        exact_mod_cast wordCount_add_le_of_ne (b := b) (L := 1) x hne N
      have hle2 : (2 : ℝ) ≤ 1 := le_of_tendsto hsum_lim hsum_le
      linarith

/-! ### Part 5: Oriented tails and finite signed coefficient transfer (Lemma 5.1, Theorem 5.2) -/

/-- The oriented tail `T_n = ∑_{j ≥ 0} a(n + 1 + j) / b^(1 + j) = ∑_{m > n} a(m) b^{n - m}`. -/
noncomputable def orientedTail (b : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, (a (n + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j)

/-- Alias `tailSeries` for `orientedTail`. -/
noncomputable abbrev tailSeries := orientedTail

open Classical in
/-- Number of shifts `n < N` with nonnegative oriented tail `T_n ≥ 0` (`Γ⁺(N)`). -/
noncomputable def posTailCount (b : ℕ) (a : ℕ → ℤ) (N : ℕ) : ℕ :=
  ((range N).filter fun n => 0 ≤ orientedTail b a n).card

open Classical in
/-- Number of shifts `n < N` with negative oriented tail `T_n < 0` (`N - Γ⁺(N)`). -/
noncomputable def negTailCount (b : ℕ) (a : ℕ → ℤ) (N : ℕ) : ℕ :=
  ((range N).filter fun n => orientedTail b a n < 0).card

open Classical in
/-- Number of bad-tail shifts `n < N` with `|T_n| ≥ b^(-L)` (`B'_L(N)`). -/
noncomputable def badTailCount (b : ℕ) (a : ℕ → ℤ) (L N : ℕ) : ℕ :=
  ((range N).filter fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|).card

theorem posTailCount_add_negTailCount (b : ℕ) (a : ℕ → ℤ) (N : ℕ) :
    posTailCount b a N + negTailCount b a N = N := by
  classical
  unfold posTailCount negTailCount
  have heq : (range N).filter (fun n => orientedTail b a n < 0) =
      (range N).filter (fun n => ¬ (0 ≤ orientedTail b a n)) :=
    Finset.filter_congr (fun _ _ => not_le.symm)
  rw [heq, Finset.card_filter_add_card_filter_not, card_range]

private lemma summable_raw_of_abs {b : ℕ} (hb : 1 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) :
    Summable fun m => (a m : ℝ) / (b : ℝ) ^ m := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  refine Summable.of_norm ?_
  convert hsum using 1
  ext m
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 m)]

private lemma summable_orientedTail_abs {b : ℕ} (hb : 1 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    Summable fun j : ℕ => |(a (n + 1 + j) : ℝ)| / (b : ℝ) ^ (1 + j) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hshift := (summable_nat_add_iff (n + 1)).mpr hsum
  have hmul := hshift.mul_left ((b : ℝ) ^ n)
  refine hmul.congr (fun j => ?_)
  have h1 : j + (n + 1) = n + 1 + j := by omega
  have h2 : n + (1 + j) = n + 1 + j := by omega
  rw [h1, ← h2, pow_add]
  field_simp [hb0.ne']

private lemma summable_orientedTail {b : ℕ} (hb : 1 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    Summable fun j : ℕ => (a (n + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  refine Summable.of_norm ?_
  convert summable_orientedTail_abs hb hsum n using 1
  ext j
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 _)]

/-- **Lemma 5.1 (integer head + oriented tail decomposition).** -/
theorem pow_mul_coeffSeries_eq_int_add_tail {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    (b : ℝ) ^ n * coeffSeries b a =
      ((∑ m ∈ range (n + 1), a m * (b : ℤ) ^ (n - m) : ℤ) : ℝ) + orientedTail b a n := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hraw := summable_raw_of_abs (show 1 ≤ b by omega) hsum
  have hsplit := hraw.sum_add_tsum_nat_add (n + 1)
  have hint : (b : ℝ) ^ n * ∑ m ∈ range (n + 1), (a m : ℝ) / (b : ℝ) ^ m =
      ((∑ m ∈ range (n + 1), a m * (b : ℤ) ^ (n - m) : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hmn : m ≤ n := by have := mem_range.mp hm; omega
    have hpow : (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [hpow]
    field_simp [hb0.ne']
  unfold coeffSeries orientedTail
  rw [← hsplit, mul_add, hint, ← tsum_mul_left]
  congr 1
  congr 1
  ext j
  have h1 : j + (n + 1) = n + 1 + j := by omega
  have h2 : n + (1 + j) = n + 1 + j := by omega
  rw [h1, ← h2, pow_add]
  field_simp [hb0.ne']

/-- **Lemma 5.1.** `{b^n F_b(a)} = {T_n}` for every absolutely convergent integer coefficient series. -/
theorem shift_coeffSeries_eq_fract_tail {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    shift b (coeffSeries b a) n = Int.fract (orientedTail b a n) := by
  unfold shift
  rw [pow_mul_coeffSeries_eq_int_add_tail hb hsum n, add_comm, Int.fract_add_intCast]

/-- Alias for `shift_coeffSeries_eq_fract_tail`. -/
theorem shift_eq_fract_tail {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    shift b (coeffSeries b a) n = Int.fract (tailSeries b a n) :=
  shift_coeffSeries_eq_fract_tail hb hsum n

/-- **Lemma 5.1 (tail recursion).** `T_n = (a(n + 1) + T_{n + 1}) / b`. -/
theorem orientedTail_succ {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    orientedTail b a n = ((a (n + 1) : ℝ) + orientedTail b a (n + 1)) / b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hst := summable_orientedTail (show 1 ≤ b by omega) hsum n
  unfold orientedTail
  rw [hst.tsum_eq_zero_add]
  have htail : (∑' j : ℕ, (a (n + 1 + (j + 1)) : ℝ) / (b : ℝ) ^ (1 + (j + 1))) =
      (∑' j : ℕ, (a (n + 1 + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j)) / (b : ℝ) := by
    rw [← tsum_div_const]
    congr 1
    ext j
    have h1 : n + 1 + (j + 1) = n + 1 + 1 + j := by omega
    have h2 : 1 + (j + 1) = (1 + j) + 1 := by omega
    rw [h1, h2, pow_succ, div_div]
  rw [htail, add_zero, pow_one, add_div]

/-- **Theorem 5.2(a) (positive side).** If `0 ≤ T < b^(-L)`, then `{T}` reads `0^L`. -/
theorem floor_fract_eq_zero {b L : ℕ} (hb : 2 ≤ b) {T : ℝ} (h0 : 0 ≤ T)
    (h1 : T < 1 / (b : ℝ) ^ L) : ⌊(b : ℝ) ^ L * Int.fract T⌋₊ = 0 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by linarith) L
  have hinv_le1 : 1 / (b : ℝ) ^ L ≤ 1 := (div_le_one hbL_pos).mpr (one_le_pow₀ hb1)
  rw [Int.fract_eq_self.mpr ⟨h0, h1.trans_le hinv_le1⟩]
  rw [floor_pow_mul_eq_iff (show 1 ≤ b by omega) h0]
  exact ⟨by simp [h0], by simpa using h1⟩

/-- **Theorem 5.2(a) (negative side).** If `-b^(-L) ≤ T < 0`, then `{T}` reads `(b - 1)^L`. -/
theorem floor_fract_eq_top {b L : ℕ} (hb : 2 ≤ b) {T : ℝ} (h0 : -(1 / (b : ℝ) ^ L) ≤ T)
    (h1 : T < 0) : ⌊(b : ℝ) ^ L * Int.fract T⌋₊ = b ^ L - 1 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by linarith) L
  have hinv_le1 : 1 / (b : ℝ) ^ L ≤ 1 := (div_le_one hbL_pos).mpr (one_le_pow₀ hb1)
  have hfr : Int.fract T = T + 1 := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
  rw [hfr, floor_pow_mul_eq_iff (show 1 ≤ b by omega) (by linarith)]
  have hge1 : 1 ≤ b ^ L := Nat.one_le_pow L b (by omega)
  rw [Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one]
  constructor
  · rw [sub_div, div_self hbL_pos.ne']
    linarith
  · have : ((b : ℝ) ^ L - 1 + 1) / (b : ℝ) ^ L = 1 := by field_simp [hbL_pos.ne']; ring
    rw [this]
    linarith

/-- **Theorem 5.2(b) (other words bounded by bad tails).** -/
theorem otherWordCount_le_badTailCount {b L : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (N : ℕ) :
    otherWordCount b L (coeffSeries b a) N ≤ badTailCount b a L N := by
  classical
  unfold otherWordCount badTailCount
  refine card_le_card (fun n hn => ?_)
  obtain ⟨hnN, hne0, hnetop⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨hnN, ?_⟩
  by_contra hlt
  push Not at hlt
  rw [abs_lt] at hlt
  rw [shift_coeffSeries_eq_fract_tail hb hsum n] at hne0 hnetop
  rcases le_or_gt 0 (orientedTail b a n) with hpos | hneg
  · exact hne0 (floor_fract_eq_zero hb hpos hlt.2)
  · exact hnetop (floor_fract_eq_top hb hlt.1.le hneg)

/-- **Theorem 5.2(c) (finite oriented-tail bound for `0^L`).**
Among the first `N` starts, the count of `0^L` differs from `#{n < N : T_n ≥ 0}` by at most
`badTailCount b a L N`. -/
theorem wordCount_zeros_sub_posTail_le {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (N : ℕ) :
    |(wordCount b L (coeffSeries b a) 0 N : ℝ) - (posTailCount b a N : ℝ)| ≤
      (badTailCount b a L N : ℝ) := by
  classical
  set P := (range N).filter fun n => 0 ≤ orientedTail b a n ∧ orientedTail b a n < 1 / (b : ℝ) ^ L
  set Q := (range N).filter fun n => -(1 / (b : ℝ) ^ L) ≤ orientedTail b a n ∧ orientedTail b a n < 0
  set W₀ := (range N).filter fun n => ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ = 0
  set Wtop := (range N).filter fun n => ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ = b ^ L - 1
  set Γ := (range N).filter fun n => 0 ≤ orientedTail b a n
  set B' := (range N).filter fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|
  have hP_W₀ : P ⊆ W₀ := by
    intro n hn
    obtain ⟨hnN, h0, h1⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnN, ?_⟩
    rw [shift_coeffSeries_eq_fract_tail hb hsum n]
    exact floor_fract_eq_zero hb h0 h1
  have hQ_Wtop : Q ⊆ Wtop := by
    intro n hn
    obtain ⟨hnN, h0, h1⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnN, ?_⟩
    rw [shift_coeffSeries_eq_fract_tail hb hsum n]
    exact floor_fract_eq_top hb h0 h1
  have htop_ne : (0 : ℕ) ≠ b ^ L - 1 := by
    have : 2 ≤ b ^ L := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hL)
    omega
  have hW₀_sub : W₀ ⊆ P ∪ B' := by
    intro n hn
    obtain ⟨hnN, heq0⟩ := mem_filter.mp hn
    rw [mem_union]
    by_cases hbad : 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|
    · exact Or.inr (mem_filter.mpr ⟨hnN, hbad⟩)
    · push Not at hbad
      rw [abs_lt] at hbad
      rcases le_or_gt 0 (orientedTail b a n) with hpos | hneg
      · exact Or.inl (mem_filter.mpr ⟨hnN, hpos, hbad.2⟩)
      · exfalso
        have htop : ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ = b ^ L - 1 := by
          rw [shift_coeffSeries_eq_fract_tail hb hsum n]
          exact floor_fract_eq_top hb hbad.1.le hneg
        exact htop_ne (heq0.symm.trans htop)
  have hP_Γ : P ⊆ Γ := by
    intro n hn
    obtain ⟨hnN, h0, _⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, h0⟩
  have hΓ_sub : Γ ⊆ P ∪ B' := by
    intro n hn
    obtain ⟨hnN, h0⟩ := mem_filter.mp hn
    rw [mem_union]
    by_cases hlt : orientedTail b a n < 1 / (b : ℝ) ^ L
    · exact Or.inl (mem_filter.mpr ⟨hnN, h0, hlt⟩)
    · push Not at hlt
      exact Or.inr (mem_filter.mpr ⟨hnN, by rwa [abs_of_nonneg h0]⟩)
  have h1 : P.card ≤ W₀.card := card_le_card hP_W₀
  have h2 : W₀.card ≤ P.card + B'.card := (card_le_card hW₀_sub).trans (card_union_le P B')
  have h3 : P.card ≤ Γ.card := card_le_card hP_Γ
  have h4 : Γ.card ≤ P.card + B'.card := (card_le_card hΓ_sub).trans (card_union_le P B')
  have h1r : (P.card : ℝ) ≤ (W₀.card : ℝ) := by exact_mod_cast h1
  have h2r : (W₀.card : ℝ) ≤ (P.card : ℝ) + (B'.card : ℝ) := by exact_mod_cast h2
  have h3r : (P.card : ℝ) ≤ (Γ.card : ℝ) := by exact_mod_cast h3
  have h4r : (Γ.card : ℝ) ≤ (P.card : ℝ) + (B'.card : ℝ) := by exact_mod_cast h4
  change |(W₀.card : ℝ) - (Γ.card : ℝ)| ≤ (B'.card : ℝ)
  rw [abs_le]
  constructor <;> linarith

/-- **Theorem 5.2(c) (finite oriented-tail bound for `(b - 1)^L`).**
Among the first `N` starts, the count of `(b - 1)^L` differs from `#{n < N : T_n < 0}` by at most
`badTailCount b a L N`. -/
theorem wordCount_maxDigit_sub_negTail_le {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (N : ℕ) :
    |(wordCount b L (coeffSeries b a) (b ^ L - 1) N : ℝ) - (negTailCount b a N : ℝ)| ≤
      (badTailCount b a L N : ℝ) := by
  classical
  set Q := (range N).filter fun n => -(1 / (b : ℝ) ^ L) ≤ orientedTail b a n ∧ orientedTail b a n < 0
  set Wtop := (range N).filter fun n => ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ = b ^ L - 1
  set Γ' := (range N).filter fun n => orientedTail b a n < 0
  set B' := (range N).filter fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|
  have hQ_Wtop : Q ⊆ Wtop := by
    intro n hn
    obtain ⟨hnN, h0, h1⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnN, ?_⟩
    rw [shift_coeffSeries_eq_fract_tail hb hsum n]
    exact floor_fract_eq_top hb h0 h1
  have htop_ne : (0 : ℕ) ≠ b ^ L - 1 := by
    have : 2 ≤ b ^ L := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hL)
    omega
  have hWtop_sub : Wtop ⊆ Q ∪ B' := by
    intro n hn
    obtain ⟨hnN, heqtop⟩ := mem_filter.mp hn
    rw [mem_union]
    by_cases hbad : 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|
    · exact Or.inr (mem_filter.mpr ⟨hnN, hbad⟩)
    · push Not at hbad
      rw [abs_lt] at hbad
      rcases le_or_gt 0 (orientedTail b a n) with hpos | hneg
      · exfalso
        have h0 : ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ = 0 := by
          rw [shift_coeffSeries_eq_fract_tail hb hsum n]
          exact floor_fract_eq_zero hb hpos hbad.2
        exact htop_ne (h0.symm.trans heqtop)
      · exact Or.inl (mem_filter.mpr ⟨hnN, hbad.1.le, hneg⟩)
  have hQ_Γ' : Q ⊆ Γ' := by
    intro n hn
    obtain ⟨hnN, _, h1⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, h1⟩
  have hΓ'_sub : Γ' ⊆ Q ∪ B' := by
    intro n hn
    obtain ⟨hnN, hneg⟩ := mem_filter.mp hn
    rw [mem_union]
    by_cases hge : -(1 / (b : ℝ) ^ L) ≤ orientedTail b a n
    · exact Or.inl (mem_filter.mpr ⟨hnN, hge, hneg⟩)
    · push Not at hge
      exact Or.inr (mem_filter.mpr ⟨hnN, by rw [abs_of_neg hneg]; linarith⟩)
  have h1 : Q.card ≤ Wtop.card := card_le_card hQ_Wtop
  have h2 : Wtop.card ≤ Q.card + B'.card := (card_le_card hWtop_sub).trans (card_union_le Q B')
  have h3 : Q.card ≤ Γ'.card := card_le_card hQ_Γ'
  have h4 : Γ'.card ≤ Q.card + B'.card := (card_le_card hΓ'_sub).trans (card_union_le Q B')
  have h1r : (Q.card : ℝ) ≤ (Wtop.card : ℝ) := by exact_mod_cast h1
  have h2r : (Wtop.card : ℝ) ≤ (Q.card : ℝ) + (B'.card : ℝ) := by exact_mod_cast h2
  have h3r : (Q.card : ℝ) ≤ (Γ'.card : ℝ) := by exact_mod_cast h3
  have h4r : (Γ'.card : ℝ) ≤ (Q.card : ℝ) + (B'.card : ℝ) := by exact_mod_cast h4
  change |(Wtop.card : ℝ) - (Γ'.card : ℝ)| ≤ (B'.card : ℝ)
  rw [abs_le]
  constructor <;> linarith

/-! ### Part 6: Sharp shadow bound, bad-tail estimates, and dominance (Theorem 5.3, Prop. 6.1, Lemma 6.2, Cor. 6.4) -/

/-- **Sharp local-support shadow bound.** The number of shifts `n < N` with a nonzero coefficient
in `(n, n + L]` is at most `L * (1 + S(N - 1))` (using only support points `≤ N - 1` plus at most
one trailing shadow window for the first support point `≥ N`). -/
theorem nearSupport_card_le_succ (a : ℕ → ℤ) (N L : ℕ) :
    nearSupportCount a N L ≤ L * (1 + supportCount a (N - 1)) := by
  classical
  unfold nearSupportCount
  set W := (range N).filter (hasLocalSupport a L)
  -- For `n ∈ W`, `nextOcc n` is the smallest `m > n` with `a m ≠ 0`.
  have hex : ∀ n ∈ W, ∃ m, n < m ∧ a m ≠ 0 := by
    intro n hn
    obtain ⟨j, hj, haj⟩ := (mem_filter.mp hn).2
    rw [mem_Icc] at hj
    exact ⟨n + j, by omega, haj⟩
  let nextOcc : ℕ → ℕ := fun n =>
    if h : ∃ m, n < m ∧ a m ≠ 0 then Nat.find h else 0
  have hnext_spec : ∀ n ∈ W,
      n < nextOcc n ∧ a (nextOcc n) ≠ 0 ∧ nextOcc n ≤ n + L ∧
      ∀ k, n < k → k < nextOcc n → a k = 0 := by
    intro n hn
    have h := hex n hn
    have hEq : nextOcc n = Nat.find h := by simp [nextOcc, h]
    rw [hEq]
    have hspec := Nat.find_spec h
    obtain ⟨j, hj, haj⟩ := (mem_filter.mp hn).2
    rw [mem_Icc] at hj
    have hle : Nat.find h ≤ n + j := Nat.find_min' h ⟨by omega, haj⟩
    refine ⟨hspec.1, hspec.2, by omega, fun k hk1 hk2 => ?_⟩
    by_contra hne
    exact Nat.find_min h hk2 ⟨hk1, hne⟩
  -- Split `W` according to whether `nextOcc n ≤ N - 1` or `nextOcc n ≥ N`.
  set W_in := W.filter (fun n => nextOcc n ≤ N - 1)
  set W_out := W.filter (fun n => ¬ (nextOcc n ≤ N - 1))
  have hW_split : W.card = W_in.card + W_out.card :=
    (Finset.card_filter_add_card_filter_not (s := W) (fun n => nextOcc n ≤ N - 1)).symm
  -- Bound `W_in` by `L * supportCount a (N - 1)`.
  have hWin_le : W_in.card ≤ L * supportCount a (N - 1) := by
    set T := (Icc 1 (N - 1)).filter (fun m => a m ≠ 0)
    have hcard : (T ×ˢ Icc 1 L).card = L * supportCount a (N - 1) := by
      rw [card_product, Nat.card_Icc, mul_comm]
      have : L + 1 - 1 = L := by omega
      rw [this]
      unfold supportCount
      congr 1
    rw [← hcard]
    refine card_le_card_of_injOn (fun n => (nextOcc n, nextOcc n - n)) ?_ ?_
    · intro n hn
      obtain ⟨hnW, hn_le⟩ := mem_filter.mp (mem_coe.mp hn)
      obtain ⟨hlt, hne, hleL, _⟩ := hnext_spec n hnW
      rw [mem_coe, mem_product, mem_filter, mem_Icc, mem_Icc]
      dsimp only
      exact ⟨⟨⟨by omega, hn_le⟩, hne⟩, ⟨by omega, by omega⟩⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      have h1 : nextOcc n₁ = nextOcc n₂ := congrArg Prod.fst heq
      have h2 : nextOcc n₁ - n₁ = nextOcc n₂ - n₂ := congrArg Prod.snd heq
      obtain ⟨hlt₁, _, _, _⟩ := hnext_spec n₁ (mem_filter.mp (mem_coe.mp hn₁)).1
      obtain ⟨hlt₂, _, _, _⟩ := hnext_spec n₂ (mem_filter.mp (mem_coe.mp hn₂)).1
      omega
  -- Bound `W_out` by `L`: all `n ∈ W_out` share the exact same `nextOcc n`.
  have hWout_le : W_out.card ≤ L := by
    have hcardL : (Icc 1 L).card = L := by rw [Nat.card_Icc]; omega
    rw [← hcardL]
    refine card_le_card_of_injOn (fun n => nextOcc n - n) ?_ ?_
    · intro n hn
      obtain ⟨hnW, _⟩ := mem_filter.mp (mem_coe.mp hn)
      obtain ⟨hlt, _, hleL, _⟩ := hnext_spec n hnW
      dsimp only
      exact mem_coe.mpr (mem_Icc.mpr ⟨by omega, by omega⟩)
    · intro n₁ hn₁ n₂ hn₂ heq
      obtain ⟨hn₁W, hn₁out⟩ := mem_filter.mp (mem_coe.mp hn₁)
      obtain ⟨hn₂W, hn₂out⟩ := mem_filter.mp (mem_coe.mp hn₂)
      have hn₁N : n₁ < N := mem_range.mp (mem_filter.mp hn₁W).1
      have hn₂N : n₂ < N := mem_range.mp (mem_filter.mp hn₂W).1
      obtain ⟨hlt₁, hne₁, _, hmin₁⟩ := hnext_spec n₁ hn₁W
      obtain ⟨hlt₂, hne₂, _, hmin₂⟩ := hnext_spec n₂ hn₂W
      -- Both `nextOcc n₁` and `nextOcc n₂` are `≥ N`, so each is `> n₁` and `> n₂`, forcing equality.
      have h12 : nextOcc n₁ ≤ nextOcc n₂ := by
        by_contra hgt
        push Not at hgt
        exact hne₂ (hmin₁ (nextOcc n₂) (by omega) hgt)
      have h21 : nextOcc n₂ ≤ nextOcc n₁ := by
        by_contra hgt
        push Not at hgt
        exact hne₁ (hmin₂ (nextOcc n₁) (by omega) hgt)
      dsimp only at heq
      omega
  calc W.card = W_in.card + W_out.card := hW_split
    _ ≤ L * supportCount a (N - 1) + L := Nat.add_le_add hWin_le hWout_le
    _ = L * (1 + supportCount a (N - 1)) := by ring

/-- **Theorem 5.3 (general shifted-tail bad-tail bound).** For every `b ≥ 2`, summable `a`, and
`N, L, k : ℕ`,
`badTailCount b a L N ≤ (L + k)(1 + S(N - 1)) + b^L * ∑_{n < N} shiftedTail b a n (L + k)`. -/
theorem badTail_card_le_of_shiftedTail {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (N L k : ℕ) :
    (badTailCount b a L N : ℝ) ≤
      (((L + k) * (1 + supportCount a (N - 1)) : ℕ) : ℝ) +
        (b : ℝ) ^ L * ∑ n ∈ range N, shiftedTail b a n (L + k) := by
  classical
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos hb0 L
  set A := (range N).filter (hasLocalSupport a (L + k))
  set B := (range N).filter (fun n => 1 / (b : ℝ) ^ L ≤ shiftedTail b a n (L + k))
  have hsub : (range N).filter (fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|) ⊆ A ∪ B := by
    intro n hn
    obtain ⟨hnN, hbad⟩ := mem_filter.mp hn
    rw [mem_union]
    by_cases hloc : hasLocalSupport a (L + k) n
    · exact Or.inl (mem_filter.mpr ⟨hnN, hloc⟩)
    · right
      refine mem_filter.mpr ⟨hnN, ?_⟩
      -- Since `a(n + 1) = ... = a(n + L + k) = 0`, `|orientedTail b a n| ≤ shiftedTail b a n (L + k)`.
      have hclear : ∀ j ∈ range (L + k), a (n + 1 + j) = 0 := by
        intro j hj
        by_contra hne
        exact hloc ⟨j + 1, mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩,
          by rwa [show n + (j + 1) = n + 1 + j by omega]⟩
      have hst := summable_orientedTail (show 1 ≤ b by omega) hsum n
      have hst_abs := summable_orientedTail_abs (show 1 ≤ b by omega) hsum n
      have hsplit := hst.sum_add_tsum_nat_add (L + k)
      have hhead0 : ∑ j ∈ range (L + k), (a (n + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j) = 0 :=
        Finset.sum_eq_zero (fun j hj => by simp [hclear j hj])
      have htail_eq : orientedTail b a n =
          ∑' j : ℕ, (a (n + (L + k) + 1 + j) : ℝ) / (b : ℝ) ^ ((L + k) + 1 + j) := by
        unfold orientedTail
        rw [← hsplit, hhead0, zero_add]
        congr 1; ext j
        have h1 : n + 1 + (j + (L + k)) = n + (L + k) + 1 + j := by omega
        have h2 : 1 + (j + (L + k)) = (L + k) + 1 + j := by omega
        rw [h1, h2]
      have hnorm_sum : Summable (fun j : ℕ =>
          ‖(a (n + (L + k) + 1 + j) : ℝ) / (b : ℝ) ^ ((L + k) + 1 + j)‖) := by
        have hs := (summable_nat_add_iff (L + k)).mpr hst_abs
        refine hs.congr (fun j => ?_)
        have h1 : n + 1 + (j + (L + k)) = n + (L + k) + 1 + j := by omega
        have h2 : 1 + (j + (L + k)) = (L + k) + 1 + j := by omega
        rw [h1, h2, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 _)]
      have hle_tail : |orientedTail b a n| ≤ shiftedTail b a n (L + k) := by
        rw [htail_eq, ← Real.norm_eq_abs]
        calc ‖∑' j : ℕ, (a (n + (L + k) + 1 + j) : ℝ) / (b : ℝ) ^ ((L + k) + 1 + j)‖
            ≤ ∑' j : ℕ, ‖(a (n + (L + k) + 1 + j) : ℝ) / (b : ℝ) ^ ((L + k) + 1 + j)‖ :=
              norm_tsum_le_tsum_norm hnorm_sum
          _ = shiftedTail b a n (L + k) := by
              unfold shiftedTail
              congr 1; ext j
              rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 _)]
      exact hbad.trans hle_tail
  have hA : A.card ≤ (L + k) * (1 + supportCount a (N - 1)) :=
    nearSupport_card_le_succ a N (L + k)
  have hB : (B.card : ℝ) ≤ (b : ℝ) ^ L * ∑ n ∈ range N, shiftedTail b a n (L + k) := by
    have hnn : ∀ n, 0 ≤ shiftedTail b a n (L + k) := fun n => tsum_nonneg (fun j => by positivity)
    have hmul : (B.card : ℝ) * (1 / (b : ℝ) ^ L) ≤ ∑ n ∈ range N, shiftedTail b a n (L + k) := by
      calc (B.card : ℝ) * (1 / (b : ℝ) ^ L)
          = ∑ _n ∈ B, (1 / (b : ℝ) ^ L) := by simp
        _ ≤ ∑ n ∈ B, shiftedTail b a n (L + k) :=
            Finset.sum_le_sum (fun n hn => (mem_filter.mp hn).2)
        _ ≤ ∑ n ∈ range N, shiftedTail b a n (L + k) :=
            Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => hnn n)
    have hstep := mul_le_mul_of_nonneg_left hmul hbL_pos.le
    have hrew : (b : ℝ) ^ L * ((B.card : ℝ) * (1 / (b : ℝ) ^ L)) = (B.card : ℝ) := by
      field_simp [hbL_pos.ne']
    linarith
  have hcard : badTailCount b a L N ≤ A.card + B.card :=
    (card_le_card hsub).trans (card_union_le A B)
  have hcard_r : (badTailCount b a L N : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hcard
  have hA_r : (A.card : ℝ) ≤ (((L + k) * (1 + supportCount a (N - 1)) : ℕ) : ℝ) := by
    exact_mod_cast hA
  linarith

/-- **Theorem 5.3 (linear-mass bad-tail bound).** Under `absMass a X ≤ C * X`, for all `N, L, k`:
`badTailCount b a L N ≤ (L + k)(1 + S(N - 1)) + C * (N + L + k + 2) / b^k`. -/
theorem badTail_card_le_linear_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ)) (N L k : ℕ) :
    (badTailCount b a L N : ℝ) ≤
      (((L + k) * (1 + supportCount a (N - 1)) : ℕ) : ℝ) +
        C * ((N + L + k + 2 : ℕ) : ℝ) / (b : ℝ) ^ k := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos hb0 L
  have hsum := summable_abs_of_linear_mass hb hmass
  have h1 := badTail_card_le_of_shiftedTail hb hsum N L k
  have h2 := sum_shiftedTail_le_of_linear_mass hb hC hmass N (L + k)
  have h3 := mul_le_mul_of_nonneg_left h2 hbL_pos.le
  have hrew : (b : ℝ) ^ L * (C * ((N + (L + k) + 2 : ℕ) : ℝ) / (b : ℝ) ^ (L + k)) =
      C * ((N + L + k + 2 : ℕ) : ℝ) / (b : ℝ) ^ k := by
    have hadd : N + (L + k) + 2 = N + L + k + 2 := by omega
    rw [hadd, pow_add]
    field_simp [hbL_pos.ne']
  linarith

/-- **Proposition 6.1 (gap-exact tail scaling).** Across a gap of `g - 1` zero coefficients
`a(n + 1) = ... = a(n + g - 1) = 0`, `T_n = T_{n + g - 1} / b^(g - 1)`. -/
theorem orientedTail_of_gap {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) {n g : ℕ} (hg : 1 ≤ g)
    (hgap : ∀ j ∈ Ioo 0 g, a (n + j) = 0) :
    orientedTail b a n = orientedTail b a (n + g - 1) / (b : ℝ) ^ (g - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hg
  clear hg
  rw [show 1 + d - 1 = d by omega, show n + (1 + d) - 1 = n + d by omega]
  induction d generalizing n with
  | zero => simp
  | succ d ih =>
    have ha1 : a (n + 1) = 0 := hgap 1 (mem_Ioo.mpr ⟨by omega, by omega⟩)
    have hgap' : ∀ j ∈ Ioo 0 (1 + d), a ((n + 1) + j) = 0 := by
      intro j hj
      rw [mem_Ioo] at hj
      have := hgap (j + 1) (mem_Ioo.mpr ⟨by omega, by omega⟩)
      rwa [show n + (j + 1) = (n + 1) + j by omega] at this
    rw [orientedTail_succ hb hsum n, ha1, Int.cast_zero, zero_add, ih hgap']
    rw [show n + 1 + d = n + (d + 1) by omega, div_div, ← pow_succ]

/-- **Lemma 6.2(b) (strict geometric tail bound).** If `|a(n + 1 + j)| ≤ H` for all `j` with
strict inequality for at least one `j`, then `|T_n| < H / (b - 1)`. -/
theorem abs_orientedTail_lt {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {n : ℕ} {H : ℝ}
    (hH : ∀ j, |(a (n + 1 + j) : ℝ)| ≤ H) (hlt : ∃ j, |(a (n + 1 + j) : ℝ)| < H) :
    |orientedTail b a n| < H / ((b : ℝ) - 1) := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < b := by linarith
  have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeo_sum : Summable (fun j : ℕ => H / (b : ℝ) ^ (1 + j)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left (H / (b : ℝ))
    refine h.congr (fun j => ?_)
    rw [pow_add, pow_one, inv_pow]; ring
  have hgeo_val : ∑' j : ℕ, H / (b : ℝ) ^ (1 + j) = H / ((b : ℝ) - 1) := by
    have hrew : (fun j : ℕ => H / (b : ℝ) ^ (1 + j)) =
        fun j : ℕ => (H / (b : ℝ)) * ((b : ℝ)⁻¹) ^ j := by
      ext j; rw [pow_add, pow_one, inv_pow]; ring
    rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    field_simp [hb_pos.ne', hbm1_pos.ne']
  have hterm_le : ∀ j : ℕ, |(a (n + 1 + j) : ℝ)| / (b : ℝ) ^ (1 + j) ≤ H / (b : ℝ) ^ (1 + j) :=
    fun j => div_le_div_of_nonneg_right (hH j) (by positivity)
  have habs_sum : Summable (fun j : ℕ => |(a (n + 1 + j) : ℝ)| / (b : ℝ) ^ (1 + j)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm_le hgeo_sum
  have hnorm_sum : Summable (fun j : ℕ => ‖(a (n + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j)‖) := by
    convert habs_sum using 1
    ext j
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb_pos _)]
  obtain ⟨j₀, hj₀⟩ := hlt
  have hstrict : |(a (n + 1 + j₀) : ℝ)| / (b : ℝ) ^ (1 + j₀) < H / (b : ℝ) ^ (1 + j₀) :=
    div_lt_div_of_pos_right hj₀ (pow_pos hb_pos _)
  have htsum_lt : ∑' j : ℕ, |(a (n + 1 + j) : ℝ)| / (b : ℝ) ^ (1 + j) <
      ∑' j : ℕ, H / (b : ℝ) ^ (1 + j) :=
    Summable.tsum_lt_tsum (i := j₀) hterm_le hstrict habs_sum hgeo_sum
  calc |orientedTail b a n|
      = ‖∑' j : ℕ, (a (n + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j : ℕ, ‖(a (n + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j)‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ = ∑' j : ℕ, |(a (n + 1 + j) : ℝ)| / (b : ℝ) ^ (1 + j) := by
        congr 1; ext j
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb_pos _)]
    _ < ∑' j : ℕ, H / (b : ℝ) ^ (1 + j) := htsum_lt
    _ = H / ((b : ℝ) - 1) := hgeo_val

/-- **Lemma 6.2(c) (sign determination under dominance).** If `|T_m| < |a(m)|`, then
`a(m) + T_m > 0 ↔ a(m) > 0`. -/
theorem sign_of_dominant {b : ℕ} {a : ℕ → ℤ} {m : ℕ}
    (hdom : |orientedTail b a m| < |(a m : ℝ)|) :
    (0 < (a m : ℝ) + orientedTail b a m ↔ 0 < a m) := by
  rcases lt_trichotomy (a m) 0 with hneg | hzero | hpos
  · have hcast : (a m : ℝ) < 0 := by exact_mod_cast hneg
    rw [abs_of_neg hcast, abs_lt] at hdom
    constructor
    · intro h; linarith
    · intro h; omega
  · simp [hzero] at hdom
    linarith [abs_nonneg (orientedTail b a m)]
  · have hcast : (0 : ℝ) < (a m : ℝ) := by exact_mod_cast hpos
    rw [abs_of_pos hcast, abs_lt] at hdom
    exact ⟨fun _ => hpos, fun _ => by linarith⟩

open Classical in
/-- **Corollary 6.4 (bounded coefficients with `H ≤ b - 1`).** If `|a(m)| ≤ H ≤ b - 1` for all `m`
and `a` is not cofinally nonzero (infinitely many zero coefficients), then
`badTailCount b a L N ≤ L * (1 + S(N - 1))`. -/
theorem badTail_card_le {b H : ℕ} (hb : 2 ≤ b) (hH : 1 ≤ H) (hHb : H + 1 ≤ b) {a : ℕ → ℤ}
    (hbd : ∀ m, |a m| ≤ H) (hcoinf : ∀ M, ∃ m > M, a m = 0) (N L : ℕ) :
    ((range N).filter fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|).card ≤
      L * (1 + supportCount a (N - 1)) := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < b := by linarith
  have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hH_le : (H : ℝ) / ((b : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hbm1_pos]
    have : (H : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hHb
    linarith
  -- Every oriented tail satisfies `|T_m| < 1`.
  have htail_lt1 : ∀ m : ℕ, |orientedTail b a m| < 1 := by
    intro m
    obtain ⟨k, hk_gt, hak⟩ := hcoinf (m + 1)
    have hbd_r : ∀ j, |(a (m + 1 + j) : ℝ)| ≤ (H : ℝ) := fun j => by
      exact_mod_cast hbd (m + 1 + j)
    have hlt_j : ∃ j, |(a (m + 1 + j) : ℝ)| < (H : ℝ) :=
      ⟨k - (m + 1), by rw [show m + 1 + (k - (m + 1)) = k by omega, hak]; simpa using hH_pos⟩
    exact (abs_orientedTail_lt hb hbd_r hlt_j).trans_le hH_le
  -- Summability of `|a(m)| / b^m` from uniform bound `|a(m)| ≤ H`.
  have hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m := by
    have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
    have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (H : ℝ))
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbd m) (by positivity)
  -- Every bad shift `n < N` has a nonzero coefficient in `(n, n + L]`.
  have hsub : (range N).filter (fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|) ⊆
      (range N).filter (hasLocalSupport a L) := by
    intro n hn
    obtain ⟨hnN, hbad⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnN, ?_⟩
    by_contra hno
    have hgap : ∀ j ∈ Ioo 0 (L + 1), a (n + j) = 0 := by
      intro j hj
      rw [mem_Ioo] at hj
      by_contra hne
      exact hno ⟨j, mem_Icc.mpr ⟨by omega, by omega⟩, hne⟩
    have hsc := orientedTail_of_gap hb hsum (n := n) (g := L + 1) (by omega) hgap
    rw [Nat.add_sub_cancel, show n + (L + 1) - 1 = n + L by omega] at hsc
    have habs : |orientedTail b a n| = |orientedTail b a (n + L)| / (b : ℝ) ^ L := by
      rw [hsc, abs_div, abs_of_pos (pow_pos hb_pos L)]
    have hlt : |orientedTail b a n| < 1 / (b : ℝ) ^ L := by
      rw [habs]
      exact div_lt_div_of_pos_right (htail_lt1 (n + L)) (pow_pos hb_pos L)
    linarith
  exact (card_le_card hsub).trans (nearSupport_card_le_succ a N L)

/-! ### Part 7: Asymptotic transfer and nonnegative sparse non-normality (Theorem 6.7, Corollary 7.1) -/

/-- Under linear coefficient mass `A(X) ≤ C * X` and density-zero support `S(N) / N → 0`,
the bad-tail frequency `B'_L(N) / N` tends to `0` for every word length `L`. -/
theorem badTailFreq_tendsto_zero_of_linear_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ}
    (hC : 0 ≤ C) (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ))
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) / (N : ℝ)) atTop (𝓝 0)) (L : ℕ) :
    Tendsto (fun N : ℕ => (badTailCount b a L N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  -- Pick `k` large enough that `2 * C / b^k < η / 2`.
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    ((tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hb1)) (max 1 (4 * C / η + 1)))
  have hbk_gt : 4 * C / η < (b : ℝ) ^ k := by
    have := (le_max_right (1 : ℝ) (4 * C / η + 1)).trans (hk k le_rfl)
    linarith
  have hbk_pos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have htail_small : 2 * C / (b : ℝ) ^ k < η / 2 := by
    rw [div_lt_iff₀ hbk_pos]
    have hmul := (div_lt_iff₀ hη).mp hbk_gt
    linarith
  -- Pick `M₁` so that `((L + k) + 1) * (1 + S(N - 1)) / N < η / 2` for `N ≥ M₁`.
  set K : ℝ := ((L + k : ℕ) : ℝ) + 1
  have hK_pos : 0 < K := by positivity
  obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp hsparse (η / (4 * K)) (by positivity)
  obtain ⟨M₂, hM₂⟩ := exists_nat_gt (4 * K / η)
  refine ⟨max (max (M₁ + 1) M₂) (L + k + 2), fun N hN => ?_⟩
  have hNM₁ : M₁ + 1 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNM₂ : M₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNLk : L + k + 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hbd := badTail_card_le_linear_mass hb hC hmass N L k
  have hdiv : (badTailCount b a L N : ℝ) / (N : ℝ) ≤
      (((L + k) * (1 + supportCount a (N - 1)) : ℕ) : ℝ) / (N : ℝ) +
        C * ((N + L + k + 2 : ℕ) : ℝ) / ((N : ℝ) * (b : ℝ) ^ k) := by
    have h1 := div_le_div_of_nonneg_right hbd hNr.le
    rw [add_div, div_div, mul_comm ((b : ℝ) ^ k) (N : ℝ)] at h1
    exact h1
  -- Bound the first term using `S(N - 1) ≤ S(N)`.
  have hsp := hM₁ N (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsp
  have hSmono : (supportCount a (N - 1) : ℝ) ≤ (supportCount a N : ℝ) := by
    exact_mod_cast supportCount_mono a (Nat.sub_le N 1)
  have hinv_small : K / (N : ℝ) < η / 4 := by
    rw [div_lt_iff₀ hNr]
    have hM₂_le : (M₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNM₂
    have hlt := (div_lt_iff₀ hη).mp (hM₂.trans_le hM₂_le)
    linarith
  have hfirst : (((L + k) * (1 + supportCount a (N - 1)) : ℕ) : ℝ) / (N : ℝ) < η / 2 := by
    rw [Nat.cast_mul, Nat.cast_add 1, Nat.cast_one, mul_add, mul_one, add_div]
    have hLK_le : ((L + k : ℕ) : ℝ) ≤ K := by dsimp only [K]; linarith
    have ht1 : ((L + k : ℕ) : ℝ) / (N : ℝ) < η / 4 :=
      (div_le_div_of_nonneg_right hLK_le hNr.le).trans_lt hinv_small
    have ht2 : ((L + k : ℕ) : ℝ) * (supportCount a (N - 1) : ℝ) / (N : ℝ) < η / 4 := by
      calc ((L + k : ℕ) : ℝ) * (supportCount a (N - 1) : ℝ) / (N : ℝ)
          ≤ K * (supportCount a N : ℝ) / (N : ℝ) := by gcongr
        _ = K * ((supportCount a N : ℝ) / (N : ℝ)) := by rw [mul_div_assoc]
        _ < K * (η / (4 * K)) := mul_lt_mul_of_pos_left hsp hK_pos
        _ = η / 4 := by field_simp [hK_pos.ne']
    linarith
  -- Bound the second term using `N + L + k + 2 ≤ 2 * N`.
  have hsecond : C * ((N + L + k + 2 : ℕ) : ℝ) / ((N : ℝ) * (b : ℝ) ^ k) < η / 2 := by
    have h2N : ((N + L + k + 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast (show N + L + k + 2 ≤ 2 * N by omega)
    have h1 : C * ((N + L + k + 2 : ℕ) : ℝ) / ((N : ℝ) * (b : ℝ) ^ k) ≤ 2 * C / (b : ℝ) ^ k := by
      rw [div_le_div_iff₀ (by positivity) hbk_pos]
      have := mul_le_mul_of_nonneg_left h2N (mul_nonneg hC hbk_pos.le)
      linarith
    exact h1.trans_lt htail_small
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  linarith

/-- **Theorem 6.7 (asymptotic oriented-tail transfer).**
1. For any fixed `L ≥ 1`, if `badTailCount b a L N / N → 0`, then `wordFreq(0^L) - posTailFreq → 0`,
   `wordFreq((b-1)^L) - negTailFreq → 0`, and `otherWordFreq → 0`.
2. If `badTailCount b a L N / N → 0` for every `L ≥ 1`, then `coeffSeries b a ∈ K_b`. -/
theorem asymptotic_oriented_tail_transfer {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) :
    (∀ L ≥ 1, Tendsto (fun N => (badTailCount b a L N : ℝ) / (N : ℝ)) atTop (𝓝 0) →
      Tendsto (fun N => wordFreq b L (coeffSeries b a) 0 N - (posTailCount b a N : ℝ) / (N : ℝ))
        atTop (𝓝 0) ∧
      Tendsto (fun N => wordFreq b L (coeffSeries b a) (b ^ L - 1) N - (negTailCount b a N : ℝ) / (N : ℝ))
        atTop (𝓝 0) ∧
      Tendsto (otherWordFreq b L (coeffSeries b a)) atTop (𝓝 0)) ∧
    ((∀ L ≥ 1, Tendsto (fun N => (badTailCount b a L N : ℝ) / (N : ℝ)) atTop (𝓝 0)) →
      Tendsto (fun N => radixDiscrepancy b (coeffSeries b a) N) atTop (𝓝 1)) := by
  constructor
  · intro L hL hbad
    refine ⟨?_, ?_, ?_⟩
    · refine squeeze_zero_norm (fun N => ?_) hbad
      rw [Real.norm_eq_abs]
      unfold wordFreq
      rw [← sub_div, abs_div, abs_of_nonneg (a := (N : ℝ)) (Nat.cast_nonneg N)]
      exact div_le_div_of_nonneg_right (wordCount_zeros_sub_posTail_le hb hL hsum N)
        (Nat.cast_nonneg N)
    · refine squeeze_zero_norm (fun N => ?_) hbad
      rw [Real.norm_eq_abs]
      unfold wordFreq
      rw [← sub_div, abs_div, abs_of_nonneg (a := (N : ℝ)) (Nat.cast_nonneg N)]
      exact div_le_div_of_nonneg_right (wordCount_maxDigit_sub_negTail_le hb hL hsum N)
        (Nat.cast_nonneg N)
    · refine squeeze_zero (fun N => by unfold otherWordFreq; positivity) (fun N => ?_) hbad
      unfold otherWordFreq
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast otherWordCount_le_badTailCount (L := L) hb hsum N) (Nat.cast_nonneg N)
  · intro hall
    rw [Metric.tendsto_atTop]
    intro η hη
    have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
    obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp
      ((tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hb1)) (max 1 (4 / η + 1)))
    have hL1 : 1 ≤ max L 1 := le_max_right L 1
    set L' : ℕ := max L 1
    have hbL'_gt : 4 / η < (b : ℝ) ^ L' := by
      have h1 : 4 / η < (b : ℝ) ^ L := by
        have := (le_max_right (1 : ℝ) (4 / η + 1)).trans (hL L le_rfl)
        linarith
      exact h1.trans_le (pow_le_pow_right₀ hb1.le (le_max_left L 1))
    have h2div : 2 / (b : ℝ) ^ L' < η / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have hmul := (div_lt_iff₀ hη).mp hbL'_gt
      linarith
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (hall L' hL1) (η / 2) (by positivity)
    refine ⟨M, fun N hN => ?_⟩
    have hfar_le : farCount b (coeffSeries b a) (1 / (b : ℝ) ^ L') N ≤ badTailCount b a L' N := by
      classical
      unfold farCount badTailCount
      refine card_le_card (fun n hn => ?_)
      obtain ⟨hnN, hfar⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hnN, ?_⟩
      by_contra hlt
      push Not at hlt
      apply hfar
      refine ⟨∑ m ∈ range (n + 1), a m * (b : ℤ) ^ (n - m), ?_⟩
      rw [pow_mul_coeffSeries_eq_int_add_tail hb hsum n, add_sub_cancel_left]
      exact hlt.le
    have hdef := discrepancy_deficit_le b (coeffSeries b a) (ε := 1 / (b : ℝ) ^ L') (by positivity) N
    have hfar_r : (farCount b (coeffSeries b a) (1 / (b : ℝ) ^ L') N : ℝ) / (N : ℝ) ≤
        (badTailCount b a L' N : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hfar_le) (Nat.cast_nonneg N)
    have hbad_small := hM N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hbad_small
    have hD_le1 : radixDiscrepancy b (coeffSeries b a) N ≤ 1 := (radixDiscrepancy_mem b _ N).2
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith [show 2 * (1 / (b : ℝ) ^ L') = 2 / (b : ℝ) ^ L' by ring]

/-- **Corollary 7.1 (nonnegative sparse series read almost exclusively `0^L`).**
For every base `b ≥ 2` (including `b = 2`), every nonnegative integer sequence `a : ℕ → ℤ`
(`∀ m, 0 ≤ a m`) with linear mass `absMass a X ≤ C * X` and density-zero support `S(N) / N → 0`,
and every word length `L : ℕ`, the frequency of `0^L` in `coeffSeries b a` tends to `1`. -/
theorem nonneg_sparse_zeros_tendsto_one {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hnonneg : ∀ m : ℕ, 0 ≤ a m) {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ))
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) / (N : ℝ)) atTop (𝓝 0)) (L : ℕ) :
    Tendsto (fun N : ℕ => wordFreq b L (coeffSeries b a) 0 N) atTop (𝓝 1) := by
  have hsum := summable_abs_of_linear_mass hb hmass
  have htail_nn : ∀ n : ℕ, 0 ≤ orientedTail b a n := fun n =>
    tsum_nonneg (fun j => div_nonneg (by exact_mod_cast hnonneg (n + 1 + j)) (by positivity))
  have hgap_le : ∀ N ≥ 1,
      1 - wordFreq b L (coeffSeries b a) 0 N ≤ (badTailCount b a L N : ℝ) / (N : ℝ) := by
    intro N hN
    classical
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hsub : (range N).filter (fun n => ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ ≠ 0) ⊆
        (range N).filter (fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|) := by
      intro n hn
      obtain ⟨hnN, hne0⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hnN, ?_⟩
      by_contra hlt
      push Not at hlt
      rw [abs_of_nonneg (htail_nn n)] at hlt
      apply hne0
      rw [shift_coeffSeries_eq_fract_tail hb hsum n]
      exact floor_fract_eq_zero hb (htail_nn n) hlt
    have hcompl : ((range N).filter fun n =>
        ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ ≠ 0).card =
        N - wordCount b L (coeffSeries b a) 0 N := by
      have htot := Finset.card_filter_add_card_filter_not (s := range N)
        (fun n => ⌊(b : ℝ) ^ L * shift b (coeffSeries b a) n⌋₊ = 0)
      rw [card_range] at htot
      simp only [ne_eq]
      unfold wordCount
      omega
    have hle : N - wordCount b L (coeffSeries b a) 0 N ≤ badTailCount b a L N := by
      rw [← hcompl]; exact card_le_card hsub
    have hle_r : (N : ℝ) - (wordCount b L (coeffSeries b a) 0 N : ℝ) ≤ (badTailCount b a L N : ℝ) := by
      rw [← Nat.cast_sub (wordCount_bounds b L (coeffSeries b a) 0 N)]
      exact_mod_cast hle
    have hdiv := div_le_div_of_nonneg_right hle_r hNr.le
    unfold wordFreq
    rw [sub_div, div_self hNr.ne'] at hdiv
    exact hdiv
  have hbad_to0 := badTailFreq_tendsto_zero_of_linear_mass hb hC hmass hsparse L
  have hgap_to0 : Tendsto (fun N : ℕ => 1 - wordFreq b L (coeffSeries b a) 0 N) atTop (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall fun N => by linarith [(wordFreq_bounds b L (coeffSeries b a) 0 N).2])
      (eventually_atTop.mpr ⟨1, hgap_le⟩) hbad_to0
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hgap_to0

/-- **Corollary 7.1 (non-simple-normality in EVERY base `b ≥ 2`, including base `2`).**
Any nonnegative integer sequence with linear mass and density-zero support produces a number
that is NOT simply normal in base `b` (including `b = 2`). -/
theorem not_simply_normal_of_nonneg_sparse {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hnonneg : ∀ m : ℕ, 0 ≤ a m) {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ))
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) / (N : ℝ)) atTop (𝓝 0)) :
    ¬ (∀ d < b, Tendsto (digitFreq b (coeffSeries b a) d) atTop (𝓝 (1 / (b : ℝ)))) := by
  intro hsn
  have h1 : Tendsto (digitFreq b (coeffSeries b a) 0) atTop (𝓝 1) :=
    nonneg_sparse_zeros_tendsto_one hb hnonneg hC hmass hsparse 1
  have h2 := hsn 0 (by omega)
  have hEq : (1 : ℝ) = 1 / (b : ℝ) := tendsto_nhds_unique h1 h2
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hlt : 1 / (b : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-! ### Part 8: Beatty odd-weight discrepancy identity (Lemma 8.0) -/

/-- **Lemma 8.0 (odd-weighted Beatty sum).** For every real `α` and `K : ℕ`,
`|∑_{k=1}^K (⌊kα⌋ - ⌊(k-1)α⌋)(2k - 1) - α K^2| ≤ 2K`. -/
theorem beatty_odd_weight (α : ℝ) (K : ℕ) :
    |∑ k ∈ Icc 1 K, ((⌊(k : ℝ) * α⌋ - ⌊((k : ℝ) - 1) * α⌋ : ℤ) : ℝ) * (2 * k - 1) -
      α * (K : ℝ) ^ 2| ≤ 2 * K := by
  let B : ℕ → ℝ := fun k => (⌊(k : ℝ) * α⌋ : ℝ)
  have hB0 : B 0 = 0 := by simp [B]
  -- Step 1: Abel summation identity over `Icc 1 K`.
  have habel : ∀ m : ℕ,
      ∑ k ∈ Icc 1 m, ((⌊(k : ℝ) * α⌋ - ⌊((k : ℝ) - 1) * α⌋ : ℤ) : ℝ) * (2 * (k : ℝ) - 1) =
        (2 * (m : ℝ) - 1) * B m - 2 * ∑ k ∈ range m, B k := by
    intro m
    induction m with
    | zero => simp [hB0]
    | succ m ih =>
      have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have hnotmem : m + 1 ∉ Icc 1 m := by simp
      rw [hIcc, Finset.sum_insert hnotmem, ih, Finset.sum_range_succ]
      have hlast : (((⌊((m + 1 : ℕ) : ℝ) * α⌋ - ⌊(((m + 1 : ℕ) : ℝ) - 1) * α⌋ : ℤ) : ℝ)) =
          B (m + 1) - B m := by
        push_cast [B]
        ring_nf
      rw [hlast]
      push_cast
      ring
  -- Step 2: Elementary identity `2 * ∑_{k < K} k = K * (K - 1)`.
  have hsum_id : ∀ m : ℕ, 2 * ∑ k ∈ range m, (k : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring
  -- Step 3: Rewrite `B k = k * α - Int.fract (k * α)` to express the error via fractional parts.
  have hB_eq : ∀ k : ℕ, B k = (k : ℝ) * α - Int.fract ((k : ℝ) * α) := by
    intro k
    dsimp only [B]
    have := Int.fract_add_floor ((k : ℝ) * α)
    linarith
  have herr :
      ∑ k ∈ Icc 1 K, ((⌊(k : ℝ) * α⌋ - ⌊((k : ℝ) - 1) * α⌋ : ℤ) : ℝ) * (2 * (k : ℝ) - 1) -
        α * (K : ℝ) ^ 2 =
      2 * (∑ k ∈ range K, Int.fract ((k : ℝ) * α)) -
        (2 * (K : ℝ) - 1) * Int.fract ((K : ℝ) * α) := by
    rw [habel K, hB_eq K]
    have hsum_B : ∑ k ∈ range K, B k =
        (∑ k ∈ range K, (k : ℝ)) * α - ∑ k ∈ range K, Int.fract ((k : ℝ) * α) := by
      simp_rw [hB_eq, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hsum_B]
    have hid := hsum_id K
    linear_combination -α * hid
  rw [herr]
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have h1_lo : 0 ≤ 2 * ∑ k ∈ range K, Int.fract ((k : ℝ) * α) :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => Int.fract_nonneg _))
    have h1_hi : 2 * ∑ k ∈ range K, Int.fract ((k : ℝ) * α) ≤ 2 * (K : ℝ) := by
      have hsum_le : ∑ k ∈ range K, Int.fract ((k : ℝ) * α) ≤ (K : ℝ) := by
        calc ∑ k ∈ range K, Int.fract ((k : ℝ) * α)
            ≤ ∑ _k ∈ range K, (1 : ℝ) := Finset.sum_le_sum (fun k _ => (Int.fract_lt_one _).le)
          _ = (K : ℝ) := by simp
      linarith
    have h2_lo : 0 ≤ (2 * (K : ℝ) - 1) * Int.fract ((K : ℝ) * α) :=
      mul_nonneg (by linarith) (Int.fract_nonneg _)
    have h2_hi : (2 * (K : ℝ) - 1) * Int.fract ((K : ℝ) * α) ≤ 2 * (K : ℝ) := by
      have hle : (2 * (K : ℝ) - 1) * Int.fract ((K : ℝ) * α) ≤ (2 * (K : ℝ) - 1) * 1 :=
        mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le (by linarith)
      linarith
    rw [abs_le]
    constructor <;> linarith

end NormalityChecker.SimpleNormalityKernel
