module

public import NormalityChecker.CoefficientTransfer

/-! # Euler's pentagonal series and Jacobi's cube series (Tracks A1 and A2)

Kernel-checked discrepancy-maximality and universal discrepancy-preservation theorems for:

1. **Euler's pentagonal series (`eulerPentagonalSum b`):**
   `E_b = 1 + ∑_{k ≥ 1} (-1)^k (b^(-k(3k-1)/2) + b^(-k(3k+1)/2))` (equal to
   `∏_{k ≥ 1} (1 - b^(-k))` by Euler's pentagonal number theorem).
   - `pentagonal_supportCount_le`: `supportCount pentCoeff M ≤ 2 * Nat.sqrt (2 * M) + 2`.
   - `pentagonal_absMass_le`: `absMass pentCoeff M ≤ M`.
   - `eulerPentagonal_discrepancy_tendsto_one`: `D_N(E_b; b) → 1` for every radix `b ≥ 2`.
   - `eulerPentagonal_preserves_discrepancy`: `D_N(x + E_b; b) - D_N(x; b) → 0` for every
     radix `b ≥ 2` and every real `x`.
   - `eulerPentagonal_finite_gap_upper`: explicit finite upper bound on `1 - D_N(E_b; b)` and
     `|D_N(x + E_b; b) - D_N(x; b)|` for every `N ≥ 1`, `L`, `ε > 0`.

2. **Jacobi's cube series (`eulerCubeSum b`):**
   `E_b³ = ∑_{k ≥ 0} (-1)^k (2k + 1) b^(-k(k+1)/2)` (by Jacobi's identity).
   - `jacobiCube_supportCount_le`: `supportCount jacobiCubeCoeff M ≤ Nat.sqrt (2 * M) + 1`.
   - `jacobiCube_absMass_le`: `absMass jacobiCubeCoeff M ≤ 4 * M`.
   - `eulerCube_discrepancy_tendsto_one`: `D_N(E_b³; b) → 1` for every radix `b ≥ 2`.
   - `eulerCube_preserves_discrepancy`: `D_N(x + E_b³; b) - D_N(x; b) → 0` for every
     radix `b ≥ 2` and every real `x`.

3. **Square-root support Cauchy convolution mass bound (`cauchy_absMass_le`):**
   If two bounded sequences have support counts `O(√M)`, their Cauchy convolution has linear
   aggregate absolute mass `absMass ≤ C · M`, feeding directly into `CoefficientTransfer`
   for `E_b²` and products of unary quadratic series (Tracks A2 and B5).
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.EulerPentagonal

open CoefficientTransfer SharpTranslation

/-! ### Part 1: Euler's pentagonal numbers and coefficients -/

/-- Lower generalized pentagonal number `k(3k - 1)/2`. -/
def pentMinus (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/-- Upper generalized pentagonal number `k(3k + 1)/2`. -/
def pentPlus (k : ℕ) : ℕ := k * (3 * k + 1) / 2

theorem two_mul_pentMinus (k : ℕ) : 2 * pentMinus k = k * (3 * k - 1) := by
  unfold pentMinus
  apply Nat.mul_div_cancel'
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨m * (3 * (m + m) - 1), by ring⟩
  · have h3 : 3 * (2 * m + 1) - 1 = 2 * (3 * m + 1) := by omega
    rw [h3]
    exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩

theorem two_mul_pentPlus (k : ℕ) : 2 * pentPlus k = k * (3 * k + 1) := by
  unfold pentPlus
  apply Nat.mul_div_cancel'
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨m * (3 * (m + m) + 1), by ring⟩
  · have h3 : 3 * (2 * m + 1) + 1 = 2 * (3 * m + 2) := by omega
    rw [h3]
    exact ⟨(2 * m + 1) * (3 * m + 2), by ring⟩

theorem pentMinus_lt_pentPlus {k : ℕ} (hk : 1 ≤ k) : pentMinus k < pentPlus k := by
  have h1 := two_mul_pentMinus k
  have h2 := two_mul_pentPlus k
  have h3 : k * (3 * k - 1) < k * (3 * k + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  omega

theorem pentPlus_lt_pentMinus_succ {k : ℕ} (hk : 1 ≤ k) : pentPlus k < pentMinus (k + 1) := by
  have h1 := two_mul_pentPlus k
  have h2 := two_mul_pentMinus (k + 1)
  have h3 : k * (3 * k + 1) < (k + 1) * (3 * (k + 1) - 1) := by
    have : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
    rw [this]; nlinarith
  omega

theorem pentMinus_strictMono : StrictMono pentMinus := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  have h1 := two_mul_pentMinus k
  have h2 := two_mul_pentMinus (k + 1)
  have h3 : k * (3 * k - 1) < (k + 1) * (3 * (k + 1) - 1) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
      have hle : 3 * k - 1 ≤ 3 * k := Nat.sub_le _ _
      rw [this]; nlinarith
  omega

theorem pentPlus_strictMono : StrictMono pentPlus := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  have h1 := two_mul_pentPlus k
  have h2 := two_mul_pentPlus (k + 1)
  have h3 : k * (3 * k + 1) < (k + 1) * (3 * (k + 1) + 1) := by nlinarith
  omega

theorem pentMinus_ne_pentPlus {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    pentMinus k ≠ pentPlus j := by
  intro heq
  rcases lt_trichotomy k j with hlt | rfl | hgt
  · have h1 := pentMinus_lt_pentPlus hk
    have h2 := pentPlus_strictMono hlt
    omega
  · exact (pentMinus_lt_pentPlus hk).ne heq
  · have h1 := pentPlus_lt_pentMinus_succ hj
    have h2 : pentMinus (j + 1) ≤ pentMinus k := pentMinus_strictMono.monotone (by omega)
    omega

/-- Signed pentagonal coefficient sequence `a(m)`:
`1` at `m = 0`, `(-1)^k` at `m = pentMinus k` or `m = pentPlus k` (`k ≥ 1`), and `0` elsewhere. -/
noncomputable def pentCoeff (m : ℕ) : ℤ :=
  by classical
  exact if m = 0 then 1
    else if h : ∃ k ≥ 1, pentMinus k = m ∨ pentPlus k = m then (-1 : ℤ) ^ h.choose
    else 0

/-- The pentagonal generating series `E_b = 1 + ∑_{k ≥ 1} (-1)^k (b^(-k(3k-1)/2) + b^(-k(3k+1)/2))`. -/
noncomputable def eulerPentagonalSum (b : ℕ) : ℝ := coeffSeries b pentCoeff

theorem abs_pentCoeff_le_one (m : ℕ) : |(pentCoeff m : ℝ)| ≤ 1 := by
  classical
  unfold pentCoeff
  split_ifs with h0 h1
  · norm_num
  · push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · norm_num

theorem pentCoeff_absMass_le (M : ℕ) : absMass pentCoeff M ≤ (M : ℝ) := by
  unfold absMass
  calc ∑ m ∈ Icc 1 M, |(pentCoeff m : ℝ)|
      ≤ ∑ _m ∈ Icc 1 M, (1 : ℝ) := Finset.sum_le_sum (fun m _ => abs_pentCoeff_le_one m)
    _ = ((Icc 1 M).card : ℝ) := by simp
    _ = (M : ℝ) := by rw [Nat.card_Icc]; simp

theorem pentagonal_index_bound {k M : ℕ} (hk : 1 ≤ k) (hm : pentMinus k ≤ M) :
    k ≤ Nat.sqrt (2 * M) + 1 := by
  have h2 := two_mul_pentMinus k
  have hsq : (k - 1) * (k - 1) ≤ 2 * M := by
    have : (k - 1) * (k - 1) ≤ k * (3 * k - 1) := by
      rcases k with _ | k'
      · omega
      · simp only [Nat.add_sub_cancel]
        have : 3 * (k' + 1) - 1 = 3 * k' + 2 := by omega
        rw [this]; nlinarith
    omega
  have hle : k - 1 ≤ Nat.sqrt (2 * M) := Nat.le_sqrt.mpr hsq
  omega

/-- Support count of the pentagonal series through `M`: at most `2 * (Nat.sqrt (2 * M) + 1)`. -/
theorem pentagonal_supportCount_le (M : ℕ) :
    supportCount pentCoeff M ≤ 2 * (Nat.sqrt (2 * M) + 1) := by
  classical
  unfold supportCount
  let K := Nat.sqrt (2 * M) + 1
  let S₁ := (Icc 1 K).image pentMinus
  let S₂ := (Icc 1 K).image pentPlus
  have hsub : (Icc 1 M).filter (fun m => pentCoeff m ≠ 0) ⊆ S₁ ∪ S₂ := by
    intro m hm
    obtain ⟨hmI, hne⟩ := mem_filter.mp hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hmI).1
    have hmM : m ≤ M := (mem_Icc.mp hmI).2
    have hm0 : m ≠ 0 := by omega
    have hex : ∃ k ≥ 1, pentMinus k = m ∨ pentPlus k = m := by
      by_contra hno
      apply hne
      unfold pentCoeff
      simp [hm0, hno]
    obtain ⟨k, hk1, hkm | hkp⟩ := hex
    · rw [mem_union]; left
      refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk1, ?_⟩, hkm⟩
      exact pentagonal_index_bound hk1 (by omega)
    · rw [mem_union]; right
      refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk1, ?_⟩, hkp⟩
      have hlt := pentMinus_lt_pentPlus hk1
      exact pentagonal_index_bound hk1 (by omega)
  calc ((Icc 1 M).filter (fun m => pentCoeff m ≠ 0)).card
      ≤ (S₁ ∪ S₂).card := card_le_card hsub
    _ ≤ S₁.card + S₂.card := card_union_le S₁ S₂
    _ ≤ (Icc 1 K).card + (Icc 1 K).card := Nat.add_le_add card_image_le card_image_le
    _ = 2 * K := by rw [Nat.card_Icc]; omega

/-- Elementary helper: `(Nat.sqrt (2 * N) + 1) / N → 0`. -/
private lemma tendsto_sqrt_div_self :
    Tendsto (fun N : ℕ => ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (4 / ε)
  refine ⟨max 1 (K * K + 1), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNK : K * K + 1 ≤ N := (le_max_right _ _).trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hKpos : (0 : ℝ) < K := lt_trans (by positivity) hK
  have hsqrt_le : (Nat.sqrt (2 * N) : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) := by
    have hsq : Nat.sqrt (2 * N) * Nat.sqrt (2 * N) ≤ 2 * N := Nat.sqrt_le (2 * N)
    have hsq_r : ((Nat.sqrt (2 * N) : ℝ)) ^ 2 ≤ 2 * (N : ℝ) := by
      rw [sq]; exact_mod_cast hsq
    exact Real.le_sqrt_of_sq_le hsq_r
  have hN_gt : (K : ℝ) ^ 2 < (N : ℝ) := by
    have : K * K < N := by omega
    rw [sq]; exact_mod_cast this
  have hK_lt_sqrt : (K : ℝ) < Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_sq hKpos.le]
    exact Real.sqrt_lt_sqrt (by positivity) hN_gt
  have h1_le_sqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
  have hsqrt2 : Real.sqrt (2 * (N : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hnum : ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
    push_cast; linarith
  have hdiv : ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 3 / Real.sqrt (N : ℝ) := by
    rw [div_le_div_iff₀ hNr (Real.sqrt_pos.mpr hNr)]
    have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt hNr.le
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have h3 : 3 / Real.sqrt (N : ℝ) < ε := by
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr hNr)]
    have h4 : 4 < (K : ℝ) * ε := (div_lt_iff₀ hε).mp hK
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  linarith

/-- **Finite discrepancy-gap upper bound for Euler's pentagonal series (Track A1).** -/
theorem eulerPentagonal_finite_gap_upper {b : ℕ} (hb : 2 ≤ b) {N : ℕ} (hN : 0 < N)
    (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    1 - radixDiscrepancy b (eulerPentagonalSum b) N ≤
      2 * ε + ((L * (2 * (Nat.sqrt (2 * (N + L)) + 1)) : ℕ) : ℝ) / (N : ℝ) +
        ((N + L + 2 : ℕ) : ℝ) / ((N : ℝ) * ε * (b : ℝ) ^ L) := by
  have htr := finite_sparse_mass_transfer hb (a := pentCoeff) (C := 1) zero_le_one
    (fun X => by simpa using pentCoeff_absMass_le X) hN L hε
  have hsup : ((L * supportCount pentCoeff (N + L) : ℕ) : ℝ) / (N : ℝ) ≤
      ((L * (2 * (Nat.sqrt (2 * (N + L)) + 1)) : ℕ) : ℝ) / (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact_mod_cast Nat.mul_le_mul_left L (pentagonal_supportCount_le (N + L))
  unfold eulerPentagonalSum
  simp only [one_mul] at htr
  linarith

/-- **Maximal discrepancy of Euler's infinite product (Track A1).**
For every integer radix `b ≥ 2`, `D_N(E_b; b) → 1`. -/
theorem eulerPentagonal_discrepancy_tendsto_one {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (eulerPentagonalSum b) N) atTop (𝓝 1) := by
  refine linear_mass_sparse_tendsto_one hb (C := 1) zero_le_one
    (fun X => by simpa using pentCoeff_absMass_le X) ?_
  refine squeeze_zero (fun N => by positivity) (fun N => ?_)
    (by simpa using tendsto_sqrt_div_self.const_mul (2 : ℝ))
  have h1 := pentagonal_supportCount_le N
  have h1r : (supportCount pentCoeff N : ℝ) ≤ 2 * ((Nat.sqrt (2 * N) : ℝ) + 1) := by
    exact_mod_cast h1
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right h1r (Nat.cast_nonneg N)

/-- **Universal discrepancy preservation by Euler's infinite product (Track A1).**
For every integer radix `b ≥ 2` and every real `x`, `D_N(x + E_b; b) - D_N(x; b) → 0`. -/
theorem eulerPentagonal_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) (x : ℝ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (x + eulerPentagonalSum b) N - radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  refine linear_mass_sparse_preserves_discrepancy hb (C := 1) zero_le_one
    (fun X => by simpa using pentCoeff_absMass_le X) ?_ x
  refine squeeze_zero (fun N => by positivity) (fun N => ?_)
    (by simpa using tendsto_sqrt_div_self.const_mul (2 : ℝ))
  have h1 := pentagonal_supportCount_le N
  have h1r : (supportCount pentCoeff N : ℝ) ≤ 2 * ((Nat.sqrt (2 * N) : ℝ) + 1) := by
    exact_mod_cast h1
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right h1r (Nat.cast_nonneg N)

/-! ### Part 2: Jacobi's cube identity `E_b³ = ∑_{k ≥ 0} (-1)^k (2k+1) b^(-k(k+1)/2)` -/

/-- Triangular number `k(k + 1)/2`. -/
def triNum (k : ℕ) : ℕ := k * (k + 1) / 2

theorem two_mul_triNum (k : ℕ) : 2 * triNum k = k * (k + 1) := by
  unfold triNum
  apply Nat.mul_div_cancel'
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨m * (m + m + 1), by ring⟩
  · exact ⟨(2 * m + 1) * (m + 1), by ring⟩

theorem triNum_strictMono : StrictMono triNum := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  have h1 := two_mul_triNum k
  have h2 := two_mul_triNum (k + 1)
  have h3 : k * (k + 1) < (k + 1) * (k + 1 + 1) := by nlinarith
  omega

/-- Signed Jacobi cube coefficient sequence: `(-1)^k (2k + 1)` at `m = triNum k`, `0` elsewhere. -/
noncomputable def jacobiCubeCoeff (m : ℕ) : ℤ :=
  by classical
  exact if h : ∃ k : ℕ, triNum k = m then (-1 : ℤ) ^ h.choose * (2 * (h.choose : ℤ) + 1) else 0

/-- Jacobi's cube series `E_b³ = ∑_{k ≥ 0} (-1)^k (2k + 1) b^(-k(k+1)/2)`. -/
noncomputable def eulerCubeSum (b : ℕ) : ℝ := coeffSeries b jacobiCubeCoeff

theorem triNum_index_bound {k M : ℕ} (hm : triNum k ≤ M) : k ≤ Nat.sqrt (2 * M) := by
  have h2 := two_mul_triNum k
  exact Nat.le_sqrt.mpr (by nlinarith)

theorem abs_jacobiCubeCoeff_triNum (k : ℕ) :
    |(jacobiCubeCoeff (triNum k) : ℝ)| = 2 * (k : ℝ) + 1 := by
  classical
  have hex : ∃ j : ℕ, triNum j = triNum k := ⟨k, rfl⟩
  have hch : hex.choose = k := triNum_strictMono.injective hex.choose_spec
  unfold jacobiCubeCoeff
  simp only [dite_eq_left, hex, hch]
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (by positivity)]

/-- Support count of Jacobi's cube series: `S(M) ≤ Nat.sqrt (2 * M)`. -/
theorem jacobiCube_supportCount_le (M : ℕ) :
    supportCount jacobiCubeCoeff M ≤ Nat.sqrt (2 * M) := by
  classical
  unfold supportCount
  let K := Nat.sqrt (2 * M)
  have hsub : (Icc 1 M).filter (fun m => jacobiCubeCoeff m ≠ 0) ⊆ (Icc 1 K).image triNum := by
    intro m hm
    obtain ⟨hmI, hne⟩ := mem_filter.mp hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hmI).1
    have hmM : m ≤ M := (mem_Icc.mp hmI).2
    have hex : ∃ k : ℕ, triNum k = m := by
      by_contra hno
      apply hne
      unfold jacobiCubeCoeff
      simp [hno]
    obtain ⟨k, rfl⟩ := hex
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [triNum] at hm1
      · exact hk
    exact mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk1, triNum_index_bound hmM⟩, rfl⟩
  calc ((Icc 1 M).filter (fun m => jacobiCubeCoeff m ≠ 0)).card
      ≤ ((Icc 1 K).image triNum).card := card_le_card hsub
    _ ≤ (Icc 1 K).card := card_image_le
    _ = K := by rw [Nat.card_Icc]; omega

private lemma sum_odd_Icc (K : ℕ) :
    ∑ k ∈ Icc 1 K, (2 * (k : ℝ) + 1) = ((K + 1 : ℕ) : ℝ) ^ 2 - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hsplit : Icc 1 (K + 1) = insert (K + 1) (Icc 1 K) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp), ih]
    push_cast; ring

/-- Aggregate absolute coefficient mass of Jacobi's cube series is linear: `A(M) ≤ 4 · M`. -/
theorem jacobiCube_absMass_le (M : ℕ) : absMass jacobiCubeCoeff M ≤ 4 * (M : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [absMass]
  let K := Nat.sqrt (2 * M)
  have hKsq : K * K ≤ 2 * M := Nat.sqrt_le (2 * M)
  have hsub : (Icc 1 M).filter (fun m => jacobiCubeCoeff m ≠ 0) ⊆ (Icc 1 K).image triNum := by
    intro m hm
    obtain ⟨hmI, hne⟩ := mem_filter.mp hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hmI).1
    have hmM : m ≤ M := (mem_Icc.mp hmI).2
    have hex : ∃ k : ℕ, triNum k = m := by
      by_contra hno
      apply hne
      unfold jacobiCubeCoeff
      simp [hno]
    obtain ⟨k, rfl⟩ := hex
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [triNum] at hm1
      · exact hk
    exact mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk1, triNum_index_bound hmM⟩, rfl⟩
  have hfilt : absMass jacobiCubeCoeff M =
      ∑ m ∈ (Icc 1 M).filter (fun m => jacobiCubeCoeff m ≠ 0), |(jacobiCubeCoeff m : ℝ)| := by
    unfold absMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    split_ifs with h
    · rfl
    · push Not at h; simp [h]
  rw [hfilt]
  calc ∑ m ∈ (Icc 1 M).filter (fun m => jacobiCubeCoeff m ≠ 0), |(jacobiCubeCoeff m : ℝ)|
      ≤ ∑ m ∈ (Icc 1 K).image triNum, |(jacobiCubeCoeff m : ℝ)| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ = ∑ k ∈ Icc 1 K, |(jacobiCubeCoeff (triNum k) : ℝ)| :=
        Finset.sum_image (fun x _ y _ h => triNum_strictMono.injective h)
    _ = ∑ k ∈ Icc 1 K, (2 * (k : ℝ) + 1) :=
        Finset.sum_congr rfl (fun k _ => abs_jacobiCubeCoeff_triNum k)
    _ = ((K + 1 : ℕ) : ℝ) ^ 2 - 1 := sum_odd_Icc K
    _ ≤ 4 * (M : ℝ) := by
        have hnat : (K + 1) ^ 2 - 1 ≤ 4 * M := by
          have h1 : (K + 1) ^ 2 - 1 = K * K + 2 * K := by
            have : (K + 1) ^ 2 = K * K + 2 * K + 1 := by ring
            omega
          rw [h1]
          by_cases hK1 : K ≤ 1
          · omega
          · nlinarith
        have hpos : 1 ≤ (K + 1) ^ 2 := by nlinarith
        have hcast : (((K + 1) ^ 2 - 1 : ℕ) : ℝ) ≤ 4 * (M : ℝ) := by exact_mod_cast hnat
        rw [Nat.cast_sub hpos] at hcast
        simpa using hcast

/-- **Maximal discrepancy of Jacobi's cube series `E_b³` (Track A2).**
For every integer radix `b ≥ 2`, `D_N(E_b³; b) → 1`. -/
theorem eulerCube_discrepancy_tendsto_one {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (eulerCubeSum b) N) atTop (𝓝 1) := by
  refine linear_mass_sparse_tendsto_one hb (C := 4) (by norm_num) jacobiCube_absMass_le ?_
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) tendsto_sqrt_div_self
  have h1 : (supportCount jacobiCubeCoeff N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) := by
    have := jacobiCube_supportCount_le N
    exact_mod_cast (this.trans (Nat.le_succ _))
  exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg N)

/-- **Universal discrepancy preservation by Jacobi's cube series `E_b³` (Track A2).**
For every integer radix `b ≥ 2` and every real `x`, `D_N(x + E_b³; b) - D_N(x; b) → 0`. -/
theorem eulerCube_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) (x : ℝ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (x + eulerCubeSum b) N - radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  refine linear_mass_sparse_preserves_discrepancy hb (C := 4) (by norm_num) jacobiCube_absMass_le ?_ x
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) tendsto_sqrt_div_self
  have h1 : (supportCount jacobiCubeCoeff N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) := by
    have := jacobiCube_supportCount_le N
    exact_mod_cast (this.trans (Nat.le_succ _))
  exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg N)

/-! ### Part 3: Cauchy convolution mass bound (Tracks A2 and B5) -/

/-- Discrete Cauchy convolution `(a * c)(m) = ∑_{i ≤ m} a(i) c(m - i)`. -/
def cauchyConv (a c : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ i ∈ range (m + 1), a i * c (m - i)

/-- **Cauchy convolution aggregate mass bound (Tracks A2 and B5).**
For any integer sequences `a, c`,
`absMass (cauchyConv a c) M ≤ (|a 0| + absMass a M) * (|c 0| + absMass c M)`.
In particular, if `a` and `c` have `O(√M)` aggregate absolute mass (for example `E_b` or
unary theta series), their Cauchy convolution has linear mass `O(M)`. -/
theorem cauchyConv_absMass_le (a c : ℕ → ℤ) (M : ℕ) :
    absMass (cauchyConv a c) M ≤
      (|(a 0 : ℝ)| + absMass a M) * (|(c 0 : ℝ)| + absMass c M) := by
  have hsum0 : ∀ f : ℕ → ℤ, |(f 0 : ℝ)| + absMass f M = ∑ i ∈ range (M + 1), |(f i : ℝ)| := by
    intro f
    unfold absMass
    rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos M)]
    have hI : Ico 1 (M + 1) = Icc 1 M := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    simp [hI]
  rw [hsum0 a, hsum0 c, Finset.sum_mul_sum]
  unfold absMass cauchyConv
  have htri : ∑ m ∈ Icc 1 M, |((∑ i ∈ range (m + 1), a i * c (m - i) : ℤ) : ℝ)| ≤
      ∑ m ∈ Icc 1 M, ∑ i ∈ range (m + 1), |(a i : ℝ)| * |(c (m - i) : ℝ)| := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul]
  refine htri.trans ?_
  let S := (Icc 1 M).sigma (fun m => range (m + 1))
  have hsig : ∑ m ∈ Icc 1 M, ∑ i ∈ range (m + 1), |(a i : ℝ)| * |(c (m - i) : ℝ)| =
      ∑ p ∈ S, |(a p.2 : ℝ)| * |(c (p.1 - p.2) : ℝ)| :=
    Finset.sum_sigma' (Icc 1 M) (fun m => range (m + 1))
      (fun m i => |(a i : ℝ)| * |(c (m - i) : ℝ)|)
  rw [hsig]
  have hinj : ∑ p ∈ S, |(a p.2 : ℝ)| * |(c (p.1 - p.2) : ℝ)| =
      ∑ q ∈ S.image (fun p => (p.2, p.1 - p.2)), |(a q.1 : ℝ)| * |(c q.2 : ℝ)| := by
    symm
    refine Finset.sum_image (fun p₁ hp₁ p₂ hp₂ heq => ?_)
    have h1 : p₁.2 = p₂.2 := congrArg Prod.fst heq
    have h2 : p₁.1 - p₁.2 = p₂.1 - p₂.2 := congrArg Prod.snd heq
    have hb₁ : p₁.2 ≤ p₁.1 := by
      have := (mem_sigma.mp hp₁).2; rw [mem_range] at this; omega
    have hb₂ : p₂.2 ≤ p₂.1 := by
      have := (mem_sigma.mp hp₂).2; rw [mem_range] at this; omega
    exact Sigma.ext (by omega) (by rw [h1])
  rw [hinj, ← Finset.sum_product']
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  obtain ⟨hp1, hp2⟩ := mem_sigma.mp hp
  rw [mem_Icc] at hp1
  rw [mem_range] at hp2
  rw [mem_product, mem_range, mem_range]
  omega

end NormalityChecker.EulerPentagonal
