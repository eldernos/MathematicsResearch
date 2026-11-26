module

public import NormalityChecker.ClassicalBarriers
public import NormalityChecker.DiscrepancyGeometry
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Tactic

/-! # Radix-power kernel tower, zero-orbit invariance, cylinder interiority, and reciprocal periods

Kernel-checked theorems supporting Phase 22 Track G1 Correction A, Track B4, Track A4, and
Track D1–D2:

1. **Strict radix-power kernel inclusion `K_b ⊊ K_{b^k}` (Track G1 Correction A, Track B4):**
   - `inv_pow_sub_one_radixDiscrepancy_pow`: for `b ≥ 2`, `k ≥ 1`, and `N ≥ 1`,
     `D_N(1 / (b^k - 1); b^k) = 1`, hence `1 / (b^k - 1) ∈ K_{b^k}`
     (`inv_pow_sub_one_mem_pow_kernel`).
   - `inv_pow_sub_one_radixDiscrepancy_le`: for `b ≥ 2`, `k ≥ 2`, and `M ≥ 1`,
     `D_{kM}(1 / (b^k - 1); b) ≤ 1 - δ` for an explicit `δ > 0` independent of `M`,
     so `1 / (b^k - 1) ∉ K_b` (`inv_pow_sub_one_not_mem_kernel`) and `K_b ⊊ K_{b^k}`
     (`strict_kernel_inclusion`).

2. **Zero-orbit subgroup invariance `M_b = M_{b^k}` and fixed-point quotient (Track B4):**
   - `circDist` (distance to the nearest integer `min (fract t) (1 - fract t)`) and its Cesàro
     mean `circMean b x N = (1 / N) ∑_{n < N} circDist (shift b x n)`.
   - Sharp two-sided finite bounds `circMean_pow_le`, `circMean_le_circMean_pow` (with sharp
     constant `(b^k - 1) / (k * (b - 1))`), `circMean_le_circMean_pow_add`, and
     `circMean_le_circMean_pow_general`, yielding `tendsto_circMean_iff_pow` and
     `zeroOrbitSubgroup_pow_eq` (`M_{b^k} = M_b`).
   - `fixedPoint_quotient_equiv` and `fixedPoint_quotient_card`: the fixed-point quotient
     `F_{b^k} / F_b` is isomorphic as an additive group to `ZMod ((b^k - 1) / (b - 1))`
     (with generator `1 / (b^k - 1)` mapping to `1`) and has cardinality `(b^k - 1) / (b - 1)`.
   - `fixedPoint_inter_zeroOrbit`: `r / (b^k - 1) ∈ M_b ↔ (b^k - 1) ∣ r`, hence
     `F_{b^k} ∩ M_b = ℤ` (`fixedPointSubgroup_inter_zeroOrbitSubgroup`).

3. **Strict cylinder interiority of coprime rationals (Track A4, Track B4):**
   - `coprime_rat_cylinder_margin`: for `b ≥ 2`, `Nat.Coprime d b`, `1 ≤ r < d`, and any
     length `L`, `r / d` lies in `[k / b^L, (k + 1) / b^L)` (with `k = r * b^L / d < b^L`)
     at distance at least `1 / (d * b^L)` from both endpoints.
   - `coprime_rat_dist_grid_ge` and `coprime_rat_cylinder_stable`: uniform `1 / (d * b^L)`
     separation from all `b`-adic grid points and cylinder stability under perturbations.

4. **Exact reciprocal period identities (Track D1–D2):**
   - `orderOf_mul_pow_sub_one`: for every `b ≥ 2`, `D ≥ 1`, and `m ≥ 1` with `D ∣ b^m - 1`
     (equivalently `orderOf (b : ZMod D) ∣ m`),
     `orderOf (b : ZMod (D * (b^m - 1))) = m * D` with zero exceptions.
   - `orderOf_mul_pow_add_one`: under the same hypotheses,
     `orderOf (b : ZMod (D * (b^m + 1))) = 2 * m` with zero exceptions.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.RadixPowerTower

open SharpTranslation DiscrepancyGeometry ClassicalBarriers

/-! ### Part 1: Strict radix-power kernel inclusion `K_b ⊊ K_{b^k}` (Track G1 Correction A, Track B4) -/

/-- Helper: if `((b : ℝ) ^ k - 1) * x` is an integer, then `shift (b ^ k) x n = Int.fract x`
for every `n : ℕ`. -/
private lemma shift_pow_eq_fract_of_int {b k : ℕ} {x : ℝ}
    (hx : ∃ m : ℤ, ((b : ℝ) ^ k - 1) * x = m) (n : ℕ) :
    shift (b ^ k) x n = Int.fract x := by
  obtain ⟨m, hm⟩ := hx
  have hper : ∀ i : ℕ, ∃ z : ℤ, ((b ^ k : ℕ) : ℝ) ^ i * x - x = z := by
    intro i
    induction i with
    | zero => exact ⟨0, by simp⟩
    | succ i ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨(b : ℤ) ^ k * z + m, ?_⟩
      push_cast
      have hpow : ((b : ℝ) ^ k) ^ (i + 1) = (b : ℝ) ^ k * ((b : ℝ) ^ k) ^ i := by
        rw [pow_succ']
      rw [hpow]
      push_cast at hz
      linear_combination (b : ℝ) ^ k * hz + hm
  obtain ⟨z, hz⟩ := hper n
  unfold shift
  exact Int.fract_eq_fract.mpr ⟨z, hz⟩

/-- Helper: for `b ≥ 2` and `k ≥ 1`, `((b : ℝ) ^ k - 1) > 0`. -/
private lemma pow_sub_one_pos_real {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    (0 : ℝ) < (b : ℝ) ^ k - 1 := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  have h1 : (1 : ℝ) < (b : ℝ) ^ k := one_lt_pow₀ hb1 (by omega)
  linarith

/-- For every `b ≥ 2`, `k ≥ 1`, and `N ≥ 1`, the rational `1 / (b^k - 1)` has base-`b^k`
extreme discrepancy identically equal to `1`. -/
theorem inv_pow_sub_one_radixDiscrepancy_pow {b k N : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    radixDiscrepancy (b ^ k) (1 / ((b : ℝ) ^ k - 1)) N = 1 := by
  have hden_ne : (b : ℝ) ^ k - 1 ≠ 0 := (pow_sub_one_pos_real hb hk).ne'
  have hconst : ∀ n < N, shift (b ^ k) (1 / ((b : ℝ) ^ k - 1)) n =
      Int.fract (1 / ((b : ℝ) ^ k - 1)) := fun n _ =>
    shift_pow_eq_fract_of_int ⟨1, by push_cast; field_simp [hden_ne]⟩ n
  rw [radixDiscrepancy_eq_sampleDisc]
  exact sampleDisc_eq_one_of_const (by omega) (Int.fract_nonneg _) (Int.fract_lt_one _) hconst

/-- **Membership in the higher kernel:** for `b ≥ 2` and `k ≥ 1`, `1 / (b^k - 1) ∈ K_{b^k}`. -/
theorem inv_pow_sub_one_mem_pow_kernel {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    Tendsto (fun N => radixDiscrepancy (b ^ k) (1 / ((b : ℝ) ^ k - 1)) N) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (inv_pow_sub_one_radixDiscrepancy_pow hb hk hN).symm

/-- Two distinct points `p < q` in `[0, 1)` cannot both miss an interval `[a, c) ⊆ [0, 1]`
of length greater than `1 - min (q - p) (1 - (q - p))`. -/
private lemma interval_len_le_of_miss_two {p q a c : ℝ} (hp : 0 ≤ p) (hq : q < 1) (hpq : p < q)
    (ha : 0 ≤ a) (hc : c ≤ 1) (hmp : ¬ (a ≤ p ∧ p < c)) (hmq : ¬ (a ≤ q ∧ q < c)) :
    c - a ≤ 1 - min (q - p) (1 - (q - p)) := by
  have h1 := min_le_left (q - p) (1 - (q - p))
  have h2 := min_le_right (q - p) (1 - (q - p))
  by_cases hac : a < c
  swap
  · linarith
  rw [not_and_or, not_le, not_lt] at hmp hmq
  rcases hmp with hp1 | hp1 <;> rcases hmq with hq1 | hq1 <;> linarith

/-- **Uniform discrepancy ceiling for `1 / (b^k - 1)` in base `b` (Track G1 Correction A):**
for `b ≥ 2`, `k ≥ 2`, and every `M ≥ 1`, `D_{kM}(1 / (b^k - 1); b)` stays bounded away from `1`
by the explicit positive margin `min (min g (1 - g)) (1 / k)` where `g = (b - 1) / (b^k - 1)`. -/
theorem inv_pow_sub_one_radixDiscrepancy_le {b k M : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) (hM : 1 ≤ M) :
    let g : ℝ := ((b : ℝ) - 1) / ((b : ℝ) ^ k - 1)
    radixDiscrepancy b (1 / ((b : ℝ) ^ k - 1)) (k * M) ≤
      1 - min (min g (1 - g)) (1 / (k : ℝ)) := by
  classical
  dsimp only
  set x : ℝ := 1 / ((b : ℝ) ^ k - 1)
  set p₀ : ℝ := 1 / ((b : ℝ) ^ k - 1)
  set p₁ : ℝ := (b : ℝ) / ((b : ℝ) ^ k - 1)
  set g : ℝ := ((b : ℝ) - 1) / ((b : ℝ) ^ k - 1)
  set h : ℝ := min g (1 - g)
  set δ : ℝ := min h (1 / (k : ℝ))
  have hden_pos : (0 : ℝ) < (b : ℝ) ^ k - 1 := pow_sub_one_pos_real hb (by omega)
  have hden_ne : (b : ℝ) ^ k - 1 ≠ 0 := hden_pos.ne'
  have hb_lt_bk : b + 1 < b ^ k := by
    have h4 : b * b ≤ b ^ k := by
      rw [← sq]
      exact Nat.pow_le_pow_right (by omega) hk
    nlinarith
  have hp0_pos : 0 < p₀ := by dsimp [p₀]; positivity
  have hp1_lt1 : p₁ < 1 := by
    dsimp [p₁]
    rw [div_lt_one hden_pos]
    have : (b : ℝ) + 1 < (b : ℝ) ^ k := by exact_mod_cast hb_lt_bk
    linarith
  have hp0_lt_p1 : p₀ < p₁ := by
    dsimp [p₀, p₁]
    refine div_lt_div_of_pos_right ?_ hden_pos
    exact_mod_cast (show 1 < b by omega)
  have hg_eq : p₁ - p₀ = g := by dsimp [p₀, p₁, g]; ring
  -- Periodic orbit values at indices `k * m` and `k * m + 1`.
  have hshift_per : ∀ m j : ℕ, shift b x (k * m + j) = shift b x j := by
    intro m j
    have hpow : ∀ t : ℕ, ∃ z : ℤ, ((b : ℝ) ^ k) ^ t * x - x = z := by
      intro t
      induction t with
      | zero => exact ⟨0, by simp⟩
      | succ t ih =>
        obtain ⟨z, hz⟩ := ih
        refine ⟨(b : ℤ) ^ k * z + 1, ?_⟩
        push_cast
        have hstep : ((b : ℝ) ^ k - 1) * x = 1 := by
          dsimp [x]; field_simp [hden_ne]
        rw [pow_succ']
        linear_combination (b : ℝ) ^ k * hz + hstep
    obtain ⟨z, hz⟩ := hpow m
    unfold shift
    refine Int.fract_eq_fract.mpr ⟨(b : ℤ) ^ j * z, ?_⟩
    push_cast
    rw [pow_add, pow_mul]
    calc ((b : ℝ) ^ k) ^ m * (b : ℝ) ^ j * x - (b : ℝ) ^ j * x
        = (b : ℝ) ^ j * (((b : ℝ) ^ k) ^ m * x - x) := by ring
      _ = (b : ℝ) ^ j * (z : ℝ) := by rw [hz]
  have hu0 : ∀ m : ℕ, shift b x (k * m) = p₀ := by
    intro m
    have h1 := hshift_per m 0
    rw [add_zero] at h1
    rw [h1]
    unfold shift
    rw [pow_zero, one_mul]
    exact Int.fract_eq_self.mpr ⟨hp0_pos.le, hp0_lt_p1.trans hp1_lt1⟩
  have hu1 : ∀ m : ℕ, shift b x (k * m + 1) = p₁ := by
    intro m
    rw [hshift_per m 1]
    unfold shift
    rw [pow_one]
    have hmul : (b : ℝ) * x = p₁ := by dsimp [x, p₁]; ring
    rw [hmul]
    exact Int.fract_eq_self.mpr ⟨hp0_pos.le.trans hp0_lt_p1.le, hp1_lt1⟩
  -- Frequency lower/upper bounds from `M` occurrences of `p₀` and `M` occurrences of `p₁`.
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hfreq_ge_of_hit : ∀ {a c : ℝ} {j : ℕ} (hj : j < k)
      (hval : ∀ m : ℕ, shift b x (k * m + j) = if j = 0 then p₀ else p₁)
      (hhit : a ≤ (if j = 0 then p₀ else p₁) ∧ (if j = 0 then p₀ else p₁) < c),
      (1 : ℝ) / k ≤ frequency (shift b x) a c (k * M) := by
    intro a c j hj hval hhit
    let img := (range M).image (fun m => k * m + j)
    have hsub : img ⊆ (range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c) := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      have hmM : m < M := mem_range.mp hm
      refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
      · calc k * m + j < k * m + k := by omega
          _ = k * (m + 1) := by ring
          _ ≤ k * M := Nat.mul_le_mul_left k hmM
      · rw [hval m]; exact hhit
    have hcard : img.card = M := by
      rw [Finset.card_image_of_injective _ (fun m₁ m₂ heq => by
        have : k * m₁ = k * m₂ := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega) this), card_range]
    unfold frequency
    have hle_nat : M ≤ ((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card :=
      calc M = img.card := hcard.symm
        _ ≤ ((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card :=
          card_le_card hsub
    have hle : (M : ℝ) ≤ (((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card : ℝ) := by
      exact_mod_cast hle_nat
    rw [Nat.cast_mul]
    calc (1 : ℝ) / (k : ℝ) = (M : ℝ) / ((k : ℝ) * (M : ℝ)) := by field_simp [hk_pos.ne', hM_pos.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hle (by positivity)
  have hfreq_le_of_miss : ∀ {a c : ℝ} {j : ℕ} (hj : j < k)
      (hval : ∀ m : ℕ, shift b x (k * m + j) = if j = 0 then p₀ else p₁)
      (hmiss : ¬ (a ≤ (if j = 0 then p₀ else p₁) ∧ (if j = 0 then p₀ else p₁) < c)),
      frequency (shift b x) a c (k * M) ≤ 1 - 1 / (k : ℝ) := by
    intro a c j hj hval hmiss
    let img := (range M).image (fun m => k * m + j)
    have himg_sub : img ⊆ range (k * M) := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      have hmM : m < M := mem_range.mp hm
      exact mem_range.mpr (by
        calc k * m + j < k * m + k := by omega
          _ = k * (m + 1) := by ring
          _ ≤ k * M := Nat.mul_le_mul_left k hmM)
    have hdisj : Disjoint ((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)) img := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      obtain ⟨m, _, rfl⟩ := mem_image.mp hn2
      have hnP := (mem_filter.mp hn1).2
      rw [hval m] at hnP
      exact hmiss hnP
    have hcard_img : img.card = M := by
      rw [Finset.card_image_of_injective _ (fun m₁ m₂ heq => by
        have : k * m₁ = k * m₂ := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega) this), card_range]
    have hcard_le : ((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card + M ≤ k * M := by
      calc ((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card + M
          = ((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card + img.card := by
            rw [hcard_img]
        _ = (((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)) ∪ img).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (range (k * M)).card :=
            card_le_card (Finset.union_subset (Finset.filter_subset _ _) himg_sub)
        _ = k * M := card_range _
    unfold frequency
    have hcard_r : (((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card : ℝ) ≤
        (k : ℝ) * (M : ℝ) - (M : ℝ) := by
      have : (((range (k * M)).filter (fun n => a ≤ shift b x n ∧ shift b x n < c)).card : ℝ) + (M : ℝ) ≤
          (k : ℝ) * (M : ℝ) := by exact_mod_cast hcard_le
      linarith
    rw [Nat.cast_mul]
    calc (((range (k * M)).filter _).card : ℝ) / ((k : ℝ) * (M : ℝ))
        ≤ ((k : ℝ) * (M : ℝ) - (M : ℝ)) / ((k : ℝ) * (M : ℝ)) :=
          div_le_div_of_nonneg_right hcard_r (by positivity)
      _ = 1 - 1 / (k : ℝ) := by field_simp [hk_pos.ne', hM_pos.ne']
  have hδ1 : δ ≤ h := min_le_left _ _
  have hδ2 : δ ≤ 1 / (k : ℝ) := min_le_right _ _
  have hh1 : h ≤ g := min_le_left _ _
  -- Check every interval `[a, c) ⊆ [0, 1]`.
  rw [radixDiscrepancy_eq_sampleDisc]
  refine sampleDisc_le_of (fun a c ha hac hc => ?_)
  have hf := frequency_bounds (shift b x) a c (k * M)
  rw [abs_le]
  constructor
  · -- Lower bound: `-(1 - δ) ≤ f - (c - a)`
    by_cases hhit : (a ≤ p₀ ∧ p₀ < c) ∨ (a ≤ p₁ ∧ p₁ < c)
    · have hf_ge : 1 / (k : ℝ) ≤ frequency (shift b x) a c (k * M) := by
        rcases hhit with h0 | h1
        · exact hfreq_ge_of_hit (j := 0) (by omega) (fun m => by simpa using hu0 m) (by simpa using h0)
        · exact hfreq_ge_of_hit (j := 1) (by omega) (fun m => by simpa using hu1 m) (by simpa using h1)
      linarith
    · rw [not_or] at hhit
      have hlen := interval_len_le_of_miss_two hp0_pos.le hp1_lt1 hp0_lt_p1 ha hc hhit.1 hhit.2
      rw [hg_eq] at hlen
      linarith
  · -- Upper bound: `f - (c - a) ≤ 1 - δ`
    by_cases hall : (a ≤ p₀ ∧ p₀ < c) ∧ (a ≤ p₁ ∧ p₁ < c)
    · have hlen : g < c - a := by rw [← hg_eq]; linarith [hall.1.1, hall.2.2]
      linarith [hf.2]
    · rw [not_and_or] at hall
      have hf_le : frequency (shift b x) a c (k * M) ≤ 1 - 1 / (k : ℝ) := by
        rcases hall with h0 | h1
        · exact hfreq_le_of_miss (j := 0) (by omega) (fun m => by simpa using hu0 m) (by simpa using h0)
        · exact hfreq_le_of_miss (j := 1) (by omega) (fun m => by simpa using hu1 m) (by simpa using h1)
      linarith

/-- **Non-membership in the base kernel (Track G1 Correction A):**
for every `b ≥ 2` and `k ≥ 2`, `1 / (b^k - 1) ∉ K_b`. -/
theorem inv_pow_sub_one_not_mem_kernel {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    ¬ Tendsto (fun N => radixDiscrepancy b (1 / ((b : ℝ) ^ k - 1)) N) atTop (𝓝 1) := by
  intro htend
  set g : ℝ := ((b : ℝ) - 1) / ((b : ℝ) ^ k - 1)
  set δ : ℝ := min (min g (1 - g)) (1 / (k : ℝ))
  have hden_pos : (0 : ℝ) < (b : ℝ) ^ k - 1 := pow_sub_one_pos_real hb (by omega)
  have hb_lt_bk : b < b ^ k := by
    calc b = b ^ 1 := (pow_one b).symm
      _ < b ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  have hg_pos : 0 < g := by
    dsimp [g]
    refine div_pos ?_ hden_pos
    have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
    linarith
  have hg_lt1 : g < 1 := by
    dsimp [g]
    rw [div_lt_one hden_pos]
    have : (b : ℝ) < (b : ℝ) ^ k := by exact_mod_cast hb_lt_bk
    linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min (lt_min hg_pos (by linarith)) ?_
    have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hev := (tendsto_order.mp htend).1 (1 - δ) (by linarith)
  rw [eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  let M : ℕ := max 1 N₀
  have hM : 1 ≤ M := le_max_left 1 N₀
  have hkM : N₀ ≤ k * M := by
    calc N₀ ≤ M := le_max_right 1 N₀
      _ = 1 * M := (one_mul M).symm
      _ ≤ k * M := Nat.mul_le_mul_right M (by omega)
  have hgt := hN₀ (k * M) hkM
  have hle := inv_pow_sub_one_radixDiscrepancy_le hb hk hM
  dsimp only [δ, g] at hgt
  linarith

/-- **Strict radix-power kernel inclusion `K_b ⊊ K_{b^k}` (Track G1 Correction A, Track B4):**
for every `b ≥ 2` and `k ≥ 2`, the discrepancy kernel `K_b` is a strict subset of `K_{b^k}`. -/
theorem strict_kernel_inclusion {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) :
    {x : ℝ | Tendsto (fun N => radixDiscrepancy b x N) atTop (𝓝 1)} ⊂
      {x : ℝ | Tendsto (fun N => radixDiscrepancy (b ^ k) x N) atTop (𝓝 1)} := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun x hx => tendsto_radixDiscrepancy_pow_one (by omega) hx, ?_⟩
  intro heq
  have hmem : 1 / ((b : ℝ) ^ k - 1) ∈
      {x : ℝ | Tendsto (fun N => radixDiscrepancy (b ^ k) x N) atTop (𝓝 1)} :=
    inv_pow_sub_one_mem_pow_kernel hb (by omega)
  rw [← heq] at hmem
  exact inv_pow_sub_one_not_mem_kernel hb hk hmem

/-! ### Part 2: Zero-orbit subgroup invariance `M_b = M_{b^k}` & Quotient `F_{b^k} / F_b` (Track B4) -/

/-- Distance from a real number `t` to the nearest integer, `‖t‖ = min ({t}, 1 - {t})`. -/
noncomputable def circDist (t : ℝ) : ℝ := min (Int.fract t) (1 - Int.fract t)

/-- Cesàro mean of the circle distance along the base-`b` orbit,
`M_N(x; b) = (1 / N) ∑_{n < N} ‖b^n x‖`. -/
noncomputable def circMean (b : ℕ) (x : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, circDist (shift b x n)) / (N : ℝ)

theorem circDist_nonneg (t : ℝ) : 0 ≤ circDist t := by
  unfold circDist
  exact le_min (Int.fract_nonneg t) (by linarith [Int.fract_lt_one t])

theorem circDist_le_half (t : ℝ) : circDist t ≤ 1 / 2 := by
  unfold circDist
  by_cases h : Int.fract t ≤ 1 / 2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem circDist_fract (t : ℝ) : circDist (Int.fract t) = circDist t := by
  simp [circDist, Int.fract_fract]

theorem circDist_add_intCast (t : ℝ) (z : ℤ) : circDist (t + z) = circDist t := by
  simp [circDist, Int.fract_add_intCast]

theorem circDist_eq_zero_iff (t : ℝ) : circDist t = 0 ↔ ∃ z : ℤ, t = z := by
  constructor
  · intro h
    unfold circDist at h
    have h1 : 0 < 1 - Int.fract t := by linarith [Int.fract_lt_one t]
    have h0 : Int.fract t = 0 := by
      rcases le_total (Int.fract t) (1 - Int.fract t) with hle | hle
      · rwa [min_eq_left hle] at h
      · rw [min_eq_right hle] at h; linarith
    refine ⟨⌊t⌋, ?_⟩
    have hf := Int.fract_add_floor t
    linarith
  · rintro ⟨z, rfl⟩
    simp [circDist, Int.fract_intCast]

theorem circDist_le_abs_sub_int (t : ℝ) (z : ℤ) : circDist t ≤ |t - (z : ℝ)| := by
  unfold circDist
  have hf := Int.fract_add_floor t
  rcases le_or_gt z ⌊t⌋ with hle | hgt
  · have hz : (z : ℝ) ≤ (⌊t⌋ : ℝ) := by exact_mod_cast hle
    have hpos : 0 ≤ t - (z : ℝ) := by linarith [Int.fract_nonneg t]
    rw [abs_of_nonneg hpos]
    exact (min_le_left _ _).trans (by linarith)
  · have hge : ⌊t⌋ + 1 ≤ z := Int.add_one_le_of_lt hgt
    have hz : (⌊t⌋ : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hge
    have hneg : t - (z : ℝ) ≤ 0 := by linarith [Int.fract_lt_one t]
    rw [abs_of_nonpos hneg]
    exact (min_le_right _ _).trans (by linarith)

theorem exists_int_abs_sub_eq_circDist (t : ℝ) : ∃ z : ℤ, |t - (z : ℝ)| = circDist t := by
  unfold circDist
  have hf := Int.fract_add_floor t
  by_cases h : Int.fract t ≤ 1 - Int.fract t
  · refine ⟨⌊t⌋, ?_⟩
    rw [min_eq_left h]
    have hsub : t - (⌊t⌋ : ℝ) = Int.fract t := by linarith
    rw [hsub, abs_of_nonneg (Int.fract_nonneg t)]
  · push Not at h
    refine ⟨⌊t⌋ + 1, ?_⟩
    rw [min_eq_right h.le]
    push_cast
    have hsub : t - ((⌊t⌋ : ℝ) + 1) = -(1 - Int.fract t) := by linarith
    rw [hsub, abs_neg, abs_of_nonneg (by linarith [Int.fract_lt_one t])]

theorem circDist_add_le (x y : ℝ) : circDist (x + y) ≤ circDist x + circDist y := by
  obtain ⟨zx, hzx⟩ := exists_int_abs_sub_eq_circDist x
  obtain ⟨zy, hzy⟩ := exists_int_abs_sub_eq_circDist y
  calc circDist (x + y) ≤ |(x + y) - ((zx + zy : ℤ) : ℝ)| := circDist_le_abs_sub_int _ _
    _ = |(x - (zx : ℝ)) + (y - (zy : ℝ))| := by push_cast; ring_nf
    _ ≤ |x - (zx : ℝ)| + |y - (zy : ℝ)| := abs_add_le _ _
    _ = circDist x + circDist y := by rw [hzx, hzy]

theorem circDist_neg (t : ℝ) : circDist (-t) = circDist t := by
  have hle : ∀ u : ℝ, circDist (-u) ≤ circDist u := by
    intro u
    obtain ⟨z, hz⟩ := exists_int_abs_sub_eq_circDist u
    calc circDist (-u) ≤ |-u - ((-z : ℤ) : ℝ)| := circDist_le_abs_sub_int _ _
      _ = |-(u - (z : ℝ))| := by push_cast; ring_nf
      _ = |u - (z : ℝ)| := abs_neg _
      _ = circDist u := hz
  exact le_antisymm (hle t) (by simpa using hle (-t))

theorem circDist_natMul_le (m : ℕ) (t : ℝ) : circDist ((m : ℝ) * t) ≤ (m : ℝ) * circDist t := by
  obtain ⟨z, hz⟩ := exists_int_abs_sub_eq_circDist t
  calc circDist ((m : ℝ) * t) ≤ |(m : ℝ) * t - (((m : ℤ) * z : ℤ) : ℝ)| :=
        circDist_le_abs_sub_int _ _
    _ = |(m : ℝ) * (t - (z : ℝ))| := by push_cast; ring_nf
    _ = (m : ℝ) * |t - (z : ℝ)| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
    _ = (m : ℝ) * circDist t := by rw [hz]

theorem circMean_nonneg (b : ℕ) (x : ℝ) (N : ℕ) : 0 ≤ circMean b x N :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => circDist_nonneg _)) (Nat.cast_nonneg N)

/-- Block-summation identity `∑_{m < kN} f(m) = ∑_{n < N} ∑_{j < k} f(kn + j)`. -/
private lemma sum_range_mul_blocks (f : ℕ → ℝ) (k N : ℕ) :
    ∑ m ∈ range (k * N), f m = ∑ n ∈ range N, ∑ j ∈ range k, f (k * n + j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- **Sharp lower comparison (Track B4, Theorem 7.1(i)):**
`M_N(x; b^k) ≤ k * M_{kN}(x; b)` for all `k ≥ 1`, `N ≥ 1`. -/
theorem circMean_pow_le {b k N : ℕ} (hk : 0 < k) (hN : 0 < N) (x : ℝ) :
    circMean (b ^ k) x N ≤ (k : ℝ) * circMean b x (k * N) := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hshift_eq : ∀ n : ℕ, shift (b ^ k) x n = shift b x (k * n) := by
    intro n; unfold shift; push_cast; rw [← pow_mul]
  let img := (range N).image (fun n => k * n)
  have himg_sub : img ⊆ range (k * N) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    exact mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hn) hk)
  have hsum_le : ∑ n ∈ range N, circDist (shift (b ^ k) x n) ≤
      ∑ m ∈ range (k * N), circDist (shift b x m) := by
    calc ∑ n ∈ range N, circDist (shift (b ^ k) x n)
        = ∑ n ∈ range N, circDist (shift b x (k * n)) := by
          refine Finset.sum_congr rfl (fun n _ => by rw [hshift_eq])
      _ = ∑ m ∈ img, circDist (shift b x m) := by
          rw [Finset.sum_image (fun n₁ _ n₂ _ h => Nat.eq_of_mul_eq_mul_left hk h)]
      _ ≤ ∑ m ∈ range (k * N), circDist (shift b x m) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun _ _ _ => circDist_nonneg _)
  unfold circMean
  rw [Nat.cast_mul]
  have hrhs : (k : ℝ) * ((∑ m ∈ range (k * N), circDist (shift b x m)) / ((k : ℝ) * (N : ℝ))) =
      (∑ m ∈ range (k * N), circDist (shift b x m)) / (N : ℝ) := by
    field_simp [hk_pos.ne', hN_pos.ne']
  rw [hrhs]
  exact div_le_div_of_nonneg_right hsum_le hN_pos.le

/-- Block upper bound on the unnormalized sum `∑_{m < kN} ‖b^m x‖`. -/
private lemma sum_circDist_mul_le {b k N : ℕ} (hb : 2 ≤ b) (x : ℝ) :
    ∑ m ∈ range (k * N), circDist (shift b x m) ≤
      (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * ∑ n ∈ range N, circDist (shift (b ^ k) x n) := by
  have hb_ne1 : (b : ℝ) ≠ 1 := by exact_mod_cast (show b ≠ 1 by omega)
  rw [sum_range_mul_blocks]
  have hblock : ∀ n ∈ range N,
      ∑ j ∈ range k, circDist (shift b x (k * n + j)) ≤
        (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * circDist (shift (b ^ k) x n) := by
    intro n _
    have hterm : ∀ j ∈ range k,
        circDist (shift b x (k * n + j)) ≤ (b : ℝ) ^ j * circDist (shift (b ^ k) x n) := by
      intro j _
      calc circDist (shift b x (k * n + j))
          = circDist ((b : ℝ) ^ (k * n + j) * x) := circDist_fract _
        _ = circDist (((b ^ j : ℕ) : ℝ) * (((b ^ k : ℕ) : ℝ) ^ n * x)) := by
            push_cast; rw [pow_add, pow_mul]; ring_nf
        _ ≤ ((b ^ j : ℕ) : ℝ) * circDist (((b ^ k : ℕ) : ℝ) ^ n * x) :=
            circDist_natMul_le (b ^ j) _
        _ = (b : ℝ) ^ j * circDist (shift (b ^ k) x n) := by
            unfold shift; push_cast; rw [circDist_fract]
    calc ∑ j ∈ range k, circDist (shift b x (k * n + j))
        ≤ ∑ j ∈ range k, (b : ℝ) ^ j * circDist (shift (b ^ k) x n) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ range k, (b : ℝ) ^ j) * circDist (shift (b ^ k) x n) := by
          rw [Finset.sum_mul]
      _ = (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * circDist (shift (b ^ k) x n) := by
          rw [geom_sum_eq hb_ne1]
  calc ∑ n ∈ range N, ∑ j ∈ range k, circDist (shift b x (k * n + j))
      ≤ ∑ n ∈ range N, (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * circDist (shift (b ^ k) x n) :=
        Finset.sum_le_sum hblock
    _ = (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * ∑ n ∈ range N, circDist (shift (b ^ k) x n) := by
        rw [Finset.mul_sum]

/-- **Sharp upper comparison at multiples `k * N` (Track B4, Theorem 7.1(ii)):**
`M_{kN}(x; b) ≤ ((b^k - 1) / (k * (b - 1))) * M_N(x; b^k)`. -/
theorem circMean_le_circMean_pow {b k N : ℕ} (hb : 2 ≤ b) (hk : 0 < k) (hN : 0 < N) (x : ℝ) :
    circMean b x (k * N) ≤
      (((b : ℝ) ^ k - 1) / ((k : ℝ) * ((b : ℝ) - 1))) * circMean (b ^ k) x N := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hb1_ne : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
    linarith
  have hsum := sum_circDist_mul_le (k := k) (N := N) hb x
  unfold circMean
  rw [Nat.cast_mul]
  have hdiv := div_le_div_of_nonneg_right hsum (show (0 : ℝ) ≤ (k : ℝ) * (N : ℝ) by positivity)
  have hrew : ((((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) *
      ∑ n ∈ range N, circDist (shift (b ^ k) x n)) / ((k : ℝ) * (N : ℝ)) =
      (((b : ℝ) ^ k - 1) / ((k : ℝ) * ((b : ℝ) - 1))) *
      ((∑ n ∈ range N, circDist (shift (b ^ k) x n)) / (N : ℝ)) := by
    field_simp [hk_pos.ne', hN_pos.ne', hb1_ne]
  rwa [hrew] at hdiv

/-- **General cutoff upper comparison (Track B4, Theorem 7.1(iii)):**
for `b ≥ 2`, `k ≥ 1`, `r < k`, and `k * N + r > 0`,
`M_{kN + r}(x; b) ≤ ((b^k - 1) / (b - 1)) * ((N + 1) / (kN + r)) * M_{N + 1}(x; b^k)`. -/
theorem circMean_le_circMean_pow_add {b k N r : ℕ} (hb : 2 ≤ b) (hr : r < k)
    (hpos : 0 < k * N + r) (x : ℝ) :
    circMean b x (k * N + r) ≤
      (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) *
        (((N + 1 : ℕ) : ℝ) / ((k * N + r : ℕ) : ℝ)) * circMean (b ^ k) x (N + 1) := by
  have hM_pos : (0 : ℝ) < ((k * N + r : ℕ) : ℝ) := by exact_mod_cast hpos
  have hN1_pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hb1_ne : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
    linarith
  have hsub : range (k * N + r) ⊆ range (k * (N + 1)) :=
    Finset.range_mono (by rw [Nat.mul_succ]; omega)
  have hsum : ∑ m ∈ range (k * N + r), circDist (shift b x m) ≤
      (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * ∑ n ∈ range (N + 1), circDist (shift (b ^ k) x n) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => circDist_nonneg _)).trans
      (sum_circDist_mul_le (k := k) (N := N + 1) hb x)
  unfold circMean
  have hdiv := div_le_div_of_nonneg_right hsum hM_pos.le
  have hrew : ((((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) *
      ∑ n ∈ range (N + 1), circDist (shift (b ^ k) x n)) / ((k * N + r : ℕ) : ℝ) =
      (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) *
        (((N + 1 : ℕ) : ℝ) / ((k * N + r : ℕ) : ℝ)) *
        ((∑ n ∈ range (N + 1), circDist (shift (b ^ k) x n)) / ((N + 1 : ℕ) : ℝ)) := by
    field_simp [hM_pos.ne', hN1_pos.ne', hb1_ne]
  rwa [hrew] at hdiv

/-- **General cutoff upper comparison with uniform constant for `M ≥ k`:**
`M_M(x; b) ≤ (2 * (b^k - 1) / (k * (b - 1))) * M_{M / k + 1}(x; b^k)`. -/
theorem circMean_le_circMean_pow_general {b k M : ℕ} (hb : 2 ≤ b) (hk : 0 < k) (hM : k ≤ M)
    (x : ℝ) :
    circMean b x M ≤
      (2 * ((b : ℝ) ^ k - 1) / ((k : ℝ) * ((b : ℝ) - 1))) * circMean (b ^ k) x (M / k + 1) := by
  set N := M / k
  set r := M % k
  have hM_eq : k * N + r = M := Nat.div_add_mod M k
  have hr : r < k := Nat.mod_lt M hk
  have hN1 : 1 ≤ N := Nat.div_pos hM hk
  have hpos : 0 < k * N + r := by omega
  have h1 := circMean_le_circMean_pow_add (N := N) (r := r) hb hr hpos x
  rw [hM_eq] at h1
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hratio : ((N + 1 : ℕ) : ℝ) / (M : ℝ) ≤ 2 / (k : ℝ) := by
    rw [div_le_div_iff₀ hM_pos hk_pos]
    have hNle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    have hkNle : (k : ℝ) * (N : ℝ) ≤ (M : ℝ) := by
      have : k * N ≤ M := Nat.mul_div_le M k
      exact_mod_cast this
    push_cast
    nlinarith
  have hfac_nn : 0 ≤ (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) := by
    have hnum : (0 : ℝ) < (b : ℝ) ^ k - 1 := pow_sub_one_pos_real hb hk
    have hden : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
      linarith
    exact div_nonneg hnum.le hden.le
  have h2 : (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * (((N + 1 : ℕ) : ℝ) / (M : ℝ)) *
      circMean (b ^ k) x (N + 1) ≤
      (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * (2 / (k : ℝ)) * circMean (b ^ k) x (N + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (circMean_nonneg _ _ _)
    exact mul_le_mul_of_nonneg_left hratio hfac_nn
  have hrew : (((b : ℝ) ^ k - 1) / ((b : ℝ) - 1)) * (2 / (k : ℝ)) =
      2 * ((b : ℝ) ^ k - 1) / ((k : ℝ) * ((b : ℝ) - 1)) := by
    rw [div_mul_div_comm]; ring
  rw [hrew] at h2
  exact h1.trans h2

/-- **Zero-orbit subgroup invariance `M_b = M_{b^k}` (Track B4, Theorem 7.1):**
for every `b ≥ 2`, `k ≥ 1`, and `x : ℝ`, `M_N(x; b^k) → 0 ↔ M_N(x; b) → 0`. -/
theorem tendsto_circMean_iff_pow {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) (x : ℝ) :
    Tendsto (circMean (b ^ k) x) atTop (𝓝 0) ↔ Tendsto (circMean b x) atTop (𝓝 0) := by
  constructor
  · intro hpow
    have hdiv_top : Tendsto (fun M : ℕ => M / k + 1) atTop atTop :=
      tendsto_atTop_atTop.mpr (fun B => ⟨k * B, fun M hM => by
        have : B ≤ M / k := (Nat.le_div_iff_mul_le hk).mpr (by rw [mul_comm]; exact hM)
        omega⟩)
    have hupper : Tendsto (fun M : ℕ =>
        (2 * ((b : ℝ) ^ k - 1) / ((k : ℝ) * ((b : ℝ) - 1))) * circMean (b ^ k) x (M / k + 1))
        atTop (𝓝 0) := by
      have h1 := (hpow.comp hdiv_top).const_mul (2 * ((b : ℝ) ^ k - 1) / ((k : ℝ) * ((b : ℝ) - 1)))
      simpa [Function.comp_def] using h1
    refine squeeze_zero' ?_ ?_ hupper
    · exact Eventually.of_forall (fun M => circMean_nonneg b x M)
    · filter_upwards [eventually_ge_atTop k] with M hM
      exact circMean_le_circMean_pow_general hb hk hM x
  · intro hbase
    have hmul_top : Tendsto (fun N : ℕ => k * N) atTop atTop :=
      tendsto_atTop_atTop.mpr (fun B => ⟨B, fun N hN => by
        calc B ≤ 1 * N := by omega
          _ ≤ k * N := Nat.mul_le_mul_right N hk⟩)
    have hupper : Tendsto (fun N : ℕ => (k : ℝ) * circMean b x (k * N)) atTop (𝓝 0) := by
      have h1 := (hbase.comp hmul_top).const_mul (k : ℝ)
      simpa [Function.comp_def] using h1
    refine squeeze_zero' ?_ ?_ hupper
    · exact Eventually.of_forall (fun N => circMean_nonneg (b ^ k) x N)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact circMean_pow_le hk hN x

/-- The zero-orbit additive subgroup `M_b = {w ∈ ℝ | M_N(w; b) → 0}` of `ℝ`. -/
noncomputable def zeroOrbitSubgroup (b : ℕ) : AddSubgroup ℝ where
  carrier := {w : ℝ | Tendsto (circMean b w) atTop (𝓝 0)}
  zero_mem' := by
    change Tendsto (circMean b 0) atTop (𝓝 0)
    have h0 : circMean b 0 = fun _ => 0 := funext fun N => by
      simp [circMean, shift, circDist]
    rw [h0]
    exact tendsto_const_nhds
  add_mem' := by
    intro w₁ w₂ hw₁ hw₂
    change Tendsto (circMean b (w₁ + w₂)) atTop (𝓝 0)
    have hadd : Tendsto (fun N => circMean b w₁ N + circMean b w₂ N) atTop (𝓝 0) := by
      simpa using hw₁.add hw₂
    refine squeeze_zero (fun N => circMean_nonneg b (w₁ + w₂) N) (fun N => ?_) hadd
    unfold circMean
    rw [← add_div, ← Finset.sum_add_distrib]
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => ?_)) (Nat.cast_nonneg N)
    calc circDist (shift b (w₁ + w₂) n)
        = circDist ((b : ℝ) ^ n * w₁ + (b : ℝ) ^ n * w₂) := by
          unfold shift; rw [circDist_fract]; congr 1; ring
      _ ≤ circDist ((b : ℝ) ^ n * w₁) + circDist ((b : ℝ) ^ n * w₂) := circDist_add_le _ _
      _ = circDist (shift b w₁ n) + circDist (shift b w₂ n) := by
          unfold shift; rw [circDist_fract, circDist_fract]
  neg_mem' := by
    intro w hw
    change Tendsto (circMean b (-w)) atTop (𝓝 0)
    have hneg : circMean b (-w) = circMean b w := funext fun N => by
      unfold circMean
      congr 1
      refine Finset.sum_congr rfl (fun n _ => ?_)
      calc circDist (shift b (-w) n)
          = circDist (-((b : ℝ) ^ n * w)) := by unfold shift; rw [circDist_fract]; congr 1; ring
        _ = circDist ((b : ℝ) ^ n * w) := circDist_neg _
        _ = circDist (shift b w n) := by unfold shift; rw [circDist_fract]
    rw [hneg]
    exact hw

/-- `M_{b^k} = M_b` as additive subgroups of `ℝ`. -/
theorem zeroOrbitSubgroup_pow_eq {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) :
    zeroOrbitSubgroup (b ^ k) = zeroOrbitSubgroup b := by
  ext x
  exact tendsto_circMean_iff_pow hb hk x

/-- The fixed-point additive subgroup `F_b = (1 / (b - 1)) ℤ ⊆ ℝ` of the radix-`b` shift. -/
noncomputable def fixedPointSubgroup (b : ℕ) : AddSubgroup ℝ where
  carrier := {x : ℝ | ∃ m : ℤ, ((b : ℝ) - 1) * x = m}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨mx, hmx⟩ ⟨my, hmy⟩
    exact ⟨mx + my, by push_cast; linarith⟩
  neg_mem' := by
    rintro x ⟨mx, hmx⟩
    exact ⟨-mx, by push_cast; linarith⟩

/-- For `b ≥ 2` and `k ≥ 1`, `b - 1` divides `b ^ k - 1`, and the quotient `(b^k - 1) / (b - 1)`
is positive. -/
private lemma sub_one_dvd_pow_sub_one (b k : ℕ) : b - 1 ∣ b ^ k - 1 := by
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow b 1 k

private lemma repunit_pos {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) :
    0 < (b ^ k - 1) / (b - 1) := by
  have hb_le : b ≤ b ^ k := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ k := Nat.pow_le_pow_right (by omega) hk
  exact Nat.div_pos (by omega) (by omega)

/-- `F_b ≤ F_{b^k}` for all `b ≥ 2` and `k : ℕ`. -/
theorem fixedPointSubgroup_le_pow {b k : ℕ} (hb : 2 ≤ b) :
    fixedPointSubgroup b ≤ fixedPointSubgroup (b ^ k) := by
  rintro x ⟨m, hm⟩
  set R : ℕ := (b ^ k - 1) / (b - 1)
  have hmul : (b - 1) * R = b ^ k - 1 := Nat.mul_div_cancel' (sub_one_dvd_pow_sub_one b k)
  have hb_le : 1 ≤ b := by omega
  have hbk_le : 1 ≤ b ^ k := one_le_pow₀ hb_le
  have hmul_r : ((b : ℝ) - 1) * (R : ℝ) = (b : ℝ) ^ k - 1 := by
    have h1 : (((b - 1) * R : ℕ) : ℝ) = ((b ^ k - 1 : ℕ) : ℝ) := by exact_mod_cast hmul
    rw [Nat.cast_mul, Nat.cast_sub hb_le, Nat.cast_sub hbk_le, Nat.cast_pow, Nat.cast_one] at h1
    exact h1
  refine ⟨(R : ℤ) * m, ?_⟩
  push_cast
  calc ((b : ℝ) ^ k - 1) * x
      = ((b : ℝ) - 1) * (R : ℝ) * x := by rw [← hmul_r]
    _ = (R : ℝ) * (((b : ℝ) - 1) * x) := by ring
    _ = (R : ℝ) * (m : ℝ) := by rw [hm]

/-- Coordinate homomorphism `F_{b^k} →+ ZMod ((b^k - 1) / (b - 1))` sending `m / (b^k - 1)` to
`m mod R`. -/
noncomputable def fixedPointCoordHom {b k : ℕ} :
    fixedPointSubgroup (b ^ k) →+ ZMod ((b ^ k - 1) / (b - 1)) where
  toFun x := ((⌊((b : ℝ) ^ k - 1) * x.1⌋ : ℤ) : ZMod ((b ^ k - 1) / (b - 1)))
  map_zero' := by simp
  map_add' x y := by
    obtain ⟨mx, hmx⟩ := x.2
    obtain ⟨my, hmy⟩ := y.2
    have hmx' : ((b : ℝ) ^ k - 1) * x.1 = (mx : ℝ) := by simpa using hmx
    have hmy' : ((b : ℝ) ^ k - 1) * y.1 = (my : ℝ) := by simpa using hmy
    have hsum : ((b : ℝ) ^ k - 1) * (x.1 + y.1) = ((mx + my : ℤ) : ℝ) := by
      push_cast; linarith
    change ((⌊((b : ℝ) ^ k - 1) * (x.1 + y.1)⌋ : ℤ) : ZMod ((b ^ k - 1) / (b - 1))) =
      ((⌊((b : ℝ) ^ k - 1) * x.1⌋ : ℤ) : ZMod ((b ^ k - 1) / (b - 1))) +
        ((⌊((b : ℝ) ^ k - 1) * y.1⌋ : ℤ) : ZMod ((b ^ k - 1) / (b - 1)))
    rw [hsum, hmx', hmy', Int.floor_intCast, Int.floor_intCast, Int.floor_intCast, Int.cast_add]

theorem fixedPointCoordHom_ker {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) :
    (fixedPointCoordHom (b := b) (k := k)).ker =
      (fixedPointSubgroup b).addSubgroupOf (fixedPointSubgroup (b ^ k)) := by
  set R : ℕ := (b ^ k - 1) / (b - 1)
  have hR_pos : 0 < R := repunit_pos hb hk
  have hR_ne : (R : ℝ) ≠ 0 := by exact_mod_cast hR_pos.ne'
  have hmul : (b - 1) * R = b ^ k - 1 := Nat.mul_div_cancel' (sub_one_dvd_pow_sub_one b k)
  have hb_le : 1 ≤ b := by omega
  have hbk_le : 1 ≤ b ^ k := one_le_pow₀ hb_le
  have hmul_r : ((b : ℝ) - 1) * (R : ℝ) = (b : ℝ) ^ k - 1 := by
    have h1 : (((b - 1) * R : ℕ) : ℝ) = ((b ^ k - 1 : ℕ) : ℝ) := by exact_mod_cast hmul
    rw [Nat.cast_mul, Nat.cast_sub hb_le, Nat.cast_sub hbk_le, Nat.cast_pow, Nat.cast_one] at h1
    exact h1
  ext x
  obtain ⟨mx, hmx⟩ := x.2
  have hmx' : ((b : ℝ) ^ k - 1) * x.1 = (mx : ℝ) := by simpa using hmx
  change ((⌊((b : ℝ) ^ k - 1) * x.1⌋ : ℤ) : ZMod R) = 0 ↔ ∃ q : ℤ, ((b : ℝ) - 1) * x.1 = (q : ℝ)
  rw [hmx', Int.floor_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hqr : (mx : ℝ) = (R : ℝ) * (q : ℝ) := by exact_mod_cast hq
    apply mul_left_cancel₀ hR_ne
    calc (R : ℝ) * (((b : ℝ) - 1) * x.1)
        = ((b : ℝ) - 1) * (R : ℝ) * x.1 := by ring
      _ = ((b : ℝ) ^ k - 1) * x.1 := by rw [hmul_r]
      _ = (mx : ℝ) := hmx'
      _ = (R : ℝ) * (q : ℝ) := hqr
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hqr : (mx : ℝ) = (R : ℝ) * (q : ℝ) := by
      calc (mx : ℝ) = ((b : ℝ) ^ k - 1) * x.1 := hmx'.symm
        _ = ((b : ℝ) - 1) * (R : ℝ) * x.1 := by rw [← hmul_r]
        _ = (R : ℝ) * (((b : ℝ) - 1) * x.1) := by ring
        _ = (R : ℝ) * (q : ℝ) := by rw [hq]
    exact_mod_cast hqr

theorem fixedPointCoordHom_surjective {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) :
    Function.Surjective (fixedPointCoordHom (b := b) (k := k)) := by
  set R : ℕ := (b ^ k - 1) / (b - 1)
  have : NeZero R := ⟨(repunit_pos hb hk).ne'⟩
  have hden_ne : (b : ℝ) ^ k - 1 ≠ 0 := (pow_sub_one_pos_real hb hk).ne'
  intro a
  let xval : ℝ := (a.val : ℝ) / ((b : ℝ) ^ k - 1)
  have hxmem : xval ∈ fixedPointSubgroup (b ^ k) := by
    refine ⟨(a.val : ℤ), ?_⟩
    push_cast [xval]
    field_simp [hden_ne]
  refine ⟨⟨xval, hxmem⟩, ?_⟩
  change ((⌊((b : ℝ) ^ k - 1) * xval⌋ : ℤ) : ZMod R) = a
  have heq : ((b : ℝ) ^ k - 1) * xval = ((a.val : ℤ) : ℝ) := by
    dsimp [xval]
    push_cast
    field_simp [hden_ne]
  rw [heq, Int.floor_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **Fixed-point quotient isomorphism (Track B4, Theorem 8.1 core):**
for every `b ≥ 2` and `k ≥ 1`, `F_{b^k} / F_b ≃+ ZMod ((b^k - 1) / (b - 1))`. -/
noncomputable def fixedPoint_quotient_equiv {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) :
    (fixedPointSubgroup (b ^ k) ⧸
      (fixedPointSubgroup b).addSubgroupOf (fixedPointSubgroup (b ^ k))) ≃+
      ZMod ((b ^ k - 1) / (b - 1)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (fixedPointCoordHom_ker hb hk).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (fixedPointCoordHom (b := b) (k := k))
      (fixedPointCoordHom_surjective hb hk))

/-- The canonical generator `1 / (b^k - 1) ∈ F_{b^k}` maps to `1 ∈ ZMod ((b^k - 1) / (b - 1))`
under `fixedPoint_quotient_equiv`. -/
theorem fixedPoint_quotient_equiv_gen {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) :
    let hmem : (1 / ((b : ℝ) ^ k - 1)) ∈ fixedPointSubgroup (b ^ k) :=
      ⟨1, by
        have hden_ne : (b : ℝ) ^ k - 1 ≠ 0 := (pow_sub_one_pos_real hb hk).ne'
        push_cast; field_simp [hden_ne]⟩
    fixedPoint_quotient_equiv hb hk (QuotientAddGroup.mk ⟨1 / ((b : ℝ) ^ k - 1), hmem⟩) = 1 := by
  intro hmem
  have hden_ne : (b : ℝ) ^ k - 1 ≠ 0 := (pow_sub_one_pos_real hb hk).ne'
  have heval : fixedPoint_quotient_equiv hb hk
      (QuotientAddGroup.mk ⟨1 / ((b : ℝ) ^ k - 1), hmem⟩) =
      fixedPointCoordHom (b := b) (k := k) ⟨1 / ((b : ℝ) ^ k - 1), hmem⟩ := rfl
  rw [heval]
  change ((⌊((b : ℝ) ^ k - 1) * (1 / ((b : ℝ) ^ k - 1))⌋ : ℤ) : ZMod ((b ^ k - 1) / (b - 1))) = 1
  rw [mul_one_div_cancel hden_ne]
  norm_num

/-- **Exact cardinality of the fixed-point quotient:**
`|F_{b^k} / F_b| = (b^k - 1) / (b - 1)`. -/
theorem fixedPoint_quotient_card {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) :
    Nat.card (fixedPointSubgroup (b ^ k) ⧸
      (fixedPointSubgroup b).addSubgroupOf (fixedPointSubgroup (b ^ k))) =
      (b ^ k - 1) / (b - 1) := by
  rw [Nat.card_congr (fixedPoint_quotient_equiv hb hk).toEquiv, Nat.card_zmod]

/-- **Fixed-point / zero-orbit intersection (Track B4, Theorem 8.1(1)):**
`r / (b^k - 1) ∈ M_b ↔ (b^k - 1) ∣ r`. -/
theorem fixedPoint_inter_zeroOrbit {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) (r : ℤ) :
    (r : ℝ) / ((b : ℝ) ^ k - 1) ∈ zeroOrbitSubgroup b ↔ ((b ^ k - 1 : ℕ) : ℤ) ∣ r := by
  set x : ℝ := (r : ℝ) / ((b : ℝ) ^ k - 1)
  have hden_ne : (b : ℝ) ^ k - 1 ≠ 0 := (pow_sub_one_pos_real hb hk).ne'
  have hshift : ∀ n : ℕ, shift (b ^ k) x n = Int.fract x :=
    shift_pow_eq_fract_of_int ⟨r, by dsimp [x]; field_simp [hden_ne]⟩
  have hconst : ∀ N : ℕ, 1 ≤ N → circMean (b ^ k) x N = circDist x := by
    intro N hN
    unfold circMean
    have hsum : ∑ n ∈ range N, circDist (shift (b ^ k) x n) = (N : ℝ) * circDist x := by
      calc ∑ n ∈ range N, circDist (shift (b ^ k) x n)
          = ∑ _n ∈ range N, circDist x :=
            Finset.sum_congr rfl (fun n _ => by rw [hshift n, circDist_fract])
        _ = (N : ℝ) * circDist x := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    rw [hsum]
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp [hN_ne]
  have hmem_iff : x ∈ zeroOrbitSubgroup b ↔ Tendsto (circMean (b ^ k) x) atTop (𝓝 0) :=
    (tendsto_circMean_iff_pow hb hk x).symm
  rw [hmem_iff]
  have hev : circMean (b ^ k) x =ᶠ[atTop] fun _ => circDist x := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hconst N hN
  rw [tendsto_congr' hev, tendsto_const_nhds_iff, circDist_eq_zero_iff]
  have hbk_le : 1 ≤ b ^ k := one_le_pow₀ (by omega)
  have hcast : ((b ^ k - 1 : ℕ) : ℝ) = (b : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub hbk_le, Nat.cast_pow, Nat.cast_one]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hr : (r : ℝ) = ((b ^ k - 1 : ℕ) : ℝ) * (z : ℝ) := by
      rw [hcast]
      have := (div_eq_iff hden_ne).mp hz
      linarith
    exact_mod_cast hr
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [div_eq_iff hden_ne, ← hcast]
    have : (r : ℝ) = ((b ^ k - 1 : ℕ) : ℝ) * (z : ℝ) := by exact_mod_cast hz
    linarith

/-- Subgroup-intersection form `F_{b^k} ∩ M_b = ℤ` (Track B4, Theorem 8.1(1)). -/
theorem fixedPointSubgroup_inter_zeroOrbitSubgroup {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ fixedPointSubgroup (b ^ k)) :
    x ∈ zeroOrbitSubgroup b ↔ ∃ z : ℤ, x = z := by
  obtain ⟨r, hr⟩ := hx
  have hden_ne : (b : ℝ) ^ k - 1 ≠ 0 := (pow_sub_one_pos_real hb hk).ne'
  have hx_eq : x = (r : ℝ) / ((b : ℝ) ^ k - 1) := by
    have hr' : ((b : ℝ) ^ k - 1) * x = (r : ℝ) := by simpa using hr
    exact (eq_div_iff hden_ne).mpr (by linarith)
  rw [hx_eq, fixedPoint_inter_zeroOrbit hb hk r]
  have hbk_le : 1 ≤ b ^ k := one_le_pow₀ (by omega)
  have hcast : ((b ^ k - 1 : ℕ) : ℝ) = (b : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub hbk_le, Nat.cast_pow, Nat.cast_one]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [div_eq_iff hden_ne, ← hcast]
    have : (r : ℝ) = ((b ^ k - 1 : ℕ) : ℝ) * (z : ℝ) := by exact_mod_cast hz
    linarith
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hr' : (r : ℝ) = ((b ^ k - 1 : ℕ) : ℝ) * (z : ℝ) := by
      rw [hcast]
      have := (div_eq_iff hden_ne).mp hz
      linarith
    exact_mod_cast hr'

/-! ### Part 3: Strict cylinder interiority of coprime rationals (Track A4, Track B4) -/

/-- **Strict cylinder interiority of coprime rationals (Track A4 Lemma 5.1, Track B4 Theorem 9.2(4)):**
if `b ≥ 2`, `d ≥ 2`, `Nat.Coprime d b`, `1 ≤ r < d`, and `L ≥ 1`, then `r / d` lies inside the
base-`b` length-`L` cylinder `[k / b^L, (k + 1) / b^L)` with `k = r * b^L / d < b^L`, at distance
at least `1 / (d * b^L)` from BOTH endpoints. -/
theorem coprime_rat_cylinder_margin {b d r L : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hcop : Nat.Coprime d b) (hr0 : 1 ≤ r) (hrd : r < d) (hL : 1 ≤ L) :
    let k : ℕ := r * b ^ L / d
    k < b ^ L ∧
      (k : ℝ) / (b : ℝ) ^ L + 1 / ((d : ℝ) * (b : ℝ) ^ L) ≤ (r : ℝ) / (d : ℝ) ∧
      (r : ℝ) / (d : ℝ) + 1 / ((d : ℝ) * (b : ℝ) ^ L) ≤ ((k + 1 : ℕ) : ℝ) / (b : ℝ) ^ L := by
  have _ := hL
  set k : ℕ := r * b ^ L / d
  set rem : ℕ := r * b ^ L % d
  have hd_pos : 0 < d := by omega
  have hb_pos : 0 < b := by omega
  have hdivmod : d * k + rem = r * b ^ L := Nat.div_add_mod (r * b ^ L) d
  have hrem_lt : rem < d := Nat.mod_lt (r * b ^ L) hd_pos
  have hrem_ne : rem ≠ 0 := by
    intro h0
    have hdvd : d ∣ r * b ^ L := Nat.dvd_of_mod_eq_zero h0
    have hcop_pow : Nat.Coprime d (b ^ L) := hcop.pow_right L
    have hdr : d ∣ r := hcop_pow.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) hdr
    omega
  have hrem_ge1 : 1 ≤ rem := by omega
  have hrem_le : rem + 1 ≤ d := by omega
  have hk_lt : k < b ^ L := by
    have hmul : r * b ^ L < b ^ L * d := by
      rw [mul_comm (b ^ L) d]
      exact Nat.mul_lt_mul_of_pos_right hrd (pow_pos hb_pos L)
    exact (Nat.div_lt_iff_lt_mul hd_pos).mpr hmul
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hbL_r : (0 : ℝ) < (b : ℝ) ^ L := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    positivity
  have hdivmod_r : (d : ℝ) * (k : ℝ) + (rem : ℝ) = (r : ℝ) * (b : ℝ) ^ L := by
    exact_mod_cast hdivmod
  refine ⟨hk_lt, ?_, ?_⟩
  · have hrem_r : (1 : ℝ) ≤ (rem : ℝ) := by exact_mod_cast hrem_ge1
    have hdiff : (r : ℝ) / (d : ℝ) - (k : ℝ) / (b : ℝ) ^ L =
        (rem : ℝ) / ((d : ℝ) * (b : ℝ) ^ L) := by
      field_simp [hd_r.ne', hbL_r.ne']
      linarith
    have hge : 1 / ((d : ℝ) * (b : ℝ) ^ L) ≤ (rem : ℝ) / ((d : ℝ) * (b : ℝ) ^ L) :=
      div_le_div_of_nonneg_right hrem_r (by positivity)
    linarith
  · have hrem_r : (rem : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hrem_le
    have hdiff : ((k + 1 : ℕ) : ℝ) / (b : ℝ) ^ L - (r : ℝ) / (d : ℝ) =
        ((d : ℝ) - (rem : ℝ)) / ((d : ℝ) * (b : ℝ) ^ L) := by
      push_cast
      field_simp [hd_r.ne', hbL_r.ne']
      linarith
    have hge : 1 / ((d : ℝ) * (b : ℝ) ^ L) ≤ ((d : ℝ) - (rem : ℝ)) / ((d : ℝ) * (b : ℝ) ^ L) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith

/-- Uniform separation from all `b`-adic grid points `m / b^L` (`m : ℤ`). -/
theorem coprime_rat_dist_grid_ge {b d r L : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hcop : Nat.Coprime d b) (hr0 : 1 ≤ r) (hrd : r < d) (m : ℤ) :
    1 / ((d : ℝ) * (b : ℝ) ^ L) ≤ |(r : ℝ) / (d : ℝ) - (m : ℝ) / (b : ℝ) ^ L| := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    positivity
  have hne : (r : ℤ) * (b : ℤ) ^ L - m * (d : ℤ) ≠ 0 := by
    intro h0
    have heq : (r : ℤ) * (b : ℤ) ^ L = m * (d : ℤ) := sub_eq_zero.mp h0
    have hdvd_z : (d : ℤ) ∣ ((r * b ^ L : ℕ) : ℤ) := ⟨m, by push_cast; linarith⟩
    have hdvd_n : d ∣ r * b ^ L := Int.natCast_dvd_natCast.mp hdvd_z
    have hdr : d ∣ r := (hcop.pow_right L).dvd_of_dvd_mul_right hdvd_n
    have := Nat.le_of_dvd (by omega) hdr
    omega
  have habs_int : (1 : ℤ) ≤ |(r : ℤ) * (b : ℤ) ^ L - m * (d : ℤ)| :=
    Int.one_le_abs hne
  have habs_r : (1 : ℝ) ≤ |(r : ℝ) * (b : ℝ) ^ L - (m : ℝ) * (d : ℝ)| := by
    exact_mod_cast habs_int
  have hrew : |(r : ℝ) / (d : ℝ) - (m : ℝ) / (b : ℝ) ^ L| =
      |(r : ℝ) * (b : ℝ) ^ L - (m : ℝ) * (d : ℝ)| / ((d : ℝ) * (b : ℝ) ^ L) := by
    have hinner : (r : ℝ) / (d : ℝ) - (m : ℝ) / (b : ℝ) ^ L =
        ((r : ℝ) * (b : ℝ) ^ L - (m : ℝ) * (d : ℝ)) / ((d : ℝ) * (b : ℝ) ^ L) := by
      field_simp [hd_pos.ne', hbL_pos.ne']
    rw [hinner, abs_div, abs_of_pos (mul_pos hd_pos hbL_pos)]
  rw [hrew]
  exact div_le_div_of_nonneg_right habs_r (by positivity)

/-- **Cylinder stability under small perturbations:** any `y` within `1 / (d * b^L)` of `r / d`
lies in the same base-`b` length-`L` cylinder `[k / b^L, (k + 1) / b^L)`, hence has the same
first `L` base-`b` digits `⌊b^L * y⌋ = k`. -/
theorem coprime_rat_cylinder_stable {b d r L : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hcop : Nat.Coprime d b) (hr0 : 1 ≤ r) (hrd : r < d) (hL : 1 ≤ L) {y : ℝ}
    (hy : |y - (r : ℝ) / (d : ℝ)| < 1 / ((d : ℝ) * (b : ℝ) ^ L)) :
    let k : ℕ := r * b ^ L / d
    (k : ℝ) / (b : ℝ) ^ L ≤ y ∧ y < ((k + 1 : ℕ) : ℝ) / (b : ℝ) ^ L ∧
      ⌊(b : ℝ) ^ L * y⌋ = (k : ℤ) := by
  have ⟨_, hlow, hhigh⟩ := coprime_rat_cylinder_margin hb hd hcop hr0 hrd hL
  set k : ℕ := r * b ^ L / d
  rw [abs_lt] at hy
  have hy_low : (k : ℝ) / (b : ℝ) ^ L ≤ y := by linarith
  have hy_high : y < ((k + 1 : ℕ) : ℝ) / (b : ℝ) ^ L := by linarith
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    positivity
  have hfloor : ⌊(b : ℝ) ^ L * y⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · have := mul_le_mul_of_nonneg_left hy_low hbL_pos.le
      rwa [mul_div_cancel₀ _ hbL_pos.ne'] at this
    · have := mul_lt_mul_of_pos_left hy_high hbL_pos
      rw [mul_div_cancel₀ _ hbL_pos.ne'] at this
      push_cast at this
      exact this
  exact ⟨hy_low, hy_high, hfloor⟩

/-! ### Part 4: Exact reciprocal period identities (Track D1–D2) -/

/-- For any `b ≥ 1`, `M`, and `n`, `(b : ZMod M)^n = 1 ↔ M ∣ b^n - 1`. -/
private lemma zmod_pow_eq_one_iff_dvd {b M n : ℕ} (hb : 1 ≤ b) :
    (b : ZMod M) ^ n = 1 ↔ M ∣ b ^ n - 1 := by
  have h1 : 1 ≤ b ^ n := one_le_pow₀ hb
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero]

/-- If `D ∣ b^m - 1` with `b ≥ 1` and `m ≥ 1`, then `Nat.Coprime b D`. -/
theorem coprime_of_dvd_pow_sub_one {b D m : ℕ} (hb : 1 ≤ b) (hm : 1 ≤ m) (hdvd : D ∣ b ^ m - 1) :
    Nat.Coprime b D := by
  refine Nat.coprime_iff_gcd_eq_one.mpr ?_
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpb : p ∣ b := hpg.trans (Nat.gcd_dvd_left b D)
  have hpD : p ∣ D := hpg.trans (Nat.gcd_dvd_right b D)
  have hpbm : p ∣ b ^ m := hpb.trans (dvd_pow_self b (by omega))
  have hpbm1 : p ∣ b ^ m - 1 := hpD.trans hdvd
  have h1 : 1 ≤ b ^ m := one_le_pow₀ hb
  have hp1 : p ∣ 1 := by
    have := Nat.dvd_sub hpbm hpbm1
    rwa [Nat.sub_sub_self h1] at this
  exact hp.not_dvd_one hp1

/-- Equivalence `D ∣ b^m - 1 ↔ orderOf (b : ZMod D) ∣ m` for `b ≥ 2`. -/
theorem dvd_pow_sub_one_iff_orderOf_dvd {b D m : ℕ} (hb : 2 ≤ b) :
    D ∣ b ^ m - 1 ↔ orderOf (b : ZMod D) ∣ m := by
  rw [← zmod_pow_eq_one_iff_dvd (by omega), orderOf_dvd_iff_pow_eq_one]

/-- Exact divisibility for pure Mersenne-like bases: `b^m - 1 ∣ b^n - 1 ↔ m ∣ n`
for all `b ≥ 2`, `m ≥ 1`, `n ≥ 1`. -/
theorem pow_sub_one_dvd_pow_sub_one_iff {b m n : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    b ^ m - 1 ∣ b ^ n - 1 ↔ m ∣ n := by
  constructor
  · intro hdvd
    set q := n / m
    set r := n % m
    have hdivmod : m * q + r = n := Nat.div_add_mod n m
    have hr_lt : r < m := Nat.mod_lt n (by omega)
    have hqm : b ^ m - 1 ∣ b ^ (m * q) - 1 := by
      rw [pow_mul]
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (b ^ m) 1 q
    have hsplit : b ^ n - 1 = b ^ r * (b ^ (m * q) - 1) + (b ^ r - 1) := by
      have h1 : 1 ≤ b ^ (m * q) := one_le_pow₀ (by omega)
      have h2 : 1 ≤ b ^ r := one_le_pow₀ (by omega)
      have h3 : b ^ r ≤ b ^ r * b ^ (m * q) := Nat.le_mul_of_pos_right _ h1
      have h4 : b ^ r * b ^ (m * q) = b ^ n := by
        rw [← pow_add, add_comm, hdivmod]
      zify [one_le_pow₀ (show 1 ≤ b by omega), h1, h2]
      have h4z : ((b : ℤ) ^ r) * ((b : ℤ) ^ (m * q)) = (b : ℤ) ^ n := by exact_mod_cast h4
      linarith
    have hdr : b ^ m - 1 ∣ b ^ r - 1 := by
      rw [hsplit] at hdvd
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hqm (b ^ r))).mp hdvd
    have hr0 : r = 0 := by
      by_contra hrne
      have hpos : 0 < b ^ r - 1 := by
        have : 1 < b ^ r := one_lt_pow₀ (by omega) hrne
        omega
      have hlt : b ^ r - 1 < b ^ m - 1 := by
        have hlt_pow : b ^ r < b ^ m := Nat.pow_lt_pow_right (by omega) hr_lt
        have h1 : 1 ≤ b ^ r := one_le_pow₀ (by omega)
        omega
      have hle := Nat.le_of_dvd hpos hdr
      omega
    exact Nat.dvd_of_mod_eq_zero hr0
  · rintro ⟨q, rfl⟩
    rw [pow_mul]
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (b ^ m) 1 q

/-- Lifting-the-Exponent at `p = 2` when `4 ∣ g - 1` and `g` is odd. -/
private lemma factorization_two_pow_sub_one_of_four_dvd {g k : ℕ} (hg : 1 < g) (hk : 0 < k)
    (h4 : 4 ∣ g - 1) (hodd : ¬ 2 ∣ g) :
    (g ^ k - 1).factorization 2 = (g - 1).factorization 2 + k.factorization 2 := by
  have hgk : 1 < g ^ k := one_lt_pow₀ hg hk.ne'
  have hd : (4 : ℤ) ∣ ((g - 1 : ℕ) : ℤ) := by exact_mod_cast h4
  rw [Int.natCast_sub hg.le, Int.natCast_one] at hd
  have hlift := Int.two_pow_sub_pow' (x := g) (y := 1) k hd (by exact_mod_cast hodd)
  have heqn : emultiplicity 2 (g ^ k - 1) = emultiplicity 2 (g - 1) + emultiplicity 2 k := by
    rw [← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity]
    simpa only [Int.natCast_sub hgk.le, Int.natCast_sub hg.le, Int.natCast_pow, Int.natCast_one,
      Nat.cast_ofNat, one_pow] using hlift
  simp only [← Nat.multiplicity_eq_factorization Nat.prime_two]
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  simpa only [multiplicity_eq_emultiplicity (Nat.sub_ne_zero_of_lt hgk),
    multiplicity_eq_emultiplicity (Nat.sub_ne_zero_of_lt hg),
    multiplicity_eq_emultiplicity hk.ne'] using heqn

/-- When `g ≡ 3 (mod 4)` and `k ≥ 1`, `4 ∣ g^k - 1 ↔ 2 ∣ k`. -/
private lemma four_dvd_pow_sub_one_iff_of_mod_four_eq_three {g k : ℕ} (hg : 1 < g)
    (hodd : ¬ 2 ∣ g) (hn4 : ¬ 4 ∣ g - 1) :
    4 ∣ g ^ k - 1 ↔ 2 ∣ k := by
  have hg_mod4 : g % 4 = 3 := by omega
  have hg_zmod : (g : ZMod 4) = -1 := by
    have : (g : ZMod 4) = ((g % 4 : ℕ) : ZMod 4) := by
      rw [← ZMod.natCast_mod]
    rw [this, hg_mod4]
    decide
  rw [← zmod_pow_eq_one_iff_dvd (by omega), hg_zmod]
  constructor
  · intro hpow
    by_contra hnot
    have hodd_k : Odd k := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
    rw [hodd_k.neg_one_pow] at hpow
    exact absurd hpow (by decide)
  · rintro ⟨j, rfl⟩
    rw [pow_mul, show (-1 : ZMod 4) ^ 2 = 1 by decide, one_pow]

/-- Prime-by-prime LTE equivalence: for `g > 1`, `D > 0`, `k > 0`, `D ∣ g - 1`, and any prime `p`,
`v_p(D * (g - 1)) ≤ v_p(g^k - 1) ↔ v_p(D) ≤ v_p(k)` with zero exceptions (covering odd primes,
`p = 2` with `4 ∣ g - 1`, and `p = 2` with `g ≡ 3 mod 4`). -/
private lemma factorization_le_iff_of_dvd_sub_one {g D k p : ℕ}
    (hg : 1 < g) (hD : 0 < D) (hk : 0 < k) (hdvd : D ∣ g - 1) (hp : p.Prime) :
    (D * (g - 1)).factorization p ≤ (g ^ k - 1).factorization p ↔
      D.factorization p ≤ k.factorization p := by
  have hg1_ne : g - 1 ≠ 0 := by omega
  have hgk_gt : 1 < g ^ k := one_lt_pow₀ hg hk.ne'
  have hgk1_ne : g ^ k - 1 ≠ 0 := by omega
  rw [Nat.factorization_mul hD.ne' hg1_ne, Finsupp.add_apply]
  by_cases hpg : p ∣ g - 1
  · have hnot : ¬ p ∣ g := by
      intro h
      have h1 := Nat.dvd_sub h hpg
      rw [Nat.sub_sub_self hg.le] at h1
      exact hp.not_dvd_one h1
    by_cases hp2 : p = 2
    · subst p
      by_cases h4 : 4 ∣ g - 1
      · rw [factorization_two_pow_sub_one_of_four_dvd hg hk h4 hnot]
        omega
      · -- Here `v_2(g - 1) = 1`, and `D ∣ g - 1` forces `v_2(D) ≤ 1`.
        have hv_g1 : (g - 1).factorization 2 = 1 := by
          have hge1 : 1 ≤ (g - 1).factorization 2 :=
            (Nat.prime_two.pow_dvd_iff_le_factorization hg1_ne).mp (by rw [pow_one]; exact hpg)
          have hlt2 : (g - 1).factorization 2 < 2 := by
            by_contra hge2
            push Not at hge2
            have := (Nat.prime_two.pow_dvd_iff_le_factorization hg1_ne).mpr hge2
            exact h4 this
          omega
        have hv_D_le : D.factorization 2 ≤ 1 := by
          have := (Nat.factorization_le_iff_dvd hD.ne' hg1_ne).mpr hdvd 2
          omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv_D_le with hD0 | hD1
        · rw [hD0, zero_add, hv_g1]
          have hge1 : 1 ≤ (g ^ k - 1).factorization 2 := by
            have hd2 : 2 ∣ g ^ k - 1 := hpg.trans (by
              simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow g 1 k)
            exact (Nat.prime_two.pow_dvd_iff_le_factorization hgk1_ne).mp (by rw [pow_one]; exact hd2)
          simp [hge1]
        · rw [hD1, hv_g1]
          have hleft : 2 ≤ (g ^ k - 1).factorization 2 ↔ 4 ∣ g ^ k - 1 := by
            rw [← Nat.prime_two.pow_dvd_iff_le_factorization hgk1_ne]
            norm_num
          have hright : 1 ≤ k.factorization 2 ↔ 2 ∣ k := by
            rw [← Nat.prime_two.pow_dvd_iff_le_factorization hk.ne', pow_one]
          rw [show 1 + 1 = 2 by rfl, hleft, hright]
          exact four_dvd_pow_sub_one_iff_of_mod_four_eq_three hg hnot h4
    · have : Fact p.Prime := ⟨hp⟩
      have hlift : (g ^ k - 1).factorization p = (g - 1).factorization p + k.factorization p := by
        simpa only [one_pow, Nat.multiplicity_eq_factorization hp] using
          Nat.multiplicity_pow_sub_pow (hp.odd_of_ne_two hp2) hg hpg hnot hk.ne'
      rw [hlift]
      omega
  · have hpD : ¬ p ∣ D := fun h => hpg (h.trans hdvd)
    rw [Nat.factorization_eq_zero_of_not_dvd hpD, Nat.factorization_eq_zero_of_not_dvd hpg, add_zero]
    simp

/-- **Complete divisibility criterion for `D * (b^m - 1)`:**
for every `b ≥ 2`, `D ≥ 1`, `m ≥ 1`, `n ≥ 1` with `D ∣ b^m - 1`,
`D * (b^m - 1) ∣ b^n - 1 ↔ m * D ∣ n`. -/
theorem mul_pow_sub_one_dvd_pow_sub_one_iff {b D m n : ℕ} (hb : 2 ≤ b) (hD : 1 ≤ D)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hdvd : D ∣ b ^ m - 1) :
    D * (b ^ m - 1) ∣ b ^ n - 1 ↔ m * D ∣ n := by
  have hg : 1 < b ^ m := one_lt_pow₀ (by omega) (by omega)
  have hbn1_ne : b ^ n - 1 ≠ 0 := by
    have : 1 < b ^ n := one_lt_pow₀ (by omega) (by omega)
    omega
  have hM_ne : D * (b ^ m - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  constructor
  · intro hM_dvd
    have hbm_dvd : b ^ m - 1 ∣ b ^ n - 1 := (dvd_mul_left (b ^ m - 1) D).trans hM_dvd
    have hm_dvd : m ∣ n := (pow_sub_one_dvd_pow_sub_one_iff hb hm hn).mp hbm_dvd
    obtain ⟨k, rfl⟩ := hm_dvd
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · omega
      · exact hk_pos
    rw [pow_mul] at hM_dvd hbn1_ne
    have hDk : D ∣ k := by
      refine (Nat.factorization_prime_le_iff_dvd (by omega) hk.ne').mp (fun p hp => ?_)
      have hle := (Nat.factorization_prime_le_iff_dvd hM_ne hbn1_ne).mpr hM_dvd p hp
      exact (factorization_le_iff_of_dvd_sub_one hg (by omega) hk hdvd hp).mp hle
    exact mul_dvd_mul_left m hDk
  · intro hmD_dvd
    obtain ⟨q, rfl⟩ := hmD_dvd
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | hq_pos
      · omega
      · exact hq_pos
    have hDq_pos : 0 < D * q := Nat.mul_pos (by omega) hq
    rw [mul_assoc, pow_mul] at hbn1_ne ⊢
    refine (Nat.factorization_prime_le_iff_dvd hM_ne hbn1_ne).mp (fun p hp => ?_)
    refine (factorization_le_iff_of_dvd_sub_one hg (by omega) hDq_pos hdvd hp).mpr ?_
    exact (Nat.factorization_prime_le_iff_dvd (by omega) hDq_pos.ne').mpr (dvd_mul_right D q) p hp

/-- **Exact reciprocal period identity for `D * (b^m - 1)` (Track D1–D2):**
for every `b ≥ 2`, `D ≥ 1`, and `m ≥ 1` with `D ∣ b^m - 1`,
`orderOf (b : ZMod (D * (b^m - 1))) = m * D` with ZERO exceptions. -/
theorem orderOf_mul_pow_sub_one {b D m : ℕ} (hb : 2 ≤ b) (hD : 1 ≤ D) (hm : 1 ≤ m)
    (hdvd : D ∣ b ^ m - 1) :
    orderOf (b : ZMod (D * (b ^ m - 1))) = m * D := by
  have hmD_pos : 1 ≤ m * D := Nat.mul_pos hm hD
  have hpow : (b : ZMod (D * (b ^ m - 1))) ^ (m * D) = 1 :=
    (zmod_pow_eq_one_iff_dvd (by omega)).mpr
      ((mul_pow_sub_one_dvd_pow_sub_one_iff hb hD hm hmD_pos hdvd).mpr dvd_rfl)
  have hord_dvd : orderOf (b : ZMod (D * (b ^ m - 1))) ∣ m * D :=
    orderOf_dvd_of_pow_eq_one hpow
  have hord_pos : 0 < orderOf (b : ZMod (D * (b ^ m - 1))) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * D, hmD_pos, hpow⟩)
  have hmD_dvd : m * D ∣ orderOf (b : ZMod (D * (b ^ m - 1))) :=
    (mul_pow_sub_one_dvd_pow_sub_one_iff hb hD hm hord_pos hdvd).mp
      ((zmod_pow_eq_one_iff_dvd (by omega)).mp (pow_orderOf_eq_one _))
  exact Nat.dvd_antisymm hord_dvd hmD_dvd

/-- Equivalent formulation of `orderOf_mul_pow_sub_one` assuming `orderOf (b : ZMod D) ∣ m`. -/
theorem orderOf_mul_pow_sub_one_of_orderOf {b D m : ℕ} (hb : 2 ≤ b) (hD : 1 ≤ D) (hm : 1 ≤ m)
    (hord : orderOf (b : ZMod D) ∣ m) :
    orderOf (b : ZMod (D * (b ^ m - 1))) = m * D :=
  orderOf_mul_pow_sub_one hb hD hm ((dvd_pow_sub_one_iff_orderOf_dvd hb).mpr hord)

/-- **Exact reciprocal period identity for `D * (b^m + 1)` (Track D1–D2):**
for every `b ≥ 2`, `D ≥ 1`, and `m ≥ 1` with `D ∣ b^m - 1`,
`orderOf (b : ZMod (D * (b^m + 1))) = 2 * m` with ZERO exceptions. -/
theorem orderOf_mul_pow_add_one {b D m : ℕ} (hb : 2 ≤ b) (hD : 1 ≤ D) (hm : 1 ≤ m)
    (hdvd : D ∣ b ^ m - 1) :
    orderOf (b : ZMod (D * (b ^ m + 1))) = 2 * m := by
  have _ := hD
  set M : ℕ := D * (b ^ m + 1)
  have hbm_ge1 : 1 ≤ b ^ m := one_le_pow₀ (by omega)
  have hsq : (b ^ m - 1) * (b ^ m + 1) = b ^ (2 * m) - 1 := by
    have h2m : 1 ≤ b ^ (2 * m) := one_le_pow₀ (by omega)
    zify [hbm_ge1, h2m]
    rw [mul_comm 2 m, pow_mul]
    ring
  have hM_dvd : M ∣ b ^ (2 * m) - 1 := by
    rw [← hsq]
    exact mul_dvd_mul_right hdvd (b ^ m + 1)
  have hpow : (b : ZMod M) ^ (2 * m) = 1 :=
    (zmod_pow_eq_one_iff_dvd (by omega)).mpr hM_dvd
  set t : ℕ := orderOf (b : ZMod M)
  have ht_pos : 0 < t :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * m, by omega, hpow⟩)
  have ht_dvd : t ∣ 2 * m := orderOf_dvd_of_pow_eq_one hpow
  have ht_le : t ≤ 2 * m := Nat.le_of_dvd (by omega) ht_dvd
  have hbt_dvd : b ^ m + 1 ∣ b ^ t - 1 := by
    have hM_t : M ∣ b ^ t - 1 :=
      (zmod_pow_eq_one_iff_dvd (by omega)).mp (pow_orderOf_eq_one (b : ZMod M))
    exact (dvd_mul_left (b ^ m + 1) D).trans hM_t
  by_contra hne
  have ht_lt : t < 2 * m := by omega
  by_cases htm : t ≤ m
  · have hpos : 0 < b ^ t - 1 := by
      have : 1 < b ^ t := one_lt_pow₀ (by omega) ht_pos.ne'
      omega
    have hlt : b ^ t - 1 < b ^ m + 1 := by
      have : b ^ t ≤ b ^ m := Nat.pow_le_pow_right (by omega) htm
      omega
    have hle := Nat.le_of_dvd hpos hbt_dvd
    omega
  · push Not at htm
    set s : ℕ := t - m
    have hs_pos : 0 < s := by omega
    have hs_lt : s < m := by omega
    have hms : m + s = t := by omega
    have hsum : (b ^ t - 1) + (b ^ s + 1) = (b ^ m + 1) * b ^ s := by
      have h1 : 1 ≤ b ^ t := one_le_pow₀ (by omega)
      zify [h1]
      rw [← hms, pow_add]
      ring
    have hdvd_bs : b ^ m + 1 ∣ b ^ s + 1 := by
      have hprod : b ^ m + 1 ∣ (b ^ t - 1) + (b ^ s + 1) := by
        rw [hsum]
        exact dvd_mul_right (b ^ m + 1) (b ^ s)
      exact (Nat.dvd_add_right hbt_dvd).mp hprod
    have hlt : b ^ s + 1 < b ^ m + 1 := by
      have : b ^ s < b ^ m := Nat.pow_lt_pow_right (by omega) hs_lt
      omega
    have hle := Nat.le_of_dvd (by positivity) hdvd_bs
    omega

/-- Equivalent formulation of `orderOf_mul_pow_add_one` assuming `orderOf (b : ZMod D) ∣ m`. -/
theorem orderOf_mul_pow_add_one_of_orderOf {b D m : ℕ} (hb : 2 ≤ b) (hD : 1 ≤ D) (hm : 1 ≤ m)
    (hord : orderOf (b : ZMod D) ∣ m) :
    orderOf (b : ZMod (D * (b ^ m + 1))) = 2 * m :=
  orderOf_mul_pow_add_one hb hD hm ((dvd_pow_sub_one_iff_orderOf_dvd hb).mpr hord)

end NormalityChecker.RadixPowerTower
