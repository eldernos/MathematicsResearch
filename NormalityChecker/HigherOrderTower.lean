module

public import NormalityChecker.SimpleNormalityKernel
public import NormalityChecker.RadixPowerTower
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Higher-order normality in the radix-power kernel tower

Kernel-checked theorems for Phase 23 (`notes/phase23/euler-square-and-higher-order-tower.md`,
§§3–6):

1. **Core definitions and order monotonicity:**
   - `OrderNormal b L x`: every base-`b` length-`L` word `v < b^L` has asymptotic frequency `1 / b^L`.
   - `Kernel b`: the extreme-discrepancy kernel `{x | D_N(x; b) → 1}`.
   - `cyclicCount b k L r v`: exact count of shifts `j < k` reading length-`L` word `v` from
     the periodic rational `r / (b^k - 1)`.
   - `orderNormal_of_le`: `L`-normality implies `L'`-normality for every `1 ≤ L' ≤ L`.

2. **Kernel decomposition and fixed-center stabilization (`K_b = F_b + M_b`):**
   - `mem_kernel_iff_exists_fixedPoint_add_zeroOrbit` and `kernel_eq_fixedPoint_add_zeroOrbit`:
     for every `b ≥ 2`, `x ∈ K_b ↔ ∃ m : ℤ, ∃ u ∈ M_b, x = m / (b - 1) + u`.
   - `mem_pow_kernel_decomp`: for `b ≥ 2`, `k ≥ 2`, and `x ∈ K_{b^k}`, there exist unique
     `r < b^k - 1` and `u ∈ M_b` with `x = r / (b^k - 1) + u`, and
     `x ∈ K_b ↔ b^k - 1 ∣ (b - 1) * r`.

3. **Coprime-rational cylinder word-frequency transfer:**
   - `wordFreq_tower_limit`: for `b ≥ 2`, `k ≥ 2`, `L ≥ 1`, `0 < r < b^k - 1`, and `u ∈ M_b`,
     `wordFreq b L (r / (b^k - 1) + u) v N → cyclicCount b k L r v / k`.

4. **Euler circuits and balanced de Bruijn blocks:**
   - `exists_euler_circuit`: Hierholzer's theorem for finite balanced strongly-connected
     directed multigraphs.
   - `exists_balanced_block`: for all `b ≥ 2` and `L ≥ 1`, there exists `0 < r < b^(b^L) - 1`
     hitting every length-`L` word exactly once and every length-`(L + 1)` word at most once.

5. **Irrational sparse zero-orbit perturbation:**
   - `sparseQuadPerturb b = ∑' k, b^(-(k + 1)(k + 2))` belongs to `M_b` and is irrational.

6. **Higher-order tower classification:**
   - `tower_iff`: `(∃ x, x ∈ K_{b^k} \ K_b ∧ OrderNormal b L x) ↔ b^L ∣ k`.
   - `tower_irrational_exact_iff`:
     `(∃ x, Irrational x ∧ x ∈ K_{b^k} \ K_b ∧ OrderNormal b L x ∧ ¬ OrderNormal b (L + 1) x) ↔ b^L ∣ k`.
   - `all_kernel_pow_iff`:
     `(∃ x, x ∈ K_{b^k} ∧ OrderNormal b L x) ↔ b^L ∣ k ∨ (b = 2 ∧ L = 1)`.

7. **Universal `L`-normal discrepancy upper bound:**
   - `radixDiscrepancy_le_grid_add`:
     `D_N(x; b) ≤ 2 / b^L + ∑_{v < b^L} |wordFreq b L x v N - 1 / b^L|`.
   - `eventually_radixDiscrepancy_le_of_orderNormal` and
     `limsup_radixDiscrepancy_le_of_orderNormal`: every `L`-normal real satisfies
     `D^+(x; b) ≤ 2 / b^L`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.HigherOrderTower

open SimpleNormalityKernel RadixPowerTower SharpTranslation DiscrepancyGeometry
  ClassicalBarriers Phase18Synthetic

/-! ### Part 1: Core definitions and order monotonicity -/

/-- A real number `x` is `L`-normal in base `b` if every base-`b` word `v < b^L` of length `L`
has asymptotic frequency `1 / b^L`. -/
def OrderNormal (b L : ℕ) (x : ℝ) : Prop :=
  ∀ v < b ^ L, Tendsto (wordFreq b L x v) atTop (𝓝 (1 / (b : ℝ) ^ L))

/-- The extreme-discrepancy kernel `K_b = {x ∈ ℝ | D_N(x; b) → 1}`. -/
def Kernel (b : ℕ) : Set ℝ :=
  {x | Tendsto (radixDiscrepancy b x) atTop (𝓝 1)}

/-- Number of cyclic shifts `j < k` at which the periodic rational `r / (b^k - 1)` reads the
base-`b` length-`L` word `v`. -/
def cyclicCount (b k L r v : ℕ) : ℕ :=
  let q := b ^ k - 1
  ((range k).filter fun j => b ^ L * (b ^ j * r % q) / q = v).card

/-- Auxiliary floor-division identity: `⌊b^(L' + d) * t⌋₊ / b^d = ⌊b^L' * t⌋₊` for `t ≥ 0`. -/
private lemma natFloor_pow_add_div {b L' d : ℕ} (hb : 1 ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    ⌊(b : ℝ) ^ (L' + d) * t⌋₊ / b ^ d = ⌊(b : ℝ) ^ L' * t⌋₊ := by
  have hbd_pos : 0 < b ^ d := pow_pos (by omega) d
  have hbd_r : (0 : ℝ) < (b : ℝ) ^ d := by exact_mod_cast hbd_pos
  have hbL'_r : (0 : ℝ) < (b : ℝ) ^ L' := pow_pos (by exact_mod_cast (show 0 < b by omega)) L'
  have hle : (⌊(b : ℝ) ^ L' * t⌋₊ : ℝ) * (b : ℝ) ^ d ≤ (b : ℝ) ^ (L' + d) * t := by
    rw [pow_add, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (mul_nonneg hbL'_r.le ht)) hbd_r.le
  have hlt : (b : ℝ) ^ (L' + d) * t < ((⌊(b : ℝ) ^ L' * t⌋₊ : ℝ) + 1) * (b : ℝ) ^ d := by
    rw [pow_add, mul_right_comm]
    exact mul_lt_mul_of_pos_right (Nat.lt_floor_add_one _) hbd_r
  have h1 : ⌊(b : ℝ) ^ L' * t⌋₊ * b ^ d ≤ ⌊(b : ℝ) ^ (L' + d) * t⌋₊ := by
    rw [Nat.le_floor_iff (mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) ht)]
    push_cast
    exact hle
  have h2 : ⌊(b : ℝ) ^ (L' + d) * t⌋₊ < (⌊(b : ℝ) ^ L' * t⌋₊ + 1) * b ^ d := by
    rw [Nat.floor_lt (mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) ht)]
    push_cast
    exact hlt
  have hdiv1 : ⌊(b : ℝ) ^ L' * t⌋₊ ≤ ⌊(b : ℝ) ^ (L' + d) * t⌋₊ / b ^ d :=
    (Nat.le_div_iff_mul_le hbd_pos).mpr h1
  have hdiv2 : ⌊(b : ℝ) ^ (L' + d) * t⌋₊ / b ^ d < ⌊(b : ℝ) ^ L' * t⌋₊ + 1 :=
    (Nat.div_lt_iff_lt_mul hbd_pos).mpr h2
  omega

/-- Counting a length-`L'` word equals the sum of counts of its `b^(L - L')` length-`L` extensions. -/
theorem wordCount_eq_sum_extensions {b L' L : ℕ} (hb : 1 ≤ b) (hL : L' ≤ L) (x : ℝ) (w N : ℕ) :
    wordCount b L' x w N =
      ∑ t ∈ range (b ^ (L - L')), wordCount b L x (w * b ^ (L - L') + t) N := by
  set d := L - L'
  have hLd : L' + d = L := by omega
  have hbd_pos : 0 < b ^ d := pow_pos (by omega) d
  unfold wordCount
  rw [← Finset.card_biUnion]
  · congr 1
    ext n
    simp only [mem_biUnion, mem_filter, mem_range]
    constructor
    · rintro ⟨hn, hw⟩
      set v := ⌊(b : ℝ) ^ L * shift b x n⌋₊
      have hv_div : v / b ^ d = w := by
        dsimp only [v]
        rw [← hLd, natFloor_pow_add_div hb (show 0 ≤ shift b x n from Int.fract_nonneg _), hw]
      refine ⟨v % b ^ d, Nat.mod_lt v hbd_pos, hn, ?_⟩
      have hdm := Nat.div_add_mod v (b ^ d)
      rw [hv_div, mul_comm (b ^ d) w] at hdm
      exact hdm.symm
    · rintro ⟨t, ht, hn, hv⟩
      refine ⟨hn, ?_⟩
      have hdiv := natFloor_pow_add_div (b := b) (L' := L') (d := d) hb
        (show 0 ≤ shift b x n from Int.fract_nonneg _)
      rw [hLd, hv] at hdiv
      rw [← hdiv, mul_comm w (b ^ d), Nat.mul_add_div hbd_pos, Nat.div_eq_of_lt ht, add_zero]
  · intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n h1 h2
    have e1 := (mem_filter.mp h1).2
    have e2 := (mem_filter.mp h2).2
    omega

/-- Finite-sum `Tendsto` helper avoiding extra topology imports. -/
private lemma tendsto_finset_sum' {ι α : Type*} {f : ι → α → ℝ} {l : Filter α}
    (s : Finset ι) {a : ι → ℝ} (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) l (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tendsto_const_nhds]
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- `L`-normality implies `L'`-normality for every lower order `L' ≤ L`. -/
theorem orderNormal_of_le {b L' L : ℕ} (hb : 1 ≤ b) (hL : L' ≤ L) {x : ℝ}
    (hx : OrderNormal b L x) : OrderNormal b L' x := by
  intro w hw
  set d := L - L'
  have hLd : L' + d = L := by omega
  have hbd_pos : (0 : ℝ) < (b : ℝ) ^ d := pow_pos (by exact_mod_cast (show 0 < b by omega)) d
  have hbL'_pos : (0 : ℝ) < (b : ℝ) ^ L' := pow_pos (by exact_mod_cast (show 0 < b by omega)) L'
  have hfreq_eq : wordFreq b L' x w =
      fun N => ∑ t ∈ range (b ^ d), wordFreq b L x (w * b ^ d + t) N := by
    funext N
    unfold wordFreq
    rw [wordCount_eq_sum_extensions hb hL x w N, Nat.cast_sum, Finset.sum_div]
  rw [hfreq_eq]
  have hsum_tend : Tendsto (fun N => ∑ t ∈ range (b ^ d), wordFreq b L x (w * b ^ d + t) N)
      atTop (𝓝 (∑ _t ∈ range (b ^ d), (1 / (b : ℝ) ^ L))) := by
    refine tendsto_finset_sum' _ fun t ht => ?_
    have ht_lt : t < b ^ d := mem_range.mp ht
    have hval_lt : w * b ^ d + t < b ^ L := by
      have h1 : (w + 1) * b ^ d ≤ b ^ L' * b ^ d := Nat.mul_le_mul_right (b ^ d) hw
      rw [← pow_add, hLd] at h1
      nlinarith
    exact hx (w * b ^ d + t) hval_lt
  have hlim_eq : ∑ _t ∈ range (b ^ d), (1 / (b : ℝ) ^ L) = 1 / (b : ℝ) ^ L' := by
    rw [Finset.sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, ← hLd, pow_add]
    field_simp [hbd_pos.ne', hbL'_pos.ne']
  rwa [hlim_eq] at hsum_tend

/-! ### Part 2: Kernel decomposition and fixed-center stabilization (`K_b = F_b + M_b`) -/

/-- `SimpleNormalityKernel.distInt` and `RadixPowerTower.circDist` coincide definitionally. -/
private lemma distInt_eq_circDist (t : ℝ) : distInt t = circDist t := rfl

/-- Markov's inequality for `farCount`: `farCount b u ε N / N ≤ circMean b u N / ε`. -/
theorem farCount_div_le_circMean (b : ℕ) (u : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (farCount b u ε N : ℝ) / (N : ℝ) ≤ circMean b u N / ε := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [farCount, circMean]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set S := (range N).filter (fun n => ¬ Near ((b : ℝ) ^ n * u) ε)
  have hsum : (S.card : ℝ) * ε ≤ ∑ n ∈ range N, circDist (shift b u n) := by
    calc (S.card : ℝ) * ε
        = ∑ _n ∈ S, ε := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ S, circDist (shift b u n) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hfar := (mem_filter.mp hn).2
          rw [near_iff_distInt_le, distInt_eq_circDist, not_le] at hfar
          unfold shift
          rw [circDist_fract]
          exact hfar.le
      _ ≤ ∑ n ∈ range N, circDist (shift b u n) :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => circDist_nonneg _)
  unfold farCount circMean
  rw [div_div, div_le_div_iff₀ hNr (mul_pos hNr hε)]
  nlinarith

/-- If `u ∈ zeroOrbitSubgroup b`, then `farCount b u ε N / N → 0` for every `ε > 0`. -/
theorem farCount_div_tendsto_zero_of_mem_zeroOrbit {b : ℕ} {u : ℝ}
    (hu : u ∈ zeroOrbitSubgroup b) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => (farCount b u ε N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => circMean b u N / ε) atTop (𝓝 0) := by
    have h1 := hu.div_const ε
    simpa using h1
  exact squeeze_zero (fun N => by positivity) (fun N => farCount_div_le_circMean b u hε N) hupper

/-- Every element of the zero-orbit subgroup `M_b` belongs to the discrepancy kernel `K_b`. -/
theorem zeroOrbit_subset_kernel (b : ℕ) {u : ℝ} (hu : u ∈ zeroOrbitSubgroup b) :
    u ∈ Kernel b := by
  have hdiff := discrepancy_transfer_tendsto b 0 u
    (fun _ hε => farCount_div_tendsto_zero_of_mem_zeroOrbit hu hε)
  have h0 : (fun N => radixDiscrepancy b (0 + u) N - radixDiscrepancy b 0 N) =
      fun N => radixDiscrepancy b u N - 1 := by
    funext N
    rw [zero_add, radixDiscrepancy_zero]
  rw [h0] at hdiff
  have h1 := hdiff.add (tendsto_const_nhds (x := (1 : ℝ)))
  simpa [Kernel] using h1

/-- Every fixed-point translate `m / (b - 1) + u` with `u ∈ M_b` belongs to `K_b`. -/
theorem fixedPoint_add_zeroOrbit_mem_kernel {b : ℕ} (hb : 2 ≤ b) (m : ℤ)
    {u : ℝ} (hu : u ∈ zeroOrbitSubgroup b) :
    (m : ℝ) / ((b : ℝ) - 1) + u ∈ Kernel b := by
  set c : ℝ := (m : ℝ) / ((b : ℝ) - 1)
  have hbm1_ne : (b : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hc_one : ∀ N ≥ 2, radixDiscrepancy b c N = 1 := by
    intro N hN
    have h0 : discDist b N c 0 = 0 := by
      rw [discDist_eq_zero_iff b hN]
      exact ⟨m, by dsimp [c]; field_simp [hbm1_ne]; ring⟩
    unfold discDist at h0
    rw [sub_zero] at h0
    linarith
  have hdiff := discrepancy_transfer_tendsto b c u
    (fun _ hε => farCount_div_tendsto_zero_of_mem_zeroOrbit hu hε)
  have hev : (fun N => radixDiscrepancy b (c + u) N - radixDiscrepancy b c N) =ᶠ[atTop]
      fun N => radixDiscrepancy b (c + u) N - 1 := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [hc_one N hN]
  rw [tendsto_congr' hev] at hdiff
  have h1 := hdiff.add (tendsto_const_nhds (x := (1 : ℝ)))
  simpa [Kernel] using h1

/-- Integer shifts belong to `zeroOrbitSubgroup b`. -/
theorem intCast_mem_zeroOrbit (b : ℕ) (z : ℤ) : (z : ℝ) ∈ zeroOrbitSubgroup b := by
  change Tendsto (circMean b (z : ℝ)) atTop (𝓝 0)
  have h0 : circMean b (z : ℝ) = fun _ => 0 := by
    funext N
    unfold circMean
    have hsum : ∑ n ∈ range N, circDist (shift b (z : ℝ) n) = 0 := by
      refine Finset.sum_eq_zero fun n _ => ?_
      unfold shift
      have : (b : ℝ) ^ n * (z : ℝ) = (((b : ℤ) ^ n * z : ℤ) : ℝ) := by push_cast; ring
      rw [this, Int.fract_intCast]
      simp [circDist]
    rw [hsum, zero_div]
  rw [h0]
  exact tendsto_const_nhds

/-- Separation between distinct fixed points `j₁ / (b - 1)` and `j₂ / (b - 1)` with `j₁, j₂ < b - 1`. -/
private lemma circDist_fixedPoint_sub_ge {b j₁ j₂ : ℕ} (hb : 2 ≤ b)
    (hj₁ : j₁ + 2 ≤ b) (hj₂ : j₂ + 2 ≤ b) (hne : j₁ ≠ j₂) :
    1 / ((b : ℝ) - 1) ≤ circDist ((j₁ : ℝ) / ((b : ℝ) - 1) - (j₂ : ℝ) / ((b : ℝ) - 1)) := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  obtain ⟨z, hz⟩ := exists_int_abs_sub_eq_circDist ((j₁ : ℝ) / ((b : ℝ) - 1) - (j₂ : ℝ) / ((b : ℝ) - 1))
  rw [← hz]
  have hnum_ne : ((j₁ : ℤ) - (j₂ : ℤ)) - z * ((b : ℤ) - 1) ≠ 0 := by
    intro h0
    have hdvd : ((b : ℤ) - 1) ∣ ((j₁ : ℤ) - (j₂ : ℤ)) := ⟨z, by linarith⟩
    obtain ⟨q, hq⟩ := hdvd
    have hq_ne : q ≠ 0 := by
      intro hq0; rw [hq0, mul_zero] at hq; omega
    rcases lt_or_gt_of_ne hq_ne with hq_neg | hq_pos
    · have : q ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ q := by omega
      nlinarith
  have h1 : (1 : ℤ) ≤ |((j₁ : ℤ) - (j₂ : ℤ)) - z * ((b : ℤ) - 1)| := Int.one_le_abs hnum_ne
  have h1r : (1 : ℝ) ≤ |((j₁ : ℝ) - (j₂ : ℝ)) - (z : ℝ) * ((b : ℝ) - 1)| := by exact_mod_cast h1
  have hrew : (j₁ : ℝ) / ((b : ℝ) - 1) - (j₂ : ℝ) / ((b : ℝ) - 1) - (z : ℝ) =
      (((j₁ : ℝ) - (j₂ : ℝ)) - (z : ℝ) * ((b : ℝ) - 1)) / ((b : ℝ) - 1) := by
    field_simp [hbm1_pos.ne']
  rw [hrew, abs_div, abs_of_pos hbm1_pos]
  exact div_le_div_of_nonneg_right h1r hbm1_pos.le

/-- Shifting `x - j / (b - 1)` by `b^n` preserves circle distance to `j / (b - 1)`. -/
private lemma circDist_shift_sub_fixedPoint {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (j n : ℕ) :
    circDist (shift b (x - (j : ℝ) / ((b : ℝ) - 1)) n) =
      circDist (shift b x n - (j : ℝ) / ((b : ℝ) - 1)) := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbm1_ne : (b : ℝ) - 1 ≠ 0 := by linarith
  have hrep : (repunit b n : ℝ) * ((b : ℝ) - 1) = (b : ℝ) ^ n - 1 := by
    exact_mod_cast repunit_mul_sub_one b n
  have hpow_j : (b : ℝ) ^ n * ((j : ℝ) / ((b : ℝ) - 1)) =
      (j : ℝ) / ((b : ℝ) - 1) + (((j * repunit b n : ℕ) : ℤ) : ℝ) := by
    push_cast
    field_simp [hbm1_ne]
    linear_combination -(j : ℝ) * hrep
  unfold shift
  rw [circDist_fract]
  have hrew : (b : ℝ) ^ n * (x - (j : ℝ) / ((b : ℝ) - 1)) =
      (Int.fract ((b : ℝ) ^ n * x) - (j : ℝ) / ((b : ℝ) - 1)) +
        ((⌊(b : ℝ) ^ n * x⌋ - ((j * repunit b n : ℕ) : ℤ) : ℤ) : ℝ) := by
    have hf := Int.fract_add_floor ((b : ℝ) ^ n * x)
    push_cast
    rw [mul_sub, hpow_j]
    push_cast
    linarith
  rw [hrew, circDist_add_intCast]

/-- **Kernel decomposition with fixed-center stabilization (`K_b = F_b + M_b`):**
for every `b ≥ 2`, `x ∈ K_b` if and only if `x = m / (b - 1) + u` for some `m : ℤ` and
`u ∈ zeroOrbitSubgroup b`. -/
theorem mem_kernel_iff_exists_fixedPoint_add_zeroOrbit {b : ℕ} (hb : 2 ≤ b) {x : ℝ} :
    x ∈ Kernel b ↔ ∃ m : ℤ, ∃ u ∈ zeroOrbitSubgroup b, x = (m : ℝ) / ((b : ℝ) - 1) + u := by
  classical
  constructor
  · intro hx
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have hb_pos : (0 : ℝ) < b := by linarith
    have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
    have hdef : Tendsto (fun N => 1 - radixDiscrepancy b x N) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx
    -- Fix `N₀ ≥ 4` such that for all `N ≥ N₀`, `δ_N < 1 / (4 * b)`.
    have hev : ∀ᶠ N in atTop, 4 ≤ N ∧ 1 - radixDiscrepancy b x N < 1 / (4 * (b : ℝ)) := by
      filter_upwards [eventually_ge_atTop 4,
        Metric.tendsto_nhds.mp hdef (1 / (4 * (b : ℝ))) (by positivity)] with N hN4 hN
      rw [Real.dist_eq, sub_zero] at hN
      exact ⟨hN4, (le_abs_self _).trans_lt hN⟩
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
    -- For every `N ≥ N₀`, extract a local fixed center `j_N`.
    have hloc : ∀ N ≥ N₀, ∃ j : ℕ, j + 2 ≤ b ∧
        (((range N).filter fun n =>
          ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
              ((b : ℝ) * (1 - radixDiscrepancy b x N) / ((b : ℝ) - 1))).card : ℝ) ≤
          (1 - radixDiscrepancy b x N) * N := by
      intro N hN
      have hN4 : 4 ≤ N := (hN₀ N hN).1
      have hδ : 1 - radixDiscrepancy b x N < 1 / (4 * (b : ℝ)) := (hN₀ N hN).2
      have hδN : 1 - radixDiscrepancy b x N < 1 / 2 - 1 / (N : ℝ) := by
        have h1 : 1 / (4 * (b : ℝ)) ≤ 1 / 8 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        have h2 : 1 / (N : ℝ) ≤ 1 / 4 :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN4)
        linarith
      exact exists_fixed_center_of_deficit_le hb (by omega) x hδN
    -- Choose the initial center `j₀` at `N₀` and show it works at every `N ≥ N₀`.
    obtain ⟨j₀, hj₀_bd, hj₀_card⟩ := hloc N₀ le_rfl
    -- Adjacent-step center agreement: any centers at `N` and `N + 1` (for `N ≥ N₀`) must coincide.
    have hadj : ∀ N ≥ N₀, ∀ j₁ j₂ : ℕ, j₁ + 2 ≤ b → j₂ + 2 ≤ b →
        ((((range N).filter fun n =>
          ¬ Near (shift b x n - (j₁ : ℝ) / ((b : ℝ) - 1))
              ((b : ℝ) * (1 - radixDiscrepancy b x N) / ((b : ℝ) - 1))).card : ℝ) ≤
          (1 - radixDiscrepancy b x N) * N) →
        ((((range (N + 1)).filter fun n =>
          ¬ Near (shift b x n - (j₂ : ℝ) / ((b : ℝ) - 1))
              ((b : ℝ) * (1 - radixDiscrepancy b x (N + 1)) / ((b : ℝ) - 1))).card : ℝ) ≤
          (1 - radixDiscrepancy b x (N + 1)) * ((N + 1 : ℕ) : ℝ)) →
        j₁ = j₂ := by
      intro N hN j₁ j₂ hj₁ hj₂ hc₁ hc₂
      by_contra hne
      have hN4 : 4 ≤ N := (hN₀ N hN).1
      have hδ1 : 1 - radixDiscrepancy b x N < 1 / (4 * (b : ℝ)) := (hN₀ N hN).2
      have hδ2 : 1 - radixDiscrepancy b x (N + 1) < 1 / (4 * (b : ℝ)) := (hN₀ (N + 1) (by omega)).2
      set B₁ := (range N).filter fun n =>
        ¬ Near (shift b x n - (j₁ : ℝ) / ((b : ℝ) - 1))
            ((b : ℝ) * (1 - radixDiscrepancy b x N) / ((b : ℝ) - 1))
      set B₂ := (range N).filter fun n =>
        ¬ Near (shift b x n - (j₂ : ℝ) / ((b : ℝ) - 1))
            ((b : ℝ) * (1 - radixDiscrepancy b x (N + 1)) / ((b : ℝ) - 1))
      have hB₂_le : (B₂.card : ℝ) ≤ (1 - radixDiscrepancy b x (N + 1)) * ((N + 1 : ℕ) : ℝ) := by
        have hsub : B₂ ⊆ (range (N + 1)).filter fun n =>
            ¬ Near (shift b x n - (j₂ : ℝ) / ((b : ℝ) - 1))
                ((b : ℝ) * (1 - radixDiscrepancy b x (N + 1)) / ((b : ℝ) - 1)) :=
          filter_subset_filter _ (range_mono (Nat.le_succ N))
        exact (Nat.cast_le.mpr (card_le_card hsub)).trans hc₂
      have hlt_N : ((B₁ ∪ B₂).card : ℝ) < (N : ℝ) := by
        have h1 : ((B₁ ∪ B₂).card : ℝ) ≤ (B₁.card : ℝ) + (B₂.card : ℝ) := by
          exact_mod_cast card_union_le B₁ B₂
        have h18 : 1 / (4 * (b : ℝ)) ≤ 1 / 8 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
        have h1' : (1 - radixDiscrepancy b x N) * (N : ℝ) ≤ (1 / 8) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right (hδ1.le.trans h18) (by linarith)
        have h2' : (1 - radixDiscrepancy b x (N + 1)) * ((N + 1 : ℕ) : ℝ) ≤
            (1 / 8) * ((N : ℝ) + 1) := by
          push_cast
          exact mul_le_mul_of_nonneg_right (hδ2.le.trans h18) (by linarith)
        linarith
      have hlt_card : (B₁ ∪ B₂).card < (range N).card := by
        rw [card_range]
        exact_mod_cast hlt_N
      obtain ⟨n, hn_rng, hn_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_card
      have hn₁ : Near (shift b x n - (j₁ : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * (1 - radixDiscrepancy b x N) / ((b : ℝ) - 1)) := by
        by_contra hfar
        exact hn_not (mem_union_left _ (mem_filter.mpr ⟨hn_rng, hfar⟩))
      have hn₂ : Near (shift b x n - (j₂ : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * (1 - radixDiscrepancy b x (N + 1)) / ((b : ℝ) - 1)) := by
        by_contra hfar
        exact hn_not (mem_union_right _ (mem_filter.mpr ⟨hn_rng, hfar⟩))
      rw [near_iff_distInt_le, distInt_eq_circDist] at hn₁ hn₂
      have hsep := circDist_fixedPoint_sub_ge hb hj₁ hj₂ hne
      have htri : circDist ((j₁ : ℝ) / ((b : ℝ) - 1) - (j₂ : ℝ) / ((b : ℝ) - 1)) ≤
          circDist (shift b x n - (j₁ : ℝ) / ((b : ℝ) - 1)) +
          circDist (shift b x n - (j₂ : ℝ) / ((b : ℝ) - 1)) := by
        have hrew : (j₁ : ℝ) / ((b : ℝ) - 1) - (j₂ : ℝ) / ((b : ℝ) - 1) =
            -(shift b x n - (j₁ : ℝ) / ((b : ℝ) - 1)) +
              (shift b x n - (j₂ : ℝ) / ((b : ℝ) - 1)) := by ring
        rw [hrew]
        exact (circDist_add_le _ _).trans_eq (by rw [circDist_neg])
      have hr₁ : (b : ℝ) * (1 - radixDiscrepancy b x N) / ((b : ℝ) - 1) <
          1 / (4 * ((b : ℝ) - 1)) := by
        rw [div_lt_div_iff₀ hbm1_pos (by positivity)]
        have : (b : ℝ) * (1 - radixDiscrepancy b x N) < 1 / 4 := by
          have := mul_lt_mul_of_pos_left hδ1 hb_pos
          have hrew : (b : ℝ) * (1 / (4 * (b : ℝ))) = 1 / 4 := by field_simp [hb_pos.ne']
          linarith
        nlinarith
      have hr₂ : (b : ℝ) * (1 - radixDiscrepancy b x (N + 1)) / ((b : ℝ) - 1) <
          1 / (4 * ((b : ℝ) - 1)) := by
        rw [div_lt_div_iff₀ hbm1_pos (by positivity)]
        have : (b : ℝ) * (1 - radixDiscrepancy b x (N + 1)) < 1 / 4 := by
          have := mul_lt_mul_of_pos_left hδ2 hb_pos
          have hrew : (b : ℝ) * (1 / (4 * (b : ℝ))) = 1 / 4 := by field_simp [hb_pos.ne']
          linarith
        nlinarith
      have hquarter : 1 / (4 * ((b : ℝ) - 1)) + 1 / (4 * ((b : ℝ) - 1)) < 1 / ((b : ℝ) - 1) := by
        have : 1 / (4 * ((b : ℝ) - 1)) + 1 / (4 * ((b : ℝ) - 1)) = 1 / (2 * ((b : ℝ) - 1)) := by
          field_simp [hbm1_pos.ne']; ring
        rw [this]
        exact one_div_lt_one_div_of_lt hbm1_pos (by linarith)
      linarith
    -- Induction on `d = N - N₀`: the single center `j₀` holds for all `N ≥ N₀`.
    have hstab : ∀ N ≥ N₀,
        (((range N).filter fun n =>
          ¬ Near (shift b x n - (j₀ : ℝ) / ((b : ℝ) - 1))
              ((b : ℝ) * (1 - radixDiscrepancy b x N) / ((b : ℝ) - 1))).card : ℝ) ≤
          (1 - radixDiscrepancy b x N) * N := by
      intro N hN
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
      induction d with
      | zero => simpa using hj₀_card
      | succ d ih =>
        obtain ⟨j', hj'_bd, hj'_card⟩ := hloc (N₀ + (d + 1)) (by omega)
        have heq := hadj (N₀ + d) (by omega) j₀ j' hj₀_bd hj'_bd (ih (by omega))
          (by simpa [add_assoc] using hj'_card)
        subst heq
        exact hj'_card
    -- Conclude `u := x - j₀ / (b - 1) ∈ zeroOrbitSubgroup b`.
    set u : ℝ := x - (j₀ : ℝ) / ((b : ℝ) - 1)
    refine ⟨(j₀ : ℤ), u, ?_, by push_cast; dsimp [u]; ring⟩
    change Tendsto (circMean b u) atTop (𝓝 0)
    have hupper : Tendsto (fun N => ((b : ℝ) / ((b : ℝ) - 1) + 1 / 2) *
        (1 - radixDiscrepancy b x N)) atTop (𝓝 0) := by
      simpa using hdef.const_mul ((b : ℝ) / ((b : ℝ) - 1) + 1 / 2)
    refine squeeze_zero' (Eventually.of_forall fun N => circMean_nonneg b u N) ?_ hupper
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    have hN₀_le : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    set δ : ℝ := 1 - radixDiscrepancy b x N
    set r : ℝ := (b : ℝ) * δ / ((b : ℝ) - 1)
    set B := (range N).filter fun n => ¬ Near (shift b x n - (j₀ : ℝ) / ((b : ℝ) - 1)) r
    set G := (range N).filter fun n => Near (shift b x n - (j₀ : ℝ) / ((b : ℝ) - 1)) r
    have hB_le : (B.card : ℝ) ≤ δ * (N : ℝ) := hstab N hN₀_le
    have hsum_split : ∑ n ∈ range N, circDist (shift b u n) =
        (∑ n ∈ G, circDist (shift b u n)) + ∑ n ∈ B, circDist (shift b u n) := by
      rw [← Finset.sum_filter_add_sum_filter_not (range N)
        (fun n => Near (shift b x n - (j₀ : ℝ) / ((b : ℝ) - 1)) r)]
    have hG_sum : ∑ n ∈ G, circDist (shift b u n) ≤ (N : ℝ) * r := by
      have h1 : ∑ n ∈ G, circDist (shift b u n) ≤ ∑ _n ∈ G, r := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hnear := (mem_filter.mp hn).2
        rw [near_iff_distInt_le, distInt_eq_circDist] at hnear
        dsimp [u]
        rwa [circDist_shift_sub_fixedPoint hb x j₀ n]
      have h2 : ∑ _n ∈ G, r = (G.card : ℝ) * r := by rw [Finset.sum_const, nsmul_eq_mul]
      have hG_le : (G.card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast ((card_filter_le _ _).trans_eq (card_range N))
      have hr_nn : 0 ≤ r := by
        have hδ_nn : 0 ≤ δ := by linarith [(radixDiscrepancy_mem b x N).2]
        dsimp [r]; positivity
      exact h1.trans (h2.le.trans (mul_le_mul_of_nonneg_right hG_le hr_nn))
    have hB_sum : ∑ n ∈ B, circDist (shift b u n) ≤ (B.card : ℝ) * (1 / 2) := by
      calc ∑ n ∈ B, circDist (shift b u n)
          ≤ ∑ _n ∈ B, (1 / 2 : ℝ) := Finset.sum_le_sum fun n _ => circDist_le_half _
        _ = (B.card : ℝ) * (1 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    unfold circMean
    rw [hsum_split]
    have htot : (∑ n ∈ G, circDist (shift b u n)) + (∑ n ∈ B, circDist (shift b u n)) ≤
        ((b : ℝ) / ((b : ℝ) - 1) + 1 / 2) * δ * (N : ℝ) := by
      have hrew : (N : ℝ) * r + δ * (N : ℝ) * (1 / 2) =
          ((b : ℝ) / ((b : ℝ) - 1) + 1 / 2) * δ * (N : ℝ) := by
        dsimp [r]; ring
      linarith
    calc ((∑ n ∈ G, circDist (shift b u n)) + ∑ n ∈ B, circDist (shift b u n)) / (N : ℝ)
        ≤ (((b : ℝ) / ((b : ℝ) - 1) + 1 / 2) * δ * (N : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right htot hNr.le
      _ = ((b : ℝ) / ((b : ℝ) - 1) + 1 / 2) * δ := mul_div_cancel_right₀ _ hNr.ne'
  · rintro ⟨m, u, hu, rfl⟩
    exact fixedPoint_add_zeroOrbit_mem_kernel hb m hu

/-- Subgroup-sum form of the kernel decomposition: `K_b = F_b + M_b`. -/
theorem kernel_eq_fixedPoint_add_zeroOrbit {b : ℕ} (hb : 2 ≤ b) :
    Kernel b = {x : ℝ | ∃ c ∈ fixedPointSubgroup b, ∃ u ∈ zeroOrbitSubgroup b, x = c + u} := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbm1_ne : (b : ℝ) - 1 ≠ 0 := by linarith
  ext x
  rw [mem_kernel_iff_exists_fixedPoint_add_zeroOrbit hb]
  constructor
  · rintro ⟨m, u, hu, rfl⟩
    exact ⟨(m : ℝ) / ((b : ℝ) - 1), ⟨m, by field_simp [hbm1_ne]⟩, u, hu, rfl⟩
  · rintro ⟨c, ⟨m, hm⟩, u, hu, rfl⟩
    refine ⟨m, u, hu, ?_⟩
    have hc : c = (m : ℝ) / ((b : ℝ) - 1) := (eq_div_iff hbm1_ne).mpr (by linarith)
    rw [hc]

/-- Every element `r / (b^k - 1) + u` with `u ∈ M_b` lies in `K_{b^k}`. -/
theorem rat_add_zeroOrbit_mem_pow_kernel {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (r : ℕ)
    {u : ℝ} (hu : u ∈ zeroOrbitSubgroup b) :
    (r : ℝ) / ((b : ℝ) ^ k - 1) + u ∈ Kernel (b ^ k) := by
  have hbk : 2 ≤ b ^ k :=
    (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hk)
  have hu' : u ∈ zeroOrbitSubgroup (b ^ k) := by rwa [zeroOrbitSubgroup_pow_eq hb (by omega)]
  have h := fixedPoint_add_zeroOrbit_mem_kernel hbk (r : ℤ) hu'
  simpa using h

/-- **Exact kernel decomposition at level `k`:** every `x ∈ K_{b^k}` has a UNIQUE representation
`x = r / (b^k - 1) + u` with `0 ≤ r < b^k - 1` and `u ∈ M_b`, and `x ∈ K_b ↔ b^k - 1 ∣ (b - 1) * r`. -/
theorem mem_pow_kernel_decomp {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) {x : ℝ}
    (hx : x ∈ Kernel (b ^ k)) :
    ∃ r < b ^ k - 1, ∃ u ∈ zeroOrbitSubgroup b,
      x = (r : ℝ) / ((b : ℝ) ^ k - 1) + u ∧
      (∀ r' < b ^ k - 1, ∀ u' ∈ zeroOrbitSubgroup b,
        x = (r' : ℝ) / ((b : ℝ) ^ k - 1) + u' → r' = r ∧ u' = u) ∧
      (x ∈ Kernel b ↔ b ^ k - 1 ∣ (b - 1) * r) := by
  have hbk2 : 2 ≤ b ^ k :=
    (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) (by omega))
  set Q : ℕ := b ^ k - 1
  have hQ_pos : 0 < Q := by omega
  have hQ_cast : (Q : ℝ) = (b : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
  have hQ_ne : (b : ℝ) ^ k - 1 ≠ 0 := by
    rw [← hQ_cast]; exact_mod_cast hQ_pos.ne'
  -- Decompose in `Kernel (b ^ k)` and reduce the numerator modulo `Q`.
  rw [mem_kernel_iff_exists_fixedPoint_add_zeroOrbit hbk2] at hx
  obtain ⟨m, u₀, hu₀, hxeq⟩ := hx
  rw [zeroOrbitSubgroup_pow_eq hb (by omega)] at hu₀
  set r : ℕ := (m % (Q : ℤ)).toNat
  set q : ℤ := m / (Q : ℤ)
  have hr_z : (r : ℤ) = m % (Q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hQ_pos.ne'))
  have hr_lt : r < Q := by
    have hQ_zpos : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ_pos
    have hlt := Int.emod_lt_of_pos m hQ_zpos
    rw [← hr_z] at hlt
    exact_mod_cast hlt
  have hm_eq : m = (Q : ℤ) * q + (r : ℤ) := by
    rw [hr_z, add_comm]
    exact (Int.emod_add_mul_ediv m (Q : ℤ)).symm
  set u : ℝ := (q : ℝ) + u₀
  have hu : u ∈ zeroOrbitSubgroup b :=
    (zeroOrbitSubgroup b).add_mem (intCast_mem_zeroOrbit b q) hu₀
  have hx_repr : x = (r : ℝ) / ((b : ℝ) ^ k - 1) + u := by
    rw [hxeq]
    have hm_r : (m : ℝ) = ((b : ℝ) ^ k - 1) * (q : ℝ) + (r : ℝ) := by
      have : (m : ℝ) = (Q : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hm_eq
      rwa [hQ_cast] at this
    push_cast at hm_r ⊢
    dsimp [u]
    field_simp [hQ_ne]
    linarith
  refine ⟨r, hr_lt, u, hu, hx_repr, ?_, ?_⟩
  · -- Uniqueness of `(r, u)`.
    intro r' hr' u' hu' hx'
    have hdiff : (((r' : ℤ) - (r : ℤ) : ℤ) : ℝ) / ((b : ℝ) ^ k - 1) = u - u' := by
      push_cast
      rw [sub_div]
      linarith
    have hmem : (((r' : ℤ) - (r : ℤ) : ℤ) : ℝ) / ((b : ℝ) ^ k - 1) ∈ zeroOrbitSubgroup b := by
      rw [hdiff]
      exact (zeroOrbitSubgroup b).sub_mem hu hu'
    have hdvd := (fixedPoint_inter_zeroOrbit hb (by omega) ((r' : ℤ) - (r : ℤ))).mp hmem
    have hr_eq : r' = r := by
      obtain ⟨t, ht⟩ := hdvd
      have ht0 : t = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · have : t ≤ -1 := by omega
          nlinarith
        · have : 1 ≤ t := by omega
          nlinarith
      rw [ht0, mul_zero] at ht
      omega
    subst hr_eq
    exact ⟨rfl, by linarith⟩
  · -- Criterion for `x ∈ Kernel b`.
    have hbm1_pos : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    have hbm1_dvd : b - 1 ∣ Q := by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow b 1 k
    set R : ℕ := Q / (b - 1)
    have hRQ : (b - 1) * R = Q := Nat.mul_div_cancel' hbm1_dvd
    have hRQ_r : ((b : ℝ) - 1) * (R : ℝ) = (b : ℝ) ^ k - 1 := by
      have : (((b - 1) * R : ℕ) : ℝ) = (Q : ℝ) := by exact_mod_cast hRQ
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one, hQ_cast] at this
      exact this
    constructor
    · intro hKb
      rw [mem_kernel_iff_exists_fixedPoint_add_zeroOrbit hb] at hKb
      obtain ⟨m', w, hw, hx_b⟩ := hKb
      have hdiff : (((r : ℤ) - m' * (R : ℤ) : ℤ) : ℝ) / ((b : ℝ) ^ k - 1) = w - u := by
        push_cast
        have hm'_eq : (m' : ℝ) / ((b : ℝ) - 1) = (m' : ℝ) * (R : ℝ) / ((b : ℝ) ^ k - 1) := by
          rw [← hRQ_r]
          have hR_ne : (R : ℝ) ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hRQ_r; exact hQ_ne hRQ_r.symm
          field_simp [hbm1_pos.ne', hR_ne]
        rw [sub_div, ← hm'_eq]
        linarith
      have hmem : (((r : ℤ) - m' * (R : ℤ) : ℤ) : ℝ) / ((b : ℝ) ^ k - 1) ∈ zeroOrbitSubgroup b := by
        rw [hdiff]
        exact (zeroOrbitSubgroup b).sub_mem hw hu
      obtain ⟨t, ht⟩ := (fixedPoint_inter_zeroOrbit hb (by omega) ((r : ℤ) - m' * (R : ℤ))).mp hmem
      have hdvd_z : (Q : ℤ) ∣ (((b - 1) * r : ℕ) : ℤ) := by
        refine ⟨((b - 1 : ℕ) : ℤ) * t + m', ?_⟩
        have hRQ_z : ((b - 1 : ℕ) : ℤ) * (R : ℤ) = (Q : ℤ) := by exact_mod_cast hRQ
        push_cast
        linear_combination ((b - 1 : ℕ) : ℤ) * ht + m' * hRQ_z
      exact Int.natCast_dvd_natCast.mp hdvd_z
    · rintro ⟨m', hm'⟩
      rw [mem_kernel_iff_exists_fixedPoint_add_zeroOrbit hb]
      refine ⟨(m' : ℤ), u, hu, ?_⟩
      rw [hx_repr]
      congr 1
      have hm'_r : ((b : ℝ) - 1) * (r : ℝ) = ((b : ℝ) ^ k - 1) * (m' : ℝ) := by
        have : (((b - 1) * r : ℕ) : ℝ) = ((Q * m' : ℕ) : ℝ) := by exact_mod_cast hm'
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one, hQ_cast] at this
        exact this
      push_cast
      field_simp [hQ_ne, hbm1_pos.ne']
      linarith

/-! ### Part 3: Coprime-rational cylinder word-frequency transfer -/

/-- The `n`-th base-`b` shift of `r / (b^k - 1)` is `(b^n * r % (b^k - 1)) / (b^k - 1)`. -/
private lemma shift_rat_pow_sub_one {b k r : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (n : ℕ) :
    shift b ((r : ℝ) / ((b : ℝ) ^ k - 1)) n =
      ((b ^ n * r % (b ^ k - 1) : ℕ) : ℝ) / ((b ^ k - 1 : ℕ) : ℝ) := by
  set q : ℕ := b ^ k - 1
  have hq_pos : 0 < q := by
    have : 2 ≤ b ^ k := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  have hq_r : (q : ℝ) = (b : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
  have hq_rpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hdiv : b ^ n * r = q * (b ^ n * r / q) + b ^ n * r % q := (Nat.div_add_mod _ _).symm
  have hrew : (b : ℝ) ^ n * ((r : ℝ) / ((b : ℝ) ^ k - 1)) =
      ((b ^ n * r % q : ℕ) : ℝ) / (q : ℝ) + ((b ^ n * r / q : ℕ) : ℤ) := by
    rw [← hq_r]
    have hdiv_r : (b : ℝ) ^ n * (r : ℝ) = (q : ℝ) * ((b ^ n * r / q : ℕ) : ℝ) +
        ((b ^ n * r % q : ℕ) : ℝ) := by exact_mod_cast hdiv
    rw [Int.cast_natCast]
    field_simp [hq_rpos.ne']
    linarith
  unfold shift
  rw [hrew, Int.fract_add_intCast]
  refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
  rw [div_lt_one hq_rpos]
  exact_mod_cast Nat.mod_lt (b ^ n * r) hq_pos

/-- Periodicity of `n ↦ b^n * r % (b^k - 1)` with period `k`. -/
private lemma pow_mul_mod_periodic {b k r : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (n : ℕ) :
    b ^ (n + k) * r % (b ^ k - 1) = b ^ n * r % (b ^ k - 1) := by
  set q : ℕ := b ^ k - 1
  have hbk_ge2 : 2 ≤ b ^ k :=
    (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hk)
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with hq1 | hq_gt
  · simp [← hq1, Nat.mod_one]
  · have hbk_mod : b ^ k % q = 1 := by
      have : b ^ k = q + 1 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hq_gt]
    rw [pow_add, mul_right_comm, Nat.mul_mod, hbk_mod, mul_one, Nat.mod_mod]

/-- General periodic shift `b ^ (k * m + j) * r % q = b ^ j * r % q`. -/
private lemma pow_mul_mod_add_mul {b k r : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (m j : ℕ) :
    b ^ (k * m + j) * r % (b ^ k - 1) = b ^ j * r % (b ^ k - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k * (m + 1) + j = (k * m + j) + k by ring, pow_mul_mod_periodic hb hk, ih]

/-- **Coprime-rational cylinder word-frequency transfer:**
for `b ≥ 2`, `k ≥ 2`, `L ≥ 1`, `0 < r < b^k - 1`, and `u ∈ zeroOrbitSubgroup b`, every length-`L`
word `v` has asymptotic frequency `cyclicCount b k L r v / k` in `r / (b^k - 1) + u`. -/
theorem wordFreq_tower_limit {b k L r : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hr : 0 < r) (hr' : r < b ^ k - 1)
    {u : ℝ} (hu : u ∈ zeroOrbitSubgroup b) (v : ℕ) :
    Tendsto (wordFreq b L ((r : ℝ) / ((b : ℝ) ^ k - 1) + u) v)
      atTop (𝓝 ((cyclicCount b k L r v : ℝ) / k)) := by
  classical
  set q : ℕ := b ^ k - 1
  have hbk_ge4 : 4 ≤ b ^ k :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
      _ ≤ b ^ k := Nat.pow_le_pow_right (by omega) hk
  have hq_ge2 : 2 ≤ q := by omega
  have hq_pos : 0 < q := by omega
  have hq_cast : (q : ℝ) = (b : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
  have hq_rpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hcop : Nat.Coprime q b :=
    (coprime_of_dvd_pow_sub_one (by omega) (by omega) (dvd_refl q)).symm
  set c : ℝ := (r : ℝ) / ((b : ℝ) ^ k - 1)
  set η : ℝ := 1 / (2 * (q : ℝ) * (b : ℝ) ^ L)
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by exact_mod_cast (show 0 < b by omega)) L
  have hη_pos : 0 < η := by positivity
  have hη_lt : η < 1 / ((q : ℝ) * (b : ℝ) ^ L) := by
    dsimp [η]
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  -- At every shift `n` where `Near (b^n * u) η`, the length-`L` word of `c + u` matches `c`.
  have hmatch : ∀ n : ℕ, Near ((b : ℝ) ^ n * u) η →
      ⌊(b : ℝ) ^ L * shift b (c + u) n⌋₊ = b ^ L * (b ^ n * r % q) / q := by
    intro n hnear
    obtain ⟨z, hz⟩ := hnear
    set r_n : ℕ := b ^ n * r % q
    have hr_n_lt : r_n < q := Nat.mod_lt _ hq_pos
    have hr_n_pos : 1 ≤ r_n := by
      by_contra h0
      have hdvd : q ∣ b ^ n * r := Nat.dvd_of_mod_eq_zero (by omega)
      have hdr : q ∣ r := (hcop.pow_right n).dvd_of_dvd_mul_left hdvd
      have := Nat.le_of_dvd hr hdr
      omega
    set δ : ℝ := (b : ℝ) ^ n * u - (z : ℝ)
    set y : ℝ := (r_n : ℝ) / (q : ℝ) + δ
    have hy_dist : |y - (r_n : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * (b : ℝ) ^ L) := by
      have : y - (r_n : ℝ) / (q : ℝ) = δ := by dsimp [y]; ring
      rw [this]
      exact hz.trans_lt hη_lt
    have hmargin := coprime_rat_cylinder_margin hb hq_ge2 hcop hr_n_pos hr_n_lt hL
    have hstab := coprime_rat_cylinder_stable hb hq_ge2 hcop hr_n_pos hr_n_lt hL hy_dist
    set w : ℕ := r_n * b ^ L / q
    have hw_lt : w < b ^ L := hmargin.1
    have hy_nn : 0 ≤ y := le_trans (by positivity) hstab.1
    have hy_lt1 : y < 1 := by
      have hle1 : ((w + 1 : ℕ) : ℝ) / (b : ℝ) ^ L ≤ 1 := by
        rw [div_le_one hbL_pos]
        exact_mod_cast hw_lt
      exact hstab.2.1.trans_le hle1
    have hshift_eq : shift b (c + u) n = y := by
      have hsc : shift b c n = (r_n : ℝ) / (q : ℝ) := shift_rat_pow_sub_one hb (by omega) n
      have hc_int : (b : ℝ) ^ n * c = (r_n : ℝ) / (q : ℝ) + (⌊(b : ℝ) ^ n * c⌋ : ℝ) := by
        have := Int.fract_add_floor ((b : ℝ) ^ n * c)
        have hsc' : Int.fract ((b : ℝ) ^ n * c) = (r_n : ℝ) / (q : ℝ) := hsc
        linarith
      unfold shift
      have hrew : (b : ℝ) ^ n * (c + u) = y + ((⌊(b : ℝ) ^ n * c⌋ + z : ℤ) : ℝ) := by
        push_cast
        conv_lhs => rw [mul_add, hc_int]
        dsimp [y, δ]
        ring
      rw [hrew, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hy_nn, hy_lt1⟩]
    rw [hshift_eq]
    have hfl_z : ⌊(b : ℝ) ^ L * y⌋ = (w : ℤ) := hstab.2.2
    have hfl_n : ⌊(b : ℝ) ^ L * y⌋₊ = w := by
      have h1 : (⌊(b : ℝ) ^ L * y⌋₊ : ℤ) = ⌊(b : ℝ) ^ L * y⌋ :=
        Int.natCast_floor_eq_floor (mul_nonneg hbL_pos.le hy_nn)
      omega
    rw [hfl_n]
    dsimp [w]
    rw [mul_comm]
  -- Compare `wordCount` with the periodic count `P N`.
  let P : ℕ → ℕ := fun N => ((range N).filter fun n => b ^ L * (b ^ n * r % q) / q = v).card
  have hcount_diff : ∀ N : ℕ,
      |(wordCount b L (c + u) v N : ℝ) - (P N : ℝ)| ≤ (farCount b u η N : ℝ) := by
    intro N
    set A := (range N).filter fun n => ⌊(b : ℝ) ^ L * shift b (c + u) n⌋₊ = v
    set B := (range N).filter fun n => b ^ L * (b ^ n * r % q) / q = v
    set F := (range N).filter fun n => ¬ Near ((b : ℝ) ^ n * u) η
    have hAB : A ⊆ B ∪ F := by
      intro n hn
      obtain ⟨hnN, hA⟩ := mem_filter.mp hn
      by_cases hnear : Near ((b : ℝ) ^ n * u) η
      · exact mem_union_left _ (mem_filter.mpr ⟨hnN, by rw [← hmatch n hnear, hA]⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hnN, hnear⟩)
    have hBA : B ⊆ A ∪ F := by
      intro n hn
      obtain ⟨hnN, hB⟩ := mem_filter.mp hn
      by_cases hnear : Near ((b : ℝ) ^ n * u) η
      · exact mem_union_left _ (mem_filter.mpr ⟨hnN, by rw [hmatch n hnear, hB]⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hnN, hnear⟩)
    have h1 : A.card ≤ B.card + F.card := (card_le_card hAB).trans (card_union_le B F)
    have h2 : B.card ≤ A.card + F.card := (card_le_card hBA).trans (card_union_le A F)
    change |(A.card : ℝ) - (B.card : ℝ)| ≤ (F.card : ℝ)
    rw [abs_le]
    have h1r : (A.card : ℝ) ≤ (B.card : ℝ) + (F.card : ℝ) := by exact_mod_cast h1
    have h2r : (B.card : ℝ) ≤ (A.card : ℝ) + (F.card : ℝ) := by exact_mod_cast h2
    constructor <;> linarith
  -- Evaluate the periodic count on complete `k`-blocks: `P (k * m) = m * C`.
  set C : ℕ := cyclicCount b k L r v
  have hP_mul : ∀ m : ℕ, P (k * m) = m * C := by
    intro m
    induction m with
    | zero => simp [P]
    | succ m ih =>
      have hsplit : P (k * (m + 1)) = P (k * m) +
          ((Ico (k * m) (k * m + k)).filter fun n => b ^ L * (b ^ n * r % q) / q = v).card := by
        dsimp [P]
        rw [Nat.mul_succ]
        have hu : range (k * m + k) = range (k * m) ∪ Ico (k * m) (k * m + k) := by
          ext n; simp only [mem_union, mem_range, mem_Ico]; omega
        have hd : Disjoint (range (k * m)) (Ico (k * m) (k * m + k)) := by
          rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
        rw [hu, Finset.filter_union, card_union_of_disjoint
          (hd.mono (filter_subset _ _) (filter_subset _ _))]
      have hblock : ((Ico (k * m) (k * m + k)).filter fun n =>
          b ^ L * (b ^ n * r % q) / q = v).card = C := by
        refine Finset.card_bij (fun n _ => n - k * m) ?_ ?_ ?_
        · intro n hn
          obtain ⟨hnI, hEq⟩ := mem_filter.mp hn
          obtain ⟨hlo, hhi⟩ := mem_Ico.mp hnI
          refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
          have hper := pow_mul_mod_add_mul (b := b) (k := k) (r := r) hb (by omega) m (n - k * m)
          rw [Nat.add_sub_cancel' hlo] at hper
          rwa [← hper]
        · intro n₁ hn₁ n₂ hn₂ heq
          have h1 := (mem_Ico.mp (mem_filter.mp hn₁).1).1
          have h2 := (mem_Ico.mp (mem_filter.mp hn₂).1).1
          omega
        · intro j hj
          obtain ⟨hj_rng, hEq⟩ := mem_filter.mp hj
          have hj_lt : j < k := mem_range.mp hj_rng
          refine ⟨k * m + j, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, by omega⟩
          rwa [pow_mul_mod_add_mul hb (by omega) m j]
      rw [hsplit, ih, hblock]
      ring
  -- Bound `|P N / N - C / k| ≤ k / N` for all `N ≥ 1`.
  have hP_err : ∀ N : ℕ, 1 ≤ N → |(P N : ℝ) / (N : ℝ) - (C : ℝ) / (k : ℝ)| ≤ (k : ℝ) / (N : ℝ) := by
    intro N hN
    set m : ℕ := N / k
    set rem : ℕ := N % k
    have hN_eq : k * m + rem = N := Nat.div_add_mod N k
    have hrem_lt : rem < k := Nat.mod_lt N (by omega)
    have hC_le : C ≤ k := (card_filter_le _ _).trans_eq (card_range k)
    have hP_lo : m * C ≤ P N := by
      rw [← hP_mul m]
      exact card_le_card (filter_subset_filter _ (range_mono (by omega)))
    have hP_hi : P N ≤ m * C + rem := by
      have hu : range N = range (k * m) ∪ Ico (k * m) N := by
        ext n; simp only [mem_union, mem_range, mem_Ico]; omega
      have hsub : (range N).filter (fun n => b ^ L * (b ^ n * r % q) / q = v) ⊆
          ((range (k * m)).filter fun n => b ^ L * (b ^ n * r % q) / q = v) ∪ Ico (k * m) N := by
        intro n hn
        obtain ⟨hnN, hEq⟩ := mem_filter.mp hn
        rw [hu, mem_union] at hnN
        rcases hnN with h1 | h2
        · exact mem_union_left _ (mem_filter.mpr ⟨h1, hEq⟩)
        · exact mem_union_right _ h2
      calc P N ≤ (((range (k * m)).filter fun n => b ^ L * (b ^ n * r % q) / q = v) ∪
              Ico (k * m) N).card := card_le_card hsub
        _ ≤ P (k * m) + (Ico (k * m) N).card := card_union_le _ _
        _ = m * C + rem := by rw [hP_mul m, Nat.card_Ico]; omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hN_r : (k : ℝ) * (m : ℝ) + (rem : ℝ) = (N : ℝ) := by exact_mod_cast hN_eq
    have hlo_r : (m : ℝ) * (C : ℝ) ≤ (P N : ℝ) := by exact_mod_cast hP_lo
    have hhi_r : (P N : ℝ) ≤ (m : ℝ) * (C : ℝ) + (rem : ℝ) := by exact_mod_cast hP_hi
    have hrem_r : (rem : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrem_lt.le
    have hC_r : (C : ℝ) ≤ (k : ℝ) := by exact_mod_cast hC_le
    rw [abs_le]
    have hrew : (P N : ℝ) / (N : ℝ) - (C : ℝ) / (k : ℝ) =
        ((P N : ℝ) * (k : ℝ) - (N : ℝ) * (C : ℝ)) / ((N : ℝ) * (k : ℝ)) := by
      field_simp [hNr.ne', hkr.ne']
    have hrhs : (k : ℝ) / (N : ℝ) = ((k : ℝ) * (k : ℝ)) / ((N : ℝ) * (k : ℝ)) := by
      field_simp [hNr.ne', hkr.ne']
    rw [hrew, hrhs, ← neg_div]
    constructor
    · refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h1 : (rem : ℝ) * (C : ℝ) ≤ (k : ℝ) * (k : ℝ) :=
        mul_le_mul hrem_r hC_r (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith
    · refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h1 : (rem : ℝ) * (k : ℝ) ≤ (k : ℝ) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hrem_r (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ (rem : ℝ) * (C : ℝ) := by positivity
      nlinarith
  -- Combine both error terms to conclude convergence.
  have hfar_tend := farCount_div_tendsto_zero_of_mem_zeroOrbit hu hη_pos
  have hkdiv_tend : Tendsto (fun N : ℕ => (k : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (k : ℝ))).mul
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hsum_tend : Tendsto (fun N : ℕ => (farCount b u η N : ℝ) / (N : ℝ) + (k : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
    simpa using hfar_tend.add hkdiv_tend
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hsum_tend ε hε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have h1 : |wordFreq b L (c + u) v N - (P N : ℝ) / (N : ℝ)| ≤
      (farCount b u η N : ℝ) / (N : ℝ) := by
    unfold wordFreq
    rw [← sub_div, abs_div, abs_of_pos hNr]
    exact div_le_div_of_nonneg_right (hcount_diff N) hNr.le
  have h2 := hP_err N hN1
  have h3 := hN₀ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h3
  rw [Real.dist_eq]
  calc |wordFreq b L (c + u) v N - (C : ℝ) / (k : ℝ)|
      = |(wordFreq b L (c + u) v N - (P N : ℝ) / (N : ℝ)) +
          ((P N : ℝ) / (N : ℝ) - (C : ℝ) / (k : ℝ))| := by ring_nf
    _ ≤ |wordFreq b L (c + u) v N - (P N : ℝ) / (N : ℝ)| +
          |(P N : ℝ) / (N : ℝ) - (C : ℝ) / (k : ℝ)| := abs_add_le _ _
    _ ≤ (farCount b u η N : ℝ) / (N : ℝ) + (k : ℝ) / (N : ℝ) := add_le_add h1 h2
    _ < ε := h3

/-! ### Part 4: Directed Euler circuits and balanced de Bruijn blocks -/

/-- A list of directed edges forms a chain when consecutive endpoints match. -/
def IsChain {V E : Type*} (src dst : E → V) : List E → Prop
  | [] => True
  | [_] => True
  | e₁ :: e₂ :: rest => dst e₁ = src e₂ ∧ IsChain src dst (e₂ :: rest)

/-- A nonempty `Nodup` directed chain whose last destination equals its first source. -/
def IsClosedTrail {V E : Type*} (src dst : E → V) (L : List E) : Prop :=
  L ≠ [] ∧ L.Nodup ∧ IsChain src dst L ∧
    ∀ h : L ≠ [], dst (L.getLast h) = src (L.head h)

/-- Helper: every bounded nonempty predicate on lists attains a maximum length. -/
private lemma exists_max_length {α : Type*} (P : List α → Prop) (B : ℕ)
    (hne : ∃ L, P L) (hbdd : ∀ L, P L → L.length ≤ B) :
    ∃ L, P L ∧ ∀ L', P L' → L'.length ≤ L.length := by
  classical
  set S := (range (B + 1)).filter fun n => ∃ L, P L ∧ L.length = n
  have hS_ne : S.Nonempty := by
    obtain ⟨L₀, hL₀⟩ := hne
    exact ⟨L₀.length, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hbdd L₀ hL₀)), L₀, hL₀, rfl⟩⟩
  set m := S.max' hS_ne
  obtain ⟨L, hL, hlen⟩ := (mem_filter.mp (S.max'_mem hS_ne)).2
  refine ⟨L, hL, fun L' hL' => ?_⟩
  rw [hlen]
  exact S.le_max' L'.length (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hbdd L' hL')), L', hL', rfl⟩)

/-- Concatenation of two nonempty chains with matching junction is a chain. -/
private lemma isChain_append {V E : Type*} {src dst : E → V} {L₁ L₂ : List E}
    (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ []) (hc₁ : IsChain src dst L₁) (hc₂ : IsChain src dst L₂)
    (hmid : dst (L₁.getLast h₁) = src (L₂.head h₂)) :
    IsChain src dst (L₁ ++ L₂) := by
  induction L₁ with
  | nil => exact absurd rfl h₁
  | cons e rest ih =>
    cases rest with
    | nil =>
      cases L₂ with
      | nil => exact absurd rfl h₂
      | cons e' rest' =>
        simp only [List.cons_append, List.nil_append, IsChain]
        exact ⟨by simpa using hmid, hc₂⟩
    | cons e₂ rest' =>
      simp only [List.cons_append, IsChain] at hc₁ ⊢
      refine ⟨hc₁.1, ih (List.cons_ne_nil _ _) hc₁.2 ?_⟩
      simpa using hmid

/-- Splitting a chain into two nonempty pieces preserves `IsChain` and yields the junction equality. -/
private lemma isChain_of_append {V E : Type*} {src dst : E → V} {L₁ L₂ : List E}
    (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ []) (hc : IsChain src dst (L₁ ++ L₂)) :
    IsChain src dst L₁ ∧ IsChain src dst L₂ ∧ dst (L₁.getLast h₁) = src (L₂.head h₂) := by
  induction L₁ with
  | nil => exact absurd rfl h₁
  | cons e rest ih =>
    cases rest with
    | nil =>
      cases L₂ with
      | nil => exact absurd rfl h₂
      | cons e' rest' =>
        simp only [List.cons_append, List.nil_append, IsChain] at hc ⊢
        exact ⟨trivial, hc.2, by simpa using hc.1⟩
    | cons e₂ rest' =>
      simp only [List.cons_append, IsChain] at hc ⊢
      have ⟨h1, h2, hm⟩ := ih (List.cons_ne_nil _ _) hc.2
      exact ⟨⟨hc.1, h1⟩, h2, by simpa using hm⟩

/-- Exact in-degree / out-degree balance identity along any `Nodup` chain. -/
private lemma chain_degree_balance {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {L : List E} (hne : L ≠ []) (hnd : L.Nodup) (hch : IsChain src dst L)
    (v : V) :
    (L.toFinset.filter fun e => src e = v).card + (if dst (L.getLast hne) = v then 1 else 0) =
      (L.toFinset.filter fun e => dst e = v).card + (if src (L.head hne) = v then 1 else 0) := by
  induction L with
  | nil => exact absurd rfl hne
  | cons e rest ih =>
    cases rest with
    | nil =>
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        List.getLast_singleton, List.head_cons, Finset.filter_singleton]
      by_cases h1 : src e = v <;> by_cases h2 : dst e = v <;> simp [h1, h2]
    | cons e₂ rest' =>
      have hnd' : e ∉ (e₂ :: rest') ∧ (e₂ :: rest').Nodup := List.nodup_cons.mp hnd
      have hch' : dst e = src e₂ ∧ IsChain src dst (e₂ :: rest') := hch
      have hih := ih (List.cons_ne_nil _ _) hnd'.2 hch'.2
      have hnotmem : e ∉ (e₂ :: rest').toFinset := by simpa using hnd'.1
      have hins : ∀ g : E → V,
          ((e :: e₂ :: rest').toFinset.filter fun x => g x = v).card =
            (if g e = v then 1 else 0) + ((e₂ :: rest').toFinset.filter fun x => g x = v).card := by
        intro g
        rw [List.toFinset_cons, Finset.filter_insert]
        by_cases hP : g e = v
        · simp only [hP, ↓reduceIte,
            card_insert_of_notMem (fun h => hnotmem (mem_filter.mp h).1), add_comm]
        · simp only [hP, ↓reduceIte, zero_add]
      rw [hins src, hins dst]
      simp only [List.getLast_cons (List.cons_ne_nil e₂ rest'), List.head_cons] at hih ⊢
      rw [hch'.1]
      by_cases h1 : src e = v <;> by_cases h2 : src e₂ = v <;>
        simp only [h1, h2, ↓reduceIte] at hih ⊢ <;> omega

/-- Every edge in a balanced finite edge set lies in a nonempty `Nodup` closed trail. -/
private lemma exists_closedTrail_of_mem_balanced {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {S : Finset E}
    (hbal : ∀ v, (S.filter fun e => src e = v).card = (S.filter fun e => dst e = v).card)
    {e₀ : E} (he₀ : e₀ ∈ S) :
    ∃ C : List E, IsClosedTrail src dst C ∧ C.toFinset ⊆ S ∧
      ∀ h : C ≠ [], C.head h = e₀ := by
  let P : List E → Prop := fun T =>
    ∃ hne : T ≠ [], T.Nodup ∧ IsChain src dst T ∧ T.toFinset ⊆ S ∧ T.head hne = e₀
  have hne_P : ∃ T, P T :=
    ⟨[e₀], List.cons_ne_nil _ _, List.nodup_singleton e₀, trivial,
      by simp [he₀], rfl⟩
  have hbdd_P : ∀ T, P T → T.length ≤ S.card := by
    rintro T ⟨_, hnd, _, hsub, _⟩
    calc T.length = T.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ S.card := card_le_card hsub
  obtain ⟨T, ⟨hne, hnd, hch, hsub, hhd⟩, hmax⟩ := exists_max_length P S.card hne_P hbdd_P
  refine ⟨T, ⟨hne, hnd, hch, fun hne' => ?_⟩, hsub, fun hne' => hhd⟩
  -- Prove `dst (T.getLast hne') = src (T.head hne')` by maximality of `T`.
  set v : V := dst (T.getLast hne')
  by_contra hne_v
  have hdeg := chain_degree_balance hne hnd hch v
  have hdst_eq : dst (T.getLast hne) = v := rfl
  have hsrc_ne : src (T.head hne) ≠ v := Ne.symm hne_v
  simp only [hdst_eq, hsrc_ne, ↓reduceIte, add_zero] at hdeg
  have hlt_out : (T.toFinset.filter fun e => src e = v).card <
      (S.filter fun e => src e = v).card := by
    rw [hbal v]
    have hle : (T.toFinset.filter fun e => dst e = v).card ≤
        (S.filter fun e => dst e = v).card := card_le_card (filter_subset_filter _ hsub)
    omega
  have hsub_out : (T.toFinset.filter fun e => src e = v) ⊆ (S.filter fun e => src e = v) :=
    filter_subset_filter _ hsub
  obtain ⟨e', he'S, he'T⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_out
  obtain ⟨he'_mem, he'_src⟩ := mem_filter.mp he'S
  have he'_notin : e' ∉ T := fun hmem => he'T (mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, he'_src⟩)
  have hT'_ne : T ++ [e'] ≠ [] := List.append_ne_nil_of_right_ne_nil T (List.cons_ne_nil _ _)
  have hT'_nd : (T ++ [e']).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_singleton e', fun a ha b hb => ?_⟩
    rw [List.mem_singleton.mp hb]
    intro heq
    exact he'_notin (heq ▸ ha)
  have hT'_ch : IsChain src dst (T ++ [e']) :=
    isChain_append hne (List.cons_ne_nil _ _) hch trivial (by simpa [v] using he'_src.symm)
  have hT'_sub : (T ++ [e']).toFinset ⊆ S := by
    intro e he
    rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at he
    rcases he with h | rfl
    · exact hsub (List.mem_toFinset.mpr h)
    · exact he'_mem
  have hT'_hd : (T ++ [e']).head hT'_ne = e₀ := by
    rw [List.head_append_of_ne_nil hne, hhd]
  have hle_max := hmax (T ++ [e']) ⟨hT'_ne, hT'_nd, hT'_ch, hT'_sub, hT'_hd⟩
  simp only [List.length_append, List.length_singleton] at hle_max
  omega

/-- Rotating a closed trail so that a specified member edge becomes its head. -/
private lemma rotate_closedTrail {V E : Type*} [DecidableEq E] {src dst : E → V} {C : List E}
    (hC : IsClosedTrail src dst C) {e : E} (he : e ∈ C) :
    ∃ C' : List E, IsClosedTrail src dst C' ∧ C'.toFinset = C.toFinset ∧ C'.length = C.length ∧
      ∀ h : C' ≠ [], C'.head h = e := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem he
  rcases hC with ⟨hne, hnd, hch, hcl⟩
  by_cases hL₁ : L₁ = []
  · subst hL₁
    exact ⟨e :: L₂, ⟨hne, hnd, hch, hcl⟩, rfl, rfl, fun _ => rfl⟩
  · have hL₂_ne : e :: L₂ ≠ [] := List.cons_ne_nil _ _
    have ⟨hch₁, hch₂, hmid⟩ := isChain_of_append hL₁ hL₂_ne hch
    have hcl_eq : dst ((e :: L₂).getLast hL₂_ne) = src (L₁.head hL₁) := by
      have := hcl hne
      rwa [List.getLast_append_of_ne_nil _ hL₂_ne, List.head_append_of_ne_nil hL₁] at this
    set C' := (e :: L₂) ++ L₁
    have hC'_ne : C' ≠ [] := List.append_ne_nil_of_left_ne_nil hL₂_ne _
    have hperm : C'.Perm (L₁ ++ e :: L₂) := List.perm_append_comm
    refine ⟨C', ⟨hC'_ne, hperm.nodup_iff.mpr hnd,
        isChain_append hL₂_ne hL₁ hch₂ hch₁ hcl_eq, fun _ => ?_⟩,
        (by ext x; simp [List.mem_toFinset, hperm.mem_iff]; tauto), hperm.length_eq, fun _ => rfl⟩
    rw [List.getLast_append_of_ne_nil _ hL₁, List.head_append_of_ne_nil hL₂_ne]
    exact hmid

/-- **Hierholzer's Theorem (directed Euler circuit):**
every finite balanced directed multigraph in which every vertex is reachable from every vertex
by a directed path (with nonempty edge set) admits an Euler circuit traversing every edge once. -/
theorem exists_euler_circuit {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (hneE : Nonempty E)
    (hbal : ∀ v : V, (univ.filter fun e => src e = v).card = (univ.filter fun e => dst e = v).card)
    (hconn : ∀ u v : V, ∃ P : List E, (P = [] ∧ u = v) ∨
      (∃ hP : P ≠ [], IsChain src dst P ∧ src (P.head hP) = u ∧ dst (P.getLast hP) = v)) :
    ∃ C : List E, IsClosedTrail src dst C ∧ C.length = Fintype.card E := by
  have hne_univ : (univ : Finset E).Nonempty := ⟨Classical.arbitrary E, mem_univ _⟩
  obtain ⟨e₀, he₀⟩ := hne_univ
  obtain ⟨C₀, hC₀, _, _⟩ := exists_closedTrail_of_mem_balanced hbal he₀
  have hbdd : ∀ C : List E, IsClosedTrail src dst C → C.length ≤ Fintype.card E := by
    intro C hC
    calc C.length = C.toFinset.card := (List.toFinset_card_of_nodup hC.2.1).symm
      _ ≤ (univ : Finset E).card := card_le_card (subset_univ _)
      _ = Fintype.card E := card_univ
  obtain ⟨C, hC, hmax⟩ := exists_max_length (IsClosedTrail src dst) (Fintype.card E) ⟨C₀, hC₀⟩ hbdd
  refine ⟨C, hC, ?_⟩
  -- Show `C.toFinset = univ` by contradiction.
  have hfull : C.toFinset = univ := by
    by_contra hne_full
    set S' : Finset E := univ \ C.toFinset
    have hS'_ne : S'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      apply hne_full
      exact subset_antisymm (subset_univ _) (fun e _ => by
        by_contra hno
        have : e ∈ S' := mem_sdiff.mpr ⟨mem_univ e, hno⟩
        rw [hemp] at this
        exact notMem_empty e this)
    -- `S'` is balanced since `C` has equal in- and out-degrees at every vertex.
    have hbal_S' : ∀ v : V, (S'.filter fun e => src e = v).card = (S'.filter fun e => dst e = v).card := by
      intro v
      have hC_bal : (C.toFinset.filter fun e => src e = v).card =
          (C.toFinset.filter fun e => dst e = v).card := by
        have hdeg := chain_degree_balance hC.1 hC.2.1 hC.2.2.1 v
        rw [hC.2.2.2 hC.1] at hdeg
        omega
      have hsdiff : ∀ P : E → Prop, [DecidablePred P] →
          (S'.filter P).card = (univ.filter P).card - (C.toFinset.filter P).card := by
        intro P _
        have hdisj : Disjoint (S'.filter P) (C.toFinset.filter P) :=
          disjoint_sdiff_self_left.mono (filter_subset _ _) (filter_subset _ _)
        have hun : S'.filter P ∪ C.toFinset.filter P = univ.filter P := by
          rw [← Finset.filter_union, sdiff_union_of_subset (subset_univ _)]
        have := card_union_of_disjoint hdisj
        rw [hun] at this
        omega
      rw [hsdiff (fun e => src e = v), hsdiff (fun e => dst e = v), hbal v, hC_bal]
    -- Every edge in `C` has both endpoints in `A := {v | ∃ e ∈ C, src e = v}`.
    let A : Set V := {v | ∃ e ∈ C, src e = v}
    have hC_dst_A : ∀ e ∈ C, dst e ∈ A := by
      intro e he
      obtain ⟨C₁, hC₁, hto, _, hhd⟩ := rotate_closedTrail hC he
      -- In `C₁`, the edge after `e` (or `e` itself if singleton) has `src = dst e`.
      rcases C₁ with _ | ⟨e₁, rest⟩
      · exact absurd rfl hC₁.1
      · have he₁ : e₁ = e := hhd (List.cons_ne_nil _ _)
        subst e₁
        cases rest with
        | nil =>
          exact ⟨e, he, (hC₁.2.2.2 (List.cons_ne_nil _ _)).symm⟩
        | cons e₂ rest' =>
          have he₂_mem : e₂ ∈ C := by
            have : e₂ ∈ (e :: e₂ :: rest').toFinset := List.mem_toFinset.mpr (by simp)
            rw [hto, List.mem_toFinset] at this
            exact this
          exact ⟨e₂, he₂_mem, hC₁.2.2.1.1.symm⟩
    -- Find an edge `e_br ∈ S'` with `src e_br ∈ A`.
    have hbridge : ∃ e_br ∈ S', src e_br ∈ A := by
      obtain ⟨e_rem, he_rem⟩ := hS'_ne
      by_cases hmemA : src e_rem ∈ A
      · exact ⟨e_rem, he_rem, hmemA⟩
      · obtain ⟨e_in, he_in⟩ := List.exists_mem_of_ne_nil C hC.1
        obtain ⟨P, hP⟩ := hconn (src e_in) (src e_rem)
        rcases hP with ⟨_, heq⟩ | ⟨hPne, hPch, hPhd, hPlast⟩
        · exact absurd ⟨e_in, he_in, heq⟩ hmemA
        · -- Walk along `P` from `src (P.head) ∈ A` to `dst (P.getLast) ∉ A` to find the first exit edge.
          have hexit : ∀ Q : List E, ∀ hQ : Q ≠ [], IsChain src dst Q →
              src (Q.head hQ) ∈ A → dst (Q.getLast hQ) ∉ A →
              ∃ e' ∈ Q, src e' ∈ A ∧ dst e' ∉ A := by
            intro Q
            induction Q with
            | nil => intro hQ; exact absurd rfl hQ
            | cons a rest ih =>
              intro hQ hQch hQa hQlast
              cases rest with
              | nil => exact ⟨a, by simp, hQa, by simpa using hQlast⟩
              | cons b rest' =>
                by_cases hda : dst a ∈ A
                · have ⟨e', he', hs', hd'⟩ := ih (List.cons_ne_nil _ _) hQch.2
                    (by rwa [List.head_cons, ← hQch.1]) (by simpa using hQlast)
                  exact ⟨e', List.mem_cons_of_mem a he', hs', hd'⟩
                · exact ⟨a, List.mem_cons_self, hQa, hda⟩
          obtain ⟨e', _, hs', hd'⟩ := hexit P hPne hPch ⟨e_in, he_in, hPhd.symm⟩
            (by rw [hPlast]; exact hmemA)
          refine ⟨e', mem_sdiff.mpr ⟨mem_univ e', ?_⟩, hs'⟩
          intro he'C
          exact hd' (hC_dst_A e' (List.mem_toFinset.mp he'C))
    -- Extract a closed trail `C₂` inside `S'` starting at `e_br`, and splice it into `C`.
    obtain ⟨e_br, he_br, ⟨e_a, he_a, he_a_src⟩⟩ := hbridge
    obtain ⟨C₂, hC₂, hC₂_sub, hC₂_hd⟩ := exists_closedTrail_of_mem_balanced hbal_S' he_br
    obtain ⟨C₁, hC₁, hC₁_to, hC₁_len, hC₁_hd⟩ := rotate_closedTrail hC he_a
    set C₃ := C₁ ++ C₂
    have hC₃_ne : C₃ ≠ [] := List.append_ne_nil_of_left_ne_nil hC₁.1 _
    have hdisj : ∀ x ∈ C₁, ∀ y ∈ C₂, x ≠ y := by
      intro x hx y hy heq
      subst heq
      have hxC : x ∈ C.toFinset := hC₁_to ▸ List.mem_toFinset.mpr hx
      have hxS' : x ∈ S' := hC₂_sub (List.mem_toFinset.mpr hy)
      exact (mem_sdiff.mp hxS').2 hxC
    have hC₃_nd : C₃.Nodup := List.nodup_append.mpr ⟨hC₁.2.1, hC₂.2.1, hdisj⟩
    have hsrc_eq : src (C₁.head hC₁.1) = src (C₂.head hC₂.1) := by
      rw [hC₁_hd hC₁.1, hC₂_hd hC₂.1, he_a_src]
    have hC₃_ch : IsChain src dst C₃ :=
      isChain_append hC₁.1 hC₂.1 hC₁.2.2.1 hC₂.2.2.1 ((hC₁.2.2.2 hC₁.1).trans hsrc_eq)
    have hC₃_cl : IsClosedTrail src dst C₃ := by
      refine ⟨hC₃_ne, hC₃_nd, hC₃_ch, fun _ => ?_⟩
      rw [List.getLast_append_of_ne_nil _ hC₂.1, List.head_append_of_ne_nil hC₁.1]
      exact (hC₂.2.2.2 hC₂.1).trans hsrc_eq.symm
    have hle := hmax C₃ hC₃_cl
    have hC₂_pos : 0 < C₂.length := List.length_pos_iff.mpr hC₂.1
    rw [List.length_append, hC₁_len] at hle
    omega
  calc C.length = C.toFinset.card := (List.toFinset_card_of_nodup hC.2.1).symm
    _ = (univ : Finset E).card := by rw [hfull]
    _ = Fintype.card E := card_univ

/-- Indexing consecutive edges in a chain. -/
private lemma isChain_getElem {V E : Type*} {src dst : E → V} {L : List E}
    (hch : IsChain src dst L) :
    ∀ i (hi : i + 1 < L.length), dst (L[i]'(by omega)) = src (L[i + 1]'hi) := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons e rest ih =>
    intro i hi
    cases rest with
    | nil => simp at hi
    | cons e₂ rest' =>
      cases i with
      | zero => exact hch.1
      | succ j => exact ih hch.2 j (by simpa using hi)

/-- Cyclic indexing along a closed trail of length `M > 0`. -/
private lemma isClosedTrail_getElem_mod {V E : Type*} {src dst : E → V} {C : List E} {M : ℕ}
    (hC : IsClosedTrail src dst C) (hM : C.length = M) (hM_pos : 0 < M) (i : ℕ) :
    dst (C[i % M]'(by rw [hM]; exact Nat.mod_lt i hM_pos)) =
      src (C[(i + 1) % M]'(by rw [hM]; exact Nat.mod_lt (i + 1) hM_pos)) := by
  set r := i % M
  have hr_lt : r < M := Nat.mod_lt i hM_pos
  by_cases hlast : r + 1 < M
  · have hmod : (i + 1) % M = r + 1 := by
      have hdiv := Nat.div_add_mod i M
      have : i + 1 = M * (i / M) + (r + 1) := by dsimp [r]; omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hlast]
    have hidx := isChain_getElem hC.2.2.1 r (by omega)
    simpa [hmod] using hidx
  · have hr_eq : r = M - 1 := by omega
    have hmod : (i + 1) % M = 0 := by
      have hdiv := Nat.div_add_mod i M
      have : i + 1 = M * (i / M + 1) := by rw [mul_add, mul_one]; dsimp [r] at hr_eq; omega
      rw [this, Nat.mul_mod_right]
    have hgetLast : C[r]'(by omega) = C.getLast hC.1 := by
      rw [List.getLast_eq_getElem]
      congr 1; omega
    have hhead : C[0]'(by omega) = C.head hC.1 := (List.head_eq_getElem_zero hC.1).symm
    have hcl := hC.2.2.2 hC.1
    dsimp only [r] at hgetLast
    simpa [hmod, hgetLast, hhead] using hcl

/-- Recursive base-`b` value of the `len`-digit word starting at `start` in digit stream `d`. -/
private def wordVal (b : ℕ) (d : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 => wordVal b d start len * b + d (start + len)

private lemma wordVal_lt {b : ℕ} {d : ℕ → ℕ} (hd : ∀ i, d i < b) (start len : ℕ) :
    wordVal b d start len < b ^ len := by
  induction len with
  | zero => simp [wordVal]
  | succ len ih =>
    simp only [wordVal, pow_succ]
    have h1 : wordVal b d start len + 1 ≤ b ^ len := ih
    have h2 : d (start + len) < b := hd _
    nlinarith

private lemma wordVal_add (b : ℕ) (d : ℕ → ℕ) (start len₁ len₂ : ℕ) :
    wordVal b d start (len₁ + len₂) =
      wordVal b d start len₁ * b ^ len₂ + wordVal b d (start + len₁) len₂ := by
  induction len₂ with
  | zero => simp [wordVal]
  | succ len₂ ih =>
    rw [← add_assoc, wordVal, ih, wordVal, pow_succ]
    have : start + (len₁ + len₂) = start + len₁ + len₂ := by omega
    rw [this]
    ring

private lemma wordVal_congr {b : ℕ} {d : ℕ → ℕ} {s₁ s₂ len : ℕ}
    (h : ∀ i < len, d (s₁ + i) = d (s₂ + i)) :
    wordVal b d s₁ len = wordVal b d s₂ len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    simp only [wordVal]
    rw [ih (fun i hi => h i (by omega)), h len (Nat.lt_succ_self len)]

private lemma wordVal_eq_zero_iff {b : ℕ} (hb : 1 ≤ b) (d : ℕ → ℕ) (start len : ℕ) :
    wordVal b d start len = 0 ↔ ∀ i < len, d (start + i) = 0 := by
  induction len with
  | zero => simp [wordVal]
  | succ len ih =>
    simp only [wordVal, Nat.add_eq_zero_iff, Nat.mul_eq_zero]
    constructor
    · rintro ⟨h1 | h1, h2⟩ i hi
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
        · exact ih.mp h1 i hlt
        · exact h2
      · omega
    · intro hall
      refine ⟨Or.inl (ih.mpr fun i hi => hall i (by omega)), hall len (Nat.lt_succ_self len)⟩

private lemma wordVal_eq_max_iff {b : ℕ} (hb : 2 ≤ b) {d : ℕ → ℕ} (hd : ∀ i, d i < b)
    (start len : ℕ) :
    wordVal b d start len = b ^ len - 1 ↔ ∀ i < len, d (start + i) = b - 1 := by
  induction len with
  | zero => simp [wordVal]
  | succ len ih =>
    have hlt := wordVal_lt hd start len
    have hpow : 1 ≤ b ^ len := Nat.one_le_pow len b (by omega)
    have hd_lt := hd (start + len)
    simp only [wordVal]
    constructor
    · intro heq i hi
      have h1 : wordVal b d start len = b ^ len - 1 := by
        have hsub : wordVal b d start len * b + d (start + len) = b ^ len * b - 1 := by
          simpa [pow_succ] using heq
        have hprod : 1 ≤ b ^ len * b := by nlinarith
        zify [hpow, show 1 ≤ b by omega, hprod] at hlt hd_lt hsub ⊢
        nlinarith
      have h2 : d (start + len) = b - 1 := by
        have : wordVal b d start len * b + d (start + len) = b ^ len * b - 1 := by
          simpa [pow_succ] using heq
        rw [h1] at this
        have : (b ^ len - 1) * b + (b - 1) = b ^ len * b - 1 := by
          zify [hpow, show 1 ≤ b by omega, show 1 ≤ b ^ len * b by nlinarith]; ring
        omega
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt' | rfl
      · exact ih.mp h1 i hlt'
      · exact h2
    · intro hall
      rw [ih.mpr (fun i hi => hall i (by omega)), hall len (Nat.lt_succ_self len), pow_succ]
      zify [hpow, show 1 ≤ b by omega, show 1 ≤ b ^ len * b by nlinarith]
      ring

/-- **Existence of balanced de Bruijn blocks:**
for every `b ≥ 2` and `L ≥ 1`, there exists `0 < r < b^(b^L) - 1` such that `r / (b^(b^L) - 1)`
hits every base-`b` length-`L` word exactly once per period and every length-`(L + 1)` word at most
once per period. -/
theorem exists_balanced_block {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) :
    ∃ r : ℕ, 0 < r ∧ r < b ^ (b ^ L) - 1 ∧
      (∀ v < b ^ L, cyclicCount b (b ^ L) L r v = 1) ∧
      (∀ v < b ^ (L + 1), cyclicCount b (b ^ L) (L + 1) r v ≤ 1) := by
  set M : ℕ := b ^ L
  set Vn : ℕ := b ^ (L - 1)
  have hb_pos : 0 < b := by omega
  have hVn_pos : 0 < Vn := pow_pos hb_pos (L - 1)
  have hM_eq : M = Vn * b := by
    dsimp [M, Vn]
    rw [← pow_succ, Nat.sub_add_cancel hL]
  have hM_ge2 : 2 ≤ M :=
    (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hL)
  have hL_le_M : L ≤ M := by
    have h1 : L < 2 ^ L := Nat.lt_two_pow_self
    have h2 : 2 ^ L ≤ b ^ L := Nat.pow_le_pow_left hb L
    omega
  -- Define the de Bruijn directed multigraph on `V = Fin Vn`, `E = Fin M`.
  let src : Fin M → Fin Vn := fun w =>
    ⟨w.val / b, (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rw [← hM_eq]; exact w.isLt)⟩
  let dst : Fin M → Fin Vn := fun w => ⟨w.val % Vn, Nat.mod_lt w.val hVn_pos⟩
  have hneE : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  -- Balancedness: every vertex has out-degree `b` and in-degree `b`.
  have hbal : ∀ v : Fin Vn,
      (univ.filter fun e : Fin M => src e = v).card =
      (univ.filter fun e : Fin M => dst e = v).card := by
    intro v
    have hout : (univ.filter fun e : Fin M => src e = v).card = b := by
      rw [← card_range b]
      refine Finset.card_bij (fun e _ => e.val % b) ?_ ?_ ?_
      · intro e _
        exact mem_range.mpr (Nat.mod_lt e.val hb_pos)
      · intro e₁ he₁ e₂ he₂ heq
        have hs1 : e₁.val / b = v.val := congrArg Fin.val (mem_filter.mp he₁).2
        have hs2 : e₂.val / b = v.val := congrArg Fin.val (mem_filter.mp he₂).2
        apply Fin.ext
        have h1 := Nat.div_add_mod e₁.val b
        have h2 := Nat.div_add_mod e₂.val b
        rw [← h1, ← h2, hs1, hs2, heq]
      · intro d hd
        have hd_lt : d < b := mem_range.mp hd
        have hw_lt : v.val * b + d < M := by
          rw [hM_eq]
          have : v.val + 1 ≤ Vn := v.isLt
          nlinarith
        refine ⟨⟨v.val * b + d, hw_lt⟩, mem_filter.mpr ⟨mem_univ _, Fin.ext ?_⟩, ?_⟩
        · change (v.val * b + d) / b = v.val
          rw [mul_comm, Nat.mul_add_div hb_pos, Nat.div_eq_of_lt hd_lt, add_zero]
        · dsimp only
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hd_lt]
    have hin : (univ.filter fun e : Fin M => dst e = v).card = b := by
      rw [← card_range b]
      refine Finset.card_bij (fun e _ => e.val / Vn) ?_ ?_ ?_
      · intro e _
        exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hVn_pos).mpr (by rw [mul_comm, ← hM_eq]; exact e.isLt))
      · intro e₁ he₁ e₂ he₂ heq
        have hd1 : e₁.val % Vn = v.val := congrArg Fin.val (mem_filter.mp he₁).2
        have hd2 : e₂.val % Vn = v.val := congrArg Fin.val (mem_filter.mp he₂).2
        apply Fin.ext
        have h1 := Nat.div_add_mod e₁.val Vn
        have h2 := Nat.div_add_mod e₂.val Vn
        rw [← h1, ← h2, hd1, hd2, heq]
      · intro c hc
        have hc_lt : c < b := mem_range.mp hc
        have hw_lt : c * Vn + v.val < M := by
          rw [hM_eq]
          have : c + 1 ≤ b := hc_lt
          have : v.val < Vn := v.isLt
          nlinarith
        refine ⟨⟨c * Vn + v.val, hw_lt⟩, mem_filter.mpr ⟨mem_univ _, Fin.ext ?_⟩, ?_⟩
        · change (c * Vn + v.val) % Vn = v.val
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt v.isLt]
        · dsimp only
          rw [mul_comm, Nat.mul_add_div hVn_pos, Nat.div_eq_of_lt v.isLt, add_zero]
    rw [hout, hin]
  -- Strong connectivity: shift `L - 1` digits of `v` into `u`.
  have hreach : ∀ k : ℕ, ∀ u : Fin Vn, ∀ w < b ^ k,
      ∃ P : List (Fin M), (P = [] ∧ u.val = (u.val * b ^ k + w) % Vn) ∨
        (∃ hP : P ≠ [], IsChain src dst P ∧ src (P.head hP) = u ∧
          (dst (P.getLast hP)).val = (u.val * b ^ k + w) % Vn) := by
    intro k
    induction k with
    | zero =>
      intro u w hw
      have hw0 : w = 0 := by simpa using hw
      subst hw0
      exact ⟨[], Or.inl ⟨rfl, by rw [pow_zero, mul_one, add_zero, Nat.mod_eq_of_lt u.isLt]⟩⟩
    | succ k ih =>
      intro u w hw
      have hw_div : w / b < b ^ k := (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rwa [← pow_succ])
      obtain ⟨P, hP⟩ := ih u (w / b) hw_div
      set x : ℕ := (u.val * b ^ k + w / b) % Vn
      have hx_lt : x < Vn := Nat.mod_lt _ hVn_pos
      have he_lt : x * b + w % b < M := by
        rw [hM_eq]
        have : x + 1 ≤ Vn := hx_lt
        have : w % b < b := Nat.mod_lt w hb_pos
        nlinarith
      let e : Fin M := ⟨x * b + w % b, he_lt⟩
      have he_src : src e = ⟨x, hx_lt⟩ := by
        apply Fin.ext
        change (x * b + w % b) / b = x
        rw [mul_comm, Nat.mul_add_div hb_pos, Nat.div_eq_of_lt (Nat.mod_lt w hb_pos), add_zero]
      have he_dst : (dst e).val = (u.val * b ^ (k + 1) + w) % Vn := by
        change (x * b + w % b) % Vn = (u.val * b ^ (k + 1) + w) % Vn
        have hmod1 : (x * b + w % b) % Vn = ((u.val * b ^ k + w / b) * b + w % b) % Vn := by
          dsimp [x]
          rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
        rw [hmod1]
        have hrew : (u.val * b ^ k + w / b) * b + w % b = u.val * b ^ (k + 1) + w := by
          have hdm := Nat.div_add_mod w b
          rw [pow_succ]
          nlinarith
        rw [hrew]
      rcases hP with ⟨rfl, hu_eq⟩ | ⟨hPne, hPch, hPhd, hPlast⟩
      · refine ⟨[e], Or.inr ⟨List.cons_ne_nil _ _, trivial, ?_, by simpa using he_dst⟩⟩
        rw [List.head_cons, he_src]
        exact Fin.ext hu_eq.symm
      · refine ⟨P ++ [e], Or.inr ⟨List.append_ne_nil_of_right_ne_nil P (List.cons_ne_nil _ _), ?_, ?_, ?_⟩⟩
        · refine isChain_append hPne (List.cons_ne_nil _ _) hPch trivial ?_
          rw [List.head_cons, he_src]
          exact Fin.ext hPlast
        · rwa [List.head_append_of_ne_nil hPne]
        · simpa using he_dst
  have hconn : ∀ u v : Fin Vn, ∃ P : List (Fin M), (P = [] ∧ u = v) ∨
      (∃ hP : P ≠ [], IsChain src dst P ∧ src (P.head hP) = u ∧ dst (P.getLast hP) = v) := by
    intro u v
    obtain ⟨P, hP⟩ := hreach (L - 1) u v.val v.isLt
    have hmod_v : (u.val * b ^ (L - 1) + v.val) % Vn = v.val := by
      change (u.val * Vn + v.val) % Vn = v.val
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt v.isLt]
    rw [hmod_v] at hP
    refine ⟨P, ?_⟩
    rcases hP with ⟨h1, h2⟩ | ⟨hPne, hPch, hPhd, hPlast⟩
    · exact Or.inl ⟨h1, Fin.ext h2⟩
    · exact Or.inr ⟨hPne, hPch, hPhd, Fin.ext hPlast⟩
  -- Apply Hierholzer's theorem to obtain an Euler circuit `C` of length `M`.
  obtain ⟨C, hC, hC_len⟩ := exists_euler_circuit src dst hneE hbal hconn
  rw [Fintype.card_fin] at hC_len
  -- Define the cyclic sequence of edges `f i = (C[i % M]).val` and appended digits `d i = f i % b`.
  let f : ℕ → ℕ := fun i => (C[i % M]'(by rw [hC_len]; exact Nat.mod_lt i (by omega))).val
  let d : ℕ → ℕ := fun i => f i % b
  have hf_per : ∀ i, f (i + M) = f i := fun i => by simp [f]
  have hd_per : ∀ i, d (i + M) = d i := fun i => by simp [d, hf_per]
  have hd_lt : ∀ i, d i < b := fun i => Nat.mod_lt _ hb_pos
  have hf_lt : ∀ i, f i < M := fun i => (C[i % M]'(by rw [hC_len]; exact Nat.mod_lt i (by omega))).isLt
  have hf_step : ∀ i, f i % Vn = f (i + 1) / b := fun i =>
    congrArg Fin.val (isClosedTrail_getElem_mod hC hC_len (by omega) i)
  -- `f` hits every `v < M` exactly once on `range M`.
  have hf_bij : ∀ v < M, ((range M).filter fun i => f i = v).card = 1 := by
    intro v hv
    have hv_mem : (⟨v, hv⟩ : Fin M) ∈ C := by
      have hfull : C.toFinset = univ :=
        Finset.eq_univ_of_card C.toFinset (by rw [List.toFinset_card_of_nodup hC.2.1, hC_len, Fintype.card_fin])
      rw [← List.mem_toFinset, hfull]
      exact mem_univ _
    obtain ⟨i₀, hi₀, hi₀_eq⟩ := List.mem_iff_getElem.mp hv_mem
    have hi₀_lt : i₀ < M := by omega
    have hfilt : ((range M).filter fun i => f i = v) = {i₀} := by
      ext i
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hiM, hfi⟩
        have hEq : C[i]'(by omega) = C[i₀]'hi₀ := by
          apply Fin.ext
          rw [hi₀_eq]
          simpa [f, Nat.mod_eq_of_lt hiM] using hfi
        exact (List.Nodup.getElem_inj_iff hC.2.1).mp hEq
      · rintro rfl
        refine ⟨hi₀_lt, ?_⟩
        simp [f, Nat.mod_eq_of_lt hi₀_lt, hi₀_eq]
    rw [hfilt, card_singleton]
  -- Key window identity: `wordVal b d (j + 1) t = f (j + t) % b^t` for all `t ≤ L`.
  have hwin : ∀ j t, t ≤ L → wordVal b d (j + 1) t = f (j + t) % b ^ t := by
    intro j t
    induction t with
    | zero => intro _; simp [wordVal, Nat.mod_one]
    | succ t ih =>
      intro ht
      simp only [wordVal]
      rw [ih (by omega)]
      have ht_le : t ≤ L - 1 := by omega
      have hstep := hf_step (j + t)
      have hdvd : b ^ t ∣ Vn := Nat.pow_dvd_pow b ht_le
      have hmod_div : (f (j + (t + 1)) / b) % b ^ t = f (j + t) % b ^ t := by
        rw [show j + (t + 1) = j + t + 1 by omega, ← hstep, Nat.mod_mod_of_dvd _ hdvd]
      have hsplit : ∀ n : ℕ, n % b ^ (t + 1) = (n / b % b ^ t) * b + n % b := by
        intro n
        have h1 := Nat.div_add_mod n b
        have h2 := Nat.div_add_mod (n / b) (b ^ t)
        have hlt_rem : (n / b % b ^ t) * b + n % b < b ^ (t + 1) := by
          rw [pow_succ]
          have : n / b % b ^ t + 1 ≤ b ^ t := Nat.mod_lt _ (pow_pos hb_pos t)
          have : n % b < b := Nat.mod_lt n hb_pos
          nlinarith
        have h3 : n = b ^ (t + 1) * (n / b / b ^ t) + ((n / b % b ^ t) * b + n % b) := by
          rw [pow_succ]; nlinarith
        conv_lhs => rw [h3]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_rem]
      rw [show j + 1 + t = j + (t + 1) by omega]
      dsimp [d]
      rw [hsplit (f (j + (t + 1))), hmod_div]
  have hwin_L : ∀ j, wordVal b d j L = f (j + L - 1) := by
    intro j
    have h1 := hwin (j + M - 1) L le_rfl
    have h2 : wordVal b d (j + M - 1 + 1) L = wordVal b d j L := by
      refine wordVal_congr fun i _ => ?_
      rw [show j + M - 1 + 1 + i = (j + i) + M by omega, hd_per]
    rw [h2, Nat.mod_eq_of_lt (hf_lt _)] at h1
    rw [h1]
    have : j + M - 1 + L = (j + L - 1) + M := by omega
    rw [this, hf_per]
  -- Define `r_j := wordVal b d j M` and `r := r_0`.
  let rot : ℕ → ℕ := fun j => wordVal b d j M
  set q : ℕ := b ^ M - 1
  have hq_pos : 0 < q := by
    have : 2 ≤ b ^ M := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hrot_pos_lt : ∀ j, 0 < rot j ∧ rot j < q := by
    intro j
    have hlt_bM : rot j < b ^ M := wordVal_lt hd_lt j M
    have hne0 : rot j ≠ 0 := by
      intro h0
      have hall0 := (wordVal_eq_zero_iff (by omega) d j M).mp h0
      have hd0 : ∀ i, d i = 0 := by
        intro i
        have hper_d : ∀ k n, d (n + k * M) = d n := by
          intro k n; induction k with
          | zero => simp
          | succ k ih => rw [show n + (k + 1) * M = (n + k * M) + M by ring, hd_per, ih]
        set t := (i + M - j % M) % M
        have ht_lt : t < M := Nat.mod_lt _ (by omega)
        have hcong : (j + t) % M = i % M := by
          have h1 : (j + t) % M = (j % M + t) % M := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          dsimp [t]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hjm : j % M < M := Nat.mod_lt j (by omega)
          have hjm_le : j % M ≤ j := Nat.mod_le j M
          have : j + (i + M - j % M) = (j - j % M + M) + i := by omega
          have hdvd_j : M ∣ j - j % M := by
            have := Nat.div_add_mod j M
            exact ⟨j / M, by omega⟩
          obtain ⟨c, hc⟩ := hdvd_j
          rw [this, hc, show M * c + M + i = i + (c + 1) * M by ring, Nat.add_mul_mod_self_right]
        have heq_d : d (j + t) = d i := by
          have hd_mod : ∀ n, d n = d (n % M) := fun n => by
            have hdm := Nat.div_add_mod n M
            conv_lhs => rw [← hdm, add_comm, mul_comm]
            exact hper_d (n / M) (n % M)
          rw [hd_mod (j + t), hcong, ← hd_mod i]
        rw [← heq_d]
        exact hall0 t ht_lt
      have hcard1 := hf_bij 1 (by omega)
      have hne_f : ((range M).filter fun i => f i = 1).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₀, hi₀⟩ := hne_f
      have hfi₀ : f i₀ = 1 := (mem_filter.mp hi₀).2
      have hw0 : wordVal b d (i₀ + M + 1 - L) L = 0 :=
        (wordVal_eq_zero_iff (by omega) d _ L).mpr fun i _ => hd0 _
      rw [hwin_L] at hw0
      have : i₀ + M + 1 - L + L - 1 = i₀ + M := by omega
      rw [this, hf_per, hfi₀] at hw0
      omega
    have hneq : rot j ≠ q := by
      intro hmax
      have hall := (wordVal_eq_max_iff hb hd_lt j M).mp hmax
      have hdtop : ∀ i, d i = b - 1 := by
        intro i
        have hper_d : ∀ k n, d (n + k * M) = d n := by
          intro k n; induction k with
          | zero => simp
          | succ k ih => rw [show n + (k + 1) * M = (n + k * M) + M by ring, hd_per, ih]
        set t := (i + M - j % M) % M
        have ht_lt : t < M := Nat.mod_lt _ (by omega)
        have hcong : (j + t) % M = i % M := by
          dsimp [t]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hjm : j % M < M := Nat.mod_lt j (by omega)
          have hjm_le : j % M ≤ j := Nat.mod_le j M
          have : j + (i + M - j % M) = (j - j % M + M) + i := by omega
          have hdvd_j : M ∣ j - j % M := by
            have := Nat.div_add_mod j M
            exact ⟨j / M, by omega⟩
          obtain ⟨c, hc⟩ := hdvd_j
          rw [this, hc, show M * c + M + i = i + (c + 1) * M by ring, Nat.add_mul_mod_self_right]
        have heq_d : d (j + t) = d i := by
          have hd_mod : ∀ n, d n = d (n % M) := fun n => by
            have hdm := Nat.div_add_mod n M
            conv_lhs => rw [← hdm, add_comm, mul_comm]
            exact hper_d (n / M) (n % M)
          rw [hd_mod (j + t), hcong, ← hd_mod i]
        rw [← heq_d]
        exact hall t ht_lt
      have hcard0 := hf_bij 0 (by omega)
      have hne_f : ((range M).filter fun i => f i = 0).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₀, hi₀⟩ := hne_f
      have hfi₀ : f i₀ = 0 := (mem_filter.mp hi₀).2
      have hwtop : wordVal b d (i₀ + M + 1 - L) L = b ^ L - 1 :=
        (wordVal_eq_max_iff hb hd_lt _ L).mpr fun i _ => hdtop _
      rw [hwin_L] at hwtop
      have : i₀ + M + 1 - L + L - 1 = i₀ + M := by omega
      rw [this, hf_per, hfi₀] at hwtop
      omega
    omega
  -- Verify `b ^ j * rot 0 % q = rot j` by induction on `j`.
  have hrot_shift : ∀ j, b ^ j * rot 0 % q = rot j := by
    intro j
    induction j with
    | zero => simpa using Nat.mod_eq_of_lt (hrot_pos_lt 0).2
    | succ j ih =>
      have hstep_rot : b * rot j = d j * q + rot (j + 1) := by
        have h1 : rot j = d j * b ^ (M - 1) + wordVal b d (j + 1) (M - 1) := by
          dsimp [rot]
          conv_lhs => rw [show M = 1 + (M - 1) by omega]
          rw [wordVal_add]
          simp [wordVal]
        have h2 : rot (j + 1) = wordVal b d (j + 1) (M - 1) * b + d j := by
          dsimp [rot]
          conv_lhs => rw [show M = (M - 1) + 1 by omega]
          rw [wordVal]
          have : j + 1 + (M - 1) = j + M := by omega
          rw [this, hd_per]
        have hpowM : b * b ^ (M - 1) = b ^ M := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega)]
        have h1_le : 1 ≤ b ^ M := Nat.one_le_pow M b (by omega)
        zify [h1_le]
        have h1z : (rot j : ℤ) = (d j : ℤ) * (b : ℤ) ^ (M - 1) + (wordVal b d (j + 1) (M - 1) : ℤ) := by
          exact_mod_cast h1
        have h2z : (rot (j + 1) : ℤ) = (wordVal b d (j + 1) (M - 1) : ℤ) * (b : ℤ) + (d j : ℤ) := by
          exact_mod_cast h2
        have hpowz : (b : ℤ) * (b : ℤ) ^ (M - 1) = (b : ℤ) ^ M := by exact_mod_cast hpowM
        dsimp [q]
        rw [Nat.cast_sub h1_le, Nat.cast_pow, Nat.cast_one]
        linear_combination (b : ℤ) * h1z - h2z + (d j : ℤ) * hpowz
      rw [pow_succ', mul_assoc, Nat.mul_mod, ih, Nat.mod_mul_mod, hstep_rot,
        mul_comm (d j) q, Nat.mul_add_mod, Nat.mod_eq_of_lt (hrot_pos_lt (j + 1)).2]
  -- Verify `b ^ L * rot j / q = wordVal b d j L`.
  have hdiv_word : ∀ j, b ^ L * rot j / q = wordVal b d j L := by
    intro j
    have h1 : rot j = wordVal b d j L * b ^ (M - L) + wordVal b d (j + L) (M - L) := by
      dsimp [rot]
      conv_lhs => rw [show M = L + (M - L) by omega]
      exact wordVal_add b d j L (M - L)
    have h2 : rot (j + L) = wordVal b d (j + L) (M - L) * b ^ L + wordVal b d j L := by
      dsimp [rot]
      conv_lhs => rw [show M = (M - L) + L by omega]
      rw [wordVal_add]
      congr 1
      refine wordVal_congr fun i _ => ?_
      rw [show j + L + (M - L) + i = (j + i) + M by omega, hd_per]
    have hpowM : b ^ L * b ^ (M - L) = b ^ M := by
      rw [← pow_add, Nat.add_sub_cancel' hL_le_M]
    have hmul_eq : b ^ L * rot j = wordVal b d j L * q + rot (j + L) := by
      have h1_le : 1 ≤ b ^ M := Nat.one_le_pow M b (by omega)
      zify [h1_le]
      have h1z : (rot j : ℤ) = (wordVal b d j L : ℤ) * (b : ℤ) ^ (M - L) +
          (wordVal b d (j + L) (M - L) : ℤ) := by exact_mod_cast h1
      have h2z : (rot (j + L) : ℤ) = (wordVal b d (j + L) (M - L) : ℤ) * (b : ℤ) ^ L +
          (wordVal b d j L : ℤ) := by exact_mod_cast h2
      have hpowz : (b : ℤ) ^ L * (b : ℤ) ^ (M - L) = (b : ℤ) ^ M := by exact_mod_cast hpowM
      dsimp [q]
      rw [Nat.cast_sub h1_le, Nat.cast_pow, Nat.cast_one]
      linear_combination (b : ℤ) ^ L * h1z - h2z + (wordVal b d j L : ℤ) * hpowz
    rw [hmul_eq, mul_comm (wordVal b d j L) q, Nat.mul_add_div hq_pos,
      Nat.div_eq_of_lt (hrot_pos_lt (j + L)).2, add_zero]
  -- Prove the length-`L` balance once and reuse it for length `L + 1`.
  have hbal_L : ∀ v < M, cyclicCount b M L (rot 0) v = 1 := by
    intro v hv
    have hcongr : ((range M).filter fun j => b ^ L * (b ^ j * rot 0 % q) / q = v) =
        ((range M).filter fun j => f (j + L - 1) = v) := by
      refine Finset.filter_congr fun j _ => ?_
      rw [hrot_shift j, hdiv_word j, hwin_L j]
    change ((range M).filter fun j => b ^ L * (b ^ j * rot 0 % q) / q = v).card = 1
    rw [hcongr]
    refine Eq.trans ?_ (hf_bij v hv)
    refine Finset.card_bij (fun j _ => (j + L - 1) % M) ?_ ?_ ?_
    · intro j hj
      obtain ⟨_, hfj⟩ := mem_filter.mp hj
      refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
      have hf_mod : ∀ n, f (n % M) = f n := fun n => by
        have hdm := Nat.div_add_mod n M
        have hper_k : ∀ k m, f (m + k * M) = f m := by
          intro k m; induction k with
          | zero => simp
          | succ k ih => rw [show m + (k + 1) * M = (m + k * M) + M by ring, hf_per, ih]
        conv_rhs => rw [← hdm, add_comm, mul_comm]
        exact (hper_k (n / M) (n % M)).symm
      rwa [hf_mod]
    · intro j₁ hj₁ j₂ hj₂ heq
      have h1 : j₁ < M := mem_range.mp (mem_filter.mp hj₁).1
      have h2 : j₂ < M := mem_range.mp (mem_filter.mp hj₂).1
      have hmod1 : (j₁ + (L - 1)) % M = (j₂ + (L - 1)) % M := by
        simpa only [show j₁ + L - 1 = j₁ + (L - 1) by omega,
          show j₂ + L - 1 = j₂ + (L - 1) by omega] using heq
      by_cases c1 : j₁ + (L - 1) < M <;> by_cases c2 : j₂ + (L - 1) < M
      · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hmod1; omega
      · have hlt2 : j₂ + (L - 1) - M < M := by omega
        have hm2 : (j₂ + (L - 1)) % M = j₂ + (L - 1) - M := by
          conv_lhs => rw [show j₂ + (L - 1) = (j₂ + (L - 1) - M) + M by omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        rw [Nat.mod_eq_of_lt c1, hm2] at hmod1; omega
      · have hlt1 : j₁ + (L - 1) - M < M := by omega
        have hm1 : (j₁ + (L - 1)) % M = j₁ + (L - 1) - M := by
          conv_lhs => rw [show j₁ + (L - 1) = (j₁ + (L - 1) - M) + M by omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
        rw [hm1, Nat.mod_eq_of_lt c2] at hmod1; omega
      · have hlt1 : j₁ + (L - 1) - M < M := by omega
        have hlt2 : j₂ + (L - 1) - M < M := by omega
        have hm1 : (j₁ + (L - 1)) % M = j₁ + (L - 1) - M := by
          conv_lhs => rw [show j₁ + (L - 1) = (j₁ + (L - 1) - M) + M by omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
        have hm2 : (j₂ + (L - 1)) % M = j₂ + (L - 1) - M := by
          conv_lhs => rw [show j₂ + (L - 1) = (j₂ + (L - 1) - M) + M by omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        rw [hm1, hm2] at hmod1; omega
    · intro i hi
      obtain ⟨hiM, hfi⟩ := mem_filter.mp hi
      have hi_lt : i < M := mem_range.mp hiM
      set j := (i + M - (L - 1)) % M
      have hj_lt : j < M := Nat.mod_lt _ (by omega)
      have hj_mod : (j + L - 1) % M = i := by
        rw [show j + L - 1 = j + (L - 1) by omega]
        dsimp [j]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have : i + M - (L - 1) + (L - 1) = i + M := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi_lt]
      refine ⟨j, mem_filter.mpr ⟨mem_range.mpr hj_lt, ?_⟩, hj_mod⟩
      have hf_mod : ∀ n, f n = f (n % M) := fun n => by
        have hdm := Nat.div_add_mod n M
        have hper_k : ∀ k m, f (m + k * M) = f m := by
          intro k m; induction k with
          | zero => simp
          | succ k ih => rw [show m + (k + 1) * M = (m + k * M) + M by ring, hf_per, ih]
        conv_lhs => rw [← hdm, add_comm, mul_comm]
        exact hper_k (n / M) (n % M)
      rw [hf_mod (j + L - 1), hj_mod, hfi]
  -- Assemble all four claims for `r := rot 0`.
  refine ⟨rot 0, (hrot_pos_lt 0).1, (hrot_pos_lt 0).2, hbal_L, ?_⟩
  · -- Length-`(L + 1)` count is at most the length-`L` count of `v / b`, which is `1`.
    intro v hv
    have hv_div : v / b < M := (Nat.div_lt_iff_lt_mul hb_pos).mpr (by simpa [M, pow_succ] using hv)
    refine le_trans ?_ (hbal_L (v / b) hv_div).le
    change ((range M).filter fun j => b ^ (L + 1) * (b ^ j * rot 0 % q) / q = v).card ≤
      ((range M).filter fun j => b ^ L * (b ^ j * rot 0 % q) / q = v / b).card
    refine card_le_card fun j hj => ?_
    obtain ⟨hjM, hv_eq⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨hjM, ?_⟩
    set y := b ^ j * rot 0 % q
    have hdiv_step : b ^ (L + 1) * y / q / b = b ^ L * y / q := by
      have hdm := Nat.div_add_mod (b ^ L * y) q
      set w := b ^ L * y / q
      set rem := b ^ L * y % q
      have hrem_lt : rem < q := Nat.mod_lt _ hq_pos
      have hmul : b ^ (L + 1) * y = q * (b * w) + b * rem := by
        rw [pow_succ']
        nlinarith
      have hdiv1 : b ^ (L + 1) * y / q = b * w + b * rem / q := by
        rw [hmul, Nat.mul_add_div hq_pos]
      have hrem_div : b * rem / q < b := (Nat.div_lt_iff_lt_mul hq_pos).mpr (by nlinarith)
      rw [hdiv1, Nat.mul_add_div hb_pos, Nat.div_eq_of_lt hrem_div, add_zero]
    rw [← hdiv_step, hv_eq]

/-! ### Part 5: Irrational sparse zero-orbit perturbation -/

/-- The sparse quadratic-schedule perturbation `u_b = ∑_{k ≥ 0} b^(-(k + 1)(k + 2))`. -/
noncomputable def sparseQuadPerturb (b : ℕ) : ℝ :=
  sparseValue b (fun k => (k + 1) * (k + 2)) (fun _ => 1)

/-- `sparseQuadPerturb b` belongs to `zeroOrbitSubgroup b` for every `b ≥ 2`. -/
theorem sparseQuadPerturb_mem_zeroOrbit {b : ℕ} (hb : 2 ≤ b) :
    sparseQuadPerturb b ∈ zeroOrbitSubgroup b := by
  classical
  change Tendsto (circMean b (sparseQuadPerturb b)) atTop (𝓝 0)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb_pos : (0 : ℝ) < b := by linarith
  have hr_pos : (0 : ℝ) < (b : ℝ)⁻¹ := inv_pos.mpr hb_pos
  have hr_lt1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have hmono : StrictMono (fun k : ℕ => (k + 1) * (k + 2)) := fun i j hij => by dsimp; nlinarith
  -- Finite upper bound: for every `w` and `N ≥ 1`,
  -- `circMean b u N ≤ 2 * b^(-w) + (w * sqrt (N + w)) / N`.
  have hbound : ∀ w N : ℕ, 1 ≤ N →
      circMean b (sparseQuadPerturb b) N ≤
        2 * ((b : ℝ)⁻¹) ^ w + ((w * Nat.sqrt (N + w) : ℕ) : ℝ) / (N : ℝ) := by
    intro w N hN
    set u := sparseQuadPerturb b
    set ε : ℝ := 2 * ((b : ℝ)⁻¹) ^ w
    have hε_nn : 0 ≤ ε := by positivity
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    set G := (range N).filter fun n => Near ((b : ℝ) ^ n * u) ε
    set B := (range N).filter fun n => ¬ Near ((b : ℝ) ^ n * u) ε
    have hsplit : ∑ n ∈ range N, circDist (shift b u n) =
        (∑ n ∈ G, circDist (shift b u n)) + ∑ n ∈ B, circDist (shift b u n) := by
      rw [← Finset.sum_filter_add_sum_filter_not (range N) (fun n => Near ((b : ℝ) ^ n * u) ε)]
    have hG_sum : ∑ n ∈ G, circDist (shift b u n) ≤ (N : ℝ) * ε := by
      calc ∑ n ∈ G, circDist (shift b u n)
          ≤ ∑ _n ∈ G, ε := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hnear := (mem_filter.mp hn).2
            rw [near_iff_distInt_le, distInt_eq_circDist] at hnear
            unfold shift; rwa [circDist_fract]
        _ = (G.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * ε := mul_le_mul_of_nonneg_right
            (by exact_mod_cast ((card_filter_le _ _).trans_eq (card_range N))) hε_nn
    have hB_sum : ∑ n ∈ B, circDist (shift b u n) ≤ (B.card : ℝ) := by
      calc ∑ n ∈ B, circDist (shift b u n)
          ≤ ∑ _n ∈ B, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => (circDist_le_half _).trans (by norm_num)
        _ = (B.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hB_card : B.card ≤ w * Nat.sqrt (N + w) := by
      have hfar := sparse_farCount_le hb hmono (A := fun _ => 1) (B := 1) (ε := ε)
        (fun _ => by simp) (w := w) (by simp [ε]) N
      exact hfar.trans (Nat.mul_le_mul_left w (quadratic_insertions_le (N + w)))
    have hB_r : (B.card : ℝ) ≤ ((w * Nat.sqrt (N + w) : ℕ) : ℝ) := by exact_mod_cast hB_card
    unfold circMean
    rw [hsplit]
    calc ((∑ n ∈ G, circDist (shift b u n)) + ∑ n ∈ B, circDist (shift b u n)) / (N : ℝ)
        ≤ ((N : ℝ) * ε + ((w * Nat.sqrt (N + w) : ℕ) : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hNr.le
      _ = ε + ((w * Nat.sqrt (N + w) : ℕ) : ℝ) / (N : ℝ) := by
          rw [add_div, mul_div_cancel_left₀ _ hNr.ne']
  -- Prove convergence to `0` using `Metric.tendsto_atTop`.
  rw [Metric.tendsto_atTop]
  intro η hη
  have hpow_tend : Tendsto (fun w : ℕ => 2 * ((b : ℝ)⁻¹) ^ w) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr_pos.le hr_lt1).const_mul 2
  obtain ⟨w, hw⟩ := (Metric.tendsto_atTop.mp hpow_tend (η / 2) (by positivity)).imp fun w hw => hw w le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hw
  set N₀ : ℕ := max (max w 1) (Nat.ceil (8 * (w : ℝ) ^ 2 / η ^ 2) + 1)
  refine ⟨N₀, fun N hN => ?_⟩
  have hNw : w ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNceil : Nat.ceil (8 * (w : ℝ) ^ 2 / η ^ 2) + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsqrt_small : ((w * Nat.sqrt (N + w) : ℕ) : ℝ) / (N : ℝ) < η / 2 := by
    rw [div_lt_iff₀ hNr]
    have hsq_lt : (((w * Nat.sqrt (N + w) : ℕ) : ℝ)) ^ 2 < (η / 2 * (N : ℝ)) ^ 2 := by
      have hN_gt : 8 * (w : ℝ) ^ 2 / η ^ 2 < (N : ℝ) := by
        have hc : 8 * (w : ℝ) ^ 2 / η ^ 2 ≤ (Nat.ceil (8 * (w : ℝ) ^ 2 / η ^ 2) : ℝ) :=
          Nat.le_ceil _
        have h1 : (Nat.ceil (8 * (w : ℝ) ^ 2 / η ^ 2) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNceil
        linarith
      have hsq_nat : Nat.sqrt (N + w) ^ 2 ≤ 2 * N := by
        rw [sq]
        exact (Nat.sqrt_le (N + w)).trans (by omega)
      have hsq_r : ((Nat.sqrt (N + w) : ℝ)) ^ 2 ≤ 2 * (N : ℝ) := by exact_mod_cast hsq_nat
      have hmul_lt : 8 * (w : ℝ) ^ 2 < η ^ 2 * (N : ℝ) := by
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < η ^ 2)).mp hN_gt
        linarith
      have hmul_N : 2 * (w : ℝ) ^ 2 * (N : ℝ) < (η / 2 * (N : ℝ)) ^ 2 := by
        have h1 : 8 * (w : ℝ) ^ 2 * (N : ℝ) < η ^ 2 * (N : ℝ) * (N : ℝ) :=
          mul_lt_mul_of_pos_right hmul_lt hNr
        nlinarith
      push_cast
      rw [mul_pow]
      have h2 : (w : ℝ) ^ 2 * (Nat.sqrt (N + w) : ℝ) ^ 2 ≤ (w : ℝ) ^ 2 * (2 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq_r (by positivity)
      linarith
    nlinarith [show 0 ≤ ((w * Nat.sqrt (N + w) : ℕ) : ℝ) by positivity,
      show 0 ≤ η / 2 * (N : ℝ) by positivity]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (circMean_nonneg b _ N)]
  linarith [hbound w N hN1]

/-- `sparseQuadPerturb b` is irrational for every base `b ≥ 2`. -/
theorem sparseQuadPerturb_irrational {b : ℕ} (hb : 2 ≤ b) :
    Irrational (sparseQuadPerturb b) := by
  intro ⟨q, hq⟩
  set m : ℕ → ℕ := fun k => (k + 1) * (k + 2)
  have hmono : StrictMono m := fun i j hij => by dsimp [m]; nlinarith
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb_pos : (0 : ℝ) < b := by linarith
  have hr_pos : (0 : ℝ) < (b : ℝ)⁻¹ := inv_pos.mpr hb_pos
  have hr_lt1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  set f : ℕ → ℝ := fun k => ((b : ℝ) ^ m k)⁻¹
  have hu_eq : sparseQuadPerturb b = ∑' k, f k := by
    unfold sparseQuadPerturb sparseValue
    simp [f, m]
  have hf_sum : Summable f := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (summable_geometric_of_lt_one hr_pos.le hr_lt1)
    dsimp [f]
    rw [← inv_pow]
    exact pow_le_pow_of_le_one hr_pos.le hr_lt1.le (hmono.id_le k)
  set K : ℕ := q.den
  have hK_pos : 0 < K := q.den_pos
  have hKr_pos : (0 : ℝ) < K := by exact_mod_cast hK_pos
  have hq_mul : (K : ℝ) * sparseQuadPerturb b = (q.num : ℝ) := by
    rw [← hq, Rat.cast_def]
    dsimp [K]
    field_simp [hKr_pos.ne']
  -- Split `u = head + tail` at `K + 1` and multiply by `K * b^(m K)`.
  have hsplit := hf_sum.sum_add_tsum_nat_add (K + 1)
  set tail : ℝ := (K : ℝ) * (b : ℝ) ^ m K * ∑' i, f (i + (K + 1))
  -- 1. `tail` is an integer.
  have htail_int : ∃ z : ℤ, tail = (z : ℝ) := by
    refine ⟨q.num * (b : ℤ) ^ m K -
        ∑ k ∈ range (K + 1), (K : ℤ) * (b : ℤ) ^ (m K - m k), ?_⟩
    have hhead : (K : ℝ) * (b : ℝ) ^ m K * ∑ k ∈ range (K + 1), f k =
        ((∑ k ∈ range (K + 1), (K : ℤ) * (b : ℤ) ^ (m K - m k) : ℤ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkle : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hmle : m k ≤ m K := hmono.monotone hkle
      have hpow : (b : ℝ) ^ m K = (b : ℝ) ^ (m K - m k) * (b : ℝ) ^ m k := by
        rw [← pow_add, Nat.sub_add_cancel hmle]
      dsimp [f]
      rw [hpow]
      field_simp [(pow_pos hb_pos (m k)).ne']
    rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hhead, ← hq_mul]
    dsimp [tail]
    rw [hu_eq, ← hsplit]
    ring
  -- 2. `tail > 0`.
  have htail_pos : 0 < tail := by
    have htsum_pos : 0 < ∑' i, f (i + (K + 1)) := by
      have hsum_tail : Summable (fun i => f (i + (K + 1))) :=
        hf_sum.comp_injective (add_left_injective (K + 1))
      have h0_pos : 0 < f (0 + (K + 1)) := by dsimp [f]; positivity
      have hle : f (0 + (K + 1)) ≤ ∑' i, f (i + (K + 1)) :=
        hsum_tail.le_tsum 0 fun i _ => by dsimp [f]; positivity
      linarith
    dsimp [tail]
    positivity
  -- 3. `tail < 1`.
  have htail_lt1 : tail < 1 := by
    have hgap : m (K + 1) - m K = 2 * (K + 2) := by
      dsimp [m]
      exact Nat.sub_eq_of_eq_add (by ring)
    have hsum_tail : Summable (fun i => f (i + (K + 1))) :=
      hf_sum.comp_injective (add_left_injective (K + 1))
    have hgeom : Summable (fun i => ((b : ℝ) ^ m (K + 1))⁻¹ * ((b : ℝ)⁻¹) ^ i) :=
      (summable_geometric_of_lt_one hr_pos.le hr_lt1).mul_left _
    have hle_sum : ∑' i, f (i + (K + 1)) ≤ 2 * ((b : ℝ) ^ m (K + 1))⁻¹ := by
      have hterm : ∀ i, f (i + (K + 1)) ≤ ((b : ℝ) ^ m (K + 1))⁻¹ * ((b : ℝ)⁻¹) ^ i := by
        intro i
        dsimp [f]
        have hm_ge : m (K + 1) + i ≤ m (i + (K + 1)) := by
          have := hmono.add_le_nat i (K + 1); omega
        rw [← inv_pow, ← inv_pow, ← pow_add]
        exact pow_le_pow_of_le_one hr_pos.le hr_lt1.le hm_ge
      have h1 := Summable.tsum_le_tsum hterm hsum_tail hgeom
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr_pos.le hr_lt1] at h1
      have hhalf : (1 - (b : ℝ)⁻¹)⁻¹ ≤ 2 := by
        have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
        have : (b : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hb2
        exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
      calc ∑' i, f (i + (K + 1))
          ≤ ((b : ℝ) ^ m (K + 1))⁻¹ * (1 - (b : ℝ)⁻¹)⁻¹ := h1
        _ ≤ ((b : ℝ) ^ m (K + 1))⁻¹ * 2 := mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ = 2 * ((b : ℝ) ^ m (K + 1))⁻¹ := by ring
    have htail_le : tail ≤ 2 * (K : ℝ) / (b : ℝ) ^ (m (K + 1) - m K) := by
      dsimp [tail]
      have hpow : (b : ℝ) ^ m (K + 1) = (b : ℝ) ^ m K * (b : ℝ) ^ (m (K + 1) - m K) := by
        rw [← pow_add, Nat.add_sub_cancel' (hmono.monotone (Nat.le_succ K))]
      calc (K : ℝ) * (b : ℝ) ^ m K * ∑' i, f (i + (K + 1))
          ≤ (K : ℝ) * (b : ℝ) ^ m K * (2 * ((b : ℝ) ^ m (K + 1))⁻¹) :=
            mul_le_mul_of_nonneg_left hle_sum (by positivity)
        _ = 2 * (K : ℝ) / (b : ℝ) ^ (m (K + 1) - m K) := by
            rw [hpow]
            field_simp [(pow_pos hb_pos (m K)).ne', (pow_pos hb_pos (m (K + 1) - m K)).ne']
    have h2K_lt : 2 * K < b ^ (m (K + 1) - m K) := by
      rw [hgap]
      have h1 : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
      have h2 : 2 * K < 2 ^ (K + 2) := by rw [pow_succ']; omega
      have h3 : 2 ^ (K + 2) ≤ 2 ^ (2 * (K + 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : 2 ^ (2 * (K + 2)) ≤ b ^ (2 * (K + 2)) := Nat.pow_le_pow_left hb _
      omega
    have h2K_r : 2 * (K : ℝ) < (b : ℝ) ^ (m (K + 1) - m K) := by exact_mod_cast h2K_lt
    have hdiv_lt1 : 2 * (K : ℝ) / (b : ℝ) ^ (m (K + 1) - m K) < 1 :=
      (div_lt_one (pow_pos hb_pos _)).mpr h2K_r
    linarith
  obtain ⟨z, hz⟩ := htail_int
  rw [hz] at htail_pos htail_lt1
  have hz0 : (0 : ℤ) < z := by exact_mod_cast htail_pos
  have hz1 : z < 1 := by exact_mod_cast htail_lt1
  omega

/-- Adding a rational to an irrational yields an irrational. -/
private lemma irrational_rat_add {q : ℚ} {u : ℝ} (hu : Irrational u) :
    Irrational ((q : ℝ) + u) := by
  intro ⟨r, hr⟩
  exact hu ⟨r - q, by push_cast; linarith⟩

/-! ### Part 6: Higher-order tower classification and binary `(2, 1)` witness -/

/-- **Main Higher-Order Tower Classification (irrational exact-order form):**
for `b ≥ 2`, `k ≥ 2`, and `L ≥ 1`, there exists an irrational `x ∈ K_{b^k} \ K_b` that is
`L`-normal and not `(L + 1)`-normal in base `b` if and only if `b^L ∣ k`. -/
theorem tower_irrational_exact_iff {b k L : ℕ}
    (hb : 2 ≤ b) (hk : 2 ≤ k) (hL : 1 ≤ L) :
    (∃ x, Irrational x ∧ x ∈ Kernel (b ^ k) \ Kernel b ∧
      OrderNormal b L x ∧ ¬ OrderNormal b (L + 1) x) ↔ b ^ L ∣ k := by
  constructor
  · -- Necessity: use `mem_pow_kernel_decomp`, `wordFreq_tower_limit` at `v = 0`, and clear denominators.
    rintro ⟨x, _, ⟨hx_pow, hx_not⟩, hnorm, _⟩
    obtain ⟨r, hr_lt, u, hu, hxeq, _, hKb_iff⟩ := mem_pow_kernel_decomp hb hk hx_pow
    have hr_pos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · exact absurd (hKb_iff.mpr (by simp)) hx_not
      · exact hpos
    have hlim1 := wordFreq_tower_limit hb hk hL hr_pos hr_lt hu 0
    rw [← hxeq] at hlim1
    have hlim2 := hnorm 0 (pow_pos (by omega) L)
    have heq := tendsto_nhds_unique hlim1 hlim2
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hbL_ne : (b : ℝ) ^ L ≠ 0 := pow_ne_zero L (by exact_mod_cast (show b ≠ 0 by omega))
    have hmul_r : (cyclicCount b k L r 0 : ℝ) * (b : ℝ) ^ L = (k : ℝ) := by
      field_simp [hk_ne, hbL_ne] at heq
      linarith
    have hmul_n : cyclicCount b k L r 0 * b ^ L = k := by exact_mod_cast hmul_r
    exact ⟨cyclicCount b k L r 0, by linarith⟩
  · -- Sufficiency: repeat a balanced de Bruijn block and add `sparseQuadPerturb b`.
    intro hdvd
    set M : ℕ := b ^ L
    have hM_ge2 : 2 ≤ M :=
      (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) hL)
    obtain ⟨r₀, hr₀_pos, hr₀_lt, hbal_L, _⟩ := exists_balanced_block hb hL
    set Q₀ : ℕ := b ^ M - 1
    set Q : ℕ := b ^ k - 1
    have hQ₀_pos : 0 < Q₀ := by
      have : 2 ≤ b ^ M := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) (by omega))
      omega
    have hQ_pos : 0 < Q := by
      have : 2 ≤ b ^ k := (show 2 ≤ b ^ 1 by simpa using hb).trans (Nat.pow_le_pow_right (by omega) (by omega))
      omega
    have hQ₀_dvd_Q : Q₀ ∣ Q := (pow_sub_one_dvd_pow_sub_one_iff hb (by omega) (by omega)).mpr hdvd
    set S : ℕ := Q / Q₀
    have hQ_eq : Q₀ * S = Q := Nat.mul_div_cancel' hQ₀_dvd_Q
    have hS_pos : 0 < S := by
      rcases Nat.eq_zero_or_pos S with h0 | hpos
      · rw [h0, mul_zero] at hQ_eq; omega
      · exact hpos
    set r : ℕ := r₀ * S
    have hr_lt_Q : r < Q := by
      calc r = r₀ * S := rfl
        _ < Q₀ * S := Nat.mul_lt_mul_of_pos_right hr₀_lt hS_pos
        _ = Q := hQ_eq
    have hQ₀_cast : (Q₀ : ℝ) = (b : ℝ) ^ M - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hQ_cast : (Q : ℝ) = (b : ℝ) ^ k - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hrat_eq : (r₀ : ℝ) / ((b : ℝ) ^ M - 1) = (r : ℝ) / ((b : ℝ) ^ k - 1) := by
      rw [← hQ₀_cast, ← hQ_cast]
      have hQ₀_r : (Q₀ : ℝ) ≠ 0 := by exact_mod_cast hQ₀_pos.ne'
      have hQ_r : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ_pos.ne'
      have hQS_r : (Q₀ : ℝ) * (S : ℝ) = (Q : ℝ) := by exact_mod_cast hQ_eq
      rw [div_eq_div_iff hQ₀_r hQ_r, ← hQS_r]
      dsimp [r]; push_cast; ring
    set u : ℝ := sparseQuadPerturb b
    have hu_mem : u ∈ zeroOrbitSubgroup b := sparseQuadPerturb_mem_zeroOrbit hb
    have hu_irr : Irrational u := sparseQuadPerturb_irrational hb
    set x : ℝ := (r₀ : ℝ) / ((b : ℝ) ^ M - 1) + u
    refine ⟨x, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · -- `Irrational x`
      have hq_eq : (((r₀ : ℚ) / (Q₀ : ℚ) : ℚ) : ℝ) = (r₀ : ℝ) / ((b : ℝ) ^ M - 1) := by
        push_cast; rw [hQ₀_cast]
      dsimp [x]
      rw [← hq_eq]
      exact irrational_rat_add (q := (r₀ : ℚ) / (Q₀ : ℚ)) hu_irr
    · -- `x ∈ Kernel (b ^ k)`
      dsimp [x]
      rw [hrat_eq]
      exact rat_add_zeroOrbit_mem_pow_kernel hb (by omega) r hu_mem
    · -- `x ∉ Kernel b`
      have hx_pow : x ∈ Kernel (b ^ k) := by
        dsimp [x]; rw [hrat_eq]; exact rat_add_zeroOrbit_mem_pow_kernel hb (by omega) r hu_mem
      obtain ⟨r', hr'_lt, u', hu', hx', huniq, hKb_iff⟩ := mem_pow_kernel_decomp hb hk hx_pow
      have hreq : r = r' := (huniq r hr_lt_Q u hu_mem (by dsimp [x]; rw [hrat_eq])).1
      subst hreq
      rw [hKb_iff]
      intro hdvd_Q
      -- `Q ∣ (b - 1) * (r₀ * S)` implies `Q₀ ∣ (b - 1) * r₀`, which forces `b^j * r₀ % Q₀ = r₀` for all `j`.
      have hdvd_Q₀ : Q₀ ∣ (b - 1) * r₀ := by
        have h1 : Q₀ * S ∣ ((b - 1) * r₀) * S := by
          rw [hQ_eq, mul_assoc]; exact hdvd_Q
        exact (Nat.mul_dvd_mul_iff_right hS_pos).mp h1
      obtain ⟨m, hm⟩ := hdvd_Q₀
      have hstep : ∀ j, b ^ j * r₀ % Q₀ = r₀ := by
        intro j
        induction j with
        | zero => simpa using Nat.mod_eq_of_lt hr₀_lt
        | succ j ih =>
          have hbr : b * r₀ = m * Q₀ + r₀ := by
            have h1 : (b - 1) * r₀ + r₀ = b * r₀ := by
              have : 1 ≤ b := by omega
              zify [this]; ring
            linarith
          rw [pow_succ', mul_assoc, Nat.mul_mod, ih, Nat.mod_mul_mod, hbr,
            mul_comm m Q₀, Nat.mul_add_mod, Nat.mod_eq_of_lt hr₀_lt]
      -- Constant rotation contradicts `cyclicCount b M L r₀ 0 = 1` and `cyclicCount b M L r₀ 1 = 1`.
      have hc0' : ((range M).filter fun j => b ^ L * (b ^ j * r₀ % Q₀) / Q₀ = 0).card = 1 :=
        hbal_L 0 (by omega)
      have hc1' : ((range M).filter fun j => b ^ L * (b ^ j * r₀ % Q₀) / Q₀ = 1).card = 1 :=
        hbal_L 1 (by omega)
      have hne0 : ((range M).filter fun j => b ^ L * (b ^ j * r₀ % Q₀) / Q₀ = 0).Nonempty :=
        Finset.card_pos.mp (by omega)
      have hne1 : ((range M).filter fun j => b ^ L * (b ^ j * r₀ % Q₀) / Q₀ = 1).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨j₀, hj₀⟩ := hne0
      obtain ⟨j₁, hj₁⟩ := hne1
      have e0 : b ^ L * r₀ / Q₀ = 0 := by
        have := (mem_filter.mp hj₀).2; rwa [hstep j₀] at this
      have e1 : b ^ L * r₀ / Q₀ = 1 := by
        have := (mem_filter.mp hj₁).2; rwa [hstep j₁] at this
      omega
    · -- `OrderNormal b L x`
      intro v hv
      have hlim := wordFreq_tower_limit hb hM_ge2 hL hr₀_pos hr₀_lt hu_mem v
      rw [hbal_L v hv, Nat.cast_one] at hlim
      simpa [x, M] using hlim
    · -- `¬ OrderNormal b (L + 1) x`
      intro hnorm1
      -- By pigeonhole, some `v₀ < b ^ (L + 1)` has `cyclicCount b M (L + 1) r₀ v₀ = 0`.
      have hsum_cnt : ∑ v ∈ range (b ^ (L + 1)), cyclicCount b M (L + 1) r₀ v ≤ M := by
        unfold cyclicCount
        rw [← Finset.card_biUnion]
        · calc ((range (b ^ (L + 1))).biUnion fun v =>
                (range M).filter fun j => b ^ (L + 1) * (b ^ j * r₀ % Q₀) / Q₀ = v).card
              ≤ (range M).card := card_le_card (by
                intro j hj
                obtain ⟨_, _, hjM⟩ := mem_biUnion.mp hj
                exact (mem_filter.mp hjM).1)
            _ = M := card_range M
        · intro v₁ _ v₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro j h1 h2
          exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
      have hex_zero : ∃ v₀ < b ^ (L + 1), cyclicCount b M (L + 1) r₀ v₀ = 0 := by
        by_contra hall
        push Not at hall
        have hge : b ^ (L + 1) ≤ ∑ v ∈ range (b ^ (L + 1)), cyclicCount b M (L + 1) r₀ v := by
          calc b ^ (L + 1) = ∑ _v ∈ range (b ^ (L + 1)), 1 := by simp
            _ ≤ ∑ v ∈ range (b ^ (L + 1)), cyclicCount b M (L + 1) r₀ v :=
                Finset.sum_le_sum fun v hv => Nat.pos_of_ne_zero (hall v (mem_range.mp hv))
        have hlt : M < b ^ (L + 1) := by
          dsimp [M]; rw [pow_succ]; nlinarith [Nat.one_le_pow L b (by omega)]
        omega
      obtain ⟨v₀, hv₀, hcnt0⟩ := hex_zero
      have hlim0 := wordFreq_tower_limit hb hM_ge2 (by omega : 1 ≤ L + 1) hr₀_pos hr₀_lt hu_mem v₀
      rw [hcnt0, Nat.cast_zero, zero_div] at hlim0
      have hlim_pos := hnorm1 v₀ hv₀
      have heq : (0 : ℝ) = 1 / (b : ℝ) ^ (L + 1) := tendsto_nhds_unique hlim0 hlim_pos
      have hpos : (0 : ℝ) < 1 / (b : ℝ) ^ (L + 1) := by
        have : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
        positivity
      linarith

/-- **Main Higher-Order Tower Classification (`K_{b^k} \ K_b`):**
for `b ≥ 2`, `k ≥ 2`, and `L ≥ 1`, there exists an `L`-normal element of `K_{b^k} \ K_b`
if and only if `b^L ∣ k`. -/
theorem tower_iff {b k L : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) (hL : 1 ≤ L) :
    (∃ x, x ∈ Kernel (b ^ k) \ Kernel b ∧ OrderNormal b L x) ↔ b ^ L ∣ k := by
  constructor
  · rintro ⟨x, ⟨hx_pow, hx_not⟩, hnorm⟩
    obtain ⟨r, hr_lt, u, hu, hxeq, _, hKb_iff⟩ := mem_pow_kernel_decomp hb hk hx_pow
    have hr_pos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · exact absurd (hKb_iff.mpr (by simp)) hx_not
      · exact hpos
    have hlim1 := wordFreq_tower_limit hb hk hL hr_pos hr_lt hu 0
    rw [← hxeq] at hlim1
    have hlim2 := hnorm 0 (pow_pos (by omega) L)
    have heq := tendsto_nhds_unique hlim1 hlim2
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hbL_ne : (b : ℝ) ^ L ≠ 0 := pow_ne_zero L (by exact_mod_cast (show b ≠ 0 by omega))
    have hmul_r : (cyclicCount b k L r 0 : ℝ) * (b : ℝ) ^ L = (k : ℝ) := by
      field_simp [hk_ne, hbL_ne] at heq
      linarith
    have hmul_n : cyclicCount b k L r 0 * b ^ L = k := by exact_mod_cast hmul_r
    exact ⟨cyclicCount b k L r 0, by linarith⟩
  · intro hdvd
    obtain ⟨x, _, hmem, hnorm, _⟩ := (tower_irrational_exact_iff hb hk hL).mpr hdvd
    exact ⟨x, hmem, hnorm⟩

/-! #### Explicit binary alternating-runs witness for `(b, L) = (2, 1)` inside `K_2` -/

/-- Pair-block index `k` such that `k * (k + 1) ≤ n < (k + 1) * (k + 2)`. -/
def altBlock (n : ℕ) : ℕ :=
  Nat.find (show ∃ j, n < (j + 1) * (j + 2) from ⟨n, by nlinarith⟩)

private lemma altBlock_spec (n : ℕ) :
    altBlock n * (altBlock n + 1) ≤ n ∧ n < (altBlock n + 1) * (altBlock n + 2) := by
  have hlt : n < (altBlock n + 1) * (altBlock n + 2) :=
    Nat.find_spec (show ∃ j, n < (j + 1) * (j + 2) from ⟨n, by nlinarith⟩)
  refine ⟨?_, hlt⟩
  rcases h : altBlock n with _ | k
  · simp
  · have hmin : ¬ n < (k + 1) * (k + 2) :=
      Nat.find_min (show ∃ j, n < (j + 1) * (j + 2) from ⟨n, by nlinarith⟩)
        (by change k < altBlock n; omega)
    nlinarith

private lemma altBlock_eq_of_mem {k n : ℕ} (hlo : k * (k + 1) ≤ n) (hhi : n < (k + 1) * (k + 2)) :
    altBlock n = k := by
  have ⟨h1, h2⟩ := altBlock_spec n
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : altBlock n + 1 ≤ k := hlt
    have : (altBlock n + 1) * (altBlock n + 2) ≤ k * (k + 1) := by nlinarith
    omega
  · have : k + 1 ≤ altBlock n := hgt
    have : (k + 1) * (k + 2) ≤ altBlock n * (altBlock n + 1) := by nlinarith
    omega

/-- Alternating binary runs: in block `k`, `k + 1` zeros followed by `k + 1` ones. -/
def altDigit (n : ℕ) : ℕ :=
  let k := altBlock n
  if n < k * (k + 1) + (k + 1) then 0 else 1

/-- The alternating-runs binary real `∑_{n ≥ 0} altDigit n / 2^(n + 1)`. -/
noncomputable def altRunsValue : ℝ :=
  ∑' n : ℕ, (altDigit n : ℝ) / (2 : ℝ) ^ (n + 1)

private lemma altDigit_le_one (n : ℕ) : altDigit n ≤ 1 := by
  unfold altDigit; dsimp only; split_ifs <;> omega

private lemma altRuns_summable :
    Summable (fun n : ℕ => (altDigit n : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right (2 : ℝ)⁻¹)
  have hle : (altDigit n : ℝ) ≤ 1 := by exact_mod_cast altDigit_le_one n
  rw [pow_succ, div_eq_mul_inv, mul_inv, ← inv_pow]
  calc (altDigit n : ℝ) * (((2 : ℝ)⁻¹) ^ n * (2 : ℝ)⁻¹)
      ≤ 1 * (((2 : ℝ)⁻¹) ^ n * (2 : ℝ)⁻¹) := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = ((2 : ℝ)⁻¹) ^ n * (2 : ℝ)⁻¹ := one_mul _

private lemma shift_altRunsValue (n : ℕ) :
    shift 2 altRunsValue n = ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) := by
  have hsum := altRuns_summable
  have hsplit := hsum.sum_add_tsum_nat_add n
  set tail : ℝ := ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)
  have htail_sum : Summable (fun j : ℕ => (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
    have h1 := (hsum.comp_injective (add_left_injective n)).mul_left ((2 : ℝ) ^ n)
    refine h1.congr fun j => ?_
    dsimp only [Function.comp_apply]
    rw [show j + n = n + j by omega, show n + j + 1 = n + (j + 1) by omega, pow_add]
    field_simp [(pow_pos (show (0 : ℝ) < 2 by norm_num) n).ne']
  have htail_nn : 0 ≤ tail := tsum_nonneg fun j => by positivity
  have htail_lt1 : tail < 1 := by
    -- Pick the start `m₀ = (altBlock n + 1) * (altBlock n + 2)` of the next block, where `altDigit m₀ = 0`.
    set k := altBlock n
    set m₀ := (k + 1) * (k + 2)
    have hn_lt : n < m₀ := (altBlock_spec n).2
    set j₀ := m₀ - n
    have hj₀ : n + j₀ = m₀ := by omega
    have hdig0 : altDigit (n + j₀) = 0 := by
      rw [hj₀]
      unfold altDigit
      have hb : altBlock m₀ = k + 1 := altBlock_eq_of_mem le_rfl (by dsimp [m₀]; nlinarith)
      rw [hb]
      have : m₀ < (k + 1) * (k + 2) + (k + 2) := by dsimp [m₀]; omega
      simp [this]
    have hgeom : Summable (fun j : ℕ => (1 : ℝ) / (2 : ℝ) ^ (j + 1)) := by
      have h := (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right (2 : ℝ)⁻¹
      refine h.congr fun j => ?_
      rw [pow_succ, inv_pow]; ring
    have hgeom_val : ∑' j : ℕ, (1 : ℝ) / (2 : ℝ) ^ (j + 1) = 1 := by
      have h1 : (fun j : ℕ => (1 : ℝ) / (2 : ℝ) ^ (j + 1)) =
          fun j => ((2 : ℝ)⁻¹) ^ j * (2 : ℝ)⁻¹ := funext fun j => by rw [pow_succ, inv_pow]; ring
      rw [h1, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    have hdiff_sum : Summable (fun j : ℕ => (1 : ℝ) / (2 : ℝ) ^ (j + 1) -
        (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) := hgeom.sub htail_sum
    have hdiff_ge : (1 : ℝ) / (2 : ℝ) ^ (j₀ + 1) ≤
        ∑' j : ℕ, ((1 : ℝ) / (2 : ℝ) ^ (j + 1) - (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
      have hle := hdiff_sum.le_tsum j₀ fun j _ => by
        have h1 : (altDigit (n + j) : ℝ) ≤ 1 := by exact_mod_cast altDigit_le_one (n + j)
        have := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1))
        linarith
      simpa [hdig0] using hle
    rw [hgeom.tsum_sub htail_sum, hgeom_val] at hdiff_ge
    have hpos : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (j₀ + 1) := by positivity
    linarith
  have hhead_int : ∃ z : ℤ, (2 : ℝ) ^ n * ∑ i ∈ range n, (altDigit i : ℝ) / (2 : ℝ) ^ (i + 1) = z := by
    refine ⟨∑ i ∈ range n, (altDigit i : ℤ) * (2 : ℤ) ^ (n - 1 - i), ?_⟩
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_lt : i < n := mem_range.mp hi
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 - i) * (2 : ℝ) ^ (i + 1) := by
      rw [← pow_add, show n - 1 - i + (i + 1) = n by omega]
    rw [hpow]
    field_simp [(pow_pos (show (0 : ℝ) < 2 by norm_num) (i + 1)).ne']
  have htail_mul : (2 : ℝ) ^ n * ∑' j : ℕ, (altDigit (j + n) : ℝ) / (2 : ℝ) ^ (j + n + 1) = tail := by
    rw [← tsum_mul_left]
    dsimp [tail]
    congr 1; ext j
    rw [show j + n = n + j by omega, show n + j + 1 = n + (j + 1) by omega, pow_add]
    field_simp [(pow_pos (show (0 : ℝ) < 2 by norm_num) n).ne']
  obtain ⟨z, hz⟩ := hhead_int
  unfold shift altRunsValue
  have hrew : (2 : ℝ) ^ n * ∑' m : ℕ, (altDigit m : ℝ) / (2 : ℝ) ^ (m + 1) = tail + (z : ℝ) := by
    rw [← hsplit, mul_add, hz, htail_mul]; ring
  rw [Nat.cast_ofNat, hrew, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨htail_nn, htail_lt1⟩]

private lemma wordAt_altRunsValue (n : ℕ) :
    ⌊(2 : ℝ) * shift 2 altRunsValue n⌋₊ = altDigit n := by
  rw [shift_altRunsValue n]
  have hsum : Summable (fun j : ℕ => (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
    have h1 := (altRuns_summable.comp_injective (add_left_injective n)).mul_left ((2 : ℝ) ^ n)
    refine h1.congr fun j => ?_
    dsimp only [Function.comp_apply]
    rw [show j + n = n + j by omega, show n + j + 1 = n + (j + 1) by omega, pow_add]
    field_simp [(pow_pos (show (0 : ℝ) < 2 by norm_num) n).ne']
  have hstep := hsum.tsum_eq_zero_add
  have hmul : (2 : ℝ) * ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) =
      (altDigit n : ℝ) + shift 2 altRunsValue (n + 1) := by
    rw [hstep, mul_add, shift_altRunsValue (n + 1)]
    congr 1
    · simp; ring
    · rw [← tsum_mul_left]
      congr 1; ext j
      rw [show n + (j + 1) = n + 1 + j by omega, show j + 1 + 1 = 1 + (j + 1) by omega, pow_add, pow_one]
      field_simp
  have hnn : 0 ≤ shift 2 altRunsValue (n + 1) := Int.fract_nonneg _
  have hlt1 : shift 2 altRunsValue (n + 1) < 1 := Int.fract_lt_one _
  rw [hmul, Nat.floor_eq_iff (by positivity)]
  exact ⟨by linarith, by linarith⟩

/-- `altRunsValue ∈ zeroOrbitSubgroup 2 ⊆ Kernel 2`. -/
theorem altRuns_mem_zeroOrbit : altRunsValue ∈ zeroOrbitSubgroup 2 := by
  classical
  change Tendsto (circMean 2 altRunsValue) atTop (𝓝 0)
  -- If `altDigit (n + i) = altDigit n` for all `i ≤ w`, then `circDist (shift 2 altRunsValue n) ≤ 2^(-(w + 1))`.
  have hconst_dist : ∀ n w : ℕ, (∀ i ≤ w, altDigit (n + i) = altDigit n) →
      circDist (shift 2 altRunsValue n) ≤ ((2 : ℝ)⁻¹) ^ (w + 1) := by
    intro n w hconst
    rw [shift_altRunsValue n]
    have hsum : Summable (fun j : ℕ => (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
      have h1 := (altRuns_summable.comp_injective (add_left_injective n)).mul_left ((2 : ℝ) ^ n)
      refine h1.congr fun j => ?_
      dsimp only [Function.comp_apply]
      rw [show j + n = n + j by omega, show n + j + 1 = n + (j + 1) by omega, pow_add]
      field_simp [(pow_pos (show (0 : ℝ) < 2 by norm_num) n).ne']
    have hgeom : Summable (fun j : ℕ => (1 : ℝ) / (2 : ℝ) ^ (j + 1)) := by
      have h := (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right (2 : ℝ)⁻¹
      refine h.congr fun j => ?_; rw [pow_succ, inv_pow]; ring
    have htail_le : ∑' j : ℕ, (altDigit (n + (j + (w + 1))) : ℝ) / (2 : ℝ) ^ (j + (w + 1) + 1) ≤
        ((2 : ℝ)⁻¹) ^ (w + 1) := by
      have hsum_t := hsum.comp_injective (add_left_injective (w + 1))
      have hgeom_t : Summable (fun j : ℕ => ((2 : ℝ)⁻¹) ^ (w + 1) * (((2 : ℝ)⁻¹) ^ j * (2 : ℝ)⁻¹)) :=
        ((summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right _).mul_left _
      have hle := Summable.tsum_le_tsum (fun j => by
        dsimp only [Function.comp_apply]
        have hd1 : (altDigit (n + (j + (w + 1))) : ℝ) ≤ 1 := by exact_mod_cast altDigit_le_one _
        have hrew : ((2 : ℝ)⁻¹) ^ (w + 1) * (((2 : ℝ)⁻¹) ^ j * (2 : ℝ)⁻¹) =
            (1 : ℝ) / (2 : ℝ) ^ (j + (w + 1) + 1) := by
          rw [one_div, ← inv_pow, pow_add, pow_add, pow_one]; ring
        rw [hrew]
        exact div_le_div_of_nonneg_right hd1 (by positivity)) hsum_t hgeom_t
      dsimp only [Function.comp_apply] at hle
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hle
      have hcoef : ((1 - (2 : ℝ)⁻¹)⁻¹ * (2 : ℝ)⁻¹) = 1 := by norm_num
      rw [hcoef, mul_one] at hle
      exact hle
    have hsplit := hsum.sum_add_tsum_nat_add (w + 1)
    have hhead_geom : ∑ j ∈ range (w + 1), (1 : ℝ) / (2 : ℝ) ^ (j + 1) = 1 - ((2 : ℝ)⁻¹) ^ (w + 1) := by
      have h1 : ∀ j, (1 : ℝ) / (2 : ℝ) ^ (j + 1) = (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ j := fun j => by
        rw [pow_succ', inv_pow]; ring
      simp_rw [h1, ← Finset.mul_sum, geom_sum_eq (show (2 : ℝ)⁻¹ ≠ 1 by norm_num)]
      ring
    rcases show altDigit n = 0 ∨ altDigit n = 1 by have := altDigit_le_one n; omega with h0 | h1
    · have hhead0 : ∑ j ∈ range (w + 1), (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [hconst j (Nat.lt_succ_iff.mp (mem_range.mp hj)), h0]; simp
      have hval_le : ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) ≤ ((2 : ℝ)⁻¹) ^ (w + 1) := by
        rw [← hsplit, hhead0, zero_add]; exact htail_le
      have hval_nn : 0 ≤ ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) :=
        tsum_nonneg fun j => by positivity
      calc circDist (∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1))
          ≤ |(∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) - ((0 : ℤ) : ℝ)| :=
            circDist_le_abs_sub_int _ 0
        _ = ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) := by
            simp [abs_of_nonneg hval_nn]
        _ ≤ ((2 : ℝ)⁻¹) ^ (w + 1) := hval_le
    · have hhead1 : ∑ j ∈ range (w + 1), (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) =
          1 - ((2 : ℝ)⁻¹) ^ (w + 1) := by
        rw [← hhead_geom]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hconst j (Nat.lt_succ_iff.mp (mem_range.mp hj)), h1, Nat.cast_one]
      have hval_ge : 1 - ((2 : ℝ)⁻¹) ^ (w + 1) ≤ ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) := by
        rw [← hsplit, hhead1]
        have : 0 ≤ ∑' j : ℕ, (altDigit (n + (j + (w + 1))) : ℝ) / (2 : ℝ) ^ (j + (w + 1) + 1) :=
          tsum_nonneg fun j => by positivity
        linarith
      have hval_le1 : ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) ≤ 1 := by
        have hlt := Int.fract_lt_one ((2 : ℝ) ^ n * altRunsValue)
        change shift 2 altRunsValue n < 1 at hlt
        rw [shift_altRunsValue n] at hlt
        exact hlt.le
      calc circDist (∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1))
          ≤ |(∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) - ((1 : ℤ) : ℝ)| :=
            circDist_le_abs_sub_int _ 1
        _ = 1 - ∑' j : ℕ, (altDigit (n + j) : ℝ) / (2 : ℝ) ^ (j + 1) := by
            rw [Int.cast_one, abs_of_nonpos (by linarith)]; ring
        _ ≤ ((2 : ℝ)⁻¹) ^ (w + 1) := by linarith
  -- Bound `circMean 2 altRunsValue N ≤ 2^(-(w + 1)) + 2 * (w + 1) * (sqrt N + 1) / N`.
  have hmean_le : ∀ w N : ℕ, 1 ≤ N →
      circMean 2 altRunsValue N ≤
        ((2 : ℝ)⁻¹) ^ (w + 1) + ((2 * (w + 1) * (Nat.sqrt N + 1) : ℕ) : ℝ) / (N : ℝ) := by
    intro w N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    let Good : ℕ → Prop := fun n => ∀ i ≤ w, altDigit (n + i) = altDigit n
    set G := (range N).filter Good
    set B := (range N).filter fun n => ¬ Good n
    have hB_card : B.card ≤ 2 * (w + 1) * (Nat.sqrt N + 1) := by
      -- Every `n ∈ B` lies within `w + 1` of either `j*(j+1) + (j+1)` or `(j+1)*(j+2)` for `j = altBlock n ≤ sqrt N`.
      set T := (range (Nat.sqrt N + 1)) ×ˢ ((range 2) ×ˢ (range (w + 1)))
      have hcard_T : T.card = 2 * (w + 1) * (Nat.sqrt N + 1) := by
        simp only [T, card_product, card_range]; ring
      rw [← hcard_T]
      refine card_le_card_of_injOn
        (fun n =>
          let j := altBlock n
          if n < j * (j + 1) + (j + 1) then
            (j, (0, j * (j + 1) + (j + 1) - 1 - n))
          else
            (j, (1, (j + 1) * (j + 2) - 1 - n))) ?_ ?_
      · intro n hn
        obtain ⟨hnN, hnotG⟩ := mem_filter.mp (mem_coe.mp hn)
        have hn_lt : n < N := mem_range.mp hnN
        set j := altBlock n
        have ⟨hj_lo, hj_hi⟩ := altBlock_spec n
        have hj_lo' : j * (j + 1) ≤ n := hj_lo
        have hj_hi' : n < (j + 1) * (j + 2) := hj_hi
        have hj_le : j ≤ Nat.sqrt N := by
          rw [Nat.le_sqrt]; nlinarith
        dsimp only
        rw [mem_coe]
        split_ifs with hhalf
        · -- First half `[j*(j+1), j*(j+1)+(j+1))`: must have `n + w ≥ j*(j+1) + (j+1)`.
          have hhalf' : n < j * (j + 1) + (j + 1) := hhalf
          have hclose : j * (j + 1) + (j + 1) ≤ n + w := by
            by_contra hfar
            apply hnotG
            intro i hi
            have hb_i : altBlock (n + i) = j := altBlock_eq_of_mem (by omega) (by nlinarith)
            unfold altDigit
            rw [hb_i]
            have h1 : n + i < j * (j + 1) + (j + 1) := by omega
            simp [hhalf, h1]
          change (j, (0, j * (j + 1) + (j + 1) - 1 - n)) ∈ T
          simp only [T, mem_product, mem_range]
          exact ⟨by omega, by omega, by omega⟩
        · -- Second half `[j*(j+1)+(j+1), (j+1)*(j+2))`: must have `n + w ≥ (j+1)*(j+2)`.
          have hhalf' : j * (j + 1) + (j + 1) ≤ n := not_lt.mp hhalf
          have hclose : (j + 1) * (j + 2) ≤ n + w := by
            by_contra hfar
            apply hnotG
            intro i hi
            have hb_i : altBlock (n + i) = j := altBlock_eq_of_mem (by omega) (by omega)
            unfold altDigit
            rw [hb_i]
            have h1 : ¬ n + i < j * (j + 1) + (j + 1) := by omega
            simp [hhalf, h1]
          change (j, (1, (j + 1) * (j + 2) - 1 - n)) ∈ T
          simp only [T, mem_product, mem_range]
          exact ⟨by omega, by omega, by omega⟩
      · intro n₁ _ n₂ _ heq
        dsimp only at heq
        split_ifs at heq with h1 h2 h2
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨hj, _, hd⟩ := heq
          rw [hj] at h1 hd
          omega
        · simp only [Prod.mk.injEq] at heq; omega
        · simp only [Prod.mk.injEq] at heq; omega
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨hj, _, hd⟩ := heq
          have ⟨_, hi1⟩ := altBlock_spec n₁
          have ⟨_, hi2⟩ := altBlock_spec n₂
          rw [hj] at hi1 hd
          omega
    have hsplit : ∑ n ∈ range N, circDist (shift 2 altRunsValue n) =
        (∑ n ∈ G, circDist (shift 2 altRunsValue n)) +
          ∑ n ∈ B, circDist (shift 2 altRunsValue n) := by
      rw [← Finset.sum_filter_add_sum_filter_not (range N) Good]
    have hG_sum : ∑ n ∈ G, circDist (shift 2 altRunsValue n) ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ (w + 1) := by
      calc ∑ n ∈ G, circDist (shift 2 altRunsValue n)
          ≤ ∑ _n ∈ G, ((2 : ℝ)⁻¹) ^ (w + 1) :=
            Finset.sum_le_sum fun n hn => hconst_dist n w (mem_filter.mp hn).2
        _ = (G.card : ℝ) * ((2 : ℝ)⁻¹) ^ (w + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ (w + 1) := mul_le_mul_of_nonneg_right
            (by exact_mod_cast ((card_filter_le _ _).trans_eq (card_range N))) (by positivity)
    have hB_sum : ∑ n ∈ B, circDist (shift 2 altRunsValue n) ≤
        ((2 * (w + 1) * (Nat.sqrt N + 1) : ℕ) : ℝ) := by
      calc ∑ n ∈ B, circDist (shift 2 altRunsValue n)
          ≤ ∑ _n ∈ B, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => (circDist_le_half _).trans (by norm_num)
        _ = (B.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ((2 * (w + 1) * (Nat.sqrt N + 1) : ℕ) : ℝ) := by exact_mod_cast hB_card
    unfold circMean
    rw [hsplit]
    calc ((∑ n ∈ G, circDist (shift 2 altRunsValue n)) +
            ∑ n ∈ B, circDist (shift 2 altRunsValue n)) / (N : ℝ)
        ≤ ((N : ℝ) * ((2 : ℝ)⁻¹) ^ (w + 1) +
            ((2 * (w + 1) * (Nat.sqrt N + 1) : ℕ) : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hNr.le
      _ = ((2 : ℝ)⁻¹) ^ (w + 1) + ((2 * (w + 1) * (Nat.sqrt N + 1) : ℕ) : ℝ) / (N : ℝ) := by
          rw [add_div, mul_div_cancel_left₀ _ hNr.ne']
  rw [Metric.tendsto_atTop]
  intro η hη
  have hpow_tend : Tendsto (fun w : ℕ => ((2 : ℝ)⁻¹) ^ (w + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨w, hw⟩ := (Metric.tendsto_atTop.mp hpow_tend (η / 2) (by positivity)).imp fun w hw => hw w le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hw
  set C : ℕ := 2 * (w + 1)
  set N₀ : ℕ := max 1 (Nat.ceil (16 * (C : ℝ) ^ 2 / η ^ 2) + 1)
  refine ⟨N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNceil : Nat.ceil (16 * (C : ℝ) ^ 2 / η ^ 2) + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsqrt_small : ((C * (Nat.sqrt N + 1) : ℕ) : ℝ) / (N : ℝ) < η / 2 := by
    rw [div_lt_iff₀ hNr]
    have hsq_lt : (((C * (Nat.sqrt N + 1) : ℕ) : ℝ)) ^ 2 < (η / 2 * (N : ℝ)) ^ 2 := by
      have hN_gt : 16 * (C : ℝ) ^ 2 / η ^ 2 < (N : ℝ) := by
        have hc : 16 * (C : ℝ) ^ 2 / η ^ 2 ≤ (Nat.ceil (16 * (C : ℝ) ^ 2 / η ^ 2) : ℝ) :=
          Nat.le_ceil _
        have h1 : (Nat.ceil (16 * (C : ℝ) ^ 2 / η ^ 2) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNceil
        linarith
      have h1_le_sqrt : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
      have hsq_nat : (Nat.sqrt N + 1) ^ 2 ≤ 4 * N := by
        have : Nat.sqrt N + 1 ≤ 2 * Nat.sqrt N := by omega
        have h2 := Nat.sqrt_le N
        nlinarith
      have hsq_r : ((Nat.sqrt N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) := by exact_mod_cast hsq_nat
      have hmul_lt : 16 * (C : ℝ) ^ 2 < η ^ 2 * (N : ℝ) := by
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < η ^ 2)).mp hN_gt
        linarith
      push_cast
      rw [mul_pow]
      have h2 : (C : ℝ) ^ 2 * ((Nat.sqrt N : ℝ) + 1) ^ 2 ≤ (C : ℝ) ^ 2 * (4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq_r (by positivity)
      have h3 : 4 * (C : ℝ) ^ 2 * (N : ℝ) < (η / 2 * (N : ℝ)) ^ 2 := by
        have := mul_lt_mul_of_pos_right hmul_lt hNr
        nlinarith
      linarith
    nlinarith [show 0 ≤ ((C * (Nat.sqrt N + 1) : ℕ) : ℝ) by positivity,
      show 0 ≤ η / 2 * (N : ℝ) by positivity]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (circMean_nonneg 2 _ N)]
  have hm := hmean_le w N hN1
  dsimp [C] at hsqrt_small
  linarith

/-- `altRunsValue` is simply normal (`1`-normal) in base `2`. -/
theorem altRuns_orderNormal_one : OrderNormal 2 1 altRunsValue := by
  -- First compute `wordCount 2 1 altRunsValue 1 (k * (k + 1))` by induction on `k`.
  have hcnt_eq : ∀ N, wordCount 2 1 altRunsValue 1 N =
      ((range N).filter fun n => altDigit n = 1).card := fun N => by
    unfold wordCount
    congr 1
    refine Finset.filter_congr fun n _ => ?_
    rw [pow_one, Nat.cast_ofNat, wordAt_altRunsValue n]
  have hcnt_block : ∀ k : ℕ, 2 * ((range (k * (k + 1))).filter fun n => altDigit n = 1).card =
      k * (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : ((range ((k + 1) * (k + 2))).filter fun n => altDigit n = 1).card =
          ((range (k * (k + 1))).filter fun n => altDigit n = 1).card + (k + 1) := by
        have hu : range ((k + 1) * (k + 2)) =
            range (k * (k + 1)) ∪ Ico (k * (k + 1)) ((k + 1) * (k + 2)) := by
          have hle : k * (k + 1) ≤ (k + 1) * (k + 2) := by nlinarith
          ext n; simp only [mem_union, mem_range, mem_Ico]; omega
        have hd : Disjoint (range (k * (k + 1))) (Ico (k * (k + 1)) ((k + 1) * (k + 2))) := by
          rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
        rw [hu, Finset.filter_union, card_union_of_disjoint
          (hd.mono (filter_subset _ _) (filter_subset _ _))]
        congr 1
        have heq_set : (Ico (k * (k + 1)) ((k + 1) * (k + 2))).filter (fun n => altDigit n = 1) =
            Ico (k * (k + 1) + (k + 1)) ((k + 1) * (k + 2)) := by
          ext n
          simp only [mem_filter, mem_Ico]
          constructor
          · rintro ⟨⟨hlo, hhi⟩, h1⟩
            have hb : altBlock n = k := altBlock_eq_of_mem hlo hhi
            unfold altDigit at h1
            dsimp only at h1
            rw [hb] at h1
            split_ifs at h1 with hlt
            exact ⟨by omega, hhi⟩
          · rintro ⟨hlo, hhi⟩
            have hb : altBlock n = k := altBlock_eq_of_mem (by omega) hhi
            refine ⟨⟨by omega, hhi⟩, ?_⟩
            unfold altDigit
            rw [hb]
            simp [show ¬ n < k * (k + 1) + (k + 1) by omega]
        rw [heq_set, Nat.card_Ico]
        exact Nat.sub_eq_of_eq_add (by ring)
      rw [hstep]
      nlinarith
  -- Bound `|wordFreq 2 1 altRunsValue 1 N - 1/2| ≤ (sqrt N + 1) / N`.
  have hfreq1 : Tendsto (wordFreq 2 1 altRunsValue 1) atTop (𝓝 (1 / (2 : ℝ) ^ 1)) := by
    have herr : ∀ N : ℕ, 1 ≤ N →
        |wordFreq 2 1 altRunsValue 1 N - 1 / (2 : ℝ)| ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) := by
      intro N hN
      set k := altBlock N
      have ⟨hk_lo, hk_hi⟩ := altBlock_spec N
      have hk_lo' : k * (k + 1) ≤ N := hk_lo
      have hk_hi' : N < (k + 1) * (k + 2) := hk_hi
      have hk_le : k ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by nlinarith)
      set cN := ((range N).filter fun n => altDigit n = 1).card
      set cB := ((range (k * (k + 1))).filter fun n => altDigit n = 1).card
      have hcB : 2 * cB = k * (k + 1) := hcnt_block k
      have hcN_lo : cB ≤ cN :=
        card_le_card (filter_subset_filter _ (range_mono hk_lo'))
      have hcN_hi : cN ≤ cB + (N - k * (k + 1)) := by
        have hu : range N = range (k * (k + 1)) ∪ Ico (k * (k + 1)) N := by
          ext n; simp only [mem_union, mem_range, mem_Ico]; omega
        have hsub : (range N).filter (fun n => altDigit n = 1) ⊆
            ((range (k * (k + 1))).filter fun n => altDigit n = 1) ∪ Ico (k * (k + 1)) N := by
          intro n hn
          obtain ⟨hnN, h1⟩ := mem_filter.mp hn
          rw [hu, mem_union] at hnN
          rcases hnN with h | h
          · exact mem_union_left _ (mem_filter.mpr ⟨h, h1⟩)
          · exact mem_union_right _ h
        calc cN ≤ (((range (k * (k + 1))).filter fun n => altDigit n = 1) ∪ Ico (k * (k + 1)) N).card :=
              card_le_card hsub
          _ ≤ cB + (Ico (k * (k + 1)) N).card := card_union_le _ _
          _ = cB + (N - k * (k + 1)) := by rw [Nat.card_Ico]
      have hN_sub : N - k * (k + 1) ≤ 2 * (k + 1) := by
        have hprod : (k + 1) * (k + 2) = k * (k + 1) + 2 * (k + 1) := by ring
        omega
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hdiff_nat : |(2 * (cN : ℝ) - (N : ℝ))| ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
        have hlo_r : (cB : ℝ) ≤ (cN : ℝ) := by exact_mod_cast hcN_lo
        have hhi_r : (cN : ℝ) ≤ (cB : ℝ) + ((N - k * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcN_hi
        have h2cB_r : 2 * (cB : ℝ) = ((k * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcB
        have hsub_r : ((N - k * (k + 1) : ℕ) : ℝ) = (N : ℝ) - ((k * (k + 1) : ℕ) : ℝ) := by
          rw [Nat.cast_sub hk_lo]
        have hsub_le : ((N - k * (k + 1) : ℕ) : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast hN_sub
        rw [abs_le]
        constructor <;> linarith
      have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ Nat.sqrt N + 1)
      unfold wordFreq
      rw [hcnt_eq N]
      have hrew : (cN : ℝ) / (N : ℝ) - 1 / 2 = (2 * (cN : ℝ) - (N : ℝ)) / (2 * (N : ℝ)) := by
        field_simp [hNr.ne']
      rw [hrew, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
      calc |2 * (cN : ℝ) - (N : ℝ)| / (2 * (N : ℝ))
          ≤ (2 * ((k + 1 : ℕ) : ℝ)) / (2 * (N : ℝ)) :=
            div_le_div_of_nonneg_right hdiff_nat (by positivity)
        _ = ((k + 1 : ℕ) : ℝ) / (N : ℝ) := by field_simp [hNr.ne']
        _ ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) :=
            div_le_div_of_nonneg_right hk1_le hNr.le
    rw [pow_one, Metric.tendsto_atTop]
    intro η hη
    set N₀ : ℕ := max 1 (Nat.ceil (4 / η ^ 2) + 1)
    refine ⟨N₀, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
    have hNceil : Nat.ceil (4 / η ^ 2) + 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    have hlt : ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) < η := by
      rw [div_lt_iff₀ hNr]
      have hsq_lt : (((Nat.sqrt N + 1 : ℕ) : ℝ)) ^ 2 < (η * (N : ℝ)) ^ 2 := by
        have hN_gt : 4 / η ^ 2 < (N : ℝ) := by
          have hc : 4 / η ^ 2 ≤ (Nat.ceil (4 / η ^ 2) : ℝ) := Nat.le_ceil _
          have h1 : (Nat.ceil (4 / η ^ 2) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNceil
          linarith
        have h1_le_sqrt : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
        have hsq_nat : (Nat.sqrt N + 1) ^ 2 ≤ 4 * N := by
          have : Nat.sqrt N + 1 ≤ 2 * Nat.sqrt N := by omega
          have h2 := Nat.sqrt_le N
          nlinarith
        have hsq_r : (((Nat.sqrt N + 1 : ℕ) : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := by exact_mod_cast hsq_nat
        have hmul : 4 < η ^ 2 * (N : ℝ) := by
          have := (div_lt_iff₀ (by positivity : (0 : ℝ) < η ^ 2)).mp hN_gt
          linarith
        have hmulN := mul_lt_mul_of_pos_right hmul hNr
        nlinarith
      nlinarith [show 0 ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) by positivity,
        show 0 ≤ η * (N : ℝ) by positivity]
    rw [Real.dist_eq]
    exact (herr N hN1).trans_lt hlt
  -- Deduce `wordFreq 2 1 altRunsValue 0 → 1/2` from `wordCount 0 + wordCount 1 = N`.
  intro v hv
  have hv01 : v = 0 ∨ v = 1 := by simp at hv; omega
  rcases hv01 with rfl | rfl
  · have hcompl : wordFreq 2 1 altRunsValue 0 =ᶠ[atTop]
        fun N => 1 - wordFreq 2 1 altRunsValue 1 N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have htot := sum_wordCount_eq (b := 2) (by omega) 1 altRunsValue N
      rw [pow_one, Finset.sum_range_succ, Finset.sum_range_one] at htot
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have htot_r : (wordCount 2 1 altRunsValue 0 N : ℝ) +
          (wordCount 2 1 altRunsValue 1 N : ℝ) = (N : ℝ) := by exact_mod_cast htot
      unfold wordFreq
      field_simp [hNr]
      linarith
    rw [tendsto_congr' hcompl]
    have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hfreq1
    convert hsub using 1
    norm_num
  · exact hfreq1

/-- **Complete Higher-Order Tower Classification (including the smaller kernel `K_b`):**
for `b ≥ 2`, `k ≥ 2`, and `L ≥ 1`, there exists an `L`-normal element of `K_{b^k}`
if and only if `b^L ∣ k` or `(b, L) = (2, 1)`. -/
theorem all_kernel_pow_iff {b k L : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) (hL : 1 ≤ L) :
    (∃ x, x ∈ Kernel (b ^ k) ∧ OrderNormal b L x) ↔ b ^ L ∣ k ∨ (b = 2 ∧ L = 1) := by
  constructor
  · rintro ⟨x, hx_pow, hnorm⟩
    by_cases hx_b : x ∈ Kernel b
    · right
      by_cases hb3 : 3 ≤ b
      · exfalso
        have h1 := orderNormal_of_le (by omega) hL hnorm
        exact not_simply_normal_of_mem_kernel hb3 hx_b fun d hd => by
          change Tendsto (wordFreq b 1 x d) atTop (𝓝 (1 / (b : ℝ)))
          simpa [pow_one] using h1 d (by simpa using hd)
      · have hb2 : b = 2 := by omega
        subst hb2
        by_cases hL2 : 2 ≤ L
        · exfalso
          have h2 := orderNormal_of_le (by omega) hL2 hnorm
          exact (not_two_normal_of_mem_binary_kernel hx_b).2 h2
        · exact ⟨rfl, by omega⟩
    · left
      exact (tower_iff hb hk hL).mp ⟨x, ⟨hx_pow, hx_b⟩, hnorm⟩
  · rintro (hdvd | ⟨rfl, rfl⟩)
    · obtain ⟨x, ⟨hx_pow, _⟩, hnorm⟩ := (tower_iff hb hk hL).mpr hdvd
      exact ⟨x, hx_pow, hnorm⟩
    · refine ⟨altRunsValue, ?_, altRuns_orderNormal_one⟩
      have hK2 : altRunsValue ∈ Kernel 2 := zeroOrbit_subset_kernel 2 altRuns_mem_zeroOrbit
      exact tendsto_radixDiscrepancy_pow_one (by omega) hK2

/-! ### Part 7: Universal `L`-normal discrepancy upper bound (`D^+ ≤ 2 / b^L`) -/

/-- Grid-interval frequency identity: for `k₁ ≤ k₂ ≤ b^L`, the frequency on `[k₁ / b^L, k₂ / b^L)`
equals the sum of `wordFreq b L x v N` over `v ∈ Ico k₁ k₂`. -/
private lemma frequency_grid_eq_sum_wordFreq {b L : ℕ} (hb : 1 ≤ b) (x : ℝ) (N : ℕ)
    {k₁ k₂ : ℕ} (_hk : k₁ ≤ k₂) :
    frequency (shift b x) ((k₁ : ℝ) / (b : ℝ) ^ L) ((k₂ : ℝ) / (b : ℝ) ^ L) N =
      ∑ v ∈ Ico k₁ k₂, wordFreq b L x v N := by
  have hbL_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by exact_mod_cast (show 0 < b by omega)) L
  unfold frequency wordFreq wordCount
  rw [← Finset.sum_div, ← Nat.cast_sum, ← Finset.card_biUnion]
  · congr 3
    ext n
    simp only [mem_filter, mem_biUnion, mem_Ico]
    have hnn : 0 ≤ shift b x n := Int.fract_nonneg _
    constructor
    · rintro ⟨hnN, hlo, hhi⟩
      set v := ⌊(b : ℝ) ^ L * shift b x n⌋₊
      have hv_lo : k₁ ≤ v := (Nat.le_floor_iff (mul_nonneg hbL_pos.le hnn)).mpr
        (by rwa [div_le_iff₀ hbL_pos, mul_comm] at hlo)
      have hv_hi : v < k₂ := (Nat.floor_lt (mul_nonneg hbL_pos.le hnn)).mpr
        (by rwa [lt_div_iff₀ hbL_pos, mul_comm] at hhi)
      exact ⟨v, ⟨hv_lo, hv_hi⟩, hnN, rfl⟩
    · rintro ⟨v, ⟨hv_lo, hv_hi⟩, hnN, hv_eq⟩
      refine ⟨hnN, ?_, ?_⟩
      · rw [div_le_iff₀ hbL_pos, mul_comm]
        exact (Nat.le_floor_iff (mul_nonneg hbL_pos.le hnn)).mp (hv_eq.symm ▸ hv_lo)
      · rw [lt_div_iff₀ hbL_pos, mul_comm]
        exact (Nat.floor_lt (mul_nonneg hbL_pos.le hnn)).mp (hv_eq.symm ▸ hv_hi)
  · intro u _ v _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n h1 h2
    exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)

/-- Frequency is monotone in the interval endpoints. -/
private lemma frequency_mono {u : ℕ → ℝ} {a₁ a₂ c₁ c₂ : ℝ} (ha : a₁ ≤ a₂) (hc : c₂ ≤ c₁) (N : ℕ) :
    frequency u a₂ c₂ N ≤ frequency u a₁ c₁ N := by
  unfold frequency
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  exact_mod_cast card_le_card fun n hn => by
    obtain ⟨hnN, hlo, hhi⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, ha.trans hlo, hhi.trans_le hc⟩

/-- **Universal grid-approximation discrepancy bound:**
for every `b ≥ 1`, `L : ℕ`, `x : ℝ`, and `N : ℕ`,
`D_N(x; b) ≤ 2 / b^L + ∑_{v < b^L} |wordFreq b L x v N - 1 / b^L|`. -/
theorem radixDiscrepancy_le_grid_add {b L : ℕ} (hb : 1 ≤ b) (x : ℝ) (N : ℕ) :
    radixDiscrepancy b x N ≤
      2 / (b : ℝ) ^ L + ∑ v ∈ range (b ^ L), |wordFreq b L x v N - 1 / (b : ℝ) ^ L| := by
  set M : ℕ := b ^ L
  have hM_pos : 0 < M := pow_pos (by omega) L
  have hMr_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hMr_eq : (M : ℝ) = (b : ℝ) ^ L := Nat.cast_pow b L
  set E : ℝ := ∑ v ∈ range M, |wordFreq b L x v N - 1 / (M : ℝ)|
  have hE_nn : 0 ≤ E := Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- Every grid interval `[k₁ / M, k₂ / M)` (`k₁ ≤ k₂ ≤ M`) has discrepancy at most `E`.
  have hgrid : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₂ ≤ M →
      |frequency (shift b x) ((k₁ : ℝ) / (M : ℝ)) ((k₂ : ℝ) / (M : ℝ)) N -
        ((k₂ : ℝ) - (k₁ : ℝ)) / (M : ℝ)| ≤ E := by
    intro k₁ k₂ hk12 hk2M
    have hfreq_sum : frequency (shift b x) ((k₁ : ℝ) / (M : ℝ)) ((k₂ : ℝ) / (M : ℝ)) N =
        ∑ v ∈ Ico k₁ k₂, wordFreq b L x v N := by
      rw [hMr_eq]
      exact frequency_grid_eq_sum_wordFreq hb x N hk12
    have hlen_sum : ((k₂ : ℝ) - (k₁ : ℝ)) / (M : ℝ) = ∑ _v ∈ Ico k₁ k₂, (1 / (M : ℝ)) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk12]
      ring
    rw [hfreq_sum, hlen_sum, ← Finset.sum_sub_distrib]
    calc |∑ v ∈ Ico k₁ k₂, (wordFreq b L x v N - 1 / (M : ℝ))|
        ≤ ∑ v ∈ Ico k₁ k₂, |wordFreq b L x v N - 1 / (M : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ range M, |wordFreq b L x v N - 1 / (M : ℝ)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => mem_range.mpr (by
            have := (mem_Ico.mp hv).2; omega)) (fun _ _ _ => abs_nonneg _)
  rw [← hMr_eq, radixDiscrepancy_eq_sampleDisc]
  refine sampleDisc_le_of fun a c ha hac hc => ?_
  rw [abs_le]
  constructor
  · -- Lower bound: `-(2 / M + E) ≤ f - (c - a)` via inward rounding `[j₁ / M, j₂ / M) ⊆ [a, c)`.
    set j₁ : ℕ := ⌊(M : ℝ) * a⌋₊ + 1
    set j₂ : ℕ := ⌊(M : ℝ) * c⌋₊
    by_cases hje : j₂ ≤ j₁
    · -- Empty interior rounding: `c - a < 2 / M`.
      have hMc : (M : ℝ) * c < (j₂ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hMa : (⌊(M : ℝ) * a⌋₊ : ℝ) ≤ (M : ℝ) * a := Nat.floor_le (mul_nonneg hMr_pos.le ha)
      have hj_r : (j₂ : ℝ) ≤ (j₁ : ℝ) := by exact_mod_cast hje
      have hlen : c - a ≤ 2 / (M : ℝ) := by
        rw [le_div_iff₀ hMr_pos]
        have hj₁_r : (j₁ : ℝ) = (⌊(M : ℝ) * a⌋₊ : ℝ) + 1 := by push_cast [j₁]; ring
        linarith
      have hf0 := (frequency_bounds (shift b x) a c N).1
      linarith
    · push Not at hje
      have hj₂_leM : j₂ ≤ M := Nat.floor_le_of_le (by nlinarith)
      have ha_lt : a ≤ (j₁ : ℝ) / (M : ℝ) := by
        rw [le_div_iff₀ hMr_pos]
        have := Nat.lt_floor_add_one ((M : ℝ) * a)
        have hj₁_r : (j₁ : ℝ) = (⌊(M : ℝ) * a⌋₊ : ℝ) + 1 := by push_cast [j₁]; ring
        linarith
      have hc_ge : (j₂ : ℝ) / (M : ℝ) ≤ c := by
        rw [div_le_iff₀ hMr_pos]
        have := Nat.floor_le (mul_nonneg hMr_pos.le (ha.trans hac.le))
        linarith
      have hmono := frequency_mono (u := shift b x) ha_lt hc_ge N
      have hgd := (abs_le.mp (hgrid j₁ j₂ hje.le hj₂_leM)).1
      have hja_err : (j₁ : ℝ) / (M : ℝ) - a ≤ 1 / (M : ℝ) := by
        have h1 : (⌊(M : ℝ) * a⌋₊ : ℝ) ≤ (M : ℝ) * a := Nat.floor_le (mul_nonneg hMr_pos.le ha)
        have hj₁_r : (j₁ : ℝ) = (⌊(M : ℝ) * a⌋₊ : ℝ) + 1 := by push_cast [j₁]; ring
        rw [sub_le_iff_le_add, div_le_iff₀ hMr_pos, add_mul, one_div_mul_cancel hMr_pos.ne']
        linarith
      have hjc_err : c - (j₂ : ℝ) / (M : ℝ) ≤ 1 / (M : ℝ) := by
        have h1 : (M : ℝ) * c < (j₂ : ℝ) + 1 := Nat.lt_floor_add_one _
        rw [le_div_iff₀ hMr_pos, sub_mul, div_mul_cancel₀ _ hMr_pos.ne']
        linarith
      have hsub_eq : ((j₂ : ℝ) - (j₁ : ℝ)) / (M : ℝ) = (j₂ : ℝ) / (M : ℝ) - (j₁ : ℝ) / (M : ℝ) :=
        sub_div _ _ _
      have h2M : (2 : ℝ) / (M : ℝ) = 1 / (M : ℝ) + 1 / (M : ℝ) := by ring
      dsimp [E] at hgd
      linarith
  · -- Upper bound: `f - (c - a) ≤ 2 / M + E` via outward rounding `[a, c) ⊆ [k₁ / M, k₂ / M)`.
    set k₁ : ℕ := ⌊(M : ℝ) * a⌋₊
    set k₂ : ℕ := min M (⌊(M : ℝ) * c⌋₊ + 1)
    have hk₁_le_k₂ : k₁ ≤ k₂ := by
      refine le_min ?_ ?_
      · exact Nat.floor_le_of_le (by nlinarith)
      · exact (Nat.floor_mono (mul_le_mul_of_nonneg_left hac.le hMr_pos.le)).trans (Nat.le_succ _)
    have hk₂_leM : k₂ ≤ M := min_le_left _ _
    have ha_ge : (k₁ : ℝ) / (M : ℝ) ≤ a := by
      rw [div_le_iff₀ hMr_pos]
      have := Nat.floor_le (mul_nonneg hMr_pos.le ha)
      linarith
    have hc_le : c ≤ (k₂ : ℝ) / (M : ℝ) := by
      rw [le_div_iff₀ hMr_pos]
      dsimp [k₂]
      rcases le_total M (⌊(M : ℝ) * c⌋₊ + 1) with hle | hle
      · rw [min_eq_left hle]; nlinarith
      · rw [min_eq_right hle]
        push_cast
        linarith [Nat.lt_floor_add_one ((M : ℝ) * c)]
    have hmono := frequency_mono (u := shift b x) ha_ge hc_le N
    have hgd := (abs_le.mp (hgrid k₁ k₂ hk₁_le_k₂ hk₂_leM)).2
    have hka_err : a - (k₁ : ℝ) / (M : ℝ) ≤ 1 / (M : ℝ) := by
      have h1 : (M : ℝ) * a < (k₁ : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hMr_pos, sub_mul, div_mul_cancel₀ _ hMr_pos.ne']
      linarith
    have hkc_err : (k₂ : ℝ) / (M : ℝ) - c ≤ 1 / (M : ℝ) := by
      have hk₂_le : k₂ ≤ ⌊(M : ℝ) * c⌋₊ + 1 := min_le_right _ _
      have hk₂_r : (k₂ : ℝ) ≤ (⌊(M : ℝ) * c⌋₊ : ℝ) + 1 := by exact_mod_cast hk₂_le
      have h1 : (⌊(M : ℝ) * c⌋₊ : ℝ) ≤ (M : ℝ) * c := Nat.floor_le (mul_nonneg hMr_pos.le (ha.trans hac.le))
      rw [le_div_iff₀ hMr_pos, sub_mul, div_mul_cancel₀ _ hMr_pos.ne']
      linarith
    have hsub_eq : ((k₂ : ℝ) - (k₁ : ℝ)) / (M : ℝ) = (k₂ : ℝ) / (M : ℝ) - (k₁ : ℝ) / (M : ℝ) :=
      sub_div _ _ _
    have h2M : (2 : ℝ) / (M : ℝ) = 1 / (M : ℝ) + 1 / (M : ℝ) := by ring
    dsimp [E] at hgd
    linarith

/-- **Asymptotic universal discrepancy bound for `L`-normal reals:**
every `L`-normal real satisfies `D_N(x; b) ≤ 2 / b^L + ε` eventually for every `ε > 0`. -/
theorem eventually_radixDiscrepancy_le_of_orderNormal {b L : ℕ} (hb : 1 ≤ b) {x : ℝ}
    (hx : OrderNormal b L x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, radixDiscrepancy b x N ≤ 2 / (b : ℝ) ^ L + ε := by
  have herr_tend : Tendsto (fun N => ∑ v ∈ range (b ^ L), |wordFreq b L x v N - 1 / (b : ℝ) ^ L|)
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun N => ∑ v ∈ range (b ^ L), |wordFreq b L x v N - 1 / (b : ℝ) ^ L|)
        atTop (𝓝 (∑ _v ∈ range (b ^ L), (0 : ℝ))) := by
      refine tendsto_finset_sum' _ fun v hv => ?_
      have h1 := ((hx v (mem_range.mp hv)).sub (tendsto_const_nhds (x := 1 / (b : ℝ) ^ L))).abs
      simpa using h1
    simpa using hsum
  filter_upwards [Metric.tendsto_nhds.mp herr_tend ε hε] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hN
  linarith [radixDiscrepancy_le_grid_add (L := L) hb x N]

/-- **`limsup` form of the universal `L`-normal discrepancy bound:**
every `L`-normal real satisfies `D^+(x; b) ≤ 2 / b^L`. -/
theorem limsup_radixDiscrepancy_le_of_orderNormal {b L : ℕ} (hb : 1 ≤ b) {x : ℝ}
    (hx : OrderNormal b L x) :
    limsup (radixDiscrepancy b x) atTop ≤ 2 / (b : ℝ) ^ L := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (radixDiscrepancy b x) :=
    (isBoundedUnder_of ⟨0, fun N => (radixDiscrepancy_mem b x N).1⟩).isCoboundedUnder_le
  exact limsup_le_of_le hcob (eventually_radixDiscrepancy_le_of_orderNormal hb hx hε)

end NormalityChecker.HigherOrderTower
end
