module

public import NormalityChecker.CoefficientTransfer
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Polynomial-mass and logarithmic-mass coefficient transfer & q-digamma reflection (Tracks B, D4)

Kernel-checked extensions of `CoefficientTransfer` beyond linear aggregate mass:

1. **Polynomial-mass sparse coefficient transfer (`Track D4` & `Track B1`):**
   For any integer radix `b ≥ 2`, degree `k : ℕ`, and integer sequence `a : ℕ → ℤ` with
   `absMass a X ≤ C * ((X + 1 : ℝ) ^ k)`:
   - `summable_abs_of_poly_mass`: `∑' m, |a(m)| / b^m` converges.
   - `sum_shiftedTail_le_of_poly_mass`:
     `∑ n < N, shiftedTail b a n L ≤ C * 2^k * ((N + L + 1)^k + M_k(b)) / b^L`.
   - `finite_poly_mass_transfer` and `finite_poly_mass_translation`: explicit finite upper bound
     on `1 - D_N(F_b(a); b)` and `|D_N(x + F_b(a); b) - D_N(x; b)|`.
   - `poly_mass_sparse_tendsto_one` & `poly_mass_sparse_preserves_discrepancy`:
     if `A(X) ≤ C * (X + 1)^k` and `S(X) * log X / X → 0` (i.e. `S(X) = o(X / log X)`), then
     `D_N(F_b(a); b) → 1` and `F_b(a) ∈ K_b`.

2. **Logarithmic-mass sparse coefficient transfer (`Track B1–B4` & weight-1 modular forms):**
   If `A(X) ≤ C * X * (log (X + 2))^γ` (for example, `γ = 1` from the divisor-function bound
   `∑_{n ≤ X} τ(n) ≪ X log X` for finite integer-valued combinations of complex even-order
   Dirichlet characters or weight-1 Eisenstein series) and `S(X) * log(log(X + 3)) / X → 0`
   (in particular whenever `S(X) ≪ X / (log X)^α` for any `α > 0`), then
   `D_N(F_b(a); b) → 1` and `F_b(a) ∈ K_b`.

3. **Exact `q`-digamma reflection identity at `q = b^(-M)` (`Track B4`):**
   For every integer radix `b ≥ 2`, modulus `M ≥ 2`, and `1 ≤ r < M`, writing `q = (b : ℝ)^(-M)`:
   `(qDigamma q (r / M) - qDigamma q ((M - r) / M)) / Real.log q = A_{r,M}(b) - A_{M-r,M}(b)`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.GeneralMassTransfer

open CoefficientTransfer Phase18Synthetic SharpTranslation

/-! ### Part 1: Geometric-moment helper and polynomial-mass transfer -/

/-- For `0 < r < 1` and any `k : ℕ`, `∑' j : ℕ, (j : ℝ)^k * r^j` converges. -/
theorem summable_pow_mul_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    Summable (fun j : ℕ => ((j : ℝ) ^ k) * r ^ j) := by
  have h1 : ∀ᶠ j : ℕ in atTop, ‖((j : ℝ) ^ k) * r ^ j‖ ≤ ((1 + r) / 2) ^ j := by
    set ρ : ℝ := (1 + r) / 2
    have hρ_pos : 0 < ρ := by dsimp only [ρ]; linarith
    have hρ_lt : ρ < 1 := by dsimp only [ρ]; linarith
    by_cases hr_zero : r = 0
    · subst hr_zero
      filter_upwards [eventually_ge_atTop 1] with j hj
      rw [zero_pow (by omega), mul_zero, norm_zero]
      exact pow_nonneg hρ_pos.le j
    · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_zero)
      have hrat : 1 < ρ / r := by
        rw [one_lt_div hr_pos]
        dsimp only [ρ]; linarith
      have hlim : Tendsto (fun j : ℕ => (j : ℝ) ^ k / (ρ / r) ^ j) atTop (𝓝 0) :=
        tendsto_pow_const_div_const_pow_of_one_lt k hrat
      filter_upwards [Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp hlim 1 zero_lt_one)] with j hj
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hj
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hdiv_pow : (ρ / r) ^ j = ρ ^ j / r ^ j := div_pow ρ r j
      rw [hdiv_pow, div_div_eq_mul_div, div_lt_iff₀ (pow_pos hρ_pos j)] at hj
      linarith
  have hρ_nonneg : 0 ≤ (1 + r) / 2 := by linarith
  have hρ_lt1 : (1 + r) / 2 < 1 := by linarith
  exact Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one hρ_nonneg hρ_lt1)
    (Nat.cofinite_eq_atTop ▸ h1)

/-- Constant bounding `∑' j : ℕ, ((j : ℝ)^k) / (b : ℝ)^(j + 1)` for `b ≥ 2`. -/
noncomputable def polyGeomConst (b k : ℕ) : ℝ :=
  ∑' j : ℕ, ((j : ℝ) ^ k) / (b : ℝ) ^ (j + 1)

theorem polyGeomConst_nonneg (b k : ℕ) : 0 ≤ polyGeomConst b k :=
  tsum_nonneg (fun j => by positivity)

/-- Summability of `∑' j, (j : ℝ)^k / b^(j + 1)` for `b ≥ 2`. -/
theorem summable_poly_div_pow {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    Summable (fun j : ℕ => ((j : ℝ) ^ k) / (b : ℝ) ^ (j + 1)) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have h := (summable_pow_mul_geom hr0 hr1 k).mul_right (b : ℝ)⁻¹
  refine h.congr (fun j => ?_)
  rw [pow_succ, inv_pow]
  ring

/-- Polynomial-mass summability: if `absMass a X ≤ C * (X + 1)^k` for all `X`, then
`∑' m, |a(m)| / b^m` converges. -/
theorem summable_abs_of_poly_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k) :
    Summable (fun m : ℕ => |(a m : ℝ)| / (b : ℝ) ^ m) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have hsum_k : Summable (fun m : ℕ => ((m : ℝ) ^ k) * ((b : ℝ)⁻¹) ^ m) :=
    summable_pow_mul_geom hr0 hr1 k
  have hsum_0 : Summable (fun m : ℕ => ((b : ℝ)⁻¹) ^ m) :=
    summable_geometric_of_lt_one hr0 hr1
  have hbound : Summable (fun m : ℕ =>
      (C * (2 : ℝ) ^ k * ((m : ℝ) ^ k) + (C * (2 : ℝ) ^ k + |(a 0 : ℝ)|)) * ((b : ℝ)⁻¹) ^ m) := by
    have h1 := hsum_k.mul_left (C * (2 : ℝ) ^ k)
    have h2 := hsum_0.mul_left (C * (2 : ℝ) ^ k + |(a 0 : ℝ)|)
    convert h1.add h2 using 1
    ext m; ring
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hbound
  rw [div_eq_mul_inv, ← inv_pow]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero]
    have : 0 ≤ C * (2 : ℝ) ^ k * ((0 : ℝ) ^ k) + C * (2 : ℝ) ^ k := by positivity
    linarith
  · have hmem : m ∈ Icc 1 m := mem_Icc.mpr ⟨hm, le_rfl⟩
    have hle1 : |(a m : ℝ)| ≤ absMass a m :=
      Finset.single_le_sum (f := fun j => |(a j : ℝ)|) (fun _ _ => abs_nonneg _) hmem
    have hpow_le : ((m + 1 : ℕ) : ℝ) ^ k ≤ (2 : ℝ) ^ k * ((m : ℝ) ^ k + 1) := by
      have hm1 : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
        have : m + 1 ≤ 2 * m := by omega
        exact_mod_cast this
      calc ((m + 1 : ℕ) : ℝ) ^ k ≤ (2 * (m : ℝ)) ^ k :=
            pow_le_pow_left₀ (by positivity) hm1 k
        _ = (2 : ℝ) ^ k * (m : ℝ) ^ k := mul_pow 2 (m : ℝ) k
        _ ≤ (2 : ℝ) ^ k * ((m : ℝ) ^ k + 1) := by
            have : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
            nlinarith
    have hle2 := (hle1.trans (hmass m)).trans (mul_le_mul_of_nonneg_left hpow_le hC)
    have ha0 : 0 ≤ |(a 0 : ℝ)| := abs_nonneg _
    linarith

/-- Elementary inequality `(u + v)^k ≤ 2^k * (u^k + v^k)` for `u, v ≥ 0`. -/
private lemma add_pow_le_two_pow_mul {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (k : ℕ) :
    (u + v) ^ k ≤ (2 : ℝ) ^ k * (u ^ k + v ^ k) := by
  have hmax : u + v ≤ 2 * max u v := by
    have h1 : u ≤ max u v := le_max_left u v
    have h2 : v ≤ max u v := le_max_right u v
    linarith
  calc (u + v) ^ k ≤ (2 * max u v) ^ k := pow_le_pow_left₀ (by positivity) hmax k
    _ = (2 : ℝ) ^ k * (max u v) ^ k := mul_pow 2 _ k
    _ ≤ (2 : ℝ) ^ k * (u ^ k + v ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total u v with hle | hle
        · rw [max_eq_right hle]; linarith [pow_nonneg hu k]
        · rw [max_eq_left hle]; linarith [pow_nonneg hv k]

/-- Bounding the sum of shifted tails `∑ n < N, shiftedTail b a n L` under polynomial mass
`absMass a X ≤ C * (X + 1)^k`. -/
theorem sum_shiftedTail_le_of_poly_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k) (N L : ℕ) :
    ∑ n ∈ range N, shiftedTail b a n L ≤
      C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) / (b : ℝ) ^ L := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < b := by positivity
  have hsum_all := summable_abs_of_poly_mass hb hC k hmass
  have hsum_n : ∀ n ∈ range N,
      Summable (fun j : ℕ => |(a (n + L + 1 + j) : ℝ)| / (b : ℝ) ^ (L + 1 + j)) := by
    intro n _
    have hshift : Summable (fun j : ℕ => |(a (j + (n + L + 1)) : ℝ)| / (b : ℝ) ^ (j + (n + L + 1))) :=
      hsum_all.comp_injective (add_left_injective (n + L + 1))
    have hmul := hshift.mul_left ((b : ℝ) ^ n)
    refine hmul.congr (fun j => ?_)
    have heq1 : j + (n + L + 1) = n + L + 1 + j := by omega
    have heq2 : n + (L + 1 + j) = n + L + 1 + j := by omega
    rw [heq1, ← heq2, pow_add]
    field_simp [hb_pos.ne']
  have hsum_rhs_const : Summable (fun j : ℕ =>
      C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j)) := by
    have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
    have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left
      (C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k) / (b : ℝ) ^ (L + 1))
    refine h.congr (fun j => ?_)
    rw [pow_add, inv_pow]; ring
  have hsum_rhs_var : Summable (fun j : ℕ =>
      C * (2 : ℝ) ^ k * ((j : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j)) := by
    have h := (summable_poly_div_pow hb k).mul_left (C * (2 : ℝ) ^ k / (b : ℝ) ^ L)
    refine h.congr (fun j => ?_)
    have : L + 1 + j = L + (j + 1) := by omega
    rw [this, pow_add]; ring
  have hsum_rhs := hsum_rhs_const.add hsum_rhs_var
  have hterm : ∀ j : ℕ,
      (∑ n ∈ range N, |(a (n + L + 1 + j) : ℝ)| / (b : ℝ) ^ (L + 1 + j)) ≤
        C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j) +
        C * (2 : ℝ) ^ k * ((j : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j) := by
    intro j
    rw [← Finset.sum_div, ← add_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have himg : ∑ n ∈ range N, |(a (n + L + 1 + j) : ℝ)| ≤ absMass a (N + L + 1 + j) := by
      unfold absMass
      have hinj : Set.InjOn (fun n => n + L + 1 + j) (range N : Set ℕ) :=
        fun x _ y _ h => by simp only at h; omega
      rw [← Finset.sum_image (f := fun m => |(a m : ℝ)|) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
      intro m hm
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
      rw [mem_range] at hn
      rw [mem_Icc]
      omega
    have hadd : (((N + L + 1 + j + 1 : ℕ) : ℝ)) = ((N + L + 2 : ℕ) : ℝ) + (j : ℝ) := by
      push_cast; ring
    have hpow := add_pow_le_two_pow_mul (u := ((N + L + 2 : ℕ) : ℝ)) (v := (j : ℝ))
      (by positivity) (by positivity) k
    have h1 := (himg.trans (hmass (N + L + 1 + j)))
    rw [hadd] at h1
    have h2 := h1.trans (mul_le_mul_of_nonneg_left hpow hC)
    linarith
  have hgeom_sum : ∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ (j + 1) ≤ 1 := by
    have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
    have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
    have hts : ∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ (j + 1) = (b : ℝ)⁻¹ * ∑' j : ℕ, ((b : ℝ)⁻¹) ^ j := by
      rw [← tsum_mul_left]
      congr 1; ext j; rw [pow_succ, inv_pow]; ring
    rw [hts, tsum_geometric_of_lt_one hr0 hr1]
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have hbm1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
    have heq : (b : ℝ)⁻¹ * (1 - (b : ℝ)⁻¹)⁻¹ = 1 / ((b : ℝ) - 1) := by
      field_simp [hb_pos.ne', hbm1.ne']
    rw [heq, div_le_one hbm1]
    linarith
  calc ∑ n ∈ range N, shiftedTail b a n L
      = ∑' j : ℕ, ∑ n ∈ range N, |(a (n + L + 1 + j) : ℝ)| / (b : ℝ) ^ (L + 1 + j) := by
        unfold shiftedTail
        rw [Summable.tsum_finsetSum hsum_n]
    _ ≤ ∑' j : ℕ, (C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j) +
                    C * (2 : ℝ) ^ k * ((j : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j)) :=
        Summable.tsum_le_tsum hterm (summable_sum hsum_n) hsum_rhs
    _ = (∑' j : ℕ, C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j)) +
        (∑' j : ℕ, C * (2 : ℝ) ^ k * ((j : ℝ) ^ k) / (b : ℝ) ^ (L + 1 + j)) :=
        hsum_rhs_const.tsum_add hsum_rhs_var
    _ = (C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k) / (b : ℝ) ^ L) *
          (∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ (j + 1)) +
        (C * (2 : ℝ) ^ k / (b : ℝ) ^ L) * polyGeomConst b k := by
        unfold polyGeomConst
        rw [← tsum_mul_left, ← tsum_mul_left]
        congr 1
        · congr 1; ext j
          have : L + 1 + j = L + (j + 1) := by omega
          rw [this, pow_add]; ring
        · congr 1; ext j
          have : L + 1 + j = L + (j + 1) := by omega
          rw [this, pow_add]; ring
    _ ≤ (C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k) / (b : ℝ) ^ L) * 1 +
        (C * (2 : ℝ) ^ k / (b : ℝ) ^ L) * polyGeomConst b k := by
        gcongr
    _ = C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) / (b : ℝ) ^ L := by
        ring

/-- **Finite polynomial-mass sparse coefficient transfer inequality (Track D4 / B1).** -/
theorem finite_poly_mass_transfer {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k)
    {N : ℕ} (hN : 0 < N) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    1 - radixDiscrepancy b (coeffSeries b a) N ≤
      2 * ε + ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) +
        C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) /
          ((N : ℝ) * ε * (b : ℝ) ^ L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := summable_abs_of_poly_mass hb hC k hmass
  have hdef := discrepancy_deficit_le b (coeffSeries b a) hε.le N
  have hfar := farCount_le_local_add_tail (show 1 ≤ b by omega) hsum N L ε
  have hmarkov := markov_tail_card_le b a N L hε
  have htail := sum_shiftedTail_le_of_poly_mass hb hC k hmass N L
  have hfar_r : (farCount b (coeffSeries b a) ε N : ℝ) ≤
      ((L * supportCount a (N + L) : ℕ) : ℝ) +
        (C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) / (b : ℝ) ^ L) / ε := by
    have h1 : (farCount b (coeffSeries b a) ε N : ℝ) ≤
        ((L * supportCount a (N + L) : ℕ) : ℝ) + (tailExceedCount b a N L ε : ℝ) := by
      exact_mod_cast hfar
    have h2 : (∑ n ∈ range N, shiftedTail b a n L) / ε ≤
        (C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) / (b : ℝ) ^ L) / ε :=
      div_le_div_of_nonneg_right htail hε.le
    linarith
  have hdiv := div_le_div_of_nonneg_right hfar_r hNr.le
  rw [add_div] at hdiv
  have hrew : ((C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) /
      (b : ℝ) ^ L) / ε) / (N : ℝ) =
      C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) /
        ((N : ℝ) * ε * (b : ℝ) ^ L) := by ring
  rw [hrew] at hdiv
  linarith

/-- Uniform translation form of `finite_poly_mass_transfer`. -/
theorem finite_poly_mass_translation {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k)
    (x : ℝ) {N : ℕ} (hN : 0 < N) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    |radixDiscrepancy b (x + coeffSeries b a) N - radixDiscrepancy b x N| ≤
      2 * ε + ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) +
        C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) /
          ((N : ℝ) * ε * (b : ℝ) ^ L) :=
  (SharpTranslation.sharp_translation b x (coeffSeries b a) hN).trans
    (finite_poly_mass_transfer hb hC k hmass hN L hε)

/-- **Asymptotic polynomial-mass sparse coefficient transfer (Track D4).**
If `A(X) ≤ C * (X + 1)^k` (arbitrary polynomial growth!) and `S(X) * log X / X → 0`
(i.e. `S(X) = o(X / log X)`), then `D_N(F_b(a); b) → 1` (`F_b(a) ∈ K_b`). -/
theorem poly_mass_sparse_tendsto_one {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k)
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b a) N) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε : ℝ := η / 6 with hε_def
  have hε : 0 < ε := by positivity
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  -- Choose `L(N) = ⌈(k + 1) * log N / log b⌉ + L₀`, where `b^L₀` kills the constant factor.
  set Kconst : ℝ := C * (2 : ℝ) ^ k * ((3 : ℝ) ^ k + polyGeomConst b k) with hKc_def
  have hKc_nonneg : 0 ≤ Kconst := by
    have := polyGeomConst_nonneg b k
    positivity
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hb1)) (max 1 (3 * Kconst / (ε * η))))
  have hL₀_ge : 3 * Kconst / (ε * η) ≤ (b : ℝ) ^ L₀ := (le_max_right _ _).trans (hL₀ L₀ le_rfl)
  -- For large `N`, `L(N) ≤ (2 * (k + 1) / log b) * log N ≤ N` and `L(N) * S(N + L(N)) / N < η / 3`.
  set α : ℝ := ((k + 1 : ℕ) : ℝ) / Real.log (b : ℝ)
  have hα_pos : 0 < α := by positivity
  -- Threshold where `L₀ + 1 ≤ α * log N` and `2 * α * log N + 2 ≤ N`.
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_div : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, pow_one, one_mul, add_zero] using h
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_atTop.mp hlog_top) (max 2 (((L₀ + 1 : ℕ) : ℝ) / α)))
  obtain ⟨M₂, hM₂⟩ := Metric.tendsto_atTop.mp hlog_div (1 / (4 * α + 4)) (by positivity)
  obtain ⟨M₃, hM₃⟩ := Metric.tendsto_atTop.mp hsparse (η / (12 * α)) (by positivity)
  refine ⟨max (max (max M₁ M₂) M₃) 8, fun N hN => ?_⟩
  have hNM₁ : M₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hNM₂ : M₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hNM₃ : M₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN8 : 8 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlogN_ge2 : (2 : ℝ) ≤ Real.log (N : ℝ) := (le_max_left _ _).trans (hM₁ N hNM₁)
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hL₀_le : ((L₀ + 1 : ℕ) : ℝ) ≤ α * Real.log (N : ℝ) := by
    have h := (le_max_right _ _).trans (hM₁ N hNM₁)
    rw [div_le_iff₀ hα_pos] at h
    linarith
  -- Define `L = Nat.ceil (α * log N) + L₀`.
  set L : ℕ := Nat.ceil (α * Real.log (N : ℝ)) + L₀
  have hL_ge_real : α * Real.log (N : ℝ) + (L₀ : ℝ) ≤ (L : ℝ) := by
    have hc := Nat.le_ceil (α * Real.log (N : ℝ))
    push_cast [L]; linarith
  have hL_le_real : (L : ℝ) ≤ 2 * α * Real.log (N : ℝ) := by
    have hc : (Nat.ceil (α * Real.log (N : ℝ)) : ℝ) < α * Real.log (N : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    push_cast [L] at *
    linarith
  have hL_le_N : (L : ℝ) ≤ (N : ℝ) := by
    have hdiv := hM₂ N hNM₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdiv
    have hmul : Real.log (N : ℝ) < (N : ℝ) / (4 * α + 4) := by
      rw [div_lt_iff₀ hNr] at hdiv
      have : (1 / (4 * α + 4)) * (N : ℝ) = (N : ℝ) / (4 * α + 4) := by ring
      linarith
    have h1 : 2 * α * Real.log (N : ℝ) ≤ (N : ℝ) := by
      have hlt : 2 * α * Real.log (N : ℝ) < 2 * α * ((N : ℝ) / (4 * α + 4)) :=
        mul_lt_mul_of_pos_left hmul (by positivity)
      have h2 : 2 * α * ((N : ℝ) / (4 * α + 4)) ≤ (N : ℝ) := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    linarith
  have hL_le_N_nat : L ≤ N := by exact_mod_cast hL_le_N
  have htr := finite_poly_mass_transfer hb hC k hmass hNpos L hε
  have hD_le : radixDiscrepancy b (coeffSeries b a) N ≤ 1 := (radixDiscrepancy_mem b _ N).2
  -- Bound the support term `L * S(N + L) / N < η / 3`.
  have hsp := hM₃ (N + L) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsp
  have hlog_mono : Real.log (N : ℝ) ≤ Real.log ((N + L : ℕ) : ℝ) :=
    Real.log_le_log hNr (by exact_mod_cast (show N ≤ N + L by omega))
  have hNL_le_2N : ((N + L : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : N + L ≤ 2 * N := by omega
    exact_mod_cast this
  have hsup_bound : ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) < η / 3 := by
    have hNL_pos : (0 : ℝ) < ((N + L : ℕ) : ℝ) := by positivity
    calc ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ)
        = (L : ℝ) * (supportCount a (N + L) : ℝ) / (N : ℝ) := by rw [Nat.cast_mul]
      _ ≤ (2 * α * Real.log (N : ℝ)) * (supportCount a (N + L) : ℝ) / (N : ℝ) := by
            gcongr
      _ ≤ (2 * α * Real.log ((N + L : ℕ) : ℝ)) * (supportCount a (N + L) : ℝ) / (N : ℝ) := by
            gcongr
      _ ≤ 4 * α * ((supportCount a (N + L) : ℝ) * Real.log ((N + L : ℕ) : ℝ) / ((N + L : ℕ) : ℝ)) := by
            have hnum_nonneg : 0 ≤ (supportCount a (N + L) : ℝ) * Real.log ((N + L : ℕ) : ℝ) := by
              have : 0 ≤ Real.log ((N + L : ℕ) : ℝ) := by linarith
              positivity
            rw [← mul_div_assoc (4 * α), div_le_div_iff₀ hNr hNL_pos]
            have hstep := mul_le_mul_of_nonneg_left hNL_le_2N
              (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * α) hnum_nonneg)
            linarith
      _ < 4 * α * (η / (12 * α)) := mul_lt_mul_of_pos_left hsp (by positivity)
      _ = η / 3 := by field_simp [hα_pos.ne']; ring
  -- Bound the tail term using `b^L ≥ b^(α log N) * b^L₀ = N^(k+1) * b^L₀`.
  have hbL_lower : (N : ℝ) ^ (k + 1) * (b : ℝ) ^ L₀ ≤ (b : ℝ) ^ L := by
    have h1 : (N : ℝ) ^ (k + 1) = Real.exp (((k + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hNr, mul_comm]
    have h2 : (b : ℝ) ^ (Nat.ceil (α * Real.log (N : ℝ))) ≥ (N : ℝ) ^ (k + 1) := by
      rw [h1, ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < b)]
      apply Real.exp_le_exp.mpr
      have hceil : α * Real.log (N : ℝ) ≤ (Nat.ceil (α * Real.log (N : ℝ)) : ℝ) :=
        Nat.le_ceil _
      have hmul := mul_le_mul_of_nonneg_left hceil hlogb_pos.le
      have hal : Real.log (b : ℝ) * (α * Real.log (N : ℝ)) = ((k + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
        simp only [α]; field_simp [hlogb_pos.ne']
      linarith
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (Nat.ceil (α * Real.log (N : ℝ))) * (b : ℝ) ^ L₀ := by
      simp only [L, pow_add]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have htail_bound :
      C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) /
        ((N : ℝ) * ε * (b : ℝ) ^ L) ≤ η / 3 := by
    have hN3 : ((N + L + 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      have : N + L + 2 ≤ 3 * N := by omega
      exact_mod_cast this
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hNk1 : (1 : ℝ) ≤ (N : ℝ) ^ k := one_le_pow₀ hN1
    have hnum_le : C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) ≤
        Kconst * (N : ℝ) ^ k := by
      have h1 : ((N + L + 2 : ℕ) : ℝ) ^ k ≤ (3 : ℝ) ^ k * (N : ℝ) ^ k := by
        calc ((N + L + 2 : ℕ) : ℝ) ^ k ≤ (3 * (N : ℝ)) ^ k :=
              pow_le_pow_left₀ (by positivity) hN3 k
          _ = (3 : ℝ) ^ k * (N : ℝ) ^ k := mul_pow 3 (N : ℝ) k
      have h2 : polyGeomConst b k ≤ polyGeomConst b k * (N : ℝ) ^ k :=
        le_mul_of_one_le_right (polyGeomConst_nonneg b k) hNk1
      simp only [Kconst]
      have : 0 ≤ C * (2 : ℝ) ^ k := by positivity
      nlinarith
    have hden_ge : (N : ℝ) * ε * ((N : ℝ) ^ (k + 1) * (b : ℝ) ^ L₀) ≤ (N : ℝ) * ε * (b : ℝ) ^ L := by
      gcongr
    have hden_ge2 : (N : ℝ) ^ k * (ε * (b : ℝ) ^ L₀) ≤ (N : ℝ) * ε * (b : ℝ) ^ L := by
      have hpow_le : (N : ℝ) ^ k ≤ (N : ℝ) * (N : ℝ) ^ (k + 1) := by
        have h1 : (N : ℝ) ^ k ≤ (N : ℝ) ^ (k + 1) := by
          rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hN1
        exact h1.trans (le_mul_of_one_le_left (by positivity) hN1)
      have hstep : (N : ℝ) ^ k * (ε * (b : ℝ) ^ L₀) ≤
          (N : ℝ) * (N : ℝ) ^ (k + 1) * (ε * (b : ℝ) ^ L₀) :=
        mul_le_mul_of_nonneg_right hpow_le (by positivity)
      linarith
    calc C * (2 : ℝ) ^ k * (((N + L + 2 : ℕ) : ℝ) ^ k + polyGeomConst b k) /
          ((N : ℝ) * ε * (b : ℝ) ^ L)
        ≤ (Kconst * (N : ℝ) ^ k) / ((N : ℝ) ^ k * (ε * (b : ℝ) ^ L₀)) := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge2
      _ = Kconst / (ε * (b : ℝ) ^ L₀) := by
          have hNk_ne : (N : ℝ) ^ k ≠ 0 := by positivity
          field_simp [hNk_ne]
      _ ≤ η / 3 := by
          rw [div_le_iff₀ (by positivity)]
          have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < ε * η)).mp hL₀_ge
          linarith
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

/-- Universal discrepancy preservation (`F_b(a) ∈ K_b`) under polynomial mass `A(X) = O(X^k)`
and super-logarithmic sparsity `S(X) = o(X / log X)`. -/
theorem poly_mass_sparse_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ}
    (hC : 0 ≤ C) (k : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k)
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (x + coeffSeries b a) N - radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  have h1 := poly_mass_sparse_tendsto_one hb hC k hmass hsparse
  have hgap : Tendsto (fun N : ℕ => 1 - radixDiscrepancy b (coeffSeries b a) N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  rw [Metric.tendsto_atTop] at hgap ⊢
  intro η hη
  obtain ⟨M, hM⟩ := hgap η hη
  refine ⟨max 1 M, fun N hN => ?_⟩
  have hNpos : 0 < N := by have := (le_max_left 1 M).trans hN; omega
  have hNM : M ≤ N := (le_max_right 1 M).trans hN
  have htr := SharpTranslation.sharp_translation b x (coeffSeries b a) hNpos
  have hMN := hM N hNM
  rw [Real.dist_eq, sub_zero] at hMN ⊢
  have hnonneg : 0 ≤ 1 - radixDiscrepancy b (coeffSeries b a) N := by
    linarith [(radixDiscrepancy_mem b (coeffSeries b a) N).2]
  rw [abs_of_nonneg hnonneg] at hMN
  exact lt_of_le_of_lt htr hMN

/-! ### Part 1b: Logarithmic-mass sparse coefficient transfer (Track B1–B4 & weight-1 forms) -/

/-- Logarithmic-mass summability: if `absMass a X ≤ C * X * (log (X + 2))^γ`, then
`∑' m, |a(m)| / b^m` converges. -/
theorem summable_abs_of_log_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (γ : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ) * (Real.log ((X + 2 : ℕ) : ℝ)) ^ γ) :
    Summable (fun m : ℕ => |(a m : ℝ)| / (b : ℝ) ^ m) := by
  refine summable_abs_of_poly_mass hb (C := C * (2 : ℝ) ^ γ) (by positivity) (γ + 1) (fun X => ?_)
  have hlog : Real.log ((X + 2 : ℕ) : ℝ) ≤ 2 * ((X + 1 : ℕ) : ℝ) := by
    have h1 : Real.log ((X + 2 : ℕ) : ℝ) ≤ ((X + 2 : ℕ) : ℝ) :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have h2 : ((X + 2 : ℕ) : ℝ) ≤ 2 * ((X + 1 : ℕ) : ℝ) := by
      have : X + 2 ≤ 2 * (X + 1) := by omega
      exact_mod_cast this
    linarith
  have hlog_nonneg : 0 ≤ Real.log ((X + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + 2 by omega))
  have hX_le : (X : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ X
  calc absMass a X ≤ C * (X : ℝ) * (Real.log ((X + 2 : ℕ) : ℝ)) ^ γ := hmass X
    _ ≤ C * ((X + 1 : ℕ) : ℝ) * (2 * ((X + 1 : ℕ) : ℝ)) ^ γ := by
        gcongr
    _ = C * (2 : ℝ) ^ γ * ((X + 1 : ℕ) : ℝ) ^ (γ + 1) := by
        rw [mul_pow, pow_succ]; ring

/-- Bounding the sum of shifted tails under logarithmic mass
`absMass a X ≤ C * X * (log (X + 2))^γ`. -/
theorem sum_shiftedTail_le_of_log_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (γ : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ) * (Real.log ((X + 2 : ℕ) : ℝ)) ^ γ)
    (N L : ℕ) :
    ∑ n ∈ range N, shiftedTail b a n L ≤
      C * (2 : ℝ) ^ γ *
        ((((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) * (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ +
         ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ + polyGeomConst b (γ + 1)) /
        (b : ℝ) ^ L := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < b := by positivity
  have hsum_all := summable_abs_of_log_mass hb hC γ hmass
  have hsum_n : ∀ n ∈ range N,
      Summable (fun j : ℕ => |(a (n + L + 1 + j) : ℝ)| / (b : ℝ) ^ (L + 1 + j)) := by
    intro n _
    have hshift : Summable (fun j : ℕ => |(a (j + (n + L + 1)) : ℝ)| / (b : ℝ) ^ (j + (n + L + 1))) :=
      hsum_all.comp_injective (add_left_injective (n + L + 1))
    have hmul := hshift.mul_left ((b : ℝ) ^ n)
    refine hmul.congr (fun j => ?_)
    have heq1 : j + (n + L + 1) = n + L + 1 + j := by omega
    have heq2 : n + (L + 1 + j) = n + L + 1 + j := by omega
    rw [heq1, ← heq2, pow_add]
    field_simp [hb_pos.ne']
  set A₀ : ℝ := ((N + L + 1 : ℕ) : ℝ)
  set lg : ℝ := Real.log ((N + L + 3 : ℕ) : ℝ)
  have hlg_nonneg : 0 ≤ lg := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + L + 3 by omega))
  -- Four summable pieces for `(A₀ + j) * (lg^γ + j^γ) / b^(L + 1 + j)`.
  have hS0 : Summable (fun j : ℕ => (A₀ * lg ^ γ) / (b : ℝ) ^ (L + 1 + j)) := by
    have h := (summable_poly_div_pow hb 0).mul_left (A₀ * lg ^ γ / (b : ℝ) ^ L)
    refine h.congr (fun j => ?_)
    have : L + 1 + j = L + (j + 1) := by omega
    rw [this, pow_add]; simp; ring
  have hS1 : Summable (fun j : ℕ => (lg ^ γ * (j : ℝ)) / (b : ℝ) ^ (L + 1 + j)) := by
    have h := (summable_poly_div_pow hb 1).mul_left (lg ^ γ / (b : ℝ) ^ L)
    refine h.congr (fun j => ?_)
    have : L + 1 + j = L + (j + 1) := by omega
    rw [this, pow_add, pow_one]; ring
  have hS2 : Summable (fun j : ℕ => (A₀ * (j : ℝ) ^ γ) / (b : ℝ) ^ (L + 1 + j)) := by
    have h := (summable_poly_div_pow hb γ).mul_left (A₀ / (b : ℝ) ^ L)
    refine h.congr (fun j => ?_)
    have : L + 1 + j = L + (j + 1) := by omega
    rw [this, pow_add]; ring
  have hS3 : Summable (fun j : ℕ => ((j : ℝ) ^ (γ + 1)) / (b : ℝ) ^ (L + 1 + j)) := by
    have h := (summable_poly_div_pow hb (γ + 1)).mul_left (1 / (b : ℝ) ^ L)
    refine h.congr (fun j => ?_)
    have : L + 1 + j = L + (j + 1) := by omega
    rw [this, pow_add]; ring
  have hS_tot := (((hS0.add hS1).add hS2).add hS3).mul_left (C * (2 : ℝ) ^ γ)
  have hterm : ∀ j : ℕ,
      (∑ n ∈ range N, |(a (n + L + 1 + j) : ℝ)| / (b : ℝ) ^ (L + 1 + j)) ≤
        C * (2 : ℝ) ^ γ *
          (((A₀ * lg ^ γ) / (b : ℝ) ^ (L + 1 + j) + (lg ^ γ * (j : ℝ)) / (b : ℝ) ^ (L + 1 + j)) +
            (A₀ * (j : ℝ) ^ γ) / (b : ℝ) ^ (L + 1 + j) +
            ((j : ℝ) ^ (γ + 1)) / (b : ℝ) ^ (L + 1 + j)) := by
    intro j
    rw [← Finset.sum_div]
    have hrhs_eq :
        C * (2 : ℝ) ^ γ *
          (((A₀ * lg ^ γ) / (b : ℝ) ^ (L + 1 + j) + (lg ^ γ * (j : ℝ)) / (b : ℝ) ^ (L + 1 + j)) +
            (A₀ * (j : ℝ) ^ γ) / (b : ℝ) ^ (L + 1 + j) +
            ((j : ℝ) ^ (γ + 1)) / (b : ℝ) ^ (L + 1 + j)) =
        (C * (2 : ℝ) ^ γ * ((A₀ + (j : ℝ)) * (lg ^ γ + (j : ℝ) ^ γ))) / (b : ℝ) ^ (L + 1 + j) := by
      rw [pow_succ]; ring
    rw [hrhs_eq]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have himg : ∑ n ∈ range N, |(a (n + L + 1 + j) : ℝ)| ≤ absMass a (N + L + 1 + j) := by
      unfold absMass
      have hinj : Set.InjOn (fun n => n + L + 1 + j) (range N : Set ℕ) :=
        fun x _ y _ h => by simp only at h; omega
      rw [← Finset.sum_image (f := fun m => |(a m : ℝ)|) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
      intro m hm
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
      rw [mem_range] at hn; rw [mem_Icc]; omega
    have hlog_add : Real.log ((N + L + 1 + j + 2 : ℕ) : ℝ) ≤ lg + (j : ℝ) := by
      have hprod : ((N + L + 1 + j + 2 : ℕ) : ℝ) ≤ ((N + L + 3 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
        have : N + L + 1 + j + 2 ≤ (N + L + 3) * (j + 1) := by nlinarith
        exact_mod_cast this
      have h1 : Real.log ((N + L + 1 + j + 2 : ℕ) : ℝ) ≤
          Real.log (((N + L + 3 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) :=
        Real.log_le_log (by positivity) hprod
      rw [Real.log_mul (by positivity) (by positivity)] at h1
      have h2 : Real.log ((j + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((j + 1 : ℕ) : ℝ) by positivity)
        push_cast at this ⊢; linarith
      linarith
    have hlog_nonneg' : 0 ≤ Real.log ((N + L + 1 + j + 2 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + L + 1 + j + 2 by omega))
    have hpow := (pow_le_pow_left₀ hlog_nonneg' hlog_add γ).trans
      (add_pow_le_two_pow_mul hlg_nonneg (Nat.cast_nonneg j) γ)
    have hcoef_eq : ((N + L + 1 + j : ℕ) : ℝ) = A₀ + (j : ℝ) := by simp only [A₀]; push_cast; ring
    have h1 := himg.trans (hmass (N + L + 1 + j))
    rw [hcoef_eq] at h1
    have h2 : C * (A₀ + (j : ℝ)) * (Real.log ((N + L + 1 + j + 2 : ℕ) : ℝ)) ^ γ ≤
        C * (A₀ + (j : ℝ)) * ((2 : ℝ) ^ γ * (lg ^ γ + (j : ℝ) ^ γ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    linarith
  have hgeom_sum : ∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ (j + 1) ≤ 1 := by
    have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
    have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
    have hts : ∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ (j + 1) = (b : ℝ)⁻¹ * ∑' j : ℕ, ((b : ℝ)⁻¹) ^ j := by
      rw [← tsum_mul_left]; congr 1; ext j; rw [pow_succ, inv_pow]; ring
    rw [hts, tsum_geometric_of_lt_one hr0 hr1]
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have hbm1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
    have heq : (b : ℝ)⁻¹ * (1 - (b : ℝ)⁻¹)⁻¹ = 1 / ((b : ℝ) - 1) := by
      field_simp [hb_pos.ne', hbm1.ne']
    rw [heq, div_le_one hbm1]; linarith
  calc ∑ n ∈ range N, shiftedTail b a n L
      = ∑' j : ℕ, ∑ n ∈ range N, |(a (n + L + 1 + j) : ℝ)| / (b : ℝ) ^ (L + 1 + j) := by
        unfold shiftedTail; rw [Summable.tsum_finsetSum hsum_n]
    _ ≤ ∑' j : ℕ, C * (2 : ℝ) ^ γ *
          (((A₀ * lg ^ γ) / (b : ℝ) ^ (L + 1 + j) + (lg ^ γ * (j : ℝ)) / (b : ℝ) ^ (L + 1 + j)) +
            (A₀ * (j : ℝ) ^ γ) / (b : ℝ) ^ (L + 1 + j) +
            ((j : ℝ) ^ (γ + 1)) / (b : ℝ) ^ (L + 1 + j)) :=
        Summable.tsum_le_tsum hterm (summable_sum hsum_n) hS_tot
    _ = C * (2 : ℝ) ^ γ *
          (((∑' j : ℕ, (A₀ * lg ^ γ) / (b : ℝ) ^ (L + 1 + j)) +
            (∑' j : ℕ, (lg ^ γ * (j : ℝ)) / (b : ℝ) ^ (L + 1 + j))) +
            (∑' j : ℕ, (A₀ * (j : ℝ) ^ γ) / (b : ℝ) ^ (L + 1 + j)) +
            (∑' j : ℕ, ((j : ℝ) ^ (γ + 1)) / (b : ℝ) ^ (L + 1 + j))) := by
        rw [tsum_mul_left, ((hS0.add hS1).add hS2).tsum_add hS3, (hS0.add hS1).tsum_add hS2,
          hS0.tsum_add hS1]
    _ = C * (2 : ℝ) ^ γ *
          (((A₀ * lg ^ γ / (b : ℝ) ^ L) * (∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ (j + 1)) +
            (lg ^ γ / (b : ℝ) ^ L) * polyGeomConst b 1) +
            (A₀ / (b : ℝ) ^ L) * polyGeomConst b γ +
            (1 / (b : ℝ) ^ L) * polyGeomConst b (γ + 1)) := by
        unfold polyGeomConst
        rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
        congr 1; congr 1; congr 1
        · congr 1
          · congr 1; ext j; rw [show L + 1 + j = L + (j + 1) by omega, pow_add]; ring
          · congr 1; ext j; rw [show L + 1 + j = L + (j + 1) by omega, pow_add, pow_one]; ring
        · congr 1; ext j; rw [show L + 1 + j = L + (j + 1) by omega, pow_add]; ring
        · congr 1; ext j; rw [show L + 1 + j = L + (j + 1) by omega, pow_add]; ring
    _ ≤ C * (2 : ℝ) ^ γ *
          (((A₀ * lg ^ γ / (b : ℝ) ^ L) * 1 +
            (lg ^ γ / (b : ℝ) ^ L) * polyGeomConst b 1) +
            (A₀ / (b : ℝ) ^ L) * polyGeomConst b γ +
            (1 / (b : ℝ) ^ L) * polyGeomConst b (γ + 1)) := by
        gcongr
    _ = C * (2 : ℝ) ^ γ *
          ((A₀ + polyGeomConst b 1) * lg ^ γ + A₀ * polyGeomConst b γ + polyGeomConst b (γ + 1)) /
          (b : ℝ) ^ L := by
        ring

/-- **Finite logarithmic-mass sparse coefficient transfer inequality (Track B1–B4 & weight-1).** -/
theorem finite_log_mass_transfer {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (γ : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ) * (Real.log ((X + 2 : ℕ) : ℝ)) ^ γ)
    {N : ℕ} (hN : 0 < N) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    1 - radixDiscrepancy b (coeffSeries b a) N ≤
      2 * ε + ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) +
        C * (2 : ℝ) ^ γ *
          ((((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) * (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ +
           ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ + polyGeomConst b (γ + 1)) /
          ((N : ℝ) * ε * (b : ℝ) ^ L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := summable_abs_of_log_mass hb hC γ hmass
  have hdef := discrepancy_deficit_le b (coeffSeries b a) hε.le N
  have hfar := farCount_le_local_add_tail (show 1 ≤ b by omega) hsum N L ε
  have hmarkov := markov_tail_card_le b a N L hε
  have htail := sum_shiftedTail_le_of_log_mass hb hC γ hmass N L
  set Bnum : ℝ := C * (2 : ℝ) ^ γ *
    ((((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) * (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ +
     ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ + polyGeomConst b (γ + 1))
  have hfar_r : (farCount b (coeffSeries b a) ε N : ℝ) ≤
      ((L * supportCount a (N + L) : ℕ) : ℝ) + (Bnum / (b : ℝ) ^ L) / ε := by
    have h1 : (farCount b (coeffSeries b a) ε N : ℝ) ≤
        ((L * supportCount a (N + L) : ℕ) : ℝ) + (tailExceedCount b a N L ε : ℝ) := by
      exact_mod_cast hfar
    have h2 : (∑ n ∈ range N, shiftedTail b a n L) / ε ≤ (Bnum / (b : ℝ) ^ L) / ε :=
      div_le_div_of_nonneg_right htail hε.le
    linarith
  have hdiv := div_le_div_of_nonneg_right hfar_r hNr.le
  rw [add_div] at hdiv
  have hrew : ((Bnum / (b : ℝ) ^ L) / ε) / (N : ℝ) = Bnum / ((N : ℝ) * ε * (b : ℝ) ^ L) := by ring
  rw [hrew] at hdiv
  linarith

/-- **Asymptotic logarithmic-mass sparse coefficient transfer (Track B1–B4 & weight-1 forms).**
If `A(X) ≤ C * X * (log (X + 2))^γ` (e.g., `γ = 1` from the divisor bound `τ(n)`) and
`S(X) * log(log(X + 3)) / X → 0` (in particular whenever `S(X) ≪ X / (log X)^α` for any `α > 0`),
then `D_N(F_b(a); b) → 1` (`F_b(a) ∈ K_b`). -/
theorem log_mass_sparse_tendsto_one {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (γ : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ) * (Real.log ((X + 2 : ℕ) : ℝ)) ^ γ)
    (hsparse : Tendsto (fun N : ℕ =>
      (supportCount a N : ℝ) * Real.log (Real.log ((N + 3 : ℕ) : ℝ)) / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b a) N) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε : ℝ := η / 6 with hε_def
  have hε : 0 < ε := by positivity
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  set Kconst : ℝ := C * (2 : ℝ) ^ γ *
    ((3 + polyGeomConst b 1) * (2 : ℝ) ^ γ + 3 * polyGeomConst b γ + polyGeomConst b (γ + 1))
  have hKc_nonneg : 0 ≤ Kconst := by
    have := polyGeomConst_nonneg b 1
    have := polyGeomConst_nonneg b γ
    have := polyGeomConst_nonneg b (γ + 1)
    positivity
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hb1)) (max 1 (3 * Kconst / (ε * η))))
  have hL₀_ge : 3 * Kconst / (ε * η) ≤ (b : ℝ) ^ L₀ := (le_max_right _ _).trans (hL₀ L₀ le_rfl)
  set α : ℝ := ((γ + 1 : ℕ) : ℝ) / Real.log (b : ℝ)
  have hα_pos : 0 < α := by positivity
  have hlog3_top : Tendsto (fun N : ℕ => Real.log ((N + 3 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3))
  have hll_top : Tendsto (fun N : ℕ => Real.log (Real.log ((N + 3 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog3_top
  have hlog_div : Tendsto (fun N : ℕ => Real.log ((N + 3 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.log ((N + 3 : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3))
      simpa [Function.comp_def, pow_one, one_mul, add_zero] using h
    refine squeeze_zero_norm' ?_ (by simpa using h1.const_mul (2 : ℝ))
    filter_upwards [eventually_ge_atTop 3] with N hN
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have : 0 ≤ Real.log ((N + 3 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 3 by omega))
      positivity)]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have hle : ((N + 3 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (show N + 3 ≤ 2 * N by omega)
    have hlg0 : 0 ≤ Real.log ((N + 3 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 3 by omega))
    push_cast at hle hlg0 ⊢
    nlinarith
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_atTop.mp hll_top) (max 2 (((L₀ + 1 : ℕ) : ℝ) / α)))
  obtain ⟨M₂, hM₂⟩ := Metric.tendsto_atTop.mp hlog_div (1 / (4 * α + 4)) (by positivity)
  obtain ⟨M₃, hM₃⟩ := Metric.tendsto_atTop.mp hsparse (η / (12 * α)) (by positivity)
  refine ⟨max (max (max M₁ M₂) M₃) 16, fun N hN => ?_⟩
  have hNM₁ : M₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hNM₂ : M₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hNM₃ : M₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set llN : ℝ := Real.log (Real.log ((N + 3 : ℕ) : ℝ))
  have hllN_ge2 : (2 : ℝ) ≤ llN := (le_max_left _ _).trans (hM₁ N hNM₁)
  have hlogN3_ge2 : (2 : ℝ) ≤ Real.log ((N + 3 : ℕ) : ℝ) := by
    have h1 : Real.exp 2 ≤ Real.log ((N + 3 : ℕ) : ℝ) := by
      have hpos : 0 < Real.log ((N + 3 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < N + 3 by omega))
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hllN_ge2
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  have hL₀_le : ((L₀ + 1 : ℕ) : ℝ) ≤ α * llN := by
    have h := (le_max_right _ _).trans (hM₁ N hNM₁)
    rw [div_le_iff₀ hα_pos] at h; linarith
  set L : ℕ := Nat.ceil (α * llN) + L₀
  have hL_le_real : (L : ℝ) ≤ 2 * α * llN := by
    have hc : (Nat.ceil (α * llN) : ℝ) < α * llN + 1 := Nat.ceil_lt_add_one (by positivity)
    push_cast [L] at *; linarith
  have hll_le_log : llN ≤ Real.log ((N + 3 : ℕ) : ℝ) :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hL_le_N : (L : ℝ) ≤ (N : ℝ) := by
    have hdiv := hM₂ N hNM₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdiv
    have hmul : Real.log ((N + 3 : ℕ) : ℝ) < (N : ℝ) / (4 * α + 4) := by
      rw [div_lt_iff₀ hNr] at hdiv
      have : (1 / (4 * α + 4)) * (N : ℝ) = (N : ℝ) / (4 * α + 4) := by ring
      linarith
    have h1 : 2 * α * Real.log ((N + 3 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have hlt : 2 * α * Real.log ((N + 3 : ℕ) : ℝ) < 2 * α * ((N : ℝ) / (4 * α + 4)) :=
        mul_lt_mul_of_pos_left hmul (by positivity)
      have h2 : 2 * α * ((N : ℝ) / (4 * α + 4)) ≤ (N : ℝ) := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have : 2 * α * llN ≤ 2 * α * Real.log ((N + 3 : ℕ) : ℝ) := by gcongr
    linarith
  have hL_le_N_nat : L ≤ N := by exact_mod_cast hL_le_N
  have htr := finite_log_mass_transfer hb hC γ hmass hNpos L hε
  have hD_le : radixDiscrepancy b (coeffSeries b a) N ≤ 1 := (radixDiscrepancy_mem b _ N).2
  -- Support term `< η / 3`.
  have hsp := hM₃ (N + L) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
    have h1 : 1 ≤ Real.log ((N + L + 3 : ℕ) : ℝ) :=
      (by linarith : (1 : ℝ) ≤ Real.log ((N + 3 : ℕ) : ℝ)).trans
        (Real.log_le_log (by positivity) (by exact_mod_cast (show N + 3 ≤ N + L + 3 by omega)))
    have h2 : 0 ≤ Real.log (Real.log ((N + L + 3 : ℕ) : ℝ)) := Real.log_nonneg h1
    positivity)] at hsp
  have hll_mono : llN ≤ Real.log (Real.log ((N + L + 3 : ℕ) : ℝ)) :=
    Real.log_le_log (by linarith)
      (Real.log_le_log (by positivity) (by exact_mod_cast (show N + 3 ≤ N + L + 3 by omega)))
  have hNL_le_2N : ((N + L : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (show N + L ≤ 2 * N by omega)
  have hsup_bound : ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) < η / 3 := by
    have hNL_pos : (0 : ℝ) < ((N + L : ℕ) : ℝ) := by positivity
    calc ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ)
        = (L : ℝ) * (supportCount a (N + L) : ℝ) / (N : ℝ) := by rw [Nat.cast_mul]
      _ ≤ (2 * α * llN) * (supportCount a (N + L) : ℝ) / (N : ℝ) := by gcongr
      _ ≤ (2 * α * Real.log (Real.log ((N + L + 3 : ℕ) : ℝ))) * (supportCount a (N + L) : ℝ) / (N : ℝ) := by
          gcongr
      _ ≤ 4 * α * ((supportCount a (N + L) : ℝ) * Real.log (Real.log ((N + L + 3 : ℕ) : ℝ)) /
            ((N + L : ℕ) : ℝ)) := by
          have hnum_nonneg : 0 ≤ (supportCount a (N + L) : ℝ) *
              Real.log (Real.log ((N + L + 3 : ℕ) : ℝ)) := by
            have : 0 ≤ Real.log (Real.log ((N + L + 3 : ℕ) : ℝ)) := by linarith
            positivity
          rw [← mul_div_assoc (4 * α), div_le_div_iff₀ hNr hNL_pos]
          have hstep := mul_le_mul_of_nonneg_left hNL_le_2N
            (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * α) hnum_nonneg)
          linarith
      _ < 4 * α * (η / (12 * α)) := mul_lt_mul_of_pos_left hsp (by positivity)
      _ = η / 3 := by field_simp [hα_pos.ne']; ring
  -- Tail term `≤ η / 3`.
  have hbL_lower : (Real.log ((N + 3 : ℕ) : ℝ)) ^ (γ + 1) * (b : ℝ) ^ L₀ ≤ (b : ℝ) ^ L := by
    have hlg_pos : 0 < Real.log ((N + 3 : ℕ) : ℝ) := by linarith
    have h1 : (Real.log ((N + 3 : ℕ) : ℝ)) ^ (γ + 1) =
        Real.exp (((γ + 1 : ℕ) : ℝ) * llN) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hlg_pos, mul_comm]
    have h2 : (Real.log ((N + 3 : ℕ) : ℝ)) ^ (γ + 1) ≤ (b : ℝ) ^ (Nat.ceil (α * llN)) := by
      rw [h1, ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < b)]
      apply Real.exp_le_exp.mpr
      have hceil : α * llN ≤ (Nat.ceil (α * llN) : ℝ) := Nat.le_ceil _
      have hmul := mul_le_mul_of_nonneg_left hceil hlogb_pos.le
      have hal : Real.log (b : ℝ) * (α * llN) = ((γ + 1 : ℕ) : ℝ) * llN := by
        simp only [α]; field_simp [hlogb_pos.ne']
      linarith
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (Nat.ceil (α * llN)) * (b : ℝ) ^ L₀ := by
      simp only [L, pow_add]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hlogNL_le : Real.log ((N + L + 3 : ℕ) : ℝ) ≤ 2 * Real.log ((N + 3 : ℕ) : ℝ) := by
    have hprod : ((N + L + 3 : ℕ) : ℝ) ≤ ((N + 3 : ℕ) : ℝ) ^ 2 := by
      have : N + L + 3 ≤ (N + 3) ^ 2 := by nlinarith
      exact_mod_cast this
    calc Real.log ((N + L + 3 : ℕ) : ℝ)
        ≤ Real.log (((N + 3 : ℕ) : ℝ) ^ 2) := Real.log_le_log (by positivity) hprod
      _ = 2 * Real.log ((N + 3 : ℕ) : ℝ) := by rw [Real.log_pow]; norm_num
  have htail_bound :
      C * (2 : ℝ) ^ γ *
        ((((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) * (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ +
         ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ + polyGeomConst b (γ + 1)) /
        ((N : ℝ) * ε * (b : ℝ) ^ L) ≤ η / 3 := by
    have hN3 : ((N + L + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      exact_mod_cast (show N + L + 1 ≤ 3 * N by omega)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hlg1 : (1 : ℝ) ≤ Real.log ((N + 3 : ℕ) : ℝ) := by linarith
    have hlg_pow1 : (1 : ℝ) ≤ (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ := one_le_pow₀ hlg1
    have hlg_pow_le : (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ ≤
        (2 : ℝ) ^ γ * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ := by
      calc (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ
          ≤ (2 * Real.log ((N + 3 : ℕ) : ℝ)) ^ γ :=
            pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + L + 3 by omega)))
              hlogNL_le γ
        _ = (2 : ℝ) ^ γ * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ := mul_pow 2 _ γ
    have hnum_le :
        C * (2 : ℝ) ^ γ *
          ((((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) * (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ +
           ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ + polyGeomConst b (γ + 1)) ≤
        Kconst * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) := by
      have hp1 := polyGeomConst_nonneg b 1
      have hpg := polyGeomConst_nonneg b γ
      have hpg1 := polyGeomConst_nonneg b (γ + 1)
      have hA1 : (((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) ≤ (3 + polyGeomConst b 1) * (N : ℝ) := by
        have : polyGeomConst b 1 ≤ polyGeomConst b 1 * (N : ℝ) := le_mul_of_one_le_right hp1 hN1
        linarith
      have hA2 : (((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) *
            (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ ≤
          ((3 + polyGeomConst b 1) * (2 : ℝ) ^ γ) * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) := by
        have h := mul_le_mul hA1 hlg_pow_le (by positivity) (by positivity)
        linarith
      have hB1 : ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ ≤
          (3 * polyGeomConst b γ) * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) := by
        have h1 : ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ ≤ 3 * (N : ℝ) * polyGeomConst b γ :=
          mul_le_mul_of_nonneg_right hN3 hpg
        have h2 : 3 * (N : ℝ) * polyGeomConst b γ ≤
            3 * (N : ℝ) * polyGeomConst b γ * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ :=
          le_mul_of_one_le_right (by positivity) hlg_pow1
        linarith
      have hC1 : polyGeomConst b (γ + 1) ≤
          polyGeomConst b (γ + 1) * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) := by
        have h1 : (1 : ℝ) ≤ (N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ := by
          exact one_le_mul_of_one_le_of_one_le hN1 hlg_pow1
        exact le_mul_of_one_le_right hpg1 h1
      have hsum_abc := add_le_add (add_le_add hA2 hB1) hC1
      have hmul_abc := mul_le_mul_of_nonneg_left hsum_abc (show (0 : ℝ) ≤ C * (2 : ℝ) ^ γ by positivity)
      have heq_rhs :
          C * (2 : ℝ) ^ γ *
            (((3 + polyGeomConst b 1) * (2 : ℝ) ^ γ) * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) +
             (3 * polyGeomConst b γ) * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) +
             polyGeomConst b (γ + 1) * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ)) =
          Kconst * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) := by
        simp only [Kconst]; ring
      linarith
    have hden_ge :
        ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) * (ε * (b : ℝ) ^ L₀) ≤
          (N : ℝ) * ε * (b : ℝ) ^ L := by
      have hpow_le : (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ ≤ (Real.log ((N + 3 : ℕ) : ℝ)) ^ (γ + 1) := by
        rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hlg1
      have h1 : (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ * (b : ℝ) ^ L₀ ≤ (b : ℝ) ^ L :=
        (mul_le_mul_of_nonneg_right hpow_le (by positivity)).trans hbL_lower
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (N : ℝ) * ε by positivity)
      linarith
    calc C * (2 : ℝ) ^ γ *
          ((((N + L + 1 : ℕ) : ℝ) + polyGeomConst b 1) * (Real.log ((N + L + 3 : ℕ) : ℝ)) ^ γ +
           ((N + L + 1 : ℕ) : ℝ) * polyGeomConst b γ + polyGeomConst b (γ + 1)) /
          ((N : ℝ) * ε * (b : ℝ) ^ L)
        ≤ (Kconst * ((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ)) /
            (((N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ) * (ε * (b : ℝ) ^ L₀)) :=
          div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
      _ = Kconst / (ε * (b : ℝ) ^ L₀) := by
          have hne : (N : ℝ) * (Real.log ((N + 3 : ℕ) : ℝ)) ^ γ ≠ 0 := by positivity
          field_simp [hne]
      _ ≤ η / 3 := by
          rw [div_le_iff₀ (by positivity)]
          have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < ε * η)).mp hL₀_ge
          linarith
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

/-- Universal discrepancy preservation (`F_b(a) ∈ K_b`) under logarithmic mass
`A(X) ≤ C * X * (log (X + 2))^γ` and `S(X) * log(log(X + 3)) / X → 0`. -/
theorem log_mass_sparse_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ}
    (hC : 0 ≤ C) (γ : ℕ)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ) * (Real.log ((X + 2 : ℕ) : ℝ)) ^ γ)
    (hsparse : Tendsto (fun N : ℕ =>
      (supportCount a N : ℝ) * Real.log (Real.log ((N + 3 : ℕ) : ℝ)) / (N : ℝ)) atTop (𝓝 0))
    (x : ℝ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (x + coeffSeries b a) N - radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  have h1 := log_mass_sparse_tendsto_one hb hC γ hmass hsparse
  have hgap : Tendsto (fun N : ℕ => 1 - radixDiscrepancy b (coeffSeries b a) N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  rw [Metric.tendsto_atTop] at hgap ⊢
  intro η hη
  obtain ⟨M, hM⟩ := hgap η hη
  refine ⟨max 1 M, fun N hN => ?_⟩
  have hNpos : 0 < N := by have := (le_max_left 1 M).trans hN; omega
  have hNM : M ≤ N := (le_max_right 1 M).trans hN
  have htr := SharpTranslation.sharp_translation b x (coeffSeries b a) hNpos
  have hMN := hM N hNM
  rw [Real.dist_eq, sub_zero] at hMN ⊢
  have hnonneg : 0 ≤ 1 - radixDiscrepancy b (coeffSeries b a) N := by
    linarith [(radixDiscrepancy_mem b (coeffSeries b a) N).2]
  rw [abs_of_nonneg hnonneg] at hMN
  exact lt_of_le_of_lt htr hMN

/-! ### Part 2: Exact `q`-digamma reflection algebraic identity (Track B4) -/

/-- The `q`-digamma function `ψ_q(z) = -log(1 - q) + log(q) * ∑' k, q^(k + z) / (1 - q^(k + z))`
for `0 < q < 1` and `z > 0`. -/
noncomputable def qDigamma (q z : ℝ) : ℝ :=
  -Real.log (1 - q) + Real.log q * ∑' k : ℕ, q ^ ((k : ℝ) + z) / (1 - q ^ ((k : ℝ) + z))

/-- Residue-class Lambert series `A_{r, M}(b) = ∑' k, 1 / (b^(k * M + r) - 1)` for `1 ≤ r < M`. -/
noncomputable def residueLambert (b M r : ℕ) : ℝ :=
  ∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k * M + r) - 1)

/-- Termwise identity relating `q^(k + r/M) / (1 - q^(k + r/M))` at `q = b^(-M)` to
`1 / (b^(k*M + r) - 1)`. -/
theorem qDigamma_term_eq_lambert {b M r : ℕ} (hb : 2 ≤ b) (hM : 1 ≤ M) (hr : 1 ≤ r) (k : ℕ) :
    let q : ℝ := ((b : ℝ) ^ M)⁻¹
    q ^ ((k : ℝ) + (r : ℝ) / (M : ℝ)) / (1 - q ^ ((k : ℝ) + (r : ℝ) / (M : ℝ))) =
      1 / ((b : ℝ) ^ (k * M + r) - 1) := by
  intro q
  have hb_pos : (0 : ℝ) < b := by positivity
  have hM_ne : (M : ℝ) ≠ 0 := by positivity
  have hq_pow : q ^ ((k : ℝ) + (r : ℝ) / (M : ℝ)) = ((b : ℝ) ^ (k * M + r))⁻¹ := by
    have h1 : q = (b : ℝ) ^ (-(M : ℝ)) := by
      simp only [q, Real.rpow_neg hb_pos.le, Real.rpow_natCast]
    rw [h1, ← Real.rpow_mul hb_pos.le]
    have hexp : -(M : ℝ) * ((k : ℝ) + (r : ℝ) / (M : ℝ)) = -((k * M + r : ℕ) : ℝ) := by
      push_cast; field_simp [hM_ne]
    rw [hexp, Real.rpow_neg hb_pos.le, Real.rpow_natCast]
  rw [hq_pow]
  have hbp_gt1 : (1 : ℝ) < (b : ℝ) ^ (k * M + r) := by
    have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
    exact one_lt_pow₀ hb1 (by omega)
  have hbp_ne : (b : ℝ) ^ (k * M + r) ≠ 0 := by positivity
  have hsub_ne : (b : ℝ) ^ (k * M + r) - 1 ≠ 0 := by linarith
  have hinv_sub_ne : 1 - ((b : ℝ) ^ (k * M + r))⁻¹ ≠ 0 := by
    have : ((b : ℝ) ^ (k * M + r))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hbp_gt1
    linarith
  field_simp [hbp_ne, hsub_ne, hinv_sub_ne]

/-- **Exact `q`-digamma reflection identity at `q = b^(-M)` (Track B4).**
For every integer radix `b ≥ 2`, modulus `M ≥ 2`, and `1 ≤ r < M`,
`(qDigamma (b^(-M)) (r / M) - qDigamma (b^(-M)) ((M - r) / M)) / Real.log (b^(-M))`
`= residueLambert b M r - residueLambert b M (M - r)`. -/
theorem qDigamma_reflection_eq_residueLambert {b M r : ℕ} (hb : 2 ≤ b) (hM : 2 ≤ M)
    (hr1 : 1 ≤ r) (hrM : r < M) :
    let q : ℝ := ((b : ℝ) ^ M)⁻¹
    (qDigamma q ((r : ℝ) / (M : ℝ)) - qDigamma q (((M - r : ℕ) : ℝ) / (M : ℝ))) / Real.log q =
      residueLambert b M r - residueLambert b M (M - r) := by
  intro q
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hq_pos : 0 < q := by positivity
  have hq_lt1 : q < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hb1 (by omega))
  have hlogq_ne : Real.log q ≠ 0 := (Real.log_neg hq_pos hq_lt1).ne
  unfold qDigamma residueLambert
  have h1 : (∑' k : ℕ, q ^ ((k : ℝ) + (r : ℝ) / (M : ℝ)) /
      (1 - q ^ ((k : ℝ) + (r : ℝ) / (M : ℝ)))) =
      ∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k * M + r) - 1) :=
    tsum_congr (fun k => qDigamma_term_eq_lambert hb (by omega) hr1 k)
  have h2 : (∑' k : ℕ, q ^ ((k : ℝ) + ((M - r : ℕ) : ℝ) / (M : ℝ)) /
      (1 - q ^ ((k : ℝ) + ((M - r : ℕ) : ℝ) / (M : ℝ)))) =
      ∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k * M + (M - r)) - 1) :=
    tsum_congr (fun k => qDigamma_term_eq_lambert hb (by omega) (by omega) k)
  rw [h1, h2]
  field_simp [hlogq_ne]
  ring

end NormalityChecker.GeneralMassTransfer
