module

public import NormalityChecker.Phase18Synthetic
public import NormalityChecker.DiscrepancyGeometry

/-! # General coefficient-to-discrepancy transfer and two-sided concentration bounds

Kernel-checked foundations for Phase 20 (Tracks A1, B1, B2, B3, B4):

1. **Finite sparse-support and coefficient-mass transfer (`Track B1`).**
   For an integer radix `b ≥ 2` and an integer-valued (possibly signed) coefficient sequence
   `a : ℕ → ℤ` with `F = ∑' m, a(m) / b^m`:
   - `near_of_no_local_support`: if `a(n+1) = ⋯ = a(n+L) = 0` and the absolute tail beyond
     `L` is at most `ε`, then `b^n F` is within `ε` of an integer.
   - `nearSupport_card_le`: at most `L · S(N+L)` shifts `n < N` have a nonzero coefficient in
     `(n, n+L]`.
   - `finite_sparse_mass_transfer`: when `∑_{1 ≤ m ≤ X} |a(m)| ≤ C · X` for all `X`, every
     `N ≥ 1`, `L ≥ 1`, `ε > 0` satisfies
       `1 - D_N(F; b) ≤ 2ε + L · S(N+L) / N + C · (N + L + 2) / (N · ε · b^L)`,
     and by `SharpTranslation.sharp_translation` the same bound controls
     `|D_N(x + F; b) - D_N(x; b)|` uniformly in `x`.
   - `linear_mass_sparse_tendsto_one` & `linear_mass_sparse_preserves_discrepancy`:
     if `A(X) = O(X)` and `S(X) = o(X)`, then `D_N(F; b) → 1` and `F` universally preserves
     asymptotic extreme discrepancy under addition (`F ∈ K_b`).

2. **General-radix displaced-source factorization (`Track B2`).**
   For every integer radix `b ≥ 2` (prime or composite), `radixVal b a` is the largest `v`
   with `b^v ∣ a` (for `a ≠ 0`), `a = b^(radixVal b a) * radixUnit b a`, `b ∤ radixUnit b a`,
   and `displaced_term_eq` reindexes `b^n (a / b^m)` by the displaced arrival `m - v`.

3. **Two-sided circular concentration lower bound (`Tracks A1, B3, B4`).**
   `one_sub_discrepancy_ge_of_bulk_and_far`: for every radix `b`, cutoff `N > 0`, and
   `0 ≤ ε₀ < δ`, if `B` is the set of shifts `n < N` within `ε₀` of an integer and `S` is the
   set of shifts `n < N` farther than `δ` from every integer, then
     `min (δ - ε₀) (min (|S|/N) (|B|/N)) ≤ 1 - D_N(x; b)`.
   Unlike one-sided binary interval bounds, this handles both signs of displacement around
   `0 mod 1` in every radix.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.CoefficientTransfer

open Phase18Synthetic SharpTranslation

/-! ### Part 1: Finite sparse-support and coefficient-mass transfer -/

/-- The base-`b` generating series `∑' m, a(m) / b^m` of an integer sequence `a`. -/
noncomputable def coeffSeries (b : ℕ) (a : ℕ → ℤ) : ℝ :=
  ∑' m : ℕ, (a m : ℝ) / (b : ℝ) ^ m

/-- Support count `S(M) = #{1 ≤ m ≤ M : a(m) ≠ 0}`. -/
noncomputable def supportCount (a : ℕ → ℤ) (M : ℕ) : ℕ :=
  by classical exact ((Icc 1 M).filter (fun m => a m ≠ 0)).card

/-- Aggregate absolute coefficient mass `A(M) = ∑_{1 ≤ m ≤ M} |a(m)|`. -/
def absMass (a : ℕ → ℤ) (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, |(a m : ℝ)|

/-- Shifted absolute tail beyond window `L` at shift `n`: `∑_{k ≥ 0} |a(n + L + 1 + k)| / b^(L + 1 + k)`. -/
noncomputable def shiftedTail (b : ℕ) (a : ℕ → ℤ) (n L : ℕ) : ℝ :=
  ∑' k : ℕ, |(a (n + L + 1 + k) : ℝ)| / (b : ℝ) ^ (L + 1 + k)

theorem absMass_nonneg (a : ℕ → ℤ) (M : ℕ) : 0 ≤ absMass a M :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem absMass_mono (a : ℕ → ℤ) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    absMass a M₁ ≤ absMass a M₂ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) (fun _ _ _ => abs_nonneg _)

theorem supportCount_mono (a : ℕ → ℤ) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    supportCount a M₁ ≤ supportCount a M₂ := by
  classical
  unfold supportCount
  exact card_le_card (filter_subset_filter _ (Icc_subset_Icc_right h))

/-- Linear-mass summability: if `∑_{1 ≤ m ≤ X} |a(m)| ≤ C · X` for all `X` and `b ≥ 2`, then
`∑' m, |a(m)| / b^m` converges. -/
theorem summable_abs_of_linear_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ}
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ)) :
    Summable (fun m : ℕ => |(a m : ℝ)| / (b : ℝ) ^ m) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have hgeo : Summable (fun m : ℕ => (m : ℝ) * ((b : ℝ)⁻¹) ^ m) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).summable
  have hbound : Summable (fun m : ℕ => (C * (m : ℝ) + |(a 0 : ℝ)|) * ((b : ℝ)⁻¹) ^ m) := by
    have h1 : Summable (fun m : ℕ => C * ((m : ℝ) * ((b : ℝ)⁻¹) ^ m)) := hgeo.mul_left C
    have h2 : Summable (fun m : ℕ => |(a 0 : ℝ)| * ((b : ℝ)⁻¹) ^ m) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left |(a 0 : ℝ)|
    convert h1.add h2 using 1
    ext m; ring
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hbound
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hmem : m ∈ Icc 1 m := mem_Icc.mpr ⟨hm, le_rfl⟩
    have hle1 : |(a m : ℝ)| ≤ absMass a m := by
      unfold absMass
      exact Finset.single_le_sum (f := fun k => |(a k : ℝ)|) (fun _ _ => abs_nonneg _) hmem
    have hle2 : |(a m : ℝ)| ≤ C * (m : ℝ) + |(a 0 : ℝ)| := by
      linarith [hmass m, abs_nonneg (a 0 : ℝ)]
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_right hle2 (by positivity)

/-- If no nonzero coefficient occurs in `(n, n+L]` and the tail beyond `L` is at most `ε`,
then `b^n F_b(a)` is within `ε` of an integer. -/
theorem near_of_no_local_support {b : ℕ} (hb : 1 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable (fun m : ℕ => |(a m : ℝ)| / (b : ℝ) ^ m))
    {n L : ℕ} {ε : ℝ}
    (hclear : ∀ j ∈ Icc 1 L, a (n + j) = 0)
    (htail : shiftedTail b a n L ≤ ε) :
    Near ((b : ℝ) ^ n * coeffSeries b a) ε := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hsum_raw : Summable (fun m : ℕ => (a m : ℝ) / (b : ℝ) ^ m) := by
    refine Summable.of_norm ?_
    convert hsum using 1
    ext m
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 m)]
  have hsplit := hsum_raw.sum_add_tsum_nat_add (n + L + 1)
  have hzero : ∑ m ∈ range (n + L + 1), (a m : ℝ) / (b : ℝ) ^ m =
      ∑ m ∈ range (n + 1), (a m : ℝ) / (b : ℝ) ^ m := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun m hm1 hm2 => ?_)
    rw [mem_range] at hm1 hm2
    have hge : 1 ≤ m - n := by omega
    have hle : m - n ≤ L := by omega
    have hEq : n + (m - n) = m := by omega
    have ha0 := hclear (m - n) (mem_Icc.mpr ⟨hge, hle⟩)
    rw [hEq] at ha0
    simp [ha0]
  refine ⟨∑ m ∈ range (n + 1), a m * (b : ℤ) ^ (n - m), ?_⟩
  have hint : (b : ℝ) ^ n * ∑ m ∈ range (n + 1), (a m : ℝ) / (b : ℝ) ^ m =
      ((∑ m ∈ range (n + 1), a m * (b : ℤ) ^ (n - m) : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hmn : m ≤ n := by rw [mem_range] at hm; omega
    have hpow : (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [hpow]
    field_simp [hb0.ne']
  have hdiff : (b : ℝ) ^ n * coeffSeries b a -
      ((∑ m ∈ range (n + 1), a m * (b : ℤ) ^ (n - m) : ℤ) : ℝ) =
      ∑' k : ℕ, (a (n + L + 1 + k) : ℝ) / (b : ℝ) ^ (L + 1 + k) := by
    unfold coeffSeries
    rw [← hsplit, mul_add, hzero, hint, add_sub_cancel_left, ← tsum_mul_left]
    congr 1
    ext k
    have hexp : k + (n + L + 1) = n + (L + 1 + k) := by omega
    rw [show k + (n + L + 1) = n + L + 1 + k by omega]
    have hpow : (b : ℝ) ^ (n + L + 1 + k) = (b : ℝ) ^ n * (b : ℝ) ^ (L + 1 + k) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    field_simp [hb0.ne']
  rw [hdiff]
  have htail_sum : Summable (fun k : ℕ => |(a (n + L + 1 + k) : ℝ)| / (b : ℝ) ^ (L + 1 + k)) := by
    have hshift := (summable_nat_add_iff (n + L + 1)).mpr hsum
    have hmul := hshift.mul_left ((b : ℝ) ^ n)
    convert hmul using 1
    ext k
    have hpow : (b : ℝ) ^ (k + (n + L + 1)) = (b : ℝ) ^ n * (b : ℝ) ^ (L + 1 + k) := by
      rw [← pow_add]; congr 1; omega
    rw [show k + (n + L + 1) = n + L + 1 + k by omega] at *
    rw [hpow]
    field_simp [hb0.ne']
  have hnorm_sum : Summable (fun k : ℕ => ‖(a (n + L + 1 + k) : ℝ) / (b : ℝ) ^ (L + 1 + k)‖) := by
    convert htail_sum using 1
    ext k
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 _)]
  calc |∑' k : ℕ, (a (n + L + 1 + k) : ℝ) / (b : ℝ) ^ (L + 1 + k)|
      = ‖∑' k : ℕ, (a (n + L + 1 + k) : ℝ) / (b : ℝ) ^ (L + 1 + k)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖(a (n + L + 1 + k) : ℝ) / (b : ℝ) ^ (L + 1 + k)‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ = shiftedTail b a n L := by
        unfold shiftedTail
        congr 1; ext k
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb0 _)]
    _ ≤ ε := htail

/-- Predicate that `a` has a nonzero coefficient in `(n, n + L]`. -/
def hasLocalSupport (a : ℕ → ℤ) (L n : ℕ) : Prop :=
  ∃ j ∈ Icc 1 L, a (n + j) ≠ 0

open Classical in
/-- Number of shifts `n < N` with a nonzero coefficient in `(n, n + L]`. -/
noncomputable def nearSupportCount (a : ℕ → ℤ) (N L : ℕ) : ℕ :=
  ((range N).filter (hasLocalSupport a L)).card

open Classical in
/-- Number of shifts `n < N` whose tail beyond `L` exceeds `ε`. -/
noncomputable def tailExceedCount (b : ℕ) (a : ℕ → ℤ) (N L : ℕ) (ε : ℝ) : ℕ :=
  ((range N).filter (fun n => ε < shiftedTail b a n L)).card

open Classical in
/-- Counting shifts with a nonzero coefficient within the next `L` positions:
`#{n < N : ∃ 1 ≤ j ≤ L, a(n + j) ≠ 0} ≤ L · S(N + L)`. -/
theorem nearSupport_card_le (a : ℕ → ℤ) (N L : ℕ) :
    nearSupportCount a N L ≤ L * supportCount a (N + L) := by
  unfold nearSupportCount
  let T := (Icc 1 (N + L)).filter (fun m => a m ≠ 0)
  have hcard : (T ×ˢ Icc 1 L).card = L * supportCount a (N + L) := by
    rw [card_product, Nat.card_Icc, mul_comm]
    have : L + 1 - 1 = L := by omega
    rw [this]
    unfold supportCount
    congr 1
  rw [← hcard]
  let pick : ℕ → ℕ := fun n =>
    if h : hasLocalSupport a L n then h.choose else 1
  refine card_le_card_of_injOn (fun n => (n + pick n, pick n)) ?_ ?_
  · intro n hn
    have hmem := mem_filter.mp (mem_coe.mp hn)
    have hnN : n < N := mem_range.mp hmem.1
    have hex : hasLocalSupport a L n := hmem.2
    have hspec := hex.choose_spec
    have hp : pick n = hex.choose := by simp only [pick, dite_eq_left, hex]
    rw [mem_coe, mem_product, mem_filter, mem_Icc, mem_Icc]
    dsimp only
    rw [hp]
    have h1 := mem_Icc.mp hspec.1
    exact ⟨⟨⟨by omega, by omega⟩, hspec.2⟩, h1⟩
  · intro n₁ _ n₂ _ heq
    have h1 : n₁ + pick n₁ = n₂ + pick n₂ := congrArg Prod.fst heq
    have h2 : pick n₁ = pick n₂ := congrArg Prod.snd heq
    omega

open Classical in
/-- Splitting `farCount` into local-support hits and large-tail shifts. -/
theorem farCount_le_local_add_tail {b : ℕ} (hb : 1 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable (fun m : ℕ => |(a m : ℝ)| / (b : ℝ) ^ m))
    (N L : ℕ) (ε : ℝ) :
    farCount b (coeffSeries b a) ε N ≤
      L * supportCount a (N + L) + tailExceedCount b a N L ε := by
  let A := (range N).filter (hasLocalSupport a L)
  let B := (range N).filter (fun n => ε < shiftedTail b a n L)
  have hsub : (range N).filter (fun n => ¬ Near ((b : ℝ) ^ n * coeffSeries b a) ε) ⊆ A ∪ B := by
    intro n hn
    obtain ⟨hnN, hfar⟩ := mem_filter.mp hn
    rw [mem_union]
    by_cases hloc : hasLocalSupport a L n
    · exact Or.inl (mem_filter.mpr ⟨hnN, hloc⟩)
    · right
      refine mem_filter.mpr ⟨hnN, ?_⟩
      by_contra hle
      push Not at hle
      have hclear : ∀ j ∈ Icc 1 L, a (n + j) = 0 := by
        intro j hj
        by_contra hne
        exact hloc ⟨j, hj, hne⟩
      exact hfar (near_of_no_local_support hb hsum hclear hle)
  have hA : A.card ≤ L * supportCount a (N + L) := nearSupport_card_le a N L
  have hB : B.card = tailExceedCount b a N L ε := rfl
  unfold farCount
  calc ((range N).filter (fun n => ¬ Near ((b : ℝ) ^ n * coeffSeries b a) ε)).card
      ≤ (A ∪ B).card := card_le_card hsub
    _ ≤ A.card + B.card := card_union_le A B
    _ ≤ L * supportCount a (N + L) + tailExceedCount b a N L ε := by omega

/-- Markov bound on the number of shifts with `shiftedTail > ε`. -/
theorem markov_tail_card_le (b : ℕ) (a : ℕ → ℤ) (N L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (tailExceedCount b a N L ε : ℝ) ≤
      (∑ n ∈ range N, shiftedTail b a n L) / ε := by
  classical
  unfold tailExceedCount
  have hnonneg : ∀ n, 0 ≤ shiftedTail b a n L := fun n =>
    tsum_nonneg (fun k => by positivity)
  rw [le_div_iff₀ hε]
  calc (((range N).filter (fun n => ε < shiftedTail b a n L)).card : ℝ) * ε
      = ∑ _n ∈ (range N).filter (fun n => ε < shiftedTail b a n L), ε := by simp
    _ ≤ ∑ n ∈ (range N).filter (fun n => ε < shiftedTail b a n L), shiftedTail b a n L :=
        Finset.sum_le_sum (fun n hn => (mem_filter.mp hn).2.le)
    _ ≤ ∑ n ∈ range N, shiftedTail b a n L :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => hnonneg n)

/-- Elementary geometric weighted-sum bound for `b ≥ 2`:
`∑' k, ((M + k : ℕ) : ℝ) / b^(L + 1 + k) ≤ (M + 1 : ℝ) / b^L`. -/
private lemma weighted_geom_bound {b : ℕ} (hb : 2 ≤ b) (M L : ℕ) :
    ∑' k : ℕ, ((M + k : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + k) ≤ ((M + 1 : ℕ) : ℝ) / (b : ℝ) ^ L := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set r : ℝ := (b : ℝ)⁻¹ with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr_half : r ≤ 1 / 2 := by
    rw [hr_def, one_div]
    exact inv_anti₀ (by norm_num) hb2
  have hr1 : r < 1 := by linarith
  have hs0 : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hs1_has := hasSum_coe_mul_geometric_of_norm_lt_one (r := r)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have hs1 : Summable (fun k : ℕ => (k : ℝ) * r ^ k) := hs1_has.summable
  have hval0 : ∑' k : ℕ, r ^ k = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hval1 : ∑' k : ℕ, (k : ℝ) * r ^ k = r * ((1 - r) ^ 2)⁻¹ := by
    rw [hs1_has.tsum_eq, div_eq_mul_inv]
  have hrew : (fun k : ℕ => ((M + k : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + k)) =
      fun k : ℕ => r ^ (L + 1) * ((M : ℝ) * r ^ k + (k : ℝ) * r ^ k) := by
    ext k
    push_cast
    rw [div_eq_mul_inv, ← inv_pow, ← hr_def, pow_add]
    ring
  rw [hrew, tsum_mul_left, Summable.tsum_add (hs0.mul_left _) hs1, tsum_mul_left, hval0, hval1]
  have hinv1 : (1 - r)⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hinv2 : r * ((1 - r) ^ 2)⁻¹ ≤ 2 := by
    have hsq : (1 / 4 : ℝ) ≤ (1 - r) ^ 2 := by nlinarith
    have hsq_inv : ((1 - r) ^ 2)⁻¹ ≤ 4 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
    nlinarith
  have hr_pow : r ^ (L + 1) = r ^ L * r := pow_succ r L
  have hbL : ((b : ℝ) ^ L)⁻¹ = r ^ L := by rw [hr_def, inv_pow]
  rw [hr_pow, div_eq_mul_inv, hbL]
  have hsum_le : (M : ℝ) * (1 - r)⁻¹ + r * ((1 - r) ^ 2)⁻¹ ≤ 2 * ((M + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have h2r : 2 * r ≤ 1 := by linarith
  calc r ^ L * r * ((M : ℝ) * (1 - r)⁻¹ + r * ((1 - r) ^ 2)⁻¹)
      ≤ r ^ L * r * (2 * ((M + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = ((M + 1 : ℕ) : ℝ) * r ^ L * (2 * r) := by ring
    _ ≤ ((M + 1 : ℕ) : ℝ) * r ^ L * 1 :=
        mul_le_mul_of_nonneg_left h2r (by positivity)
    _ = ((M + 1 : ℕ) : ℝ) * r ^ L := mul_one _

/-- Total shifted tail budget under linear coefficient mass `A(X) ≤ C · X`:
`∑_{n < N} shiftedTail b a n L ≤ C · (N + L + 2) / b^L`. -/
theorem sum_shiftedTail_le_of_linear_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ)) (N L : ℕ) :
    ∑ n ∈ range N, shiftedTail b a n L ≤ C * ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hsum_all := summable_abs_of_linear_mass hb hmass
  have hsum_n : ∀ n ∈ range N,
      Summable (fun k : ℕ => |(a (n + L + 1 + k) : ℝ)| / (b : ℝ) ^ (L + 1 + k)) := by
    intro n _
    have hshift := (summable_nat_add_iff (n + L + 1)).mpr hsum_all
    have hmul := hshift.mul_left ((b : ℝ) ^ n)
    convert hmul using 1
    ext k
    have hpow : (b : ℝ) ^ (k + (n + L + 1)) = (b : ℝ) ^ n * (b : ℝ) ^ (L + 1 + k) := by
      rw [← pow_add]; congr 1; omega
    rw [show k + (n + L + 1) = n + L + 1 + k by omega] at *
    rw [hpow]
    field_simp [hb0.ne']
  unfold shiftedTail
  rw [← Summable.tsum_finsetSum hsum_n]
  have hterm : ∀ k : ℕ,
      ∑ n ∈ range N, |(a (n + L + 1 + k) : ℝ)| / (b : ℝ) ^ (L + 1 + k) ≤
        C * ((N + L + 1 + k : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + k) := by
    intro k
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsub : ∑ n ∈ range N, |(a (n + L + 1 + k) : ℝ)| ≤ absMass a (N + L + 1 + k) := by
      unfold absMass
      have hre : ∑ n ∈ range N, |(a (n + L + 1 + k) : ℝ)| =
          ∑ m ∈ (range N).image (fun n => n + L + 1 + k), |(a m : ℝ)| := by
        rw [Finset.sum_image]
        intro x _ y _ hxy; dsimp only at hxy; omega
      rw [hre]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
      intro m hm
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
      rw [mem_range] at hn
      rw [mem_Icc]
      omega
    exact hsub.trans (hmass (N + L + 1 + k))
  have hsum_rhs : Summable (fun k : ℕ => C * ((N + L + 1 + k : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + k)) := by
    have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
    have hr0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
    have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
    have hs0 := (summable_geometric_of_lt_one hr0 hr1).mul_left (C * ((N + L + 1 : ℕ) : ℝ) * (b : ℝ)⁻¹ ^ (L + 1))
    have hs1 := (hasSum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).summable.mul_left
      (C * (b : ℝ)⁻¹ ^ (L + 1))
    convert hs0.add hs1 using 1
    ext k
    push_cast
    rw [div_eq_mul_inv, ← inv_pow, pow_add]
    ring
  calc ∑' k : ℕ, ∑ n ∈ range N, |(a (n + L + 1 + k) : ℝ)| / (b : ℝ) ^ (L + 1 + k)
      ≤ ∑' k : ℕ, C * ((N + L + 1 + k : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + k) :=
        Summable.tsum_le_tsum hterm (summable_sum (fun n hn => hsum_n n hn)) hsum_rhs
    _ = C * ∑' k : ℕ, ((N + L + 1 + k : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + k) := by
        rw [← tsum_mul_left]; congr 1; ext k; ring
    _ ≤ C * (((N + L + 1 + 1 : ℕ) : ℝ) / (b : ℝ) ^ L) :=
        mul_le_mul_of_nonneg_left (weighted_geom_bound hb (N + L + 1) L) hC
    _ = C * ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
        rw [mul_div_assoc]

/-- **Finite sparse-support / linear-mass discrepancy-transfer inequality (Track B1).**
For every radix `b ≥ 2`, integer sequence `a` with `A(X) ≤ C · X`, cutoff `N ≥ 1`,
window `L`, and threshold `ε > 0`,
`1 - D_N(F_b(a); b) ≤ 2ε + L · S(N+L) / N + C · (N + L + 2) / (N · ε · b^L)`. -/
theorem finite_sparse_mass_transfer {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ))
    {N : ℕ} (hN : 0 < N) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    1 - radixDiscrepancy b (coeffSeries b a) N ≤
      2 * ε + ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) +
        C * ((N + L + 2 : ℕ) : ℝ) / ((N : ℝ) * ε * (b : ℝ) ^ L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := summable_abs_of_linear_mass hb hmass
  have hdef := discrepancy_deficit_le b (coeffSeries b a) hε.le N
  have hfar := farCount_le_local_add_tail (show 1 ≤ b by omega) hsum N L ε
  have hmarkov := markov_tail_card_le b a N L hε
  have htail := sum_shiftedTail_le_of_linear_mass hb hC hmass N L
  have hfar_r : (farCount b (coeffSeries b a) ε N : ℝ) ≤
      ((L * supportCount a (N + L) : ℕ) : ℝ) +
        (C * ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L) / ε := by
    have h1 : (farCount b (coeffSeries b a) ε N : ℝ) ≤
        ((L * supportCount a (N + L) : ℕ) : ℝ) + (tailExceedCount b a N L ε : ℝ) := by
      exact_mod_cast hfar
    have h2 : (∑ n ∈ range N, shiftedTail b a n L) / ε ≤
        (C * ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L) / ε :=
      div_le_div_of_nonneg_right htail hε.le
    linarith
  have hdiv := div_le_div_of_nonneg_right hfar_r hNr.le
  rw [add_div] at hdiv
  have hrew : ((C * ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L) / ε) / (N : ℝ) =
      C * ((N + L + 2 : ℕ) : ℝ) / ((N : ℝ) * ε * (b : ℝ) ^ L) := by ring
  rw [hrew] at hdiv
  linarith

/-- Uniform translation version of `finite_sparse_mass_transfer`: bounds
`|D_N(x + F_b(a); b) - D_N(x; b)|` for every `x : ℝ`. -/
theorem finite_sparse_mass_translation {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ))
    (x : ℝ) {N : ℕ} (hN : 0 < N) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    |radixDiscrepancy b (x + coeffSeries b a) N - radixDiscrepancy b x N| ≤
      2 * ε + ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) +
        C * ((N + L + 2 : ℕ) : ℝ) / ((N : ℝ) * ε * (b : ℝ) ^ L) :=
  (SharpTranslation.sharp_translation b x (coeffSeries b a) hN).trans
    (finite_sparse_mass_transfer hb hC hmass hN L hε)

/-- **Asymptotic coefficient-to-discrepancy transfer (Track B1).**
If `A(X) = O(X)` and `S(X) = o(X)`, then `D_N(F_b(a); b) → 1`. -/
theorem linear_mass_sparse_tendsto_one {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ))
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b a) N) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε : ℝ := η / 6 with hε_def
  have hε : 0 < ε := by positivity
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  -- Choose fixed `L` large enough that `2 * C / (ε * b^L) ≤ η / 3`.
  have hpow_top : Tendsto (fun L : ℕ => (b : ℝ) ^ L) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hb1
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp ((tendsto_atTop.mp hpow_top) (max 1 (6 * C / (ε * η))))
  have hL_ge : 6 * C / (ε * η) ≤ (b : ℝ) ^ L := (le_max_right _ _).trans (hL L le_rfl)
  -- Choose `M₀` so that for `N ≥ M₀`, `N ≥ L + 2` and `(L + 1) * S(N + L) / (N + L) < η / 6`.
  have hL1_pos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp hsparse (η / (6 * ((L : ℝ) + 1))) (by positivity)
  refine ⟨max (L + 2) M₁, fun N hN => ?_⟩
  have hNL : L + 2 ≤ N := (le_max_left _ _).trans hN
  have hNM₁ : M₁ ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have htr := finite_sparse_mass_transfer hb hC hmass hNpos L hε
  have hD_le : radixDiscrepancy b (coeffSeries b a) N ≤ 1 :=
    (radixDiscrepancy_mem b _ N).2
  -- Bound the support term: `L * S(N + L) / N ≤ 2 * L * S(N + L) / (N + L) < η / 3`.
  have hsp := hM₁ (N + L) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsp
  have hN_add_le : ((N + L : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : N + L ≤ 2 * N := by omega
    exact_mod_cast this
  have hsup_bound : ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) < η / 3 := by
    have hNL_pos : (0 : ℝ) < ((N + L : ℕ) : ℝ) := by positivity
    have h1 : ((L * supportCount a (N + L) : ℕ) : ℝ) / (N : ℝ) ≤
        2 * (L : ℝ) * ((supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ)) := by
      rw [Nat.cast_mul, mul_div_assoc]
      have hratio : ((supportCount a (N + L) : ℝ) / (N : ℝ)) ≤
          2 * ((supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ)) := by
        rw [div_le_iff₀ hNr, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hNL_pos]
        have := mul_le_mul_of_nonneg_left hN_add_le (Nat.cast_nonneg (α := ℝ) (supportCount a (N + L)))
        linarith
      calc (L : ℝ) * ((supportCount a (N + L) : ℝ) / (N : ℝ))
          ≤ (L : ℝ) * (2 * ((supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg L)
        _ = 2 * (L : ℝ) * ((supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ)) := by ring
    have h2 : 2 * (L : ℝ) * ((supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ)) <
        2 * ((L : ℝ) + 1) * (η / (6 * ((L : ℝ) + 1))) := by
      have h0 : 0 ≤ (supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ) := by positivity
      calc 2 * (L : ℝ) * ((supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ))
          ≤ 2 * ((L : ℝ) + 1) * ((supportCount a (N + L) : ℝ) / ((N + L : ℕ) : ℝ)) := by
            gcongr; linarith
        _ < 2 * ((L : ℝ) + 1) * (η / (6 * ((L : ℝ) + 1))) :=
            mul_lt_mul_of_pos_left hsp (by positivity)
    have h3 : 2 * ((L : ℝ) + 1) * (η / (6 * ((L : ℝ) + 1))) = η / 3 := by
      field_simp [hL1_pos.ne']; ring
    linarith
  -- Bound the tail term: `C * (N + L + 2) / (N * ε * b^L) ≤ 2 * C / (ε * b^L) ≤ η / 3`.
  have htail_bound : C * ((N + L + 2 : ℕ) : ℝ) / ((N : ℝ) * ε * (b : ℝ) ^ L) ≤ η / 3 := by
    have hN2 : ((N + L + 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have : N + L + 2 ≤ 2 * N := by omega
      exact_mod_cast this
    have h1 : C * ((N + L + 2 : ℕ) : ℝ) / ((N : ℝ) * ε * (b : ℝ) ^ L) ≤
        2 * C / (ε * (b : ℝ) ^ L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc C * ((N + L + 2 : ℕ) : ℝ) * (ε * (b : ℝ) ^ L)
          ≤ C * (2 * (N : ℝ)) * (ε * (b : ℝ) ^ L) := by
            gcongr
        _ = 2 * C * ((N : ℝ) * ε * (b : ℝ) ^ L) := by ring
    have h2 : 2 * C / (ε * (b : ℝ) ^ L) ≤ η / 3 := by
      rw [div_le_iff₀ (by positivity)]
      have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < ε * η)).mp hL_ge
      linarith
    linarith
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

/-- **Universal discrepancy preservation (`F_b(a) ∈ K_b`).**
Under `A(X) = O(X)` and `S(X) = o(X)`, `F_b(a)` universally preserves asymptotic extreme
discrepancy under addition: `D_N(x + F_b(a); b) - D_N(x; b) → 0` for every `x : ℝ`. -/
theorem linear_mass_sparse_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ}
    (hC : 0 ≤ C) (hmass : ∀ X : ℕ, absMass a X ≤ C * (X : ℝ))
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) / (N : ℝ)) atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (x + coeffSeries b a) N - radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  have h1 := linear_mass_sparse_tendsto_one hb hC hmass hsparse
  have hgap : Tendsto (fun N : ℕ => 1 - radixDiscrepancy b (coeffSeries b a) N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  rw [Metric.tendsto_atTop] at hgap ⊢
  intro η hη
  obtain ⟨M, hM⟩ := hgap η hη
  refine ⟨max 1 M, fun N hN => ?_⟩
  have hNpos : 0 < N := by have := (le_max_left 1 M).trans hN; omega
  have hNM : M ≤ N := (le_max_right 1 M).trans hN
  have htr := SharpTranslation.sharp_translation b x (coeffSeries b a) hNpos
  have hg := hM N hNM
  have hnn : 0 ≤ 1 - radixDiscrepancy b (coeffSeries b a) N := by
    linarith [(radixDiscrepancy_mem b (coeffSeries b a) N).2]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hg
  rw [Real.dist_eq, sub_zero]
  linarith

/-! ### Part 2: General-radix displaced-source factorization (Track B2) -/

/-- Auxiliary recursion for `radixVal`: counts how many times `b` divides `n` (with fuel `k`). -/
def radixValAux (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => if b ∣ n then 1 + radixValAux b k (n / b) else 0

/-- Largest `v` such that `b^v ∣ a` (for `b ≥ 2` and `a ≠ 0`), and `0` for `a = 0` or `b < 2`.
Works for arbitrary composite radices as well as prime radices. -/
def radixVal (b : ℕ) (a : ℤ) : ℕ :=
  if 2 ≤ b ∧ a ≠ 0 then radixValAux b a.natAbs a.natAbs else 0

/-- Normalized coefficient `U = a / b^(radixVal b a)`. -/
def radixUnit (b : ℕ) (a : ℤ) : ℤ :=
  a / (b : ℤ) ^ radixVal b a

private lemma radixValAux_dvd_and_not_dvd {b : ℕ} (hb : 2 ≤ b) :
    ∀ k n : ℕ, 0 < n → n ≤ k →
      b ^ radixValAux b k n ∣ n ∧ ¬ b ∣ (n / b ^ radixValAux b k n) := by
  intro k
  induction k with
  | zero =>
    intro n hn hle; omega
  | succ k ih =>
    intro n hn hle
    unfold radixValAux
    split_ifs with hdvd
    · obtain ⟨q, rfl⟩ := hdvd
      have hq_pos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with rfl | hq
        · simp at hn
        · exact hq
      have hq_lt : q < b * q := by nlinarith
      have hdiv : b * q / b = q := Nat.mul_div_cancel_left q (by omega)
      rw [hdiv]
      obtain ⟨h1, h2⟩ := ih q hq_pos (by omega)
      constructor
      · rw [add_comm 1, pow_succ']
        exact Nat.mul_dvd_mul_left b h1
      · rw [add_comm 1, pow_succ', Nat.mul_div_mul_left _ _ (by omega)]
        exact h2
    · simpa using hdvd

/-- `b^(radixVal b a)` divides `a` for every integer `a` and radix `b`. -/
theorem radixVal_pow_dvd (b : ℕ) (a : ℤ) : (b : ℤ) ^ radixVal b a ∣ a := by
  unfold radixVal
  split_ifs with h
  · obtain ⟨hb, ha⟩ := h
    have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
    have hd := (radixValAux_dvd_and_not_dvd hb a.natAbs a.natAbs hpos le_rfl).1
    exact Int.natCast_dvd.mpr hd
  · simp

/-- Exact displaced-source factorization: `a = b^(radixVal b a) * radixUnit b a`. -/
theorem radixVal_mul_radixUnit (b : ℕ) (a : ℤ) :
    a = (b : ℤ) ^ radixVal b a * radixUnit b a := by
  unfold radixUnit
  exact (Int.mul_ediv_cancel' (radixVal_pow_dvd b a)).symm

/-- Maximality of `radixVal`: for `b ≥ 2` and `a ≠ 0`, `b` does not divide `radixUnit b a`. -/
theorem not_dvd_radixUnit {b : ℕ} (hb : 2 ≤ b) {a : ℤ} (ha : a ≠ 0) :
    ¬ (b : ℤ) ∣ radixUnit b a := by
  have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hspec := radixValAux_dvd_and_not_dvd hb a.natAbs a.natAbs hpos le_rfl
  have hval : radixVal b a = radixValAux b a.natAbs a.natAbs := by
    simp [radixVal, hb, ha]
  intro hdvd
  have hfac := radixVal_mul_radixUnit b a
  obtain ⟨q, hq⟩ := hdvd
  rw [hq] at hfac
  have habs : a.natAbs = b ^ radixVal b a * (b * q.natAbs) := by
    have := congrArg Int.natAbs hfac
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have hdiv : a.natAbs / b ^ radixVal b a = b * q.natAbs := by
    rw [habs, Nat.mul_div_cancel_left _ (pow_pos (by omega) _)]
  rw [hval] at hdiv
  apply hspec.2
  rw [hdiv]
  exact dvd_mul_right b _

/-- **Displaced-source shift identity (Track B2).**
For `a = b^v U` (`v = radixVal b a`, `U = radixUnit b a`), the shifted term `b^n (a / b^m)`
is an integer whenever `m ≤ n + v`, and equals `U / b^(m - v - n)` whenever `n + v < m`. -/
theorem displaced_term_eq {b : ℕ} (hb : 1 ≤ b) (a : ℤ) (m n : ℕ) :
    (m ≤ n + radixVal b a →
      ∃ j : ℤ, (b : ℝ) ^ n * ((a : ℝ) / (b : ℝ) ^ m) = j) ∧
    (n + radixVal b a < m →
      (b : ℝ) ^ n * ((a : ℝ) / (b : ℝ) ^ m) =
        (radixUnit b a : ℝ) / (b : ℝ) ^ (m - radixVal b a - n)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hfac : (a : ℝ) = (b : ℝ) ^ radixVal b a * (radixUnit b a : ℝ) := by
    exact_mod_cast radixVal_mul_radixUnit b a
  constructor
  · intro hle
    refine ⟨radixUnit b a * (b : ℤ) ^ (n + radixVal b a - m), ?_⟩
    rw [hfac]
    push_cast
    have hpow : (b : ℝ) ^ n * (b : ℝ) ^ radixVal b a =
        (b : ℝ) ^ (n + radixVal b a - m) * (b : ℝ) ^ m := by
      rw [← pow_add, ← pow_add, Nat.sub_add_cancel hle]
    have : (b : ℝ) ^ n * ((b : ℝ) ^ radixVal b a * (radixUnit b a : ℝ) / (b : ℝ) ^ m) =
        ((b : ℝ) ^ n * (b : ℝ) ^ radixVal b a) * (radixUnit b a : ℝ) / (b : ℝ) ^ m := by ring
    rw [this, hpow]
    field_simp [hb0.ne']
  · intro hlt
    rw [hfac]
    have hpow : (b : ℝ) ^ m = (b : ℝ) ^ n * (b : ℝ) ^ radixVal b a *
        (b : ℝ) ^ (m - radixVal b a - n) := by
      rw [← pow_add, ← pow_add]
      congr 1; omega
    rw [hpow]
    field_simp [hb0.ne']

/-! ### Part 3: Two-sided circular concentration lower bound (Tracks A1, B3, B4) -/

private lemma near_fract_of_near {y ε : ℝ} (h : Near y ε) :
    Near (Int.fract y) ε := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j - ⌊y⌋, ?_⟩
  rw [Int.fract]
  push_cast
  have : y - ↑⌊y⌋ - (↑j - ↑⌊y⌋) = y - ↑j := by ring
  rw [this]
  exact hj

private lemma near_of_near_fract {y ε : ℝ} (h : Near (Int.fract y) ε) :
    Near y ε := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j + ⌊y⌋, ?_⟩
  rw [Int.fract] at hj
  push_cast
  have : y - (↑j + ↑⌊y⌋) = y - ↑⌊y⌋ - ↑j := by ring
  rw [this]
  exact hj

/-- Two points in the same circle arc of length `l` differ modulo `ℤ` by less than `l`. -/
private lemma exists_int_dist_lt_of_mem_arc {u v α l : ℝ}
    (hu : Int.fract (u - α) < l) (hv : Int.fract (v - α) < l) :
    ∃ k : ℤ, |v - u - k| < l := by
  refine ⟨⌊v - α⌋ - ⌊u - α⌋, ?_⟩
  have h1 : 0 ≤ Int.fract (u - α) := Int.fract_nonneg _
  have h2 : 0 ≤ Int.fract (v - α) := Int.fract_nonneg _
  have hEq : v - u - ((⌊v - α⌋ - ⌊u - α⌋ : ℤ) : ℝ) = Int.fract (v - α) - Int.fract (u - α) := by
    rw [Int.fract, Int.fract]; push_cast; ring
  rw [hEq, abs_lt]
  constructor <;> linarith

/-- **Two-sided circular concentration lower bound (Tracks A1, B3, B4).**
In any radix `b`, for any `x : ℝ`, `N > 0`, and `ε₀, δ : ℝ`:
let `B` be the bulk of shifts `n < N` with `Near (b^n x) ε₀` and `S` the far shifts `n < N`
with `¬ Near (b^n x) δ`. Then
`min (δ - ε₀) (min (|S|/N) (|B|/N)) ≤ 1 - D_N(x; b)`. -/
theorem one_sub_discrepancy_ge_of_bulk_and_far (b : ℕ) (x : ℝ) {N : ℕ} (hN : 0 < N)
    (ε₀ δ : ℝ) :
    min (δ - ε₀)
      (min ((by classical exact (((range N).filter (fun n => ¬ Near ((b : ℝ) ^ n * x) δ)).card : ℝ) / N))
           ((by classical exact (((range N).filter (fun n => Near ((b : ℝ) ^ n * x) ε₀)).card : ℝ) / N)))
      ≤ 1 - radixDiscrepancy b x N := by
  classical
  set B := (range N).filter (fun n => Near ((b : ℝ) ^ n * x) ε₀)
  set S := (range N).filter (fun n => ¬ Near ((b : ℝ) ^ n * x) δ)
  set Δ := min (δ - ε₀) (min ((S.card : ℝ) / N) ((B.card : ℝ) / N))
  have hΔ1 : Δ ≤ δ - ε₀ := min_le_left _ _
  have hΔS : Δ ≤ (S.card : ℝ) / N := (min_le_right _ _).trans (min_le_left _ _)
  have hΔB : Δ ≤ (B.card : ℝ) / N := (min_le_right _ _).trans (min_le_right _ _)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  suffices hD : radixDiscrepancy b x N ≤ 1 - Δ by linarith
  rw [radixDiscrepancy_eq_sampleDisc]
  refine sampleDisc_le_of (fun a c ha hac hc => ?_)
  obtain ⟨α, l, hl0, hl1, heq⟩ :=
    interval_eq_arc_excess (u := shift b x) (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) hN ha hac hc
  rw [← heq]
  set A := (range N).filter (fun n => Int.fract (shift b x n - α) < l)
  change (A.card : ℝ) / N - l ≤ 1 - Δ
  by_cases hlen : δ - ε₀ ≤ l
  · have hA_le : (A.card : ℝ) / N ≤ 1 := by
      rw [div_le_one hNr]
      exact_mod_cast ((card_filter_le _ _).trans_eq (card_range N))
    linarith
  · push Not at hlen
    by_cases hmeet : ∃ n ∈ B, n ∈ A
    · -- `A` meets the bulk `B`, so every point in `A` is within `ε₀ + l < δ` of an integer,
      -- hence `A` is disjoint from `S`.
      obtain ⟨n₀, hn₀B, hn₀A⟩ := hmeet
      have hdisj : Disjoint A S := by
        rw [Finset.disjoint_left]
        intro m hmA hmS
        have hnear₀ : Near (shift b x n₀) ε₀ := near_fract_of_near (mem_filter.mp hn₀B).2
        obtain ⟨k, hk⟩ := exists_int_dist_lt_of_mem_arc (mem_filter.mp hn₀A).2 (mem_filter.mp hmA).2
        obtain ⟨j, hj⟩ := hnear₀
        have hnear_m : Near (shift b x m) δ := by
          refine ⟨j + k, ?_⟩
          have htri : |shift b x m - ((j + k : ℤ) : ℝ)| ≤
              |shift b x m - shift b x n₀ - (k : ℝ)| + |shift b x n₀ - (j : ℝ)| := by
            have : shift b x m - ((j + k : ℤ) : ℝ) =
                (shift b x m - shift b x n₀ - (k : ℝ)) + (shift b x n₀ - (j : ℝ)) := by
              push_cast; ring
            rw [this]
            exact abs_add_le _ _
          linarith
        exact (mem_filter.mp hmS).2 (near_of_near_fract hnear_m)
      have hcard : A.card + S.card ≤ N := by
        rw [← card_union_of_disjoint hdisj, ← card_range N]
        exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      have hcard_r : (A.card : ℝ) / N + (S.card : ℝ) / N ≤ 1 := by
        rw [← add_div, div_le_one hNr]
        exact_mod_cast hcard
      linarith
    · -- `A` misses the entire bulk `B`, so `A` and `B` are disjoint.
      push Not at hmeet
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro m hmA hmB
        exact hmeet m hmB hmA
      have hcard : A.card + B.card ≤ N := by
        rw [← card_union_of_disjoint hdisj, ← card_range N]
        exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      have hcard_r : (A.card : ℝ) / N + (B.card : ℝ) / N ≤ 1 := by
        rw [← add_div, div_le_one hNr]
        exact_mod_cast hcard
      linarith

end NormalityChecker.CoefficientTransfer
