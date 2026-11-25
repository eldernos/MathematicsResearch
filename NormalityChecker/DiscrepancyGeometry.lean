module

public import NormalityChecker.SharpTranslation
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # The discrepancy pseudometric on the circle

For a radix `b` and a cutoff `N`, put `d_N(x,y) = 1 - D_N(x - y)`, where `D_N` is the extreme
interval discrepancy `radixDiscrepancy` of the first `N` radix shifts.  This file proves, by the
exact translation inequality `|D_N(x+z) - D_N(x)| ≤ 1 - D_N(z)` of `SharpTranslation`:

* `d_N` is nonnegative, vanishes on the diagonal, is symmetric, translation invariant, invariant
  under integer translation, and satisfies the triangle inequality for `N > 0`
  (`discDist_self`, `discDist_comm`, `discDist_translate`, `discDist_triangle`);
* `d_N(x,y)` is the largest change `|D_N(w + x - y) - D_N(w)|` over origins `w`
  (`discDist_isGreatest`), and `D_N` is 1-Lipschitz for `d_N` (`radixDiscrepancy_lipschitz`);
* for `N ≥ 2`, `d_N(x,y) = 0` exactly when `(b-1)(x-y)` is an integer
  (`discDist_eq_zero_iff`); otherwise `d_N(x,y)` is bounded below by an explicit positive
  constant (`discDist_pos_bound`);
* multiplication by an integer `m` is `|m|`-Lipschitz (`discDist_intMul_le`);
* the asymptotic quantity `asymDist = limsup_N d_N` is again symmetric, translation invariant and
  satisfies the triangle inequality, vanishes when `(b-1)(x-y)` is an integer, equals one when
  `D_N(x-y) → 0`, and integer multipliers are `|m|`-Lipschitz for it.  (It is only a pseudometric:
  by a density argument, which is not formalized here, its kernel also contains the `x - y`
  whose shift orbit is eventually constant.)
-/

@[expose] public section

open Finset Filter

namespace NormalityChecker.DiscrepancyGeometry

open SharpTranslation

/-- The discrepancy distance `d_N(x,y) = 1 - D_N(x - y)`. -/
noncomputable def discDist (b N : ℕ) (x y : ℝ) : ℝ := 1 - radixDiscrepancy b (x - y) N

theorem discDist_nonneg (b N : ℕ) (x y : ℝ) : 0 ≤ discDist b N x y := by
  have := sampleDisc_le_one (shift b (x - y)) N
  unfold discDist
  rw [radixDiscrepancy_eq_sampleDisc]
  linarith

theorem discDist_le_one (b N : ℕ) (x y : ℝ) : discDist b N x y ≤ 1 := by
  have := sampleDisc_nonneg (shift b (x - y)) N
  unfold discDist
  rw [radixDiscrepancy_eq_sampleDisc]
  linarith

theorem discDist_self (b N : ℕ) (x : ℝ) : discDist b N x x = 0 := by
  simp [discDist, radixDiscrepancy_zero]

/-- Translation invariance. -/
theorem discDist_translate (b N : ℕ) (x y t : ℝ) :
    discDist b N (x + t) (y + t) = discDist b N x y := by
  simp [discDist]

/-- One side of symmetry, for the translation increment `z ↦ 1 - D_N(z)`. -/
private lemma phi_le_neg (b : ℕ) {N : ℕ} (hN : 0 < N) (z : ℝ) :
    1 - radixDiscrepancy b z N ≤ 1 - radixDiscrepancy b (-z) N := by
  have h := sharp_translation b z (-z) hN
  rw [add_neg_cancel, radixDiscrepancy_zero] at h
  have hz := sampleDisc_le_one (shift b z) N
  rw [← radixDiscrepancy_eq_sampleDisc] at hz
  rwa [abs_of_nonneg (by linarith)] at h

theorem discDist_comm (b : ℕ) {N : ℕ} (hN : 0 < N) (x y : ℝ) :
    discDist b N x y = discDist b N y x := by
  have h1 := phi_le_neg b hN (x - y)
  have h2 := phi_le_neg b hN (y - x)
  rw [neg_sub] at h1
  rw [neg_sub] at h2
  unfold discDist
  linarith

/-- **Triangle inequality.** -/
theorem discDist_triangle (b : ℕ) {N : ℕ} (hN : 0 < N) (x y z : ℝ) :
    discDist b N x z ≤ discDist b N x y + discDist b N y z := by
  have h1 := (abs_le.mp (sharp_translation b (y - z) (x - y) hN)).1
  have e : y - z + (x - y) = x - z := by ring
  rw [e] at h1
  unfold discDist
  linarith

/-- `d_N(x,y)` is the largest change of `D_N` under translation by `x - y`, over all origins. -/
theorem discDist_isGreatest (b : ℕ) {N : ℕ} (hN : 0 < N) (x y : ℝ) :
    IsGreatest (Set.range fun w : ℝ =>
      |radixDiscrepancy b (w + (x - y)) N - radixDiscrepancy b w N|) (discDist b N x y) :=
  sharp_translation_isGreatest b (x - y) hN

/-- `D_N` is 1-Lipschitz for the discrepancy distance. -/
theorem radixDiscrepancy_lipschitz (b : ℕ) {N : ℕ} (hN : 0 < N) (x y : ℝ) :
    |radixDiscrepancy b x N - radixDiscrepancy b y N| ≤ discDist b N x y := by
  have h := sharp_translation b y (x - y) hN
  rwa [add_sub_cancel] at h

theorem shift_mem (b : ℕ) (x : ℝ) (n : ℕ) : 0 ≤ shift b x n ∧ shift b x n < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The radix shifts are `ℤ`-periodic in the starting point. -/
theorem shift_add_intCast (b : ℕ) (x : ℝ) (k : ℤ) (n : ℕ) :
    shift b (x + k) n = shift b x n := by
  unfold shift
  have : (b : ℝ) ^ n * (x + k) = (b : ℝ) ^ n * x + ((b ^ n * k : ℤ) : ℝ) := by push_cast; ring
  rw [this, Int.fract_add_intCast]

theorem radixDiscrepancy_add_intCast (b : ℕ) (x : ℝ) (k : ℤ) (N : ℕ) :
    radixDiscrepancy b (x + k) N = radixDiscrepancy b x N := by
  rw [radixDiscrepancy_eq_sampleDisc, radixDiscrepancy_eq_sampleDisc]
  congr 1
  funext n
  exact shift_add_intCast b x k n

theorem discDist_add_intCast (b N : ℕ) (x y : ℝ) (k : ℤ) :
    discDist b N (x + k) y = discDist b N x y := by
  unfold discDist
  rw [add_sub_right_comm, radixDiscrepancy_add_intCast]

/-! ### The zero set -/

private lemma freq_ge_of_mem {u : ℕ → ℝ} {N : ℕ} {a c : ℝ} {i : ℕ} (hi : i < N)
    (h : a ≤ u i ∧ u i < c) :
    (1 : ℝ) / N ≤ frequency u a c N := by
  unfold frequency
  have : 0 < ((range N).filter (fun i => a ≤ u i ∧ u i < c)).card :=
    Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, h⟩⟩
  have h1 : (1 : ℝ) ≤ (((range N).filter (fun i => a ≤ u i ∧ u i < c)).card : ℝ) := by
    exact_mod_cast this
  exact div_le_div_of_nonneg_right h1 (by positivity)

private lemma freq_le_of_miss {u : ℕ → ℝ} {N : ℕ} {a c : ℝ} {i : ℕ} (hi : i < N)
    (h : ¬(a ≤ u i ∧ u i < c)) :
    frequency u a c N ≤ 1 - 1 / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  unfold frequency
  have hs : (range N).filter (fun i => a ≤ u i ∧ u i < c) ⊂ range N := by
    refine (Finset.filter_subset _ _).ssubset_of_ne ?_
    intro heq
    have : i ∈ (range N).filter (fun i => a ≤ u i ∧ u i < c) := by
      rw [heq]; exact mem_range.mpr hi
    exact h (mem_filter.mp this).2
  have h1 : (((range N).filter (fun i => a ≤ u i ∧ u i < c)).card : ℝ) + 1 ≤ N := by
    have := Finset.card_lt_card hs
    rw [card_range] at this
    exact_mod_cast this
  rw [div_le_iff₀ hN, sub_mul, one_mul, div_mul_cancel₀ _ hN.ne']
  linarith

/-- Two distinct points `p < q` of `[0,1)` cannot both miss an interval `[a,c)` of length more
than `1 - min (q - p) (1 - (q - p))`. -/
private lemma miss_length {p q a c : ℝ} (hp : 0 ≤ p) (hq : q < 1) (hpq : p < q) (hc : c ≤ 1)
    (ha : 0 ≤ a) (hmp : ¬(a ≤ p ∧ p < c)) (hmq : ¬(a ≤ q ∧ q < c)) :
    c - a ≤ 1 - min (q - p) (1 - (q - p)) := by
  have h1 := min_le_left (q - p) (1 - (q - p))
  have h2 := min_le_right (q - p) (1 - (q - p))
  by_cases hac : a < c
  swap
  · linarith
  rw [not_and_or, not_le, not_lt] at hmp hmq
  rcases hmp with hp1 | hp1 <;> rcases hmq with hq1 | hq1
  · linarith
  · linarith
  · linarith
  · linarith

/-- If the first two samples are distinct points of `[0,1)`, the discrepancy stays a definite
distance below one. -/
theorem sampleDisc_le_one_sub {u : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N) (hu : ∀ n, 0 ≤ u n ∧ u n < 1)
    (h01 : u 0 ≠ u 1) :
    sampleDisc u N ≤ 1 - min (min |u 0 - u 1| (1 - |u 0 - u 1|)) (1 / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set g := |u 0 - u 1| with hg
  set h := min g (1 - g) with hh
  set δ := min h (1 / N) with hδ
  have hδ1 : δ ≤ h := min_le_left _ _
  have hδ2 : δ ≤ 1 / N := min_le_right _ _
  have hh1 : h ≤ g := min_le_left _ _
  have hh2 : h ≤ 1 - g := min_le_right _ _
  refine sampleDisc_le_of fun a c ha hac hc => ?_
  have f0 := frequency_bounds u a c N
  rw [abs_le]
  constructor
  · -- `ℓ - f ≤ 1 - δ`
    by_cases hmiss : (a ≤ u 0 ∧ u 0 < c) ∨ (a ≤ u 1 ∧ u 1 < c)
    · have : (1 : ℝ) / N ≤ frequency u a c N := by
        rcases hmiss with hm | hm
        · exact freq_ge_of_mem (by omega) hm
        · exact freq_ge_of_mem (by omega) hm
      linarith
    · rw [not_or] at hmiss
      have hlen : c - a ≤ 1 - h := by
        rcases lt_or_gt_of_ne h01 with hlt | hlt
        · have := miss_length (hu 0).1 (hu 1).2 hlt hc ha hmiss.1 hmiss.2
          rw [hh, hg, abs_of_neg (by linarith)]
          simpa [neg_sub] using this
        · have := miss_length (hu 1).1 (hu 0).2 hlt hc ha hmiss.2 hmiss.1
          rw [hh, hg, abs_of_pos (by linarith)]
          simpa using this
      linarith
  · -- `f - ℓ ≤ 1 - δ`
    by_cases hall : (a ≤ u 0 ∧ u 0 < c) ∧ (a ≤ u 1 ∧ u 1 < c)
    · have : g < c - a := by
        rw [hg, abs_lt]
        constructor <;> linarith [hall.1.1, hall.1.2, hall.2.1, hall.2.2]
      linarith [f0.2]
    · have hmiss : ∃ i, i < N ∧ ¬(a ≤ u i ∧ u i < c) := by
        rw [not_and_or] at hall
        rcases hall with h0 | h1
        · exact ⟨0, by omega, h0⟩
        · exact ⟨1, by omega, h1⟩
      obtain ⟨i, hi, hmi⟩ := hmiss
      have := freq_le_of_miss hi hmi
      linarith

/-- A constant sample of `[0,1)` has discrepancy one. -/
theorem sampleDisc_eq_one_of_const {u : ℕ → ℝ} {N : ℕ} (hN : 0 < N) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p < 1) (hu : ∀ n < N, u n = p) : sampleDisc u N = 1 := by
  refine le_antisymm (sampleDisc_le_one u N) ?_
  refine le_of_forall_sub_le fun ε hε => ?_
  set c := min (p + ε) 1 with hc
  have hpc : p < c := lt_min (by linarith) hp1
  have hfreq : frequency u p c N = 1 := by
    unfold frequency
    have : (range N).filter (fun i => p ≤ u i ∧ u i < c) = range N := by
      apply Finset.filter_true_of_mem
      intro i hi
      rw [hu i (mem_range.mp hi)]
      exact ⟨le_rfl, hpc⟩
    rw [this, card_range, div_self (by exact_mod_cast hN.ne')]
  have h := interval_le_sampleDisc u N hp0 hpc (min_le_right _ _)
  rw [hfreq] at h
  have hcl : c - p ≤ ε := by
    have := min_le_left (p + ε) 1
    linarith
  have h2 : 1 - ε ≤ |1 - (c - p)| := by
    rw [abs_of_nonneg (by linarith [min_le_right (p + ε) 1])]
    linarith
  linarith

/-- **Zero set at finite cutoff.** For `N ≥ 2` the discrepancy distance vanishes exactly on the
pairs for which `(b - 1)(x - y)` is an integer. -/
theorem discDist_eq_zero_iff (b : ℕ) {N : ℕ} (hN : 2 ≤ N) (x y : ℝ) :
    discDist b N x y = 0 ↔ ∃ k : ℤ, ((b : ℝ) - 1) * (x - y) = k := by
  have key : ∀ z : ℝ, radixDiscrepancy b z N = 1 ↔ ∃ k : ℤ, ((b : ℝ) - 1) * z = k := by
    intro z
    constructor
    · intro hD
      by_contra hno
      push Not at hno
      have hne : shift b z 0 ≠ shift b z 1 := by
        intro heq
        unfold shift at heq
        rw [pow_zero, one_mul, pow_one] at heq
        obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp heq
        exact hno (-m) (by push_cast; linarith)
      have hlt := sampleDisc_le_one_sub (u := shift _ _) hN (fun n => shift_mem _ _ n) hne
      rw [radixDiscrepancy_eq_sampleDisc] at hD
      rw [hD] at hlt
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hpos : 0 < min (min |shift b z 0 - shift b z 1| (1 - |shift b z 0 - shift b z 1|))
          (1 / (N : ℝ)) := by
        refine lt_min (lt_min (abs_pos.mpr (sub_ne_zero.mpr hne)) ?_) (by positivity)
        have h0 : 0 ≤ shift b z 0 := Int.fract_nonneg _
        have h1 : 0 ≤ shift b z 1 := Int.fract_nonneg _
        have h0' : shift b z 0 < 1 := Int.fract_lt_one _
        have h1' : shift b z 1 < 1 := Int.fract_lt_one _
        rw [sub_pos, abs_lt]
        constructor <;> linarith
      linarith
    · rintro ⟨k, hk⟩
      have hper : ∀ n : ℕ, ∃ m : ℤ, (b : ℝ) ^ n * z - z = m := by
        intro n
        induction n with
        | zero => exact ⟨0, by simp⟩
        | succ n ih =>
          obtain ⟨m, hm⟩ := ih
          refine ⟨b * m + k, ?_⟩
          push_cast
          rw [← hm, ← hk]; ring
      rw [radixDiscrepancy_eq_sampleDisc]
      refine sampleDisc_eq_one_of_const (p := shift b z 0) (by omega) (Int.fract_nonneg _)
        (Int.fract_lt_one _) fun n _ => ?_
      unfold shift
      rw [pow_zero, one_mul]
      exact Int.fract_eq_fract.mpr (by obtain ⟨m, hm⟩ := hper n; exact ⟨m, hm⟩)
  unfold discDist
  rw [sub_eq_zero, eq_comm]
  exact key _

/-- Quantitative form of the zero set: if the first two shifts of `x - y` differ, then
`d_N(x,y) ≥ min (min g (1 - g)) (1/N)`, where `g` is the gap between them. -/
theorem discDist_pos_bound (b : ℕ) {N : ℕ} (hN : 2 ≤ N) (x y : ℝ)
    (hne : shift b (x - y) 0 ≠ shift b (x - y) 1) :
    min (min |shift b (x - y) 0 - shift b (x - y) 1|
        (1 - |shift b (x - y) 0 - shift b (x - y) 1|)) (1 / N) ≤ discDist b N x y := by
  have := sampleDisc_le_one_sub (u := shift _ _) hN (fun n => shift_mem _ _ n) hne
  unfold discDist
  rw [radixDiscrepancy_eq_sampleDisc]
  linarith

/-! ### Integer multipliers -/

/-- Any translation-invariant function satisfying the triangle inequality and `d x x = 0`
is `m`-Lipschitz for multiplication by a natural number `m`. -/
theorem natMul_le_of_triangle {d : ℝ → ℝ → ℝ} (hself : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (htrans : ∀ x y t, d (x + t) (y + t) = d x y)
    (m : ℕ) (x y : ℝ) : d (m * x) (m * y) ≤ m * d x y := by
  induction m with
  | zero => simp [hself]
  | succ m ih =>
    have h := htri (((m : ℝ) + 1) * x) (m * x + y) (((m : ℝ) + 1) * y)
    have h1 : d (((m : ℝ) + 1) * x) (m * x + y) = d x y := by
      have := htrans x y (m * x)
      rw [add_comm x] at this
      rw [← this]; congr 1 <;> ring
    have h2 : d (m * x + y) (((m : ℝ) + 1) * y) = d (m * x) (m * y) := by
      have := htrans (m * x) (m * y) y
      rw [← this]; congr 1; ring
    push_cast
    linarith

/-- Integer version of `natMul_le_of_triangle`, for symmetric `d` with `d (-x) (-y) = d x y`
reflected through symmetry. -/
theorem intMul_le_of_triangle {d : ℝ → ℝ → ℝ} (hself : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (htrans : ∀ x y t, d (x + t) (y + t) = d x y)
    (hcomm : ∀ x y, d x y = d y x) (m : ℤ) (x y : ℝ) :
    d (m * x) (m * y) ≤ |(m : ℝ)| * d x y := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · simpa using natMul_le_of_triangle hself htri htrans n x y
  · have key : d (((-(n : ℤ) : ℤ) : ℝ) * x) (((-(n : ℤ) : ℤ) : ℝ) * y) = d (n * y) (n * x) := by
      have e1 : (((-(n : ℤ) : ℤ) : ℝ) * x) = -(n * x) := by push_cast; ring
      have e2 : (((-(n : ℤ) : ℤ) : ℝ) * y) = -(n * y) := by push_cast; ring
      rw [e1, e2, ← htrans _ _ (n * x + n * y)]
      congr 1 <;> ring
    rw [key, hcomm]
    simpa using natMul_le_of_triangle hself htri htrans n x y

/-- Multiplication by a natural number `m` is `m`-Lipschitz. -/
theorem discDist_natMul_le (b : ℕ) {N : ℕ} (hN : 0 < N) (m : ℕ) (x y : ℝ) :
    discDist b N (m * x) (m * y) ≤ m * discDist b N x y :=
  natMul_le_of_triangle (discDist_self b N) (discDist_triangle b hN) (discDist_translate b N)
    m x y

/-- **Integer multipliers are Lipschitz:** `d_N(m x, m y) ≤ |m| d_N(x,y)`. -/
theorem discDist_intMul_le (b : ℕ) {N : ℕ} (hN : 0 < N) (m : ℤ) (x y : ℝ) :
    discDist b N (m * x) (m * y) ≤ |(m : ℝ)| * discDist b N x y :=
  intMul_le_of_triangle (discDist_self b N) (discDist_triangle b hN) (discDist_translate b N)
    (discDist_comm b hN) m x y

/-! ### The asymptotic distance -/

/-- The asymptotic discrepancy distance `limsup_N d_N(x,y) = 1 - liminf_N D_N(x - y)`. -/
noncomputable def asymDist (b : ℕ) (x y : ℝ) : ℝ := limsup (fun N => discDist b N x y) atTop

private lemma discDist_boundedLE (b : ℕ) (x y : ℝ) :
    IsBoundedUnder (· ≤ ·) atTop (fun N => discDist b N x y) :=
  isBoundedUnder_of ⟨1, fun N => discDist_le_one b N x y⟩

private lemma discDist_boundedGE (b : ℕ) (x y : ℝ) :
    IsBoundedUnder (· ≥ ·) atTop (fun N => discDist b N x y) :=
  isBoundedUnder_of ⟨0, fun N => discDist_nonneg b N x y⟩

private lemma discDist_cobLE (b : ℕ) (x y : ℝ) :
    IsCoboundedUnder (· ≤ ·) atTop (fun N => discDist b N x y) :=
  (discDist_boundedGE b x y).isCoboundedUnder_le

theorem asymDist_nonneg (b : ℕ) (x y : ℝ) : 0 ≤ asymDist b x y :=
  le_limsup_of_frequently_le (Frequently.of_forall fun N => discDist_nonneg b N x y)
    (discDist_boundedLE b x y)

theorem asymDist_le_one (b : ℕ) (x y : ℝ) : asymDist b x y ≤ 1 :=
  limsup_le_of_le (discDist_cobLE b x y) (Eventually.of_forall fun N => discDist_le_one b N x y)

theorem asymDist_self (b : ℕ) (x : ℝ) : asymDist b x x = 0 := by
  simp [asymDist, discDist_self]

theorem asymDist_comm (b : ℕ) (x y : ℝ) : asymDist b x y = asymDist b y x :=
  limsup_congr (eventually_atTop.mpr ⟨1, fun _ hN => discDist_comm b hN x y⟩)

theorem asymDist_translate (b : ℕ) (x y t : ℝ) :
    asymDist b (x + t) (y + t) = asymDist b x y := by
  simp [asymDist, discDist_translate]

theorem asymDist_add_intCast (b : ℕ) (x y : ℝ) (k : ℤ) :
    asymDist b (x + k) y = asymDist b x y := by
  simp [asymDist, discDist_add_intCast]

/-- **Triangle inequality for the asymptotic distance.** -/
theorem asymDist_triangle (b : ℕ) (x y z : ℝ) :
    asymDist b x z ≤ asymDist b x y + asymDist b y z := by
  have hle : (fun N => discDist b N x z) ≤ᶠ[atTop]
      (fun N => discDist b N x y) + (fun N => discDist b N y z) :=
    eventually_atTop.mpr ⟨1, fun N hN => discDist_triangle b hN x y z⟩
  refine (limsup_le_limsup hle (discDist_cobLE b x z) ?_).trans ?_
  · exact (isBoundedUnder_le_add (discDist_boundedLE b x y) (discDist_boundedLE b y z))
  · exact limsup_add_le (discDist_boundedGE b x y) (discDist_boundedLE b x y)
      (discDist_cobLE b y z) (discDist_boundedLE b y z)

/-- If `(b-1)(x-y)` is an integer, the asymptotic distance vanishes. -/
theorem asymDist_eq_zero_of_int (b : ℕ) (x y : ℝ) (h : ∃ k : ℤ, ((b : ℝ) - 1) * (x - y) = k) :
    asymDist b x y = 0 := by
  unfold asymDist
  have hev : (fun N => discDist b N x y) =ᶠ[atTop] fun _ => (0 : ℝ) :=
    eventually_atTop.mpr ⟨2, fun N hN => (discDist_eq_zero_iff b hN x y).mpr h⟩
  rw [limsup_congr hev]
  simp

/-- If `D_N(x - y) → 0` (for instance when `x - y` is simply normal to base `b` in the
discrepancy sense), the asymptotic distance attains its maximum value one. -/
theorem asymDist_eq_one_of_tendsto (b : ℕ) (x y : ℝ)
    (h : Tendsto (fun N => radixDiscrepancy b (x - y) N) atTop (nhds 0)) :
    asymDist b x y = 1 := by
  have h1 : Tendsto (fun N => discDist b N x y) atTop (nhds 1) := by
    simpa [discDist] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  exact h1.limsup_eq

/-- **Integer multipliers are Lipschitz for the asymptotic distance.** -/
theorem asymDist_intMul_le (b : ℕ) (m : ℤ) (x y : ℝ) :
    asymDist b (m * x) (m * y) ≤ |(m : ℝ)| * asymDist b x y :=
  intMul_le_of_triangle (asymDist_self b) (asymDist_triangle b) (asymDist_translate b)
    (asymDist_comm b) m x y

end NormalityChecker.DiscrepancyGeometry
