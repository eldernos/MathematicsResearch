module

public import NormalityChecker.BinaryDiscrepancy

/-! # The exact worst-case change of discrepancy under translation

For every real `z`, every `x` and every `N > 0`,
`|D_N(x+z) - D_N(x)| ≤ 1 - D_N(z)`, with equality at `x = 0` (`sharp_translation`,
`sharp_translation_zero`, `sharp_translation_isGreatest`). Here `D_N` is the extreme interval
discrepancy `radixDiscrepancy` over half-open subintervals of `[0,1]`.

The proof works for arbitrary finite circle samples (`sampleDisc_paired`): if
`q_n ≡ p_n ± r_n (mod 1)` then `D(q) ≤ D(p) + 1 - D(r)`. Its three ingredients are
1. every arc of the circle, wrapping or not, has centered count at most `D` (`arc_le`);
2. every centered interval count in the supremum is the positive excess of some arc, by
   complementation (`interval_eq_arc_excess`);
3. a finite comparison: on the samples whose `r_n` lies in an arc of length `l`, the sample
   `q_n` is within circle distance `l/2` of a fixed rotation of `p_n` (`paired_arc_le`).
-/

@[expose] public section

open Finset Filter

namespace NormalityChecker.SharpTranslation

/-- Extreme interval discrepancy of an arbitrary finite sample. -/
noncomputable def sampleDisc (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup {d | ∃ a c : ℝ, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧ d = |frequency u a c N - (c - a)|}

theorem radixDiscrepancy_eq_sampleDisc (b : ℕ) (x : ℝ) (N : ℕ) :
    radixDiscrepancy b x N = sampleDisc (shift b x) N := rfl

private lemma bdd (u : ℕ → ℝ) (N : ℕ) :
    BddAbove {d | ∃ a c : ℝ, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧ d = |frequency u a c N - (c - a)|} := by
  refine ⟨1, ?_⟩
  rintro _ ⟨a, c, ha, hac, hc, rfl⟩
  have f := frequency_bounds u a c N
  rw [abs_le]; constructor <;> linarith [f.1, f.2]

theorem interval_le_sampleDisc (u : ℕ → ℝ) (N : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hac : a < c)
    (hc : c ≤ 1) : |frequency u a c N - (c - a)| ≤ sampleDisc u N :=
  le_csSup (bdd u N) ⟨a, c, ha, hac, hc, rfl⟩

theorem sampleDisc_le_of {u : ℕ → ℝ} {N : ℕ} {D : ℝ}
    (H : ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 → |frequency u a c N - (c - a)| ≤ D) :
    sampleDisc u N ≤ D := by
  refine csSup_le ⟨_, 0, 1, le_rfl, zero_lt_one, le_rfl, rfl⟩ ?_
  rintro _ ⟨a, c, ha, hac, hc, rfl⟩
  exact H a c ha hac hc

theorem sampleDisc_nonneg (u : ℕ → ℝ) (N : ℕ) : 0 ≤ sampleDisc u N :=
  (abs_nonneg _).trans (interval_le_sampleDisc u N le_rfl zero_lt_one le_rfl)

theorem sampleDisc_le_one (u : ℕ → ℝ) (N : ℕ) : sampleDisc u N ≤ 1 :=
  sampleDisc_le_of (fun a c _ _ _ => by
    have f := frequency_bounds u a c N
    rw [abs_le]; constructor <;> linarith [f.1, f.2])

/-- A possibly degenerate interval. -/
theorem interval_le_sampleDisc' (u : ℕ → ℝ) (N : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ 1) : |frequency u a c N - (c - a)| ≤ sampleDisc u N := by
  rcases hac.lt_or_eq with h | rfl
  · exact interval_le_sampleDisc u N ha h hc
  · have : frequency u a a N = 0 := by
      unfold frequency
      rw [Finset.filter_false_of_mem (fun i _ h => absurd (h.1.trans_lt h.2) (lt_irrefl _))]
      simp
    rw [this, sub_self, sub_zero, abs_zero]; exact sampleDisc_nonneg u N

/-! ### Arcs -/

/-- Number of samples `n < N` in the arc `[α, α+l)` of the circle. -/
noncomputable def arcCount (u : ℕ → ℝ) (α l : ℝ) (N : ℕ) : ℕ :=
  ((range N).filter (fun n => Int.fract (u n - α) < l)).card

private lemma fract_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Int.fract t = t :=
  Int.fract_eq_self.mpr ⟨h0, h1⟩

private lemma fract_of_neg {t : ℝ} (h0 : -1 ≤ t) (h1 : t < 0) : Int.fract t = t + 1 := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- A non-wrapping arc. -/
private lemma arc_iff_inner {a l y : ℝ} (ha : 0 ≤ a) (hl : 0 ≤ l) (hal : a + l ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y < 1) : Int.fract (y - a) < l ↔ a ≤ y ∧ y < a + l := by
  by_cases h : a ≤ y
  · rw [fract_of_mem (by linarith) (by linarith)]
    constructor
    · intro h'; exact ⟨h, by linarith⟩
    · intro h'; linarith [h'.2]
  · push Not at h
    rw [fract_of_neg (by linarith) (by linarith)]
    constructor
    · intro h'; linarith
    · intro h'; linarith [h'.1]

/-- A wrapping arc is the complement of an interval. -/
private lemma arc_iff_outer {a l y : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hal : 1 < a + l) (hy0 : 0 ≤ y)
    (hy1 : y < 1) : Int.fract (y - a) < l ↔ ¬ (a + l - 1 ≤ y ∧ y < a) := by
  by_cases h : a ≤ y
  · rw [fract_of_mem (by linarith) (by linarith)]
    constructor
    · intro _ h'; linarith [h'.2]
    · intro _; linarith
  · push Not at h
    rw [fract_of_neg (by linarith) (by linarith)]
    constructor
    · intro h' h''; linarith [h''.1]
    · intro h'
      by_contra h''
      push Not at h''
      exact h' ⟨by linarith, h⟩

private lemma card_compl (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((range N).filter (fun n => ¬ P n)).card = N - ((range N).filter P).card := by
  have := Finset.card_filter_add_card_filter_not (s := range N) P
  rw [card_range] at this
  omega

/-- **Arc bound.** Every arc of length `l ∈ [0,1]` has centered count at most the extreme
interval discrepancy. -/
theorem arc_le {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n ∧ u n < 1) {N : ℕ} (hN : 0 < N) (α : ℝ)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    |(arcCount u α l N : ℝ) / N - l| ≤ sampleDisc u N := by
  classical
  set a := Int.fract α
  have ha0 : 0 ≤ a := Int.fract_nonneg α
  have ha1 : a < 1 := Int.fract_lt_one α
  have hshift : ∀ y, Int.fract (y - α) = Int.fract (y - a) := by
    intro y
    have : y - α = (y - a) + ((-⌊α⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor α; push_cast; dsimp [a]; linarith
    rw [this, Int.fract_add_intCast]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hal : a + l ≤ 1
  · have heq : arcCount u α l N = ((range N).filter (fun n => a ≤ u n ∧ u n < a + l)).card := by
      unfold arcCount
      congr 1
      exact Finset.filter_congr (fun n _ => by
        rw [hshift]; exact arc_iff_inner ha0 hl0 hal (hu n).1 (hu n).2)
    have := interval_le_sampleDisc' u N ha0 (by linarith : a ≤ a + l) hal
    rw [show a + l - a = l by ring] at this
    rw [heq]; exact this
  · push Not at hal
    have heq : arcCount u α l N =
        N - ((range N).filter (fun n => a + l - 1 ≤ u n ∧ u n < a)).card := by
      unfold arcCount
      rw [← card_compl]
      congr 1
      exact Finset.filter_congr (fun n _ => by
        rw [hshift]; exact arc_iff_outer ha0 ha1 hal (hu n).1 (hu n).2)
    have hint := interval_le_sampleDisc' u N (by linarith : 0 ≤ a + l - 1) (by linarith) ha1.le
    have hle : ((range N).filter (fun n => a + l - 1 ≤ u n ∧ u n < a)).card ≤ N :=
      (card_filter_le _ _).trans_eq (card_range N)
    rw [heq, Nat.cast_sub hle]
    have hf : frequency u (a + l - 1) a N =
        (((range N).filter (fun n => a + l - 1 ≤ u n ∧ u n < a)).card : ℝ) / N := rfl
    rw [hf] at hint
    have : ((N : ℝ) - ((range N).filter (fun n => a + l - 1 ≤ u n ∧ u n < a)).card) / N - l =
        -((((range N).filter (fun n => a + l - 1 ≤ u n ∧ u n < a)).card : ℝ) / N -
          (a - (a + l - 1))) := by
      field_simp; ring
    rw [this, abs_neg]; exact hint

/-- **Complementation.** Every centered interval count is the positive excess of an arc. -/
theorem interval_eq_arc_excess {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n ∧ u n < 1) {N : ℕ}
    (hN : 0 < N) {a c : ℝ} (ha : 0 ≤ a) (hac : a < c) (hc : c ≤ 1) :
    ∃ α l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧
      (arcCount u α l N : ℝ) / N - l = |frequency u a c N - (c - a)| := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : frequency u a c N = (((range N).filter (fun n => a ≤ u n ∧ u n < c)).card : ℝ) / N :=
    rfl
  by_cases hs : c - a ≤ frequency u a c N
  · refine ⟨a, c - a, by linarith, by linarith, ?_⟩
    have heq : arcCount u a (c - a) N = ((range N).filter (fun n => a ≤ u n ∧ u n < c)).card := by
      unfold arcCount
      congr 1
      exact Finset.filter_congr (fun n _ => by
        rw [arc_iff_inner ha (by linarith) (by linarith) (hu n).1 (hu n).2, show a + (c - a) = c by ring])
    rw [heq, ← hf, abs_of_nonneg (by linarith)]
  · push Not at hs
    refine ⟨c, 1 - (c - a), by linarith, by linarith, ?_⟩
    have hpt : ∀ y, 0 ≤ y → y < 1 → (Int.fract (y - c) < 1 - (c - a) ↔ ¬ (a ≤ y ∧ y < c)) := by
      intro y hy0 hy1
      by_cases h : c ≤ y
      · rw [fract_of_mem (by linarith) (by linarith)]
        constructor
        · intro _ h'; linarith [h'.2]
        · intro _; linarith
      · push Not at h
        rw [fract_of_neg (by linarith) (by linarith)]
        constructor
        · intro h' h''; linarith [h''.1]
        · intro h'
          by_contra h''
          push Not at h''
          exact h' ⟨by linarith, h⟩
    have heq : arcCount u c (1 - (c - a)) N =
        N - ((range N).filter (fun n => a ≤ u n ∧ u n < c)).card := by
      unfold arcCount
      rw [← card_compl]
      congr 1
      exact Finset.filter_congr (fun n _ => hpt _ (hu n).1 (hu n).2)
    have hle : ((range N).filter (fun n => a ≤ u n ∧ u n < c)).card ≤ N :=
      (card_filter_le _ _).trans_eq (card_range N)
    rw [heq, Nat.cast_sub hle, abs_of_neg (by linarith), hf]
    field_simp
    ring

/-! ### The paired comparison -/

private lemma count_le (P Q bad : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred bad] (h : ∀ n, P n → ¬ bad n → Q n) (N : ℕ) :
    ((range N).filter P).card ≤ ((range N).filter Q).card + ((range N).filter bad).card := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro n hn
  rw [mem_filter] at hn
  rw [mem_union, mem_filter, mem_filter]
  by_cases hb : bad n
  · exact Or.inr ⟨hn.1, hb⟩
  · exact Or.inl ⟨hn.1, h n hn.2 hb⟩

private lemma int_eq_zero_of_abs_lt {t : ℝ} {i : ℤ} (h : t = i) (h1 : -1 < t) (h2 : t < 1) :
    i = 0 := by
  subst h
  have a : (-1 : ℤ) < i := by exact_mod_cast h1
  have b : i < 1 := by exact_mod_cast h2
  omega

/-- **Finite arc comparison for paired samples.** If `q_n ≡ p_n + s r_n (mod 1)` with
`s = ±1`, then for every arc `[α, α+l)` of length `l ≥ 0`,
`D(q) ≤ D(p) + 1 - (μ_r(arc) - l)`. -/
theorem paired_arc_le {p q r : ℕ → ℝ} {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hp : ∀ n, 0 ≤ p n ∧ p n < 1) (hq : ∀ n, 0 ≤ q n ∧ q n < 1)
    (pair : ∀ n, ∃ i : ℤ, q n = p n + s * r n + i) {N : ℕ} (hN : 0 < N) (α : ℝ) {l : ℝ}
    (hl0 : 0 ≤ l) :
    sampleDisc q N ≤ sampleDisc p N + 1 - ((arcCount r α l N : ℝ) / N - l) := by
  classical
  set D := sampleDisc p N
  set G := arcCount r α l N with hG
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 ≤ D := sampleDisc_nonneg p N
  let bad : ℕ → Prop := fun n => ¬ (Int.fract (r n - α) < l)
  have hbad : ((range N).filter bad).card = N - G := card_compl N _
  have hGN : G ≤ N := (card_filter_le _ _).trans_eq (card_range N)
  have hbadr : (((range N).filter bad).card : ℝ) / N = 1 - (G : ℝ) / N := by
    rw [hbad, Nat.cast_sub hGN]; field_simp
  have hGr : (G : ℝ) / N ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hGN)
  set γ := s * (α + l / 2) with hγ
  -- on a good position, `q n = p n + γ + δ + i` with `|δ| ≤ l/2`
  have good : ∀ n, ¬ bad n → ∃ δ : ℝ, -(l / 2) ≤ δ ∧ δ ≤ l / 2 ∧ ∃ i : ℤ,
      q n = p n + γ + δ + i := by
    intro n hn
    simp only [bad, not_not] at hn
    set t := Int.fract (r n - α)
    have ht0 : 0 ≤ t := Int.fract_nonneg _
    have hr : r n = α + t + ⌊r n - α⌋ := by have := Int.fract_add_floor (r n - α); linarith
    obtain ⟨i, hi⟩ := pair n
    rcases hs with rfl | rfl
    · refine ⟨t - l / 2, by linarith, by linarith, i + ⌊r n - α⌋, ?_⟩
      rw [hi, hγ]; push_cast; linear_combination hr
    · refine ⟨-(t - l / 2), by linarith, by linarith, i - ⌊r n - α⌋, ?_⟩
      rw [hi, hγ]; push_cast; linear_combination (-1 : ℝ) * hr
  have freqdef : ∀ (w : ℕ → ℝ) (a c : ℝ),
      frequency w a c N = (((range N).filter (fun i => a ≤ w i ∧ w i < c)).card : ℝ) / N :=
    fun _ _ _ => rfl
  have arcdef : ∀ (w : ℕ → ℝ) (β m : ℝ),
      (arcCount w β m N : ℝ) / N =
        (((range N).filter (fun n => Int.fract (w n - β) < m)).card : ℝ) / N :=
    fun _ _ _ => rfl
  rw [show D + 1 - ((G : ℝ) / N - l) = D + l + (1 - (G : ℝ) / N) by ring]
  apply sampleDisc_le_of
  intro a c ha hac hc
  have hfreq := frequency_bounds q a c N
  rw [abs_le]; constructor
  · -- lower bound
    by_cases hw : c - a ≤ l
    · linarith [hfreq.1]
    push Not at hw
    have cnt := count_le (fun n => Int.fract (p n - (a + l / 2 - γ)) < c - a - l)
      (fun n => a ≤ q n ∧ q n < c) bad (by
        intro n hn hg
        obtain ⟨δ, hδ1, hδ2, i, hi⟩ := good n hg
        set v := Int.fract (p n - (a + l / 2 - γ))
        have hv0 : 0 ≤ v := Int.fract_nonneg _
        have hv := Int.fract_add_floor (p n - (a + l / 2 - γ))
        have hz : ⌊p n - (a + l / 2 - γ)⌋ + i = 0 :=
          int_eq_zero_of_abs_lt (t := q n - a - (l / 2 + δ + v))
            (by rw [hi]; push_cast; linarith) (by linarith [hq n]) (by linarith [hq n])
        have hq' : q n = a + (l / 2 + δ + v) := by
          have : ((⌊p n - (a + l / 2 - γ)⌋ + i : ℤ) : ℝ) = 0 := by exact_mod_cast hz
          push_cast at this; rw [hi]; linarith
        rw [hq']; constructor <;> linarith) N
    have harc := arc_le hp hN (a + l / 2 - γ) (by linarith : 0 ≤ c - a - l) (by linarith)
    have hcnt : (arcCount p (a + l / 2 - γ) (c - a - l) N : ℝ) / N ≤
        frequency q a c N + (1 - (G : ℝ) / N) := by
      rw [arcdef, freqdef, ← hbadr, ← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast cnt) hNr.le
    rw [abs_le] at harc
    linarith [harc.1]
  · -- upper bound
    by_cases hw : 1 ≤ c - a + l
    · linarith [hfreq.2]
    push Not at hw
    have cnt := count_le (fun n => a ≤ q n ∧ q n < c)
      (fun n => Int.fract (p n - (a - l / 2 - γ)) < c - a + l) bad (by
        intro n hn hg
        obtain ⟨δ, hδ1, hδ2, i, hi⟩ := good n hg
        have he : p n - (a - l / 2 - γ) = (q n - a + (l / 2 - δ)) + ((-i : ℤ) : ℝ) := by
          rw [hi]; push_cast; ring
        rw [he, Int.fract_add_intCast,
          fract_of_mem (by linarith [hn.1]) (by linarith [hn.2])]
        linarith [hn.2]) N
    have harc := arc_le hp hN (a - l / 2 - γ) (by linarith : 0 ≤ c - a + l) hw.le
    have hcnt : frequency q a c N ≤
        (arcCount p (a - l / 2 - γ) (c - a + l) N : ℝ) / N + (1 - (G : ℝ) / N) := by
      rw [arcdef, freqdef, ← hbadr, ← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast cnt) hNr.le
    rw [abs_le] at harc
    linarith [harc.2]

/-- **Paired samples.** If `q_n ≡ p_n ± r_n (mod 1)` for samples in `[0,1)`, then
`D_N(q) ≤ D_N(p) + 1 - D_N(r)`. -/
theorem sampleDisc_paired {p q r : ℕ → ℝ} {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hp : ∀ n, 0 ≤ p n ∧ p n < 1) (hq : ∀ n, 0 ≤ q n ∧ q n < 1) (hr : ∀ n, 0 ≤ r n ∧ r n < 1)
    (pair : ∀ n, ∃ i : ℤ, q n = p n + s * r n + i) {N : ℕ} (hN : 0 < N) :
    sampleDisc q N ≤ sampleDisc p N + 1 - sampleDisc r N := by
  have : sampleDisc r N ≤ sampleDisc p N + 1 - sampleDisc q N := by
    apply sampleDisc_le_of
    intro a c ha hac hc
    obtain ⟨α, l, hl0, hl1, heq⟩ := interval_eq_arc_excess hr hN ha hac hc
    have := paired_arc_le hs hp hq pair hN α hl0
    rw [← heq]; linarith
  linarith

private lemma shift_mem (b : ℕ) (x : ℝ) (n : ℕ) : 0 ≤ shift b x n ∧ shift b x n < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **The exact worst-case change.** For every real `x`, `z` and every `N > 0`,
`|D_N(x+z) - D_N(x)| ≤ 1 - D_N(z)`. -/
theorem sharp_translation (b : ℕ) (x z : ℝ) {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy b (x + z) N - radixDiscrepancy b x N| ≤ 1 - radixDiscrepancy b z N := by
  simp only [radixDiscrepancy_eq_sampleDisc]
  have h1 := sampleDisc_paired (p := shift b x) (q := shift b (x + z)) (r := shift b z)
    (s := 1) (Or.inl rfl) (shift_mem b x) (shift_mem b (x + z)) (shift_mem b z) (fun n => by
      refine ⟨⌊(b : ℝ) ^ n * x⌋ + ⌊(b : ℝ) ^ n * z⌋ - ⌊(b : ℝ) ^ n * (x + z)⌋, ?_⟩
      unfold shift; rw [Int.fract, Int.fract, Int.fract]; push_cast; ring) hN
  have h2 := sampleDisc_paired (p := shift b (x + z)) (q := shift b x) (r := shift b z)
    (s := -1) (Or.inr rfl) (shift_mem b (x + z)) (shift_mem b x) (shift_mem b z) (fun n => by
      refine ⟨⌊(b : ℝ) ^ n * (x + z)⌋ - ⌊(b : ℝ) ^ n * z⌋ - ⌊(b : ℝ) ^ n * x⌋, ?_⟩
      unfold shift; rw [Int.fract, Int.fract, Int.fract]; push_cast; ring) hN
  rw [abs_le]; constructor <;> linarith

/-- The orbit of zero has extreme discrepancy one at every cutoff. -/
theorem radixDiscrepancy_zero (b N : ℕ) : radixDiscrepancy b 0 N = 1 := by
  rw [radixDiscrepancy_eq_sampleDisc]
  refine le_antisymm (sampleDisc_le_one _ N) ?_
  have hz : ∀ n, shift b 0 n = 0 := fun n => by simp [shift]
  have key : ∀ a : ℝ, 0 < a → a < 1 → 1 - a ≤ sampleDisc (shift b 0) N := by
    intro a ha0 ha1
    have h := interval_le_sampleDisc (shift b 0) N ha0.le ha1 le_rfl
    have hf : frequency (shift b 0) a 1 N = 0 := by
      unfold frequency
      rw [Finset.filter_false_of_mem (fun i _ h => by rw [hz] at h; linarith [h.1])]
      simp
    rw [hf, zero_sub, abs_neg, abs_of_pos (by linarith)] at h
    exact h
  by_contra hcon
  push Not at hcon
  set D := sampleDisc (shift b 0) N
  have hD := sampleDisc_nonneg (shift b 0) N
  have := key ((1 - D) / 2) (by linarith) (by linarith)
  linarith

/-- **Equality at `x = 0`.** -/
theorem sharp_translation_zero (b : ℕ) (z : ℝ) (N : ℕ) :
    |radixDiscrepancy b (0 + z) N - radixDiscrepancy b 0 N| = 1 - radixDiscrepancy b z N := by
  rw [zero_add, radixDiscrepancy_zero, abs_of_nonpos (by
    linarith [sampleDisc_le_one (shift b z) N, radixDiscrepancy_eq_sampleDisc b z N])]
  ring

/-- **Sharpness.** `sup_x |D_N(x+z) - D_N(x)| = 1 - D_N(z)`, and the supremum is attained
at `x = 0`. -/
theorem sharp_translation_isGreatest (b : ℕ) (z : ℝ) {N : ℕ} (hN : 0 < N) :
    IsGreatest (Set.range fun x : ℝ =>
      |radixDiscrepancy b (x + z) N - radixDiscrepancy b x N|) (1 - radixDiscrepancy b z N) :=
  ⟨⟨0, sharp_translation_zero b z N⟩, by
    rintro _ ⟨x, rfl⟩; exact sharp_translation b x z hN⟩

end NormalityChecker.SharpTranslation
