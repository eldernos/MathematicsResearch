module

public import NormalityChecker.SharpDiscrepancy
public import NormalityChecker.JointWeyl
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Kernel-checked Phase 17 core bounds spanning Tracks A, B and D:
1. Two-sided finite binary discrepancy gap (`Track B3`): lower gap from binary transitions and
   upper gap from the frequency of `1`-bits via optimized all-zero prefix intervals `[0, 2⁻ᴸ)`.
2. General two-prime single-shape maximum `M_{p,q} = (p - 1)(q - 1) / (2pq - p - q)` (`Track D4`),
   extending Phase 16's `4/11` at `(p, q) = (3, 5)` to all real `p, q > 1`.
3. General multidimensional Weyl corollary for arbitrary finite collections of established
   polynomial degrees (`Track A3`).
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace NormalityChecker.Phase17DiscrepancyBounds

/-! ### Part 1: Two-sided finite binary discrepancy gap (Track B3) -/

/-- Lower discrepancy gap in terms of adjacent binary transitions (`01` and `10`):
for every real `x` and `N ≥ 1`, `min (1/3) (transitionFrequency x N) - 1/N ≤ 1 - binaryDiscrepancy x N`. -/
theorem one_sub_discrepancy_ge_transition (x : ℝ) {N : ℕ} (hN : 0 < N) :
    min (1 / 3 : ℝ) (transitionFrequency x N) - 1 / (N : ℝ) ≤ 1 - binaryDiscrepancy x N := by
  have h := sharp_finite_discrepancy x hN
  by_cases hτ : transitionFrequency x N ≤ 1 / 3
  · have hmax : max (2 / 3 : ℝ) (1 - transitionFrequency x N) = 1 - transitionFrequency x N :=
      max_eq_right (by linarith)
    have hmin : min (1 / 3 : ℝ) (transitionFrequency x N) = transitionFrequency x N :=
      min_eq_right hτ
    linarith
  · push Not at hτ
    have hmax : max (2 / 3 : ℝ) (1 - transitionFrequency x N) = 2 / 3 :=
      max_eq_left (by linarith)
    have hmin : min (1 / 3 : ℝ) (transitionFrequency x N) = 1 / 3 :=
      min_eq_left hτ.le
    linarith

/-- If `shift 2 x n ≥ 2⁻ᴸ` (`L ≥ 1`), then some position `n + j` with `j ≤ L - 1` has a `1`-bit
(`shift 2 x (n + j) ≥ 1/2`). -/
theorem nonzero_shift_has_one_bit (x : ℝ) :
    ∀ (L n : ℕ), 1 ≤ L → (1 / 2 : ℝ) ^ L ≤ shift 2 x n →
      ∃ j ≤ L - 1, (1 / 2 : ℝ) ≤ shift 2 x (n + j) := by
  intro L
  induction L with
  | zero =>
    intro _ hL _
    omega
  | succ k ih =>
    intro n _ hlow
    by_cases h1 : (1 / 2 : ℝ) ≤ shift 2 x n
    · exact ⟨0, Nat.zero_le _, by simpa using h1⟩
    · push Not at h1
      cases k with
      | zero =>
        norm_num at hlow
        linarith
      | succ k' =>
        have hstep : shift 2 x (n + 1) = 2 * shift 2 x n := by
          rw [binary_shift_step]
          simp only [h1, ite_true]
        have hlow' : (1 / 2 : ℝ) ^ (k' + 1) ≤ shift 2 x (n + 1) := by
          rw [hstep]
          rw [pow_succ] at hlow
          linarith
        obtain ⟨j, hj, hbit⟩ := ih (n + 1) (by omega) hlow'
        refine ⟨j + 1, by omega, ?_⟩
        rwa [show n + (j + 1) = (n + 1) + j by omega]

/-- Frequency of shifts in `[2⁻ᴸ, 1)` is controlled by `L` times the `1`-bit frequency plus
the boundary allowance `(L - 1) / N`. -/
theorem upper_freq_le_one_bits (x : ℝ) {L : ℕ} (hL : 1 ≤ L) (N : ℕ) :
    frequency (shift 2 x) ((1 / 2 : ℝ) ^ L) 1 N ≤
      ((L - 1 : ℕ) : ℝ) / (N : ℝ) + (L : ℝ) * frequency (shift 2 x) (1 / 2) 1 N := by
  classical
  have hcnt := count_within_steps
    (P := fun n => (1 / 2 : ℝ) ^ L ≤ shift 2 x n ∧ shift 2 x n < 1)
    (Q := fun n => (1 / 2 : ℝ) ≤ shift 2 x n ∧ shift 2 x n < 1)
    N (L - 1)
    (fun n hn => by
      obtain ⟨j, hj, hbit⟩ := nonzero_shift_has_one_bit x L n hL hn.1
      exact ⟨j, hj, hbit, Int.fract_lt_one _⟩)
  have hL1 : (L - 1) + 1 = L := by omega
  rw [hL1] at hcnt
  unfold frequency
  rw [← mul_div_assoc, ← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcnt) (Nat.cast_nonneg _)

/-- Upper discrepancy gap in terms of the `1`-bit frequency: for every real `x`, `L ≥ 1`, and `N ≥ 1`,
`1 - binaryDiscrepancy x N ≤ (1/2)^L + (L - 1)/N + L * frequency (shift 2 x) (1/2) 1 N`.
Optimizing `L = ⌈(1/2) log₂(log N)⌉` when the `1`-bit frequency is `O(1 / √(log N))` yields
`1 - D_N(x) = O((log log N) / √(log N))`. -/
theorem one_sub_discrepancy_le_one_bits (x : ℝ) {L N : ℕ} (hL : 1 ≤ L) (hN : 0 < N) :
    1 - binaryDiscrepancy x N ≤
      (1 / 2 : ℝ) ^ L + ((L - 1 : ℕ) : ℝ) / (N : ℝ) +
        (L : ℝ) * frequency (shift 2 x) (1 / 2) 1 N := by
  have hpow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ L := by positivity
  have hpow_le : (1 / 2 : ℝ) ^ L ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hdisc := interval_le_discrepancy x N (a := 0) (c := (1 / 2 : ℝ) ^ L) le_rfl hpow_pos hpow_le
  have hlow : frequency (shift 2 x) 0 ((1 / 2 : ℝ) ^ L) N - (1 / 2 : ℝ) ^ L ≤ binaryDiscrepancy x N := by
    have h1 := (abs_le.mp hdisc).2
    linarith
  have hfull : frequency (shift 2 x) 0 1 N = 1 := by
    unfold frequency
    have hall : (range N).filter (fun i => (0 : ℝ) ≤ shift 2 x i ∧ shift 2 x i < 1) = range N := by
      apply filter_true_of_mem
      intro i _
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    rw [hall, card_range, div_self (Nat.cast_ne_zero.mpr hN.ne')]
  have hsplit := anchored_difference (shift 2 x) (a := (1 / 2 : ℝ) ^ L) (c := 1) hpow_pos.le hpow_le N
  have hup := upper_freq_le_one_bits x hL N
  linarith

/-- Lower discrepancy gap from two separated positive-mass intervals `[0, ε)` and `[3ε, 1/2)`:
if `0 < ε ≤ 1/6`, `Δ ≤ ε`, and both `[0, ε)` and `[3ε, 1/2)` receive empirical frequency at least `Δ`,
then `Δ ≤ 1 - binaryDiscrepancy x N` (equivalently `binaryDiscrepancy x N ≤ 1 - Δ`).
Used in Track B to establish the matching lower bound `1 - D_N(L_f) ≫ (log log N) / (log N)^{1-δ}`. -/
theorem one_sub_discrepancy_ge_of_separated_mass (x : ℝ) {N : ℕ} (hN : 0 < N)
    {ε Δ : ℝ} (hε0 : 0 < ε) (hε6 : 6 * ε ≤ 1) (hΔε : Δ ≤ ε)
    (hlow : Δ ≤ frequency (shift 2 x) 0 ε N)
    (hmid : Δ ≤ frequency (shift 2 x) (3 * ε) (1 / 2) N) :
    Δ ≤ 1 - binaryDiscrepancy x N := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hdisj : ∀ {a₁ c₁ a₂ c₂ : ℝ}, (c₁ ≤ a₂ ∨ c₂ ≤ a₁) →
      frequency (shift 2 x) a₁ c₁ N + frequency (shift 2 x) a₂ c₂ N ≤ 1 := by
    intro a₁ c₁ a₂ c₂ hsep
    let I := (range N).filter (fun n => a₁ ≤ shift 2 x n ∧ shift 2 x n < c₁)
    let J := (range N).filter (fun n => a₂ ≤ shift 2 x n ∧ shift 2 x n < c₂)
    have hd : Disjoint I J := by
      apply disjoint_left.mpr
      intro n hI hJ
      obtain ⟨_, h1, h2⟩ := mem_filter.mp hI
      obtain ⟨_, h3, h4⟩ := mem_filter.mp hJ
      rcases hsep with h | h <;> linarith
    have hcard : I.card + J.card ≤ N := by
      rw [← card_union_of_disjoint hd, ← card_range N]
      exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    unfold frequency
    change (I.card : ℝ) / (N : ℝ) + (J.card : ℝ) / (N : ℝ) ≤ 1
    rw [← add_div, div_le_one hNpos]
    exact_mod_cast hcard
  have hmono : ∀ {a₁ c₁ a₂ c₂ : ℝ}, a₂ ≤ a₁ → c₁ ≤ c₂ →
      frequency (shift 2 x) a₁ c₁ N ≤ frequency (shift 2 x) a₂ c₂ N := by
    intro a₁ c₁ a₂ c₂ ha hc
    unfold frequency
    apply div_le_div_of_nonneg_right _ hNpos.le
    apply Nat.cast_le.mpr (card_le_card ?_)
    intro n hn
    obtain ⟨hnN, h1, h2⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, ha.trans h1, h2.trans_le hc⟩
  suffices hD : binaryDiscrepancy x N ≤ 1 - Δ by linarith
  apply discrepancy_le
  intro a c ha hac hc
  obtain ⟨hf0, hf1⟩ := frequency_bounds (shift 2 x) a c N
  rw [abs_le]
  constructor
  · by_cases hlen : c - a ≤ 1 - ε
    · linarith
    · push Not at hlen
      have hsub : frequency (shift 2 x) (3 * ε) (1 / 2) N ≤ frequency (shift 2 x) a c N :=
        hmono (by linarith) (by linarith)
      linarith
  · by_cases hlen : ε ≤ c - a
    · linarith
    · push Not at hlen
      by_cases hright : c ≤ 3 * ε
      · have hd := hdisj (a₁ := a) (c₁ := c) (a₂ := 3 * ε) (c₂ := 1 / 2) (Or.inl hright)
        linarith
      · push Not at hright
        have hd := hdisj (a₁ := a) (c₁ := c) (a₂ := 0) (c₂ := ε) (Or.inr (by linarith))
        linarith

/-! ### Part 2: General two-prime single-shape maximum (Track D4) -/

/-- Exact single-shape maximum relative length for the primary corner `(1, 1)` of
`α(b, p) α(b, q)` for arbitrary real parameters `p, q > 1` and ratio `r = Q / P > 0`:
`min (((q - 1)/q) * r, (p - 1)/p) / (1 + r) ≤ (p - 1)(q - 1) / (2pq - p - q)`. -/
theorem general_single_shape_one_one_max {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 0 < r) :
    min (((q - 1) / q) * r) ((p - 1) / p) / (1 + r) ≤
      (p - 1) * (q - 1) / (2 * p * q - p - q) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hden : 0 < 2 * p * q - p - q := by nlinarith
  have hr1 : 0 < 1 + r := by linarith
  rw [div_le_div_iff₀ hr1 hden]
  by_cases h : r ≤ q * (p - 1) / (p * (q - 1))
  · have hmin : min (((q - 1) / q) * r) ((p - 1) / p) ≤ ((q - 1) / q) * r := min_le_left _ _
    have hr_bound : r * (p * (q - 1)) ≤ q * (p - 1) := by
      exact (le_div_iff₀ (by positivity)).mp h
    have hmul : (((q - 1) / q) * r) * (2 * p * q - p - q) ≤ (p - 1) * (q - 1) * (1 + r) := by
      have hclear : (q - 1) * r * (2 * p * q - p - q) ≤ q * ((p - 1) * (q - 1) * (1 + r)) := by
        have hdiff :
            q * ((p - 1) * (q - 1) * (1 + r)) - (q - 1) * r * (2 * p * q - p - q) =
              (q - 1) * (q * (p - 1) - r * (p * (q - 1))) := by ring
        nlinarith
      have hrew : (((q - 1) / q) * r) * (2 * p * q - p - q) =
          ((q - 1) * r * (2 * p * q - p - q)) / q := by ring
      rw [hrew, div_le_iff₀ hq0]
      linarith
    have h1 : min (((q - 1) / q) * r) ((p - 1) / p) * (2 * p * q - p - q) ≤
        (((q - 1) / q) * r) * (2 * p * q - p - q) :=
      mul_le_mul_of_nonneg_right hmin hden.le
    exact h1.trans hmul
  · push Not at h
    have hmin : min (((q - 1) / q) * r) ((p - 1) / p) ≤ (p - 1) / p := min_le_right _ _
    have hr_bound : q * (p - 1) < r * (p * (q - 1)) := by
      exact (div_lt_iff₀ (by positivity)).mp h
    have hmul : ((p - 1) / p) * (2 * p * q - p - q) ≤ (p - 1) * (q - 1) * (1 + r) := by
      have hclear : (p - 1) * (2 * p * q - p - q) ≤ p * ((p - 1) * (q - 1) * (1 + r)) := by
        have hdiff :
            p * ((p - 1) * (q - 1) * (1 + r)) - (p - 1) * (2 * p * q - p - q) =
              (p - 1) * (r * (p * (q - 1)) - q * (p - 1)) := by ring
        nlinarith
      have hrew : ((p - 1) / p) * (2 * p * q - p - q) =
          ((p - 1) * (2 * p * q - p - q)) / p := by ring
      rw [hrew, div_le_iff₀ hp0]
      linarith
    have h1 : min (((q - 1) / q) * r) ((p - 1) / p) * (2 * p * q - p - q) ≤
        ((p - 1) / p) * (2 * p * q - p - q) :=
      mul_le_mul_of_nonneg_right hmin hden.le
    exact h1.trans hmul

/-- Equality in `general_single_shape_one_one_max` is attained at `r = q(p - 1) / (p(q - 1))`. -/
theorem general_single_shape_one_one_attained {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    min (((q - 1) / q) * (q * (p - 1) / (p * (q - 1)))) ((p - 1) / p) /
        (1 + q * (p - 1) / (p * (q - 1))) =
      (p - 1) * (q - 1) / (2 * p * q - p - q) := by
  have hp0 : p ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have hden : 2 * p * q - p - q ≠ 0 := by nlinarith
  have heq : ((q - 1) / q) * (q * (p - 1) / (p * (q - 1))) = (p - 1) / p := by
    field_simp [hp0, hq0, hq1]
  rw [heq, min_self]
  have h1r : 1 + q * (p - 1) / (p * (q - 1)) ≠ 0 := by positivity
  rw [div_eq_div_iff h1r hden]
  field_simp [hp0, hq1]
  ring

/-! ### Part 3: Multidimensional Weyl theorem for arbitrary established polynomial degrees (Track A3) -/

/-- If `deg : Fin k → ℕ` lists distinct degrees and every nonzero integer polynomial in `α`
whose degree lies in `Set.range deg` is normal in base `b`, then the powers `(α^(deg i))` are
jointly uniformly distributed in `[0, 1)^k`. -/
theorem jointUniform_of_established_degrees {b k : ℕ} {α : ℝ} (deg : Fin k → ℕ)
    (hinj : Function.Injective deg)
    (hnorm : ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ∈ Set.range deg →
      NormalIn b (Polynomial.aeval α P)) :
    JointUniform b (fun i => α ^ (deg i)) := by
  classical
  apply JointWeyl.rectangle_of_scalar_normal
  intro t ht
  let P : Polynomial ℤ := ∑ i : Fin k, Polynomial.C (t i) * Polynomial.X ^ (deg i)
  have hcoeff : ∀ d : ℕ, P.coeff d = if h : ∃ i, deg i = d then t h.choose else 0 := by
    intro d
    have hsum : P.coeff d = ∑ i : Fin k, (Polynomial.C (t i) * Polynomial.X ^ (deg i)).coeff d := by
      simp [P]
    rw [hsum]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : ∃ i, deg i = d
    · simp only [h, dite_true]
      let i₀ := h.choose
      have hi₀ : deg i₀ = d := h.choose_spec
      rw [Finset.sum_eq_single i₀]
      · simp [i₀, hi₀]
      · intro j _ hne
        have hne_deg : d ≠ deg j := fun hEq => hne (hinj (hEq.symm.trans hi₀.symm))
        simp [hne_deg]
      · intro hnot; exact absurd (mem_univ i₀) hnot
    · simp only [h, dite_false]
      apply Finset.sum_eq_zero
      intro j _
      have hne_deg : d ≠ deg j := fun hEq => h ⟨j, hEq.symm⟩
      simp [hne_deg]
  have hPne : P ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    intro hzero
    have hc := hcoeff (deg i)
    have hex : ∃ j, deg j = deg i := ⟨i, rfl⟩
    rw [hzero, Polynomial.coeff_zero] at hc
    simp only [hex, dite_true] at hc
    have hch : hex.choose = i := hinj hex.choose_spec
    rw [hch] at hc
    exact hi hc.symm
  have hdeg_mem : P.natDegree ∈ Set.range deg := by
    have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
    rw [hcoeff] at hlead
    by_cases h : ∃ i, deg i = P.natDegree
    · exact h
    · simp only [h, dite_false] at hlead
      exact absurd rfl hlead
  have heval : Polynomial.aeval α P = ∑ i : Fin k, (t i : ℝ) * α ^ (deg i) := by
    simp only [P, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  rw [← heval]
  exact hnorm P hPne hdeg_mem

/-- Echelon-basis multidimensional Weyl theorem (Phase 17 Track A, Theorem 8): if `P : Fin k → ℤ[X]`
are nonzero integer polynomials with pairwise distinct degrees and every nonzero integer polynomial
whose degree lies in `Set.range (fun i => (P i).natDegree)` is normal at `α` in base `b`, then
`(P_1(α), …, P_k(α))` is jointly uniformly distributed in `[0, 1)^k`. -/
theorem jointUniform_of_echelon_degrees {b k : ℕ} {α : ℝ} (P : Fin k → Polynomial ℤ)
    (hne : ∀ i, P i ≠ 0)
    (hinj : Function.Injective (fun i => (P i).natDegree))
    (hnorm : ∀ Q : Polynomial ℤ, Q ≠ 0 → Q.natDegree ∈ Set.range (fun i => (P i).natDegree) →
      NormalIn b (Polynomial.aeval α Q)) :
    JointUniform b (fun i => Polynomial.aeval α (P i)) := by
  classical
  apply JointWeyl.rectangle_of_scalar_normal
  intro t ht
  let S : Finset (Fin k) := univ.filter (fun i => t i ≠ 0)
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  obtain ⟨i₀, hi₀S, hi₀max⟩ := S.exists_max_image (fun i => (P i).natDegree) hSne
  have hti₀ : t i₀ ≠ 0 := (mem_filter.mp hi₀S).2
  let Q : Polynomial ℤ := ∑ i : Fin k, Polynomial.C (t i) * P i
  have hQ_coeff : ∀ d : ℕ, Q.coeff d = ∑ i : Fin k, t i * (P i).coeff d := by
    intro d
    simp [Q]
  have hQ_lead : Q.coeff (P i₀).natDegree = t i₀ * (P i₀).leadingCoeff := by
    rw [hQ_coeff, Finset.sum_eq_single i₀]
    · rfl
    · intro j _ hji
      by_cases htj : t j = 0
      · simp [htj]
      · have hjS : j ∈ S := mem_filter.mpr ⟨mem_univ j, htj⟩
        have hle : (P j).natDegree ≤ (P i₀).natDegree := hi₀max j hjS
        have hlt : (P j).natDegree < (P i₀).natDegree :=
          lt_of_le_of_ne hle (fun heq => hji (hinj heq))
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    · intro hnot; exact absurd (mem_univ i₀) hnot
  have hQ_lead_ne : Q.coeff (P i₀).natDegree ≠ 0 := by
    rw [hQ_lead]
    exact mul_ne_zero hti₀ (Polynomial.leadingCoeff_ne_zero.mpr (hne i₀))
  have hQne : Q ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hQ_lead_ne
    exact hQ_lead_ne rfl
  have hQ_deg_le : Q.natDegree ≤ (P i₀).natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro d hd
    rw [hQ_coeff]
    apply Finset.sum_eq_zero
    intro j _
    by_cases htj : t j = 0
    · simp [htj]
    · have hjS : j ∈ S := mem_filter.mpr ⟨mem_univ j, htj⟩
      have hlt : (P j).natDegree < d := lt_of_le_of_lt (hi₀max j hjS) hd
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  have hQ_deg_ge : (P i₀).natDegree ≤ Q.natDegree :=
    Polynomial.le_natDegree_of_ne_zero hQ_lead_ne
  have hQ_deg : Q.natDegree = (P i₀).natDegree := le_antisymm hQ_deg_le hQ_deg_ge
  have heval : Polynomial.aeval α Q = ∑ i : Fin k, (t i : ℝ) * Polynomial.aeval α (P i) := by
    simp only [Q, map_sum, map_mul, Polynomial.aeval_C]
    rfl
  rw [← heval]
  exact hnorm Q hQne ⟨i₀, hQ_deg.symm⟩

/-! ## Section 4. Erdős–Borwein carry knapsack dual & parity Bonferroni inequality (Phase 17 Track C) -/

/-- Pointwise dual inequality of Track C Theorem 1(a): for any `D`, residue `r`,
nonnegative integer carry `c`, and dual weight `lam ≥ 0`, the indicator that the top bit of
`(r + c) % 2^D` is `1` is bounded above by the indicator `r ≥ 2^(D-1)` plus `lam * c` plus the
linear knapsack weight `max 0 (1 - lam * (2^(D-1) - r))` when `r < 2^(D-1)`. -/
theorem carry_knapsack_le {D r c : ℕ} {lam : ℝ}
    (hlam : 0 ≤ lam) :
    (if 2 ^ (D - 1) ≤ (r + c) % 2 ^ D then (1 : ℝ) else 0) ≤
      (if 2 ^ (D - 1) ≤ r then (1 : ℝ) else 0) + lam * (c : ℝ) +
      (if r < 2 ^ (D - 1) then max 0 (1 - lam * ((2 ^ (D - 1) - r : ℕ) : ℝ)) else 0) := by
  have hc0 : 0 ≤ lam * (c : ℝ) := mul_nonneg hlam (Nat.cast_nonneg c)
  by_cases hge : 2 ^ (D - 1) ≤ r
  · have hnotlt : ¬ r < 2 ^ (D - 1) := not_lt.mpr hge
    simp only [hge, ite_true, hnotlt, ite_false, add_zero]
    split_ifs <;> linarith
  · have hlt : r < 2 ^ (D - 1) := lt_of_not_ge hge
    simp only [hge, ite_false, hlt, ite_true, zero_add]
    by_cases htop : 2 ^ (D - 1) ≤ (r + c) % 2 ^ D
    · simp only [htop, ite_true]
      have hrc : 2 ^ (D - 1) ≤ r + c := le_trans htop (Nat.mod_le (r + c) (2 ^ D))
      have hcge : 2 ^ (D - 1) - r ≤ c := by omega
      have hcge_r : ((2 ^ (D - 1) - r : ℕ) : ℝ) ≤ (c : ℝ) := Nat.cast_le.mpr hcge
      have hmul : lam * ((2 ^ (D - 1) - r : ℕ) : ℝ) ≤ lam * (c : ℝ) :=
        mul_le_mul_of_nonneg_left hcge_r hlam
      have hmax : 1 - lam * ((2 ^ (D - 1) - r : ℕ) : ℝ) ≤
          max 0 (1 - lam * ((2 ^ (D - 1) - r : ℕ) : ℝ)) := le_max_right _ _
      linarith
    · simp only [htop, ite_false]
      have hmax0 : (0 : ℝ) ≤ max 0 (1 - lam * ((2 ^ (D - 1) - r : ℕ) : ℝ)) := le_max_left _ _
      linarith

private lemma parity_bonferroni_step (r n : ℕ) :
    (∑ k ∈ range (r + 1), (-2 : ℤ) ^ k * (Nat.choose (n + 1) k : ℤ)) +
      (∑ k ∈ range (r + 1), (-2 : ℤ) ^ k * (Nat.choose n k : ℤ)) =
      2 * (-2 : ℤ) ^ r * (Nat.choose n r : ℤ) := by
  have hrec : ∑ k ∈ range (r + 1), (-2 : ℤ) ^ k * (Nat.choose (n + 1) k : ℤ) =
      (1 : ℤ) + ∑ k ∈ range r, (-2 : ℤ) ^ (k + 1) * ((Nat.choose n k : ℤ) + (Nat.choose n (k + 1) : ℤ)) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.choose_succ_succ,
      Nat.cast_add, add_comm]
  rw [hrec]
  have hsplit : ∑ k ∈ range r, (-2 : ℤ) ^ (k + 1) * ((Nat.choose n k : ℤ) + (Nat.choose n (k + 1) : ℤ)) =
      (-2 : ℤ) * (∑ k ∈ range r, (-2 : ℤ) ^ k * (Nat.choose n k : ℤ)) +
      ∑ k ∈ range r, (-2 : ℤ) ^ (k + 1) * (Nat.choose n (k + 1) : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ']
    ring
  rw [hsplit]
  have hshift : (1 : ℤ) + ∑ k ∈ range r, (-2 : ℤ) ^ (k + 1) * (Nat.choose n (k + 1) : ℤ) =
      ∑ k ∈ range (r + 1), (-2 : ℤ) ^ k * (Nat.choose n k : ℤ) := by
    rw [Finset.sum_range_succ']
    simp [add_comm]
  have hlast : ∑ k ∈ range (r + 1), (-2 : ℤ) ^ k * (Nat.choose n k : ℤ) =
      (∑ k ∈ range r, (-2 : ℤ) ^ k * (Nat.choose n k : ℤ)) + (-2 : ℤ) ^ r * (Nat.choose n r : ℤ) :=
    Finset.sum_range_succ _ _
  linarith

/-- Parity Bonferroni dual inequality (Phase 17 Track C, Theorem 4): for every odd `r = 2m + 1`
and every nonnegative integer `n`, the truncated binomial expansion of `(1 - 2)^n` at degree `r`
is a pointwise lower bound on `(-1)^n`. -/
theorem parity_bonferroni_dual_le (m n : ℕ) :
    ∑ k ∈ range (2 * m + 2), (-2 : ℤ) ^ k * (Nat.choose n k : ℤ) ≤ (-1 : ℤ) ^ n := by
  let r := 2 * m + 1
  let Δ : ℕ → ℤ := fun t => (-1 : ℤ) ^ t - ∑ k ∈ range (r + 1), (-2 : ℤ) ^ k * (Nat.choose t k : ℤ)
  have hΔ_step : ∀ t, Δ (t + 1) + Δ t = 2 ^ (r + 1) * (Nat.choose t r : ℤ) := by
    intro t
    have hpow : (-1 : ℤ) ^ (t + 1) + (-1 : ℤ) ^ t = 0 := by rw [pow_succ]; ring
    have hneg : 2 * (-2 : ℤ) ^ r = -(2 : ℤ) ^ (r + 1) := by
      have : (-2 : ℤ) ^ r = -(2 : ℤ) ^ r := by
        change (-2 : ℤ) ^ (2 * m + 1) = -(2 : ℤ) ^ (2 * m + 1)
        rw [pow_succ, pow_succ, pow_mul, pow_mul]
        norm_num
      rw [this, pow_succ]
      ring
    have hs := parity_bonferroni_step r t
    rw [hneg] at hs
    dsimp only [Δ]
    linarith
  have hΔ_two : ∀ t, Δ t ≤ Δ (t + 2) := by
    intro t
    have h1 := hΔ_step t
    have h2 := hΔ_step (t + 1)
    have hch : (Nat.choose t r : ℤ) ≤ (Nat.choose (t + 1) r : ℤ) := by
      exact_mod_cast Nat.choose_le_succ t r
    have hpos : (0 : ℤ) ≤ (2 : ℤ) ^ (r + 1) := by positivity
    nlinarith
  have hΔ_base : ∀ t ≤ r, Δ t = 0 := by
    intro t ht
    have hbinom : ((-2 : ℤ) + 1) ^ t = ∑ k ∈ range (t + 1), (-2 : ℤ) ^ k * 1 ^ (t - k) * (Nat.choose t k : ℤ) :=
      add_pow (-2 : ℤ) 1 t
    have heq : ∑ k ∈ range (r + 1), (-2 : ℤ) ^ k * (Nat.choose t k : ℤ) =
        ∑ k ∈ range (t + 1), (-2 : ℤ) ^ k * (Nat.choose t k : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ hk
      have hgt : t < k := by
        rw [Finset.mem_range] at hk
        omega
      simp [Nat.choose_eq_zero_of_lt hgt]
    dsimp only [Δ]
    rw [heq]
    have h1 : ((-2 : ℤ) + 1) ^ t = (-1 : ℤ) ^ t := by norm_num
    rw [← h1, hbinom]
    simp
  have hΔ_nonneg : ∀ t, 0 ≤ Δ t := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      by_cases hle : t ≤ r
      · rw [hΔ_base t hle]
      · by_cases h1 : t = r + 1
        · subst h1
          have hs := hΔ_step r
          rw [hΔ_base r le_rfl] at hs
          have hpos : (0 : ℤ) ≤ (2 : ℤ) ^ (r + 1) * (Nat.choose r r : ℤ) := by positivity
          linarith
        · have ht2 : t - 2 < t := by omega
          have hsub : (t - 2) + 2 = t := by omega
          have hle2 := hΔ_two (t - 2)
          rw [hsub] at hle2
          exact le_trans (ih (t - 2) ht2) hle2
  have hn := hΔ_nonneg n
  dsimp only [Δ, r] at hn
  linarith

/-! ## Section 5. Minimized `(3, 31)` cyclic-descent closed-orbit certificate (Phase 17 Track A3.3) -/

/-- Modulus for the `(e, p) = (3, 31)` minimized cyclic-descent certificate. -/
def descent31P : ℕ := 31

/-- Reduced transition matrix `X₀` over `ℤ/31ℤ` (dimension 5). -/
def descent31X0 : List (List ℕ) :=
  [[1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1],
   [18, 7, 27, 24, 18], [18, 4, 24, 27, 21]]

/-- Reduced transition matrix `X₁` over `ℤ/31ℤ` (dimension 5). -/
def descent31X1 : List (List ℕ) :=
  [[0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [10, 12, 11, 20, 10],
   [4, 30, 23, 2, 4], [19, 0, 24, 1, 19]]

/-- Closed 57-vector orbit in `(ℤ/31ℤ)⁵` for the `(3, 31)` cyclic-descent automaton. -/
def descent31Orbit : List (List ℕ) :=
  [[1, 9, 21, 23, 22], [1, 21, 22, 15, 29], [9, 23, 6, 23, 3], [9, 6, 3, 6, 28],
   [23, 23, 23, 23, 23], [9, 3, 28, 3, 16], [6, 6, 6, 6, 6], [9, 28, 16, 28, 23],
   [3, 3, 3, 3, 3], [9, 16, 23, 16, 6], [28, 28, 28, 28, 28], [16, 16, 16, 16, 16],
   [1, 22, 29, 29, 1], [21, 15, 9, 15, 28], [21, 9, 28, 9, 4], [15, 15, 15, 15, 15],
   [21, 28, 4, 28, 18], [9, 9, 9, 9, 9], [21, 4, 18, 4, 15], [21, 18, 15, 18, 9],
   [4, 4, 4, 4, 4], [18, 18, 18, 18, 18], [1, 29, 1, 26, 25], [22, 29, 5, 29, 19],
   [22, 5, 19, 5, 16], [29, 29, 29, 29, 29], [22, 19, 16, 19, 10], [5, 5, 5, 5, 5],
   [22, 16, 10, 16, 29], [19, 19, 19, 19, 19], [22, 10, 29, 10, 5], [10, 10, 10, 10, 10],
   [1, 1, 25, 20, 21], [29, 26, 23, 26, 17], [29, 23, 17, 23, 5], [26, 26, 26, 26, 26],
   [29, 17, 5, 17, 12], [29, 5, 12, 5, 26], [17, 17, 17, 17, 17], [29, 12, 26, 12, 23],
   [12, 12, 12, 12, 12], [1, 25, 21, 8, 22], [1, 20, 8, 20, 15], [1, 8, 15, 8, 29],
   [20, 20, 20, 20, 20], [1, 15, 29, 15, 26], [8, 8, 8, 8, 8], [1, 29, 26, 29, 20],
   [1, 26, 20, 26, 8], [25, 8, 22, 8, 19], [25, 22, 19, 22, 13], [25, 19, 13, 19, 1],
   [22, 22, 22, 22, 22], [25, 13, 1, 13, 8], [25, 1, 8, 1, 22], [13, 13, 13, 13, 13],
   [1, 1, 1, 1, 1]]

/-- Successor table `(succ₀, succ₁)` indexing into `descent31Orbit`. -/
def descent31Succ : List (List ℕ) :=
  [[1, 2], [12, 13], [3, 4], [5, 6], [4, 4], [7, 8], [6, 6], [9, 10], [8, 8], [2, 11],
   [10, 10], [11, 11], [22, 23], [14, 15], [16, 17], [15, 15], [18, 10], [17, 17], [19, 20],
   [13, 21], [20, 20], [21, 21], [32, 33], [24, 25], [26, 27], [25, 25], [28, 29], [27, 27],
   [30, 11], [29, 29], [23, 31], [31, 31], [41, 42], [34, 35], [36, 4], [35, 35], [37, 38],
   [39, 27], [38, 38], [33, 40], [40, 40], [1, 49], [43, 44], [45, 46], [44, 44], [47, 15],
   [46, 46], [48, 25], [42, 35], [50, 46], [51, 52], [53, 29], [52, 52], [54, 55], [49, 56],
   [55, 55], [56, 56]]

/-- Matrix-vector multiplication modulo `31`. -/
def descent31MulVec (M : List (List ℕ)) (v : List ℕ) : List ℕ :=
  M.map fun row => ((List.zipWith (fun a b => a * b) row v).foldl (fun a b => a + b) 0) % descent31P

/-- Iterate the reduced `(3, 31)` automaton along a binary word `w`. -/
def descent31Run : List Bool → List ℕ → List ℕ
  | [], v => v
  | false :: w, v => descent31Run w (descent31MulVec descent31X0 v)
  | true :: w, v => descent31Run w (descent31MulVec descent31X1 v)

/-- Finite certificate check: every orbit vector has first coordinate nonzero mod 31, and both
transition matrices map every orbit vector to its listed in-bounds successor. -/
def descent31Check : Bool :=
  (List.range descent31Orbit.length).all fun i =>
    let s0 := (descent31Succ.getD i []).getD 0 0
    let s1 := (descent31Succ.getD i []).getD 1 0
    s0 < descent31Orbit.length &&
    s1 < descent31Orbit.length &&
    (descent31Orbit.getD i []).headD 0 % descent31P != 0 &&
    descent31MulVec descent31X0 (descent31Orbit.getD i []) == descent31Orbit.getD s0 [] &&
    descent31MulVec descent31X1 (descent31Orbit.getD i []) == descent31Orbit.getD s1 []

/-- Kernel-checked verification of the 57-vector `(3, 31)` minimized cyclic-descent orbit. -/
theorem descent31Check_true : descent31Check = true := by decide

private lemma descent31_step_and_nonzero {i : ℕ} (hi : i < descent31Orbit.length) :
    (descent31Succ.getD i []).getD 0 0 < descent31Orbit.length ∧
    (descent31Succ.getD i []).getD 1 0 < descent31Orbit.length ∧
    (descent31Orbit.getD i []).headD 0 % descent31P ≠ 0 ∧
    descent31MulVec descent31X0 (descent31Orbit.getD i []) =
      descent31Orbit.getD ((descent31Succ.getD i []).getD 0 0) [] ∧
    descent31MulVec descent31X1 (descent31Orbit.getD i []) =
      descent31Orbit.getD ((descent31Succ.getD i []).getD 1 0) [] := by
  have hall := List.all_eq_true.mp descent31Check_true i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq] at hall
  exact ⟨hall.1.1.1.1, hall.1.1.1.2, hall.1.1.2, hall.1.2, hall.2⟩

/-- For every finite binary word `w`, running the minimized `(3, 31)` cyclic-descent automaton from
any orbit state stays inside `descent31Orbit` and ends with first coordinate nonzero modulo `31`. -/
theorem descent31_all_words_nonzero (w : List Bool) :
    ∀ i < descent31Orbit.length,
      (descent31Run w (descent31Orbit.getD i [])).headD 0 % descent31P ≠ 0 := by
  induction w with
  | nil =>
    intro i hi
    exact (descent31_step_and_nonzero hi).2.2.1
  | cons b w ih =>
    intro i hi
    have hstep := descent31_step_and_nonzero hi
    cases b with
    | false =>
      simp only [descent31Run, hstep.2.2.2.1]
      exact ih _ hstep.1
    | true =>
      simp only [descent31Run, hstep.2.2.2.2]
      exact ih _ hstep.2.1

end NormalityChecker.Phase17DiscrepancyBounds
