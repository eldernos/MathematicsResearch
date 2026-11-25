module

public import NormalityChecker.BinaryDiscrepancy
public import Mathlib.Computability.Halting
public import Mathlib.RingTheory.Algebraic.Basic

/-! Kernel-checked computability and undecidability of binary normality classification (Phase 17 Track F2).

Given any two binary digit oracles `a, b : ℕ → Bool` representing:
- a transcendental binary-normal real `α₀ = binarySeries a`, and
- a transcendental real `α₁ = binarySeries b` with limiting binary discrepancy `1`,

we construct for every partial recursive program code `c : Nat.Partrec.Code` the switched binary
sequence `switchedDigit a b c n`, which outputs `a n` while `evaln n c 0` has not halted and
switches permanently to `b n` once `c` halts on input `0`.

We prove unconditionally in Lean:
1. If `a` and `b` are computable, then `(c, n) ↦ switchedDigit a b c n` is computable.
2. Every switched real `x_c = binarySeries (switchedDigit a b c)` differs from `α₀` or `α₁` by a
   dyadic rational, hence is transcendental over `ℚ` and satisfies the promise
   `Tendsto (binaryDiscrepancy x_c) atTop (𝓝 0) ∨ Tendsto (binaryDiscrepancy x_c) atTop (𝓝 1)`.
3. `NormalIn 2 x_c ↔ ¬ (c.eval 0).Dom`, while the reversed construction satisfies
   `NormalIn 2 y_c ↔ (c.eval 0).Dom`.
4. Consequently, both directly on the switched-parameter family (`normality_not_computable`,
   `normality_not_re`, `normality_not_co_re`) and uniformly over arbitrary digit-oracle codes
   `Nat.Partrec.Code` via s-m-n parameter specialization (`Names`,
   `no_computable_normality_decider_on_names`, `no_re_normality_recognizer_on_names`,
   `no_re_nonnormality_recognizer_on_names`), recognizing binary normality of computable
   transcendental reals under the promise `D_N → 0` or `D_N → 1` is neither computable
   (`¬ ComputablePred`), nor recursively enumerable (`¬ REPred`), nor co-recursively enumerable.
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace NormalityChecker.ComputableNormalityUndecidability

/-- The real number in `[0, 1]` encoded by a binary digit sequence `d : ℕ → Bool`. -/
noncomputable def binarySeries (d : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, if d n then (2 : ℝ)⁻¹ ^ (n + 1) else 0

lemma summable_binarySeries (d : ℕ → Bool) :
    Summable (fun n : ℕ => if d n then (2 : ℝ)⁻¹ ^ (n + 1) else 0) := by
  have hgeom : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_left (2 : ℝ)⁻¹
    simpa [pow_succ'] using h
  refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_) hgeom
  split_ifs
  · exact le_rfl
  · positivity

/-- If two binary digit sequences agree from index `t` onward, their real values differ by a
dyadic rational `m / 2^t`. -/
theorem binarySeries_finite_edit_dyadic {d₁ d₂ : ℕ → Bool} {t : ℕ}
    (h : ∀ n ≥ t, d₁ n = d₂ n) :
    ∃ m : ℤ, binarySeries d₁ - binarySeries d₂ = (m : ℝ) / (2 : ℝ) ^ t := by
  let f : ℕ → ℝ := fun n =>
    (if d₁ n then (2 : ℝ)⁻¹ ^ (n + 1) else 0) - (if d₂ n then (2 : ℝ)⁻¹ ^ (n + 1) else 0)
  have hsub : binarySeries d₁ - binarySeries d₂ = ∑' n : ℕ, f n :=
    ((summable_binarySeries d₁).tsum_sub (summable_binarySeries d₂)).symm
  have hzero : ∀ n ∉ range t, f n = 0 := by
    intro n hn
    have hge : t ≤ n := Nat.le_of_not_lt (by simpa [mem_range] using hn)
    simp only [f, h n hge, sub_self]
  have hfin : ∑' n : ℕ, f n = ∑ n ∈ range t, f n := tsum_eq_sum hzero
  refine ⟨∑ n ∈ range t,
      ((if d₁ n then (1 : ℤ) else 0) - (if d₂ n then 1 else 0)) * (2 : ℤ) ^ (t - 1 - n), ?_⟩
  rw [hsub, hfin]
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro n hn
  have hlt : n < t := mem_range.mp hn
  have hpow : ((2 : ℝ) ^ (t - 1 - n)) / (2 : ℝ) ^ t = (2 : ℝ)⁻¹ ^ (n + 1) := by
    have hsum_exp : (n + 1) + (t - 1 - n) = t := by omega
    rw [inv_pow, div_eq_iff (by positivity : (2 : ℝ) ^ t ≠ 0), eq_comm,
      inv_mul_eq_iff_eq_mul₀ (by positivity : (2 : ℝ) ^ (n + 1) ≠ 0), ← pow_add, hsum_exp]
  dsimp only [f]
  cases d₁ n <;> cases d₂ n <;> simp [hpow, neg_div]

/-- Adding a rational number preserves transcendence over `ℚ`. -/
theorem transcendental_add_rat {x : ℝ} (hx : Transcendental ℚ x) (q : ℚ) :
    Transcendental ℚ (x + (q : ℝ)) := by
  intro halg
  apply hx
  obtain ⟨p, hp0, hpeval⟩ := halg
  refine ⟨p.comp (Polynomial.X + Polynomial.C q), ?_, ?_⟩
  · intro hcomp
    apply hp0
    have hback := congrArg (fun r => r.comp (Polynomial.X - Polynomial.C q)) hcomp
    simp only [Polynomial.zero_comp, Polynomial.comp_assoc, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X] at hback
    exact hback
  · rw [Polynomial.aeval_comp, map_add, Polynomial.aeval_X, Polynomial.aeval_C]
    simpa using hpeval

/-- Adding a dyadic rational `m / 2^t` leaves all binary shifts from index `t` onward unchanged. -/
theorem shift_add_dyadic_eq {x : ℝ} {m : ℤ} {t n : ℕ} (hn : t ≤ n) :
    shift 2 (x + (m : ℝ) / (2 : ℝ) ^ t) n = shift 2 x n := by
  unfold shift
  have hmul : (2 : ℝ) ^ n * (x + (m : ℝ) / (2 : ℝ) ^ t) =
      (2 : ℝ) ^ n * x + ((m * (2 : ℤ) ^ (n - t) : ℤ) : ℝ) := by
    have hsplit : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - t) * (2 : ℝ) ^ t := by
      rw [← pow_add]; congr 1; omega
    have h2t : (2 : ℝ) ^ t ≠ 0 := by positivity
    push_cast
    rw [mul_add, hsplit]
    field_simp [h2t]
  simp only [Nat.cast_ofNat]
  rw [hmul, Int.fract_add_intCast]

private lemma frequency_sub_le_of_eventually_eq {u v : ℕ → ℝ} {t N : ℕ}
    (h : ∀ n ≥ t, u n = v n) (a c : ℝ) :
    |frequency u a c N - frequency v a c N| ≤ (t : ℝ) / (N : ℝ) := by
  classical
  by_cases hN : N = 0
  · subst hN; simp [frequency]
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  let A := (range N).filter (fun n => a ≤ u n ∧ u n < c)
  let B := (range N).filter (fun n => a ≤ v n ∧ v n < c)
  have hAB : A.card ≤ B.card + t := by
    have hsub : A ⊆ B ∪ range t := by
      intro n hn
      by_cases hlt : n < t
      · exact mem_union_right _ (mem_range.mpr hlt)
      · have hge : t ≤ n := Nat.le_of_not_lt hlt
        obtain ⟨hnN, h1, h2⟩ := mem_filter.mp hn
        rw [h n hge] at h1 h2
        exact mem_union_left _ (mem_filter.mpr ⟨hnN, h1, h2⟩)
    exact (card_le_card hsub).trans ((card_union_le B (range t)).trans_eq (by rw [card_range]))
  have hBA : B.card ≤ A.card + t := by
    have hsub : B ⊆ A ∪ range t := by
      intro n hn
      by_cases hlt : n < t
      · exact mem_union_right _ (mem_range.mpr hlt)
      · have hge : t ≤ n := Nat.le_of_not_lt hlt
        obtain ⟨hnN, h1, h2⟩ := mem_filter.mp hn
        rw [← h n hge] at h1 h2
        exact mem_union_left _ (mem_filter.mpr ⟨hnN, h1, h2⟩)
    exact (card_le_card hsub).trans ((card_union_le A (range t)).trans_eq (by rw [card_range]))
  have hABr : (A.card : ℝ) ≤ (B.card : ℝ) + (t : ℝ) := by exact_mod_cast hAB
  have hBAr : (B.card : ℝ) ≤ (A.card : ℝ) + (t : ℝ) := by exact_mod_cast hBA
  unfold frequency
  change |(A.card : ℝ) / (N : ℝ) - (B.card : ℝ) / (N : ℝ)| ≤ (t : ℝ) / (N : ℝ)
  rw [← sub_div, abs_div, abs_of_pos hNpos]
  apply div_le_div_of_nonneg_right _ hNpos.le
  rw [abs_le]
  constructor <;> linarith

/-- If two reals have identical binary shifts from index `t` onward, their binary discrepancies
at cutoff `N` differ by at most `t / N`. -/
theorem binaryDiscrepancy_sub_le_of_eventually_eq {x y : ℝ} {t N : ℕ}
    (h : ∀ n ≥ t, shift 2 x n = shift 2 y n) :
    |binaryDiscrepancy x N - binaryDiscrepancy y N| ≤ (t : ℝ) / (N : ℝ) := by
  have hxy : binaryDiscrepancy x N ≤ binaryDiscrepancy y N + (t : ℝ) / (N : ℝ) := by
    apply discrepancy_le
    intro a c ha hac hc
    have hf := abs_le.mp (frequency_sub_le_of_eventually_eq h a c (N := N))
    have hy := abs_le.mp (interval_le_discrepancy y N ha hac hc)
    rw [abs_le]
    constructor <;> linarith
  have hyx : binaryDiscrepancy y N ≤ binaryDiscrepancy x N + (t : ℝ) / (N : ℝ) := by
    apply discrepancy_le
    intro a c ha hac hc
    have h' : ∀ n ≥ t, shift 2 y n = shift 2 x n := fun n hn => (h n hn).symm
    have hf := abs_le.mp (frequency_sub_le_of_eventually_eq h' a c (N := N))
    have hx := abs_le.mp (interval_le_discrepancy x N ha hac hc)
    rw [abs_le]
    constructor <;> linarith
  rw [abs_le]
  constructor <;> linarith

/-- Adding a dyadic rational preserves any limiting binary discrepancy value `L`. -/
theorem binaryDiscrepancy_tendsto_iff_add_dyadic (x : ℝ) (m : ℤ) (t : ℕ) (L : ℝ) :
    Tendsto (binaryDiscrepancy (x + (m : ℝ) / (2 : ℝ) ^ t)) atTop (𝓝 L) ↔
      Tendsto (binaryDiscrepancy x) atTop (𝓝 L) := by
  have hdiff : Tendsto (fun N : ℕ =>
      binaryDiscrepancy (x + (m : ℝ) / (2 : ℝ) ^ t) N - binaryDiscrepancy x N) atTop (𝓝 0) := by
    apply squeeze_zero_norm
    · intro N
      simpa only [Real.norm_eq_abs] using
        binaryDiscrepancy_sub_le_of_eventually_eq (fun n hn => shift_add_dyadic_eq hn) (N := N)
    · exact tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)
  constructor
  · intro h1
    have h2 := h1.sub hdiff
    simpa only [sub_sub_cancel, sub_zero] using h2
  · intro h1
    have h2 := h1.add hdiff
    simpa only [add_sub_cancel, add_zero] using h2

private lemma discrepancy_tendsto_zero_iff (y : ℝ) :
    asymptoticDiscrepancy y = 0 ↔ Tendsto (binaryDiscrepancy y) atTop (𝓝 0) := by
  have hbu : IsBoundedUnder (· ≤ ·) atTop (binaryDiscrepancy y) :=
    isBoundedUnder_of_eventually_le (.of_forall fun N => (discrepancy_bounds y N).2)
  have hbl : IsBoundedUnder (· ≥ ·) atTop (binaryDiscrepancy y) :=
    isBoundedUnder_of_eventually_ge (.of_forall fun N => (discrepancy_bounds y N).1)
  constructor
  · intro hz
    apply tendsto_of_liminf_eq_limsup _ hz hbu hbl
    exact le_antisymm
      (hz ▸ liminf_le_limsup hbu hbl)
      (le_liminf_of_le (isCoboundedUnder_ge_of_le _ fun N => (discrepancy_bounds y N).2)
        (.of_forall fun N => (discrepancy_bounds y N).1))
  · exact Tendsto.limsup_eq

/-- Adding a dyadic rational preserves binary normality. -/
theorem normalIn_two_iff_add_dyadic (x : ℝ) (m : ℤ) (t : ℕ) :
    NormalIn 2 (x + (m : ℝ) / (2 : ℝ) ^ t) ↔ NormalIn 2 x := by
  rw [normal_iff_discrepancy_zero, normal_iff_discrepancy_zero,
    discrepancy_tendsto_zero_iff, discrepancy_tendsto_zero_iff,
    binaryDiscrepancy_tendsto_iff_add_dyadic]

/-- The switched binary digit sequence: follows `a` while program `c` has not halted on input `0`
within `n` bounded-evaluation steps, and switches permanently to `b` once `c` halts. -/
def switchedDigit (a b : ℕ → Bool) (c : Nat.Partrec.Code) (n : ℕ) : Bool :=
  if (Nat.Partrec.Code.evaln n c 0).isSome then b n else a n

/-- Uniform computability of the switched binary digit oracle `(c, n) ↦ switchedDigit a b c n`. -/
theorem switchedDigit_computable {a b : ℕ → Bool} (ha : Computable a) (hb : Computable b) :
    Computable (fun p : Nat.Partrec.Code × ℕ => switchedDigit a b p.1 p.2) := by
  have heval : Computable (fun p : Nat.Partrec.Code × ℕ => Nat.Partrec.Code.evaln p.2 p.1 0) := by
    have hp := Nat.Partrec.Code.primrec_evaln.to_comp
    have htriple : Computable (fun p : Nat.Partrec.Code × ℕ => ((p.2, p.1), (0 : ℕ))) :=
      Computable.pair (Computable.pair Computable.snd Computable.fst) (Computable.const 0)
    simpa using hp.comp htriple
  have hisSome : Computable (fun p : Nat.Partrec.Code × ℕ =>
      (Nat.Partrec.Code.evaln p.2 p.1 0).isSome) :=
    (Primrec.option_isSome.to_comp).comp heval
  simpa only [switchedDigit, Bool.cond_eq_ite] using
    Computable.cond hisSome (hb.comp Computable.snd) (ha.comp Computable.snd)

/-- Fundamental promise and halting-problem reduction for the switched real `binarySeries (switchedDigit a b c)`:
for every program code `c`, the real is transcendental over `ℚ`, has limiting binary discrepancy
in `{0, 1}`, and is binary normal if and only if `c` does not halt on input `0`. -/
theorem switched_real_promise_and_reduction {a b : ℕ → Bool}
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1))
    (c : Nat.Partrec.Code) :
    Transcendental ℚ (binarySeries (switchedDigit a b c)) ∧
    (Tendsto (binaryDiscrepancy (binarySeries (switchedDigit a b c))) atTop (𝓝 0) ∨
      Tendsto (binaryDiscrepancy (binarySeries (switchedDigit a b c))) atTop (𝓝 1)) ∧
    (NormalIn 2 (binarySeries (switchedDigit a b c)) ↔ ¬ (Nat.Partrec.Code.eval c 0).Dom) := by
  have ha_disc : Tendsto (binaryDiscrepancy (binarySeries a)) atTop (𝓝 0) :=
    (discrepancy_tendsto_zero_iff _).mp ((normal_iff_discrepancy_zero _).mp ha_norm)
  have hb_not_norm : ¬ NormalIn 2 (binarySeries b) := by
    intro hbn
    have hz : asymptoticDiscrepancy (binarySeries b) = 0 :=
      (normal_iff_discrepancy_zero _).mp hbn
    have h1 : asymptoticDiscrepancy (binarySeries b) = 1 := hb_disc.limsup_eq
    linarith
  by_cases hdom : (Nat.Partrec.Code.eval c 0).Dom
  · obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    have hagree : ∀ n ≥ t, switchedDigit a b c n = b n := by
      intro n hn
      have hmem : x ∈ Nat.Partrec.Code.evaln n c 0 := Nat.Partrec.Code.evaln_mono hn ht
      have hsome : (Nat.Partrec.Code.evaln n c 0).isSome = true := by
        rw [Option.mem_def] at hmem
        simp [hmem]
      simp [switchedDigit, hsome]
    obtain ⟨m, hm⟩ := binarySeries_finite_edit_dyadic hagree
    have heq : binarySeries (switchedDigit a b c) = binarySeries b + (m : ℝ) / (2 : ℝ) ^ t := by
      linarith
    have hrat : (m : ℝ) / (2 : ℝ) ^ t = ((m / (2 : ℚ) ^ t : ℚ) : ℝ) := by push_cast; rfl
    refine ⟨?_, Or.inr ?_, ?_⟩
    · rw [heq, hrat]
      exact transcendental_add_rat hb_tr _
    · rw [heq]
      exact (binaryDiscrepancy_tendsto_iff_add_dyadic _ m t 1).mpr hb_disc
    · rw [heq, normalIn_two_iff_add_dyadic]
      exact iff_of_false hb_not_norm (not_not.mpr hdom)
  · have hagree : ∀ n, switchedDigit a b c n = a n := by
      intro n
      have hnone : Nat.Partrec.Code.evaln n c 0 = none := by
        cases hopt : Nat.Partrec.Code.evaln n c 0 with
        | none => rfl
        | some x =>
          exfalso
          apply hdom
          exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound hopt⟩
      simp [switchedDigit, hnone]
    have heq : binarySeries (switchedDigit a b c) = binarySeries a := by
      congr 1; funext n; exact hagree n
    rw [heq]
    exact ⟨ha_tr, Or.inl ha_disc, iff_of_true ha_norm hdom⟩

/-- Reversed reduction: `switchedDigit b a c` yields a transcendental real with limiting discrepancy
in `{0, 1}` that is binary normal if and only if `c` halts on input `0`. -/
theorem reversed_switched_real_reduction {a b : ℕ → Bool}
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1))
    (c : Nat.Partrec.Code) :
    Transcendental ℚ (binarySeries (switchedDigit b a c)) ∧
    (Tendsto (binaryDiscrepancy (binarySeries (switchedDigit b a c))) atTop (𝓝 0) ∨
      Tendsto (binaryDiscrepancy (binarySeries (switchedDigit b a c))) atTop (𝓝 1)) ∧
    (NormalIn 2 (binarySeries (switchedDigit b a c)) ↔ (Nat.Partrec.Code.eval c 0).Dom) := by
  have ha_disc : Tendsto (binaryDiscrepancy (binarySeries a)) atTop (𝓝 0) :=
    (discrepancy_tendsto_zero_iff _).mp ((normal_iff_discrepancy_zero _).mp ha_norm)
  have hb_not_norm : ¬ NormalIn 2 (binarySeries b) := by
    intro hbn
    have hz : asymptoticDiscrepancy (binarySeries b) = 0 :=
      (normal_iff_discrepancy_zero _).mp hbn
    have h1 : asymptoticDiscrepancy (binarySeries b) = 1 := hb_disc.limsup_eq
    linarith
  by_cases hdom : (Nat.Partrec.Code.eval c 0).Dom
  · obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    have hagree : ∀ n ≥ t, switchedDigit b a c n = a n := by
      intro n hn
      have hmem : x ∈ Nat.Partrec.Code.evaln n c 0 := Nat.Partrec.Code.evaln_mono hn ht
      have hsome : (Nat.Partrec.Code.evaln n c 0).isSome = true := by
        rw [Option.mem_def] at hmem
        simp [hmem]
      simp [switchedDigit, hsome]
    obtain ⟨m, hm⟩ := binarySeries_finite_edit_dyadic hagree
    have heq : binarySeries (switchedDigit b a c) = binarySeries a + (m : ℝ) / (2 : ℝ) ^ t := by
      linarith
    have hrat : (m : ℝ) / (2 : ℝ) ^ t = ((m / (2 : ℚ) ^ t : ℚ) : ℝ) := by push_cast; rfl
    refine ⟨?_, Or.inl ?_, ?_⟩
    · rw [heq, hrat]
      exact transcendental_add_rat ha_tr _
    · rw [heq]
      exact (binaryDiscrepancy_tendsto_iff_add_dyadic _ m t 0).mpr ha_disc
    · rw [heq, normalIn_two_iff_add_dyadic]
      exact iff_of_true ha_norm hdom
  · have hagree : ∀ n, switchedDigit b a c n = b n := by
      intro n
      have hnone : Nat.Partrec.Code.evaln n c 0 = none := by
        cases hopt : Nat.Partrec.Code.evaln n c 0 with
        | none => rfl
        | some x =>
          exfalso
          apply hdom
          exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound hopt⟩
      simp [switchedDigit, hnone]
    have heq : binarySeries (switchedDigit b a c) = binarySeries b := by
      congr 1; funext n; exact hagree n
    rw [heq]
    exact ⟨hb_tr, Or.inr hb_disc, iff_of_false hb_not_norm hdom⟩

/-- Binary normality is not decidable (`¬ ComputablePred`), even under the promise that the input
code specifies a computable transcendental real with limiting binary discrepancy in `{0, 1}`. -/
theorem normality_not_computable {a b : ℕ → Bool}
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1)) :
    ¬ ComputablePred (fun c : Nat.Partrec.Code => NormalIn 2 (binarySeries (switchedDigit a b c))) := by
  intro hcomp
  have hhalt : ComputablePred (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) := by
    have hnot := hcomp.not
    exact hnot.of_eq (fun c => by
      have hiff := (switched_real_promise_and_reduction ha_tr ha_norm hb_tr hb_disc c).2.2
      rw [hiff, not_not])
  exact ComputablePred.halting_problem 0 hhalt

/-- Binary normality is not recursively enumerable (`¬ REPred`) on the same computable transcendental
`{0, 1}`-discrepancy promise family. -/
theorem normality_not_re {a b : ℕ → Bool}
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1)) :
    ¬ REPred (fun c : Nat.Partrec.Code => NormalIn 2 (binarySeries (switchedDigit a b c))) := by
  intro hre
  have hnot_re : REPred (fun c : Nat.Partrec.Code => ¬ (Nat.Partrec.Code.eval c 0).Dom) :=
    hre.of_eq (fun c => (switched_real_promise_and_reduction ha_tr ha_norm hb_tr hb_disc c).2.2)
  exact ComputablePred.halting_problem_not_re 0 hnot_re

/-- Binary normality is not co-recursively enumerable (`¬ REPred` for its complement) on the reversed
computable transcendental `{0, 1}`-discrepancy promise family. -/
theorem normality_not_co_re {a b : ℕ → Bool}
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1)) :
    ¬ REPred (fun c : Nat.Partrec.Code => ¬ NormalIn 2 (binarySeries (switchedDigit b a c))) := by
  intro hcore
  have hnot_re : REPred (fun c : Nat.Partrec.Code => ¬ (Nat.Partrec.Code.eval c 0).Dom) :=
    hcore.of_eq (fun c => not_congr (reversed_switched_real_reduction ha_tr ha_norm hb_tr hb_disc c).2.2)
  exact ComputablePred.halting_problem_not_re 0 hnot_re

/-- Program code `code` is a total binary digit oracle for `s : ℕ → Bool`, returning `(s n).toNat`
on every natural index `n`. -/
def Names (code : Nat.Partrec.Code) (s : ℕ → Bool) : Prop :=
  ∀ n : ℕ, code.eval n = Part.some (s n).toNat

/-- Promise predicate for a binary digit stream `s`: its real value is transcendental over `ℚ`
and its binary discrepancy converges to either `0` or `1`. -/
def TranscendentalZeroOnePromise (s : ℕ → Bool) : Prop :=
  Transcendental ℚ (binarySeries s) ∧
  (Tendsto (binaryDiscrepancy (binarySeries s)) atTop (𝓝 0) ∨
    Tendsto (binaryDiscrepancy (binarySeries s)) atTop (𝓝 1))

/-- s-m-n parameter specialization: given computable digit oracles `a` and `b`, there is a total
computable map `f : Nat.Partrec.Code → Nat.Partrec.Code` sending every program code `c` to a digit
oracle code naming `switchedDigit a b c`. -/
theorem exists_switchedDigit_index_map {a b : ℕ → Bool}
    (ha : Computable a) (hb : Computable b) :
    ∃ f : Nat.Partrec.Code → Nat.Partrec.Code,
      Computable f ∧ ∀ c : Nat.Partrec.Code, Names (f c) (switchedDigit a b c) := by
  have htoNat : Computable (fun x : Bool => x.toNat) := by
    have h := Computable.cond (Computable.id (α := Bool)) (Computable.const (1 : ℕ)) (Computable.const 0)
    exact h.of_eq (fun x => by cases x <;> rfl)
  have hsw : Computable (fun p : Nat.Partrec.Code × ℕ => (switchedDigit a b p.1 p.2).toNat) :=
    htoNat.comp (switchedDigit_computable ha hb)
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hsw.partrec
  refine ⟨fun c => u.curry (Encodable.encode c), ?_, ?_⟩
  · exact (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode).to_comp
  · intro c n
    rw [Nat.Partrec.Code.eval_curry, hu]
    change (Part.ofOption (Encodable.decode (α := Nat.Partrec.Code × ℕ) (Encodable.encode (c, n)))).bind
      (fun p => Part.some (Encodable.encode (switchedDigit a b p.1 p.2).toNat)) =
      Part.some (switchedDigit a b c n).toNat
    simp

/-- No recursively enumerable predicate on arbitrary digit-oracle codes `Nat.Partrec.Code` can
recognize binary normality even under the promise that the named real is transcendental with
limiting binary discrepancy in `{0, 1}`. -/
theorem no_re_normality_recognizer_on_names {a b : ℕ → Bool}
    (ha_comp : Computable a) (hb_comp : Computable b)
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1)) :
    ¬ ∃ P : Nat.Partrec.Code → Prop,
        REPred P ∧ ∀ code s, Names code s → TranscendentalZeroOnePromise s →
          (P code ↔ NormalIn 2 (binarySeries s)) := by
  rintro ⟨P, hP_re, hP_spec⟩
  obtain ⟨f, hf_comp, hf_names⟩ := exists_switchedDigit_index_map ha_comp hb_comp
  have hpull : REPred (fun c : Nat.Partrec.Code => P (f c)) := hP_re.comp hf_comp
  have heq : REPred (fun c : Nat.Partrec.Code => NormalIn 2 (binarySeries (switchedDigit a b c))) :=
    hpull.of_eq (fun c => by
      have hred := switched_real_promise_and_reduction ha_tr ha_norm hb_tr hb_disc c
      exact hP_spec (f c) (switchedDigit a b c) (hf_names c) ⟨hred.1, hred.2.1⟩)
  exact normality_not_re ha_tr ha_norm hb_tr hb_disc heq

/-- No recursively enumerable predicate on arbitrary digit-oracle codes `Nat.Partrec.Code` can
recognize binary nonnormality under the same transcendental `{0, 1}`-discrepancy promise. -/
theorem no_re_nonnormality_recognizer_on_names {a b : ℕ → Bool}
    (ha_comp : Computable a) (hb_comp : Computable b)
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1)) :
    ¬ ∃ P : Nat.Partrec.Code → Prop,
        REPred P ∧ ∀ code s, Names code s → TranscendentalZeroOnePromise s →
          (P code ↔ ¬ NormalIn 2 (binarySeries s)) := by
  rintro ⟨P, hP_re, hP_spec⟩
  obtain ⟨g, hg_comp, hg_names⟩ := exists_switchedDigit_index_map hb_comp ha_comp
  have hpull : REPred (fun c : Nat.Partrec.Code => P (g c)) := hP_re.comp hg_comp
  have heq : REPred (fun c : Nat.Partrec.Code => ¬ NormalIn 2 (binarySeries (switchedDigit b a c))) :=
    hpull.of_eq (fun c => by
      have hred := reversed_switched_real_reduction ha_tr ha_norm hb_tr hb_disc c
      exact hP_spec (g c) (switchedDigit b a c) (hg_names c) ⟨hred.1, hred.2.1⟩)
  exact normality_not_co_re ha_tr ha_norm hb_tr hb_disc heq

/-- No computable predicate on arbitrary digit-oracle codes `Nat.Partrec.Code` can decide binary
normality under the transcendental `{0, 1}`-discrepancy promise. -/
theorem no_computable_normality_decider_on_names {a b : ℕ → Bool}
    (ha_comp : Computable a) (hb_comp : Computable b)
    (ha_tr : Transcendental ℚ (binarySeries a))
    (ha_norm : NormalIn 2 (binarySeries a))
    (hb_tr : Transcendental ℚ (binarySeries b))
    (hb_disc : Tendsto (binaryDiscrepancy (binarySeries b)) atTop (𝓝 1)) :
    ¬ ∃ P : Nat.Partrec.Code → Prop,
        ComputablePred P ∧ ∀ code s, Names code s → TranscendentalZeroOnePromise s →
          (P code ↔ NormalIn 2 (binarySeries s)) := by
  rintro ⟨P, hP_comp, hP_spec⟩
  exact no_re_normality_recognizer_on_names ha_comp hb_comp ha_tr ha_norm hb_tr hb_disc
    ⟨P, hP_comp.to_re, hP_spec⟩

end NormalityChecker.ComputableNormalityUndecidability
