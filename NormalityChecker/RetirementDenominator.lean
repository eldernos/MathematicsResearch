module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic

/-! # Reduced denominators of valuation-scheduled prefixes

The insertion at position `a k`, for `k ≥ 1`, has weight
`1 / p^(s * padicValNat p k)`. If the positions are multiples of the order
of the radix modulo `p`, all terms in the deepest layer have the same
nonzero residue after clearing denominators. The layer contains exactly
`K / p^(Nat.log p K)` terms through insertion `K`.
-/

@[expose] public section
open Finset
namespace NormalityChecker.RetirementDenominator

/-- The rational sum through insertion `K`, shifted by `n` radix places.
The index `i` in the sum represents insertion `i + 1`. -/
def shiftedPrefix (b p s : ℕ) (a : ℕ → ℕ) (K n : ℕ) : ℚ :=
  (b : ℚ)^n * ∑ i ∈ range K,
    1 / ((p : ℚ)^(s * padicValNat p (i+1)) * (b : ℚ)^(a (i+1)))

/-- The natural numerator obtained by clearing the deepest possible pole
at a shift at or beyond all `K` insertions. -/
def scaledNumerator (b p s : ℕ) (a : ℕ → ℕ) (K n : ℕ) : ℕ :=
  ∑ i ∈ range K,
    b^(n - a (i+1)) * p^(s * (Nat.log p K - padicValNat p (i+1)))

private lemma depth_le {p K i : ℕ} (hi : i ∈ range K) :
    padicValNat p (i+1) ≤ Nat.log p K := by
  rw [Nat.padicValNat_def]
  exact (multiplicity_le_nat_log _).trans (Nat.log_mono_right (mem_range.mp hi))

private lemma inserted {a : ℕ → ℕ} {K n i : ℕ} (ha : Monotone a)
    (hcut : K = 0 ∨ a K ≤ n) (hi : i ∈ range K) : a (i+1) ≤ n := by
  obtain rfl | h := hcut
  · simp at hi
  · exact (ha (mem_range.mp hi)).trans h

theorem shiftedPrefix_eq_div {b p s K n : ℕ} {a : ℕ → ℕ}
    (hb : 0 < b) (hp : 0 < p) (ha : Monotone a) (hcut : K = 0 ∨ a K ≤ n) :
    shiftedPrefix b p s a K n =
      (scaledNumerator b p s a K n : ℚ) / (p : ℚ)^(s * Nat.log p K) := by
  have bn : (b : ℚ) ≠ 0 := by positivity
  have pn : (p : ℚ) ≠ 0 := by positivity
  simp only [shiftedPrefix, scaledNumerator, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    mul_sum, sum_div]
  apply sum_congr rfl
  intro i hi
  rw [pow_sub₀ _ bn (inserted ha hcut hi), Nat.mul_sub,
    pow_sub₀ _ pn (Nat.mul_le_mul_left s (depth_le hi))]
  field_simp

/-- The valuation layer of maximal depth consists of the multiples of
`p^(Nat.log p K)` among the first `K` positive indices. -/
theorem maximalLayer_card {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ((range K).filter (fun i => padicValNat p (i+1) = Nat.log p K)).card =
      K / p^(Nat.log p K) := by
  rw [← Nat.card_multiples]
  congr 1
  apply filter_congr
  intro i hi
  rw [Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.succ_ne_zero _),
    ← Nat.padicValNat_def]
  exact ⟨fun h => h.ge, fun h => le_antisymm (depth_le hi) h⟩

theorem maximalLayer_count_bounds {p K : ℕ} (hp : p.Prime) (hK : 0 < K) :
    1 ≤ K / p^(Nat.log p K) ∧ K / p^(Nat.log p K) < p := by
  have pos := pow_pos hp.pos (Nat.log p K)
  constructor
  · exact (Nat.le_div_iff_mul_le pos).mpr (by simpa using Nat.pow_log_le_self p hK.ne')
  · apply (Nat.div_lt_iff_lt_mul pos).mpr
    simpa only [pow_succ'] using Nat.lt_pow_succ_log_self hp.one_lt K

/-- Each deepest term contributes `b^n` modulo `p`; all shallower terms
vanish when `s > 0`. This identity includes the empty prefix. -/
theorem scaledNumerator_mod {b p s K n : ℕ} {a : ℕ → ℕ} (hp : p.Prime)
    (hs : 0 < s) (ha : Monotone a) (hcut : K = 0 ∨ a K ≤ n)
    (period : ∀ k, 0 < k → orderOf (b : ZMod p) ∣ a k) :
    (scaledNumerator b p s a K n : ZMod p) =
      (K / p^(Nat.log p K) : ℕ) * (b : ZMod p)^n := by
  let J := Nat.log p K
  have term (i : ℕ) (hi : i ∈ range K) :
      (b : ZMod p)^(n - a (i+1)) * (p : ZMod p)^(s * (J - padicValNat p (i+1))) =
        if padicValNat p (i+1) = J then (b : ZMod p)^n else 0 := by
    split_ifs with top
    · have one := orderOf_dvd_iff_pow_eq_one.mp (period (i+1) (Nat.succ_pos _))
      have e := Nat.sub_add_cancel (inserted ha hcut hi)
      simpa [top, pow_add, one] using
        (congrArg (fun m => (b : ZMod p)^m) e)
    · have lt : padicValNat p (i+1) < J := lt_of_le_of_ne (depth_le hi) top
      simp [zero_pow (Nat.mul_pos hs (Nat.sub_pos_of_lt lt)).ne']
  simp only [scaledNumerator, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [sum_congr rfl term, ← sum_filter]
  simp [J, maximalLayer_card hp]

/-- Exact reduced denominator for every truncation and every shift at or
beyond its last insertion. In particular `K = 0` and `s = 0` give one. -/
theorem shiftedPrefix_den {b p s K n : ℕ} {a : ℕ → ℕ} (hp : p.Prime)
    (off : ¬ p ∣ b) (ha : Monotone a) (hcut : K = 0 ∨ a K ≤ n)
    (period : ∀ k, 0 < k → orderOf (b : ZMod p) ∣ a k) :
    (shiftedPrefix b p s a K n).den = p^(s * Nat.log p K) := by
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => off (h ▸ dvd_zero _))
  rw [shiftedPrefix_eq_div hb hp.pos ha hcut]
  by_cases hK : K = 0
  · simp [hK, scaledNumerator]
  by_cases hs : s = 0
  · simp [hs]
  let : Fact p.Prime := ⟨hp⟩
  have bounds := maximalLayer_count_bounds hp (Nat.pos_of_ne_zero hK)
  have unit : ¬ p ∣ scaledNumerator b p s a K n := by
    rw [← ZMod.natCast_eq_zero_iff, scaledNumerator_mod hp (Nat.pos_of_ne_zero hs) ha hcut period]
    exact mul_ne_zero ((ZMod.natCast_eq_zero_iff ..).not.mpr
      (Nat.not_dvd_of_pos_of_lt bounds.1 bounds.2))
      (pow_ne_zero _ ((ZMod.natCast_eq_zero_iff ..).not.mpr off))
  have cop := (hp.coprime_iff_not_dvd.mpr unit).symm.pow_right (s * Nat.log p K)
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using
    (Rat.den_div_eq_of_coprime (a := (scaledNumerator b p s a K n : ℤ))
      (b := ((p^(s * Nat.log p K) : ℕ) : ℤ)) (by exact_mod_cast pow_pos hp.pos _)
      (by simpa using cop))

/-- The largest positive insertion index reached by shift `n`, or zero
before the first insertion. For strictly increasing `a`, the search bound
`n` suffices because `k ≤ a k`. -/
def lastInsertion (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => a k ≤ n) n

/-- At the left endpoint the new insertion is included. At the next
insertion the index changes. This also covers the initial empty interval. -/
theorem lastInsertion_eq_iff {a : ℕ → ℕ} (ha : StrictMono a) (n K : ℕ) :
    lastInsertion a n = K ↔ (K = 0 ∨ a K ≤ n) ∧ n < a (K+1) := by
  rw [lastInsertion, Nat.findGreatest_eq_iff]
  constructor
  · rintro ⟨_, inRange, last⟩
    refine ⟨or_iff_not_imp_left.mpr inRange, lt_of_not_ge (fun h => ?_)⟩
    exact last (Nat.lt_succ_self K) ((ha.id_le _).trans h) h
  · rintro ⟨h, next⟩
    refine ⟨?_, fun nz => h.resolve_left nz, fun k hk _ => ?_⟩
    · rcases h with rfl | le
      · exact Nat.zero_le _
      · exact (ha.id_le K).trans le
    · exact (next.trans_le (ha.monotone hk)).not_ge

/-- The reduced denominator of the full rational prefix at every shift. -/
theorem fullPrefix_den {b p s : ℕ} {a : ℕ → ℕ} (hp : p.Prime) (off : ¬ p ∣ b)
    (ha : StrictMono a) (period : ∀ k, 0 < k → orderOf (b : ZMod p) ∣ a k) (n : ℕ) :
    (shiftedPrefix b p s a (lastInsertion a n) n).den =
      p^(s * Nat.log p (lastInsertion a n)) :=
  shiftedPrefix_den hp off ha.monotone ((lastInsertion_eq_iff ha n _).mp rfl).1 period

/-- For the principal polynomial schedule, the formula holds after the
`K`-th insertion even if the fixed truncation is shifted farther. -/
theorem polynomialPrefix_den {b p s d K n : ℕ} (hp : p.Prime) (off : ¬ p ∣ b)
    (hcut : K = 0 ∨ orderOf (b : ZMod p) * K^d ≤ n) :
    (shiftedPrefix b p s (fun k => orderOf (b : ZMod p) * k^d) K n).den =
      p^(s * Nat.log p K) :=
  shiftedPrefix_den hp off (fun _ _ le => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le _))
    hcut (fun _ _ => dvd_mul_right ..)

end NormalityChecker.RetirementDenominator
