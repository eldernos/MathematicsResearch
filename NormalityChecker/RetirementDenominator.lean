module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import NormalityChecker.ArithmeticCertificate
public import NormalityChecker.MaskGrid
public import NormalityChecker.PartialUniformity

/-! # Reduced denominators of valuation-scheduled prefixes

The insertion at position `a k`, for `k ≥ 1`, has weight
`1 / p^(s * padicValNat p k)`. If the positions are multiples of the order
of the radix modulo `p`, all terms in the deepest layer have the same
nonzero residue after clearing denominators. The layer contains exactly
`K / p^(Nat.log p K)` terms through insertion `K`.

If the schedule grows at least quadratically, a block that crosses no
insertion has total real approximation error at most two. The remaining
blocks occupy a vanishing share of every prefix. The fixed-support orbit
estimate then gives discrepancy tending to zero for positive `s`. At
`s = 0` the rational model is integral and discrepancy tends to one.
-/

@[expose] public section
open Finset Filter
open scoped Topology
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

/-- The infinite series in its grouped form. -/
noncomputable def value (b p s : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑' i : ℕ, 1 / ((p : ℝ)^(s * padicValNat p (i+1)) * (b : ℝ)^a (i+1))

/-- Even a coefficient of size one costs at most two in total shifted
real error on a whole interval ending by the next insertion. -/
theorem cleanBlock_error {b p s K n B : ℕ} {a : ℕ → ℕ} (hb : 2 ≤ b) (hp : 0 < p)
    (ha : StrictMono a) (clean : n + B ≤ a (K+1)) :
    ∑ i ∈ range B, |(b : ℝ)^(n+i) * value b p s a -
      (b : ℝ)^i * (shiftedPrefix b p s a K n : ℝ)| ≤ 2 := by
  let f (i : ℕ) := 1 / ((p : ℝ)^(s * padicValNat p (i+1)) * (b : ℝ)^a (i+1))
  have br : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have bp : (0 : ℝ) < b := by linarith
  have pr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have major (i K m : ℕ) (hm : m ≤ a (K+1)) :
      (b : ℝ)^m * f (i+K) ≤ (1/2 : ℝ)^i := by
    have idx : i + m ≤ a (i+K+1) := (Nat.add_le_add_left hm i).trans
      (by simpa only [Nat.add_assoc] using ha.add_le_nat i (K+1))
    have power := (pow_le_pow_left₀ (by norm_num) br i)
    dsimp [f]
    rw [one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (b : ℝ)^m * 2^i ≤ (b : ℝ)^(i+m) := by rw [pow_add, mul_comm]; gcongr
         _ ≤ (b : ℝ)^a (i+K+1) := pow_le_pow_right₀ (by linarith) idx
         _ ≤ (p : ℝ)^(s * padicValNat p (i+K+1)) * (b : ℝ)^a (i+K+1) :=
           le_mul_of_one_le_left (by positivity) (one_le_pow₀ pr)
  have sm : Summable f := .of_nonneg_of_le (fun i => by dsimp [f]; positivity)
    (fun i => by simpa using major i 0 0 (Nat.zero_le _)) summable_geometric_two
  let tail := ∑' i, f (i+K)
  have tailpos : 0 ≤ tail := tsum_nonneg (fun i => by dsimp [f]; positivity)
  have cap : (b : ℝ)^(n+B) * tail ≤ 2 := by
    rw [show (b : ℝ)^(n+B) * tail = ∑' i, (b : ℝ)^(n+B) * f (i+K) from tsum_mul_left.symm]
    exact ((((summable_nat_add_iff K).mpr sm).mul_left _).tsum_le_tsum
      (fun i => major i K _ clean) summable_geometric_two).trans_eq tsum_geometric_two
  have trunc : (shiftedPrefix b p s a K n : ℝ) = (b : ℝ)^n * ∑ i ∈ range K, f i := by
    simp [shiftedPrefix, f]
  have diff (i : ℕ) : (b : ℝ)^(n+i) * value b p s a -
      (b : ℝ)^i * (shiftedPrefix b p s a K n : ℝ) = (b : ℝ)^(n+i)*tail := by
    rw [show value b p s a = (∑ j ∈ range K, f j) + tail from (sm.sum_add_tsum_nat_add K).symm,
      trunc, pow_add]
    ring
  simp_rw [diff, abs_of_nonneg (mul_nonneg (pow_nonneg bp.le _) tailpos), pow_add, mul_assoc]
  rw [← mul_sum, ← sum_mul, ← mul_assoc]
  have geom := geom_sum_mul (b : ℝ) B
  have small : ∑ i ∈ range B, (b : ℝ)^i ≤ (b : ℝ)^B := by
    have z : 0 ≤ ∑ i ∈ range B, (b : ℝ)^i := sum_nonneg (fun _ _ => by positivity)
    nlinarith only [geom, mul_nonneg z (sub_nonneg.mpr br)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left small (by positivity)) tailpos).trans
    (by rwa [← pow_add])

/- On a scale of size 16^k use blocks of length 2^k. At most 4^(k+1)
blocks cross an insertion because the schedule grows at least quadratically. -/
private theorem mean_zero_on_clean_blocks {a : ℕ → ℕ} (ha : StrictMono a)
    (square : ∀ k, k^2 ≤ a k) (f : ℕ → ℂ) (unit : ∀ i, ‖f i‖ ≤ 1)
    (good : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, 16^k ≤ n → n < 16^(k+1) →
      n + 2^k ≤ a (lastInsertion a n + 1) →
      ‖∑ i ∈ range (2^k), f (n+i)‖ ≤ ε * (2 : ℝ)^k) :
    Tendsto (mean f) atTop (𝓝 0) := by
  apply mean_zero_of_radix_cells (c := 16) (S := 1) (by decide) (by decide)
  intro u hu ε pos
  have ub := mem_Ico.mp hu
  have geom := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).const_mul 5
  simp only [mul_zero] at geom
  filter_upwards [good (ε/2) (half_pos pos), geom.eventually_le_const (half_pos pos)]
    with k orbit few T hT
  let U := u * 8^k
  let E := (range (4^(k+1))).image (fun j => a j / 2^k - U)
  have card : E.card ≤ 4^(k+1) := card_image_le.trans_eq (card_range _)
  have eq16 : (8 : ℕ)^k * 2^k = 16^k := (mul_pow 8 2 k).symm
  have bp : 0 < (2 : ℕ)^k := by positivity
  have cell : u*16^k = U*2^k := by rw [← eq16]; dsimp [U]; ring
  have est := prefix_block_bound f unit (s := u*16^k) bp (hT.trans_eq eq16.symm) E
    (half_pos pos).le (fun l hl he => by
      let n := (U+l)*2^k
      have start : u*16^k + l*2^k = n := by rw [cell, ← Nat.add_mul]
      have low : 16^k ≤ n := (Nat.le_mul_of_pos_left _ ub.1).trans (by omega)
      have high : n+2^k ≤ 16^(k+1) := calc
        n+2^k = u*16^k + (l+1)*2^k := by rw [← start]; ring
        _ ≤ u*16^k + 8^k*2^k := Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) _
        _ ≤ 16^(k+1) := by rw [eq16, ← Nat.succ_mul, pow_succ']; exact Nat.mul_le_mul_right _ ub.2
      have clean : n+2^k ≤ a (lastInsertion a n+1) := by
        by_contra! crossed
        let j := lastInsertion a n + 1
        have after : n < a j := ((lastInsertion_eq_iff ha n _).mp rfl).2
        have bound : j < 4^(k+1) := by
          apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
          have eqpow : (4^(k+1) : ℕ)^2 = 16^(k+1) := by rw [← pow_mul, Nat.mul_comm, pow_mul]; rfl
          exact (square j).trans_lt ((crossed.trans_le high).trans_eq eqpow.symm)
        have q : a j / 2^k = U+l := le_antisymm
          (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul bp).mpr (by simpa [Nat.succ_mul, n] using crossed)))
          ((Nat.le_div_iff_mul_le bp).mpr after.le)
        exact he (mem_image.mpr ⟨j, mem_range.mpr bound, by rw [q]; omega⟩)
      simpa only [start, Nat.cast_pow, Nat.cast_ofNat] using
        orbit n low (by omega) clean)
  have few' : (E.card : ℝ) + 1 ≤ ε/2 * (8 : ℝ)^k := by
    have h := mul_le_mul_of_nonneg_right few (show (0 : ℝ) ≤ 8^k by positivity)
    have id : (1/2 : ℝ)^k * 8^k = 4^k := by rw [← mul_pow]; norm_num
    have c : (E.card : ℝ) ≤ 4^(k+1) := by exact_mod_cast card
    rw [mul_assoc, id] at h
    rw [pow_succ] at c
    linarith only [c, h, one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := k)]
  push_cast at est
  have eqR : (8 : ℝ)^k * 2^k = 16^k := by exact_mod_cast eq16
  apply est.trans
  nlinarith only [mul_le_mul_of_nonneg_right few' (show (0 : ℝ) ≤ 2^k by positivity),
    congrArg (fun x : ℝ => ε*x) eqR, congrArg (fun x : ℝ => (ε/2)*x) eqR]

/-- Every sufficiently late full prefix has arbitrarily large reduced
denominator when the valuation weight exponent is positive. -/
theorem fullPrefix_den_tendsto {b p s : ℕ} {a : ℕ → ℕ} (hp : p.Prime)
    (off : ¬ p ∣ b) (hs : 0 < s) (ha : StrictMono a)
    (period : ∀ k, 0 < k → orderOf (b : ZMod p) ∣ a k) :
    Tendsto (fun n => (shiftedPrefix b p s a (lastInsertion a n) n).den) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop (a (p^M))] with n hn
  have idx : p^M ≤ lastInsertion a n := Nat.le_findGreatest ((ha.id_le _).trans hn) hn
  have depth := Nat.le_log_of_pow_le hp.one_lt idx
  rw [fullPrefix_den hp off ha period]
  exact (Nat.lt_pow_self hp.two_le (n := M)).le.trans (Nat.pow_le_pow_right hp.pos
    (depth.trans (Nat.le_mul_of_pos_left _ hs)))

/-- All-prefix normality for `s > 0` whenever insertion positions are
strictly increasing multiples of the order and grow at least quadratically.
There is no upper growth bound on the schedule. -/
theorem normal_of_positive {b p s : ℕ} {a : ℕ → ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (off : ¬ p ∣ b) (hs : 0 < s) (ha : StrictMono a) (square : ∀ k, k^2 ≤ a k)
    (period : ∀ k, 0 < k → orderOf (b : ZMod p) ∣ a k) :
    NormalIn b (value b p s a) := by
  apply normal_of_fourier hb
  intro h hh
  apply mean_zero_on_clean_blocks ha square _ (fun _ => (norm_phase _).le)
  intro ε pos
  let C := 2 * Real.pi * |(h : ℝ)|
  have cn : 0 ≤ C := by dsimp [C]; positivity
  have estimate := fixed_support_orbit_estimate hb hp.one_lt (hp.coprime_iff_not_dvd.mpr off).symm
  obtain ⟨M, cancel⟩ := estimate (8*s) (ε/2) (half_pos pos)
  have big := (fullPrefix_den_tendsto hp off hs ha period).eventually_ge_atTop (h.natAbs*M)
  obtain ⟨N, hN⟩ := eventually_atTop.mp big
  have grow : Tendsto (fun k : ℕ => (2 : ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (16 : ℕ))).eventually_ge_atTop N,
    grow.eventually_ge_atTop (2*C/(ε/2)), eventually_ge_atTop 1] with k large err hk n low high clean
  let K := lastInsertion a n
  let y := shiftedPrefix b p s a K n
  have den : y.den = p^(s * Nat.log p K) := fullPrefix_den hp off ha period n
  have np : 0 < n := (pow_pos (by decide : 0 < 16) k).trans_le low
  have cap : p^(Nat.log p K) ≤ n := by
    rcases Nat.eq_zero_or_pos K with zero | nz
    · simpa [zero] using (show 1 ≤ n from np)
    · exact (Nat.pow_log_le_self _ nz.ne').trans (Nat.findGreatest_le n)
  have top : y.den ≤ (2^k)^(8*s) := calc
    y.den = (p^(Nat.log p K))^s := by rw [den, ← pow_mul, Nat.mul_comm]
    _ ≤ (16^(k+1))^s := Nat.pow_le_pow_left (cap.trans high.le) _
    _ ≤ (2^k)^(8*s) := by
      rw [show 16 = 2^4 by decide, ← pow_mul, ← pow_mul, ← pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      rw [← Nat.mul_assoc k 8 s, ← Nat.mul_assoc 4 (k+1) s]
      exact Nat.mul_le_mul_right s (by omega : 4*(k+1) ≤ k*8)
  have support : y.den ∣ p^(s * Nat.log p K) := den ▸ dvd_rfl
  have orb := model_orbit_bound h hh y cancel (hN n (large.trans low)) support top
  let f i := phase ((h : ℝ) * ((b : ℝ)^(n+i) * value b p s a))
  let g i := phase ((h : ℝ) * ((b : ℝ)^i * y))
  have diff (i : ℕ) : ‖f i - g i‖ ≤ C * |(b : ℝ)^(n+i) * value b p s a - (b : ℝ)^i * y| := by
    apply (phase_sub_le ..).trans_eq
    rw [← mul_sub, abs_mul, ← mul_assoc]
  have dist := (norm_sum_le (range (2^k)) (fun i => f i-g i)).trans (sum_le_sum (fun i _ => diff i))
  rw [sum_sub_distrib, ← mul_sum] at dist
  have total := cleanBlock_error (s := s) hb hp.pos ha clean
  have tri := le_trans (norm_le_norm_add_norm_sub' (∑ i ∈ range (2^k), f i) (∑ i ∈ range (2^k), g i))
    (add_le_add orb (dist.trans (mul_le_mul_of_nonneg_left total cn)))
  push_cast at tri
  apply tri.trans
  linarith only [(div_le_iff₀ (half_pos pos)).mp err]

private theorem frequency_zero_of_zero {b p : ℕ} {a : ℕ → ℕ} (hb : 2 ≤ b) (hp : 0 < p)
    (ha : StrictMono a) (square : ∀ k, k^2 ≤ a k) {r : ℝ} (hr : 0 < r) :
    Tendsto (frequency (shift b (value b p 0 a)) r (1-r)) atTop (𝓝 0) := by
  classical
  let x := value b p 0 a
  let I (n : ℕ) := r ≤ shift b x n ∧ shift b x n < 1-r
  let f (n : ℕ) : ℂ := if I n then 1 else 0
  have avg : Tendsto (mean f) atTop (𝓝 0) := by
    apply mean_zero_on_clean_blocks ha square _ (fun i => by dsimp [f]; split_ifs <;> simp)
    intro ε pos
    have grow : Tendsto (fun k : ℕ => (2 : ℝ)^k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    filter_upwards [grow.eventually_ge_atTop ((2/r)/ε)] with k hk n _ _ clean
    let K := lastInsertion a n
    let A := scaledNumerator b p 0 a K n
    have prefixZ : (shiftedPrefix b p 0 a K n : ℝ) = A := by
      rw [shiftedPrefix_eq_div (by omega) hp ha.monotone ((lastInsertion_eq_iff ha n _).mp rfl).1]
      simp [A, K]
    let e (i : ℕ) := |(b : ℝ)^(n+i)*x - (b : ℝ)^i * A|
    have each (i : ℕ) : ‖f (n+i)‖ ≤ e i/r := by
      dsimp only [f]
      split_ifs with hit
      · rw [norm_one, le_div_iff₀ hr, one_mul]
        let v := (b : ℝ)^(n+i)*x
        let z : ℤ := (b : ℤ)^i * A
        change r ≤ Int.fract v ∧ Int.fract v < 1-r at hit
        have id : e i = |v-z| := by simp [e, v, z]
        rw [id]
        by_cases lo : z ≤ ⌊v⌋
        · apply le_trans _ (le_abs_self _)
          have cz : (z : ℝ) ≤ ⌊v⌋ := by exact_mod_cast lo
          linarith only [hit.1, Int.fract_add_floor v, cz]
        · apply le_trans _ (neg_le_abs _)
          have cz : (⌊v⌋ : ℝ)+1 ≤ z := by exact_mod_cast (show ⌊v⌋+1 ≤ z by omega)
          linarith only [hit.2, Int.fract_add_floor v, cz]
      · rw [norm_zero]
        exact div_nonneg (abs_nonneg _) hr.le
    have total := cleanBlock_error (s := 0) hb hp ha clean
    rw [prefixZ] at total
    apply (norm_sum_le ..).trans ((sum_le_sum (fun i _ => each i)).trans ?_)
    rw [← sum_div]
    exact (div_le_div_of_nonneg_right total hr.le).trans (by linarith only [(div_le_iff₀ pos).mp hk])
  have re := Complex.continuous_re.continuousAt.tendsto.comp avg
  apply re.congr
  intro N
  simp [mean, f, frequency, I, x, Complex.div_natCast_re]

/-- Unit coefficients give discrepancy tending to one through every cutoff.
This half of the switch requires no alignment of the insertion positions. -/
theorem discrepancy_of_zero {b p : ℕ} {a : ℕ → ℕ} (hb : 2 ≤ b) (hp : 0 < p)
    (ha : StrictMono a) (square : ∀ k, k^2 ≤ a k) :
    Tendsto (radixDiscrepancy b (value b p 0 a)) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε pos
  let r := min (ε/4) (1/4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have h₁ := min_le_left (ε/4) (1/4)
  have h₂ := min_le_right (ε/4) (1/4)
  have interior := frequency_zero_of_zero (p := p) hb hp ha square hr
  filter_upwards [interior.eventually_lt_const hr] with N small
  have bound := PolynomialMasks.interval_le_radix (b := b) (N := N) (value b p 0 a) hr.le
    (show r < 1-r by dsimp [r]; linarith only [h₂]) (by linarith only [hr])
  have upper := (radix_discrepancy_bounds b (value b p 0 a) N).2
  have lower := (abs_le.mp bound).1
  rw [Real.dist_eq, abs_lt]
  dsimp only [r] at *
  constructor <;> linarith

private theorem discrepancy_zero_of_normal {b : ℕ} {x : ℝ} (hn : NormalIn b x) :
    Tendsto (radixDiscrepancy b x) atTop (𝓝 0) := by
  have hb := hn.1
  have grow : Tendsto (fun k : ℕ => (b : ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hb)
  rw [Metric.tendsto_nhds]
  intro ε pos
  obtain ⟨k, hk, large⟩ := ((eventually_gt_atTop 0).and (grow.eventually_gt_atTop (2/ε))).exists
  have mesh := discrepancy_of_fixed_cells (b := b) (x := x)
    (pow_pos (by omega : 0 < b) k) (fun j hj => by simpa using hn.2 k j hk hj)
  have bound : limsup (radixDiscrepancy b x) atTop < ε := by
    apply mesh.trans_lt
    push_cast
    exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (b : ℝ)^k)).mpr
      (by linarith only [(div_lt_iff₀ pos).mp large])
  filter_upwards [eventually_lt_of_limsup_lt bound (isBoundedUnder_of_eventually_le
    (.of_forall (fun N => (radix_discrepancy_bounds b x N).2)))] with N small
  simpa [Real.dist_eq, abs_of_nonneg (radix_discrepancy_bounds b x N).1] using small

/-- The full discrepancy switch for the grouped series on any strictly
increasing schedule of order multiples satisfying the quadratic lower bound. -/
theorem discrepancy_switch {b p s : ℕ} {a : ℕ → ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (off : ¬ p ∣ b) (ha : StrictMono a) (square : ∀ k, k^2 ≤ a k)
    (period : ∀ k, 0 < k → orderOf (b : ZMod p) ∣ a k) :
    Tendsto (radixDiscrepancy b (value b p s a)) atTop (𝓝 (if s = 0 then 1 else 0)) := by
  rcases Nat.eq_zero_or_pos s with rfl | pos
  · simpa using discrepancy_of_zero hb hp.pos ha square
  · simpa [pos.ne'] using discrepancy_zero_of_normal (normal_of_positive hb hp off pos ha square period)

theorem normal_iff_pos {b p s : ℕ} {a : ℕ → ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (off : ¬ p ∣ b) (ha : StrictMono a) (square : ∀ k, k^2 ≤ a k)
    (period : ∀ k, 0 < k → orderOf (b : ZMod p) ∣ a k) :
    NormalIn b (value b p s a) ↔ 0 < s := by
  refine ⟨fun hn => ?_, fun hs => normal_of_positive hb hp off hs ha square period⟩
  rcases Nat.eq_zero_or_pos s with rfl | pos
  · exact False.elim (zero_ne_one (tendsto_nhds_unique (discrepancy_zero_of_normal hn)
      (discrepancy_of_zero hb hp.pos ha square)))
  · exact pos

/-- In particular the principal family at `a k = ord_p(b) * k^d` realizes
the discrepancy switch in every degree `d ≥ 2`, for all off-radix primes. -/
theorem polynomial_discrepancy_switch {b p s d : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (off : ¬ p ∣ b) (hd : 2 ≤ d) :
    Tendsto (radixDiscrepancy b (value b p s (fun k => orderOf (b : ZMod p) * k^d)))
      atTop (𝓝 (if s = 0 then 1 else 0)) := by
  let : Fact p.Prime := ⟨hp⟩
  have bt : (b : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr off
  have ht := (isUnit_iff_ne_zero.mpr bt).isOfFinOrder.orderOf_pos
  apply discrepancy_switch hb hp off (fun i j lt => Nat.mul_lt_mul_of_pos_left
    (Nat.pow_lt_pow_left lt (by omega)) ht) _ (fun _ _ => dvd_mul_right ..)
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | pos
  · simp
  · exact (Nat.pow_le_pow_right pos hd).trans (Nat.le_mul_of_pos_left _ ht)

end NormalityChecker.RetirementDenominator
