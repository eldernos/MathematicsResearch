module

public import NormalityChecker.SignedShellDiscrepancy
public import Mathlib.Analysis.Real.OfDigits
import Mathlib.Topology.Order.LiminfLimsup

/-! Reverse binary histories at geometric shell boundaries and their largest limit words. -/

@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker.SignedPhases

abbrev ShellWord := ℕ → Bool

/-- Compare at the first unequal coordinate, if there is one. -/
def WordLE (s t : ShellWord) : Prop :=
  ∀ n, (∀ i < n, s i = t i) → s n ≤ t n

/-- A one-sided word which dominates every suffix in lexicographic order. -/
def SuffixMaximal (s : ShellWord) : Prop := ∀ h, WordLE (fun i => s (i+h)) s

def extremeDigit {p : ℕ} (hp : 1 < p) (d : Bool) : Fin p :=
  ⟨if d then p-1 else 0, by split <;> omega⟩

/-- Read bits as the extreme digits 0 and p−1 in radix p. -/
noncomputable def historyValue {p : ℕ} (hp : 1 < p) (s : ShellWord) : ℝ :=
  Real.ofDigits (fun i => extremeDigit hp (s i))

theorem historyValue_bounds {p : ℕ} (hp : 1 < p) (s : ShellWord) :
    0 ≤ historyValue hp s ∧ historyValue hp s ≤ 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

theorem continuous_historyValue {p : ℕ} (hp : 1 < p) : Continuous (historyValue hp) :=
  Real.continuous_ofDigits.comp (continuous_pi fun i =>
    (continuous_of_discreteTopology (f := extremeDigit hp)).comp (continuous_apply i))

/-- The diameter of a cylinder of depth n is at most p⁻ⁿ. -/
theorem historyValue_prefix {p : ℕ} (hp : 1 < p) {s t : ShellWord} (n : ℕ)
    (h : ∀ i < n, s i = t i) :
    |historyValue hp s - historyValue hp t| ≤ ((p : ℝ)^n)⁻¹ :=
  Real.abs_ofDigits_sub_ofDigits_le fun i hi => congrArg _ (h i hi)

private lemma historyValue_step {p : ℕ} (hp : 1 < p) (s : ShellWord) :
    historyValue hp s = ((if s 0 then (p:ℝ)-1 else 0) +
        historyValue hp (fun i => s (i+1))) / p := by
  unfold historyValue
  rw [Real.ofDigits_eq_sum_add_ofDigits _ 1]
  simp only [Finset.sum_range_one, Real.ofDigitsTerm, zero_add, pow_one, extremeDigit]
  cases s 0 <;> simp [Nat.cast_sub (show 1 ≤ p by omega), div_eq_inv_mul]
  ring

private lemma common_prefix_diff {p : ℕ} (hp : 1 < p) {s t : ShellWord} (n : ℕ)
    (h : ∀ i < n, s i = t i) :
    historyValue hp s - historyValue hp t = ((p:ℝ)^n)⁻¹ *
      (historyValue hp (fun i => s (i+n)) - historyValue hp (fun i => t (i+n))) := by
  unfold historyValue
  rw [Real.ofDigits_eq_sum_add_ofDigits (fun i => extremeDigit hp (s i)) n,
      Real.ofDigits_eq_sum_add_ofDigits (fun i => extremeDigit hp (t i)) n]
  have eq := Finset.sum_congr (s₁ := Finset.range n) rfl (fun i hi =>
    show Real.ofDigitsTerm (fun k => extremeDigit hp (s k)) i =
      Real.ofDigitsTerm (fun k => extremeDigit hp (t k)) i by simp [Real.ofDigitsTerm, h i (mem_range.mp hi)])
  rw [eq]; ring

private lemma first_difference {s t : ShellWord} (h : s ≠ t) :
    ∃ n, (∀ i < n, s i = t i) ∧ s n ≠ t n := by
  classical
  have ex : ∃ n, s n ≠ t n := by simpa [funext_iff] using h
  exact ⟨Nat.find ex, fun i hi => not_not.mp (Nat.find_min ex hi), Nat.find_spec ex⟩

private lemma digit_gap {p : ℕ} (hp : 1 < p) {s t : ShellWord} {n : ℕ}
    (eq : ∀ i < n, s i = t i) (hs : s n = false) (ht : t n = true) :
    ((p:ℝ)^n)⁻¹ * (((p:ℝ)-2)/p) ≤ historyValue hp t - historyValue hp s := by
  rw [common_prefix_diff hp n (fun i hi => (eq i hi).symm)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [historyValue_step hp (fun i => t (i+n)), historyValue_step hp (fun i => s (i+n))]
  simp only [zero_add, ht, hs, ite_true, Bool.false_eq_true, ite_false, ← sub_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [(historyValue_bounds hp (fun i => t (i+1+n))).1,
    (historyValue_bounds hp (fun i => s (i+1+n))).2]

theorem historyValue_mono {p : ℕ} (hp : 1 < p) {s t : ShellWord} (h : WordLE s t) :
    historyValue hp s ≤ historyValue hp t := by
  by_cases eq : s = t
  · simp [eq]
  obtain ⟨n, pre, ne⟩ := first_difference eq
  have le := h n pre
  have hs : s n = false := by
    cases e : s n <;> cases f : t n <;> simp_all
    exact (by decide : ¬ true ≤ false) le
  have ht : t n = true := by cases e : t n <;> simp_all
  have two : (2:ℝ) ≤ p := by exact_mod_cast hp
  linarith [(digit_gap hp pre hs ht), mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg p) n))
    (div_nonneg (sub_nonneg.mpr two) (Nat.cast_nonneg p))]

private lemma wordLE_of_ternary_le {s t : ShellWord}
    (h : historyValue (p:=3) (by decide) s ≤ historyValue (p:=3) (by decide) t) : WordLE s t := by
  intro n pre
  cases hs : s n <;> cases ht : t n <;> try decide
  have gap := digit_gap (p:=3) (by decide) (fun i hi => (pre i hi).symm) ht hs
  have pos : 0 < ((3:ℝ)^n)⁻¹ * ((3-2)/3) := by positivity
  exact False.elim ((not_lt_of_ge h) (sub_pos.mp (pos.trans_le gap)))

/-- The j most recent bits in reverse order, with zero padding into the past. -/
def reverseHistory (z : ShellWord) (j : ℕ) : ShellWord :=
  fun i => if i < j then z (j-1-i) else false

private lemma shift_history (z : ShellWord) (h j : ℕ) (hj : h ≤ j) :
    (fun i => reverseHistory z j (i+h)) = reverseHistory z (j-h) := by
  funext i
  simp only [reverseHistory]
  split_ifs <;> first | rfl | (congr 1; omega)

private noncomputable def boundaryValues {p : ℕ} (hp : 1 < p) (z : ShellWord) : ℕ → ℝ :=
  historyValue hp ∘ reverseHistory z

private lemma boundary_high {p : ℕ} (hp : 1 < p) (z : ShellWord) :
    IsBoundedUnder (· ≤ ·) atTop (boundaryValues hp z) :=
  isBoundedUnder_of_eventually_le (.of_forall fun j => (historyValue_bounds hp (reverseHistory z j)).2)

private lemma boundary_low {p : ℕ} (hp : 1 < p) (z : ShellWord) :
    IsCoboundedUnder (· ≤ ·) atTop (boundaryValues hp z) :=
  isCoboundedUnder_le_of_le atTop fun j => (historyValue_bounds hp (reverseHistory z j)).1

private lemma history_at_limsup {p : ℕ} (hp : 1 < p) (z : ShellWord) :
    ∃ s, MapClusterPt s atTop (reverseHistory z) ∧
      historyValue hp s = limsup (boundaryValues hp z) atTop := by
  obtain ⟨a, ha, grow⟩ := exists_seq_tendsto_limsup (boundary_low hp z) (boundary_high hp z)
  obtain ⟨s, _, φ, inc, conv⟩ := isCompact_univ.isSeqCompact
    (x := reverseHistory z ∘ a) (fun _ => Set.mem_univ _)
  exact ⟨s, MapClusterPt.of_comp (grow.comp inc.tendsto_atTop) conv.mapClusterPt,
    tendsto_nhds_unique ((continuous_historyValue hp).continuousAt.tendsto.comp conv)
      (ha.comp inc.tendsto_atTop)⟩

private lemma suffix_cluster {z s : ShellWord} (hs : MapClusterPt s atTop (reverseHistory z))
    (h : ℕ) : MapClusterPt (fun i => s (i+h)) atTop (reverseHistory z) := by
  obtain ⟨a, conv, grow⟩ := hs.exists_seq_tendsto
  have ct : Continuous (fun w : ShellWord => fun i => w (i+h)) :=
    continuous_pi fun i => continuous_apply (i+h)
  apply MapClusterPt.of_comp (show Tendsto (fun k => a k - h) atTop atTop from
    (tendsto_sub_atTop_nat h).comp grow)
  apply Tendsto.mapClusterPt
  apply (ct.continuousAt.tendsto.comp conv).congr'
  filter_upwards [grow.eventually_ge_atTop h] with k hk using shift_history z h (a k) hk

/-- For each chronological pattern there is a single lexicographically largest
limiting history. It gives the boundary limsup simultaneously in every radix. -/
theorem exists_maximal_limit_history (z : ShellWord) :
    ∃ s, MapClusterPt s atTop (reverseHistory z) ∧ SuffixMaximal s ∧
      (∀ t, MapClusterPt t atTop (reverseHistory z) → WordLE t s) ∧
      ∀ {p : ℕ} (hp : 1 < p), limsup (fun j => historyValue hp (reverseHistory z j)) atTop =
        historyValue hp s := by
  obtain ⟨s, hs, top⟩ := history_at_limsup (p:=3) (by decide) z
  have largest (t : ShellWord) (ht : MapClusterPt t atTop (reverseHistory z)) : WordLE t s := by
    apply wordLE_of_ternary_le
    rw [top]
    exact (ht.continuousAt_comp (continuous_historyValue _).continuousAt).le_limsup (boundary_high _ z)
  refine ⟨s, hs, fun h => largest _ (suffix_cluster hs h), largest, fun {p} hp => ?_⟩
  obtain ⟨t, ht, top'⟩ := history_at_limsup hp z
  exact le_antisymm (top' ▸ historyValue_mono hp (largest t ht))
    ((hs.continuousAt_comp (continuous_historyValue hp).continuousAt).le_limsup (boundary_high hp z))


private lemma false_head {s : ShellWord} (hs : SuffixMaximal s) (h : s 0 = false) :
    s = fun _ => false := by
  funext i
  have le := hs i 0 (by simp)
  simpa [h, Bool.le_iff_imp] using le

private lemma false_before_true {u s : ShellWord} (hu : u 0 = false) (hs : s 0 = true) :
    WordLE u s := by
  rintro (_ | n) eq
  · simp [hu, hs, Bool.le_iff_imp]
  · simpa [hu, hs] using eq 0 (Nat.zero_lt_succ n)

private lemma zero_historyValue {p : ℕ} (hp : 1 < p) :
    historyValue hp (fun _ => false) = 0 := by
  simp [historyValue, Real.ofDigits, Real.ofDigitsTerm, extremeDigit]

/-- At the end of a reversed prefix the first digits of the history reproduce it. -/
private lemma block_match {s z : ShellWord} {e l : ℕ} (hl : l ≤ e)
    (bits : ∀ j, e-l ≤ j → j < e → z j = s (e-1-j)) :
    ∀ i < l, reverseHistory z e i = s i := by
  intro i hi
  rw [reverseHistory, ite_eq_left (by omega), bits _ (by omega) (by omega)]
  congr 1
  omega

/-- Inside a padded block, the first k bits of the history are dominated
by a suffix after filling any missing earlier bits with zeros. -/
private lemma block_upper {p : ℕ} (hp : 1 < p) {s z : ShellWord} (hs : SuffixMaximal s)
    (one : s 0 = true) {a d e j k : ℕ} (hj : a ≤ j) (je : j < e) (room : a+k ≤ d)
    (bits : ∀ u, a ≤ u → u < e → z u = if d ≤ u then s (e-1-u) else false) :
    historyValue hp (reverseHistory z (j+1)) ≤ historyValue hp s + ((p:ℝ)^k)⁻¹ := by
  by_cases active : d ≤ j
  · let w : ShellWord := fun i => if i < k then reverseHistory z (j+1) i else false
    have le (i : ℕ) : w i ≤ s (i+(e-1-j)) := by
      by_cases hi : i < k
      · have ij : i < j+1 := by omega
        simp only [w, ite_eq_left hi, reverseHistory, ite_eq_left ij, Nat.add_sub_cancel]
        rw [bits (j-i) (by omega) (by omega)]
        split
        · rw [show e-1-(j-i) = i+(e-1-j) by omega]
        · exact Bool.false_le _
      · simp only [w, ite_eq_right hi, Bool.false_le]
    have comp := (historyValue_mono hp (s:=w) (t:=fun i => s (i+(e-1-j))) (fun n _ => le n)).trans
      (historyValue_mono hp (hs _))
    have err := (abs_le.mp (historyValue_prefix hp (s:=reverseHistory z (j+1)) (t:=w) k
      (fun i hi => by simp [w, hi]))).2
    linarith
  · have zero : reverseHistory z (j+1) 0 = false := by simp [reverseHistory, bits j hj je, active]
    exact (historyValue_mono hp (false_before_true zero one)).trans
      (le_add_of_nonneg_right (by positivity))

/-- In [n²,(n+1)²), write n zero bits and then the first n+1 bits in reverse. -/
def realizingPattern (s : ShellWord) (j : ℕ) : Bool :=
  let n := Nat.sqrt j
  if n^2+n ≤ j then s ((n+1)^2-1-j) else false

private lemma realizing_bits (s : ShellWord) (n j : ℕ) (lo : n^2 ≤ j) (hi : j < (n+1)^2) :
    realizingPattern s j = if n^2+n ≤ j then s ((n+1)^2-1-j) else false := by
  simp [realizingPattern, ← Nat.eq_sqrt'.mpr ⟨lo, hi⟩]

private lemma value_at_realizing_ends {p : ℕ} (hp : 1 < p) (s : ShellWord) (n : ℕ) :
    |historyValue hp (reverseHistory (realizingPattern s) ((n+1)^2)) - historyValue hp s| ≤
      ((p:ℝ)^n)⁻¹ := by
  apply historyValue_prefix
  apply block_match (by nlinarith : n ≤ (n+1)^2)
  intro j lo hi
  have d : n^2+n ≤ j := by
    have : (n+1)^2 = n^2+n+(n+1) := by ring
    omega
  rw [realizing_bits s n j (by omega) hi, ite_eq_left d]

/-- Every suffix-maximal word is attained by one explicit chronological pattern
in all radices, including words with a terminating binary expansion. -/
theorem realizingPattern_limsup (s : ShellWord) (hs : SuffixMaximal s) {p : ℕ} (hp : 1 < p) :
    limsup (fun j => historyValue hp (reverseHistory (realizingPattern s) j)) atTop =
      historyValue hp s := by
  have pr : (1:ℝ) < p := by exact_mod_cast hp
  have tiny : Tendsto (fun n : ℕ => ((p:ℝ)^n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt pr)
  let z := realizingPattern s
  have low := boundary_low hp z
  have high := boundary_high hp z
  refine le_antisymm ((limsup_le_iff low high).2 ?_) ?_
  · intro y hy
    by_cases one : s 0 = true
    · obtain ⟨k, hk⟩ := (tiny.eventually_lt_const (sub_pos.mpr hy)).exists
      filter_upwards [eventually_ge_atTop (k^2+1)] with J hJ
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
      let n := j.sqrt
      have ⟨lo, hi⟩ := (Nat.eq_sqrt' (a:=n) (n:=j)).mp rfl
      have kn : k ≤ n := Nat.le_sqrt'.mpr (by omega)
      have up := block_upper hp hs one lo hi (show n^2+k ≤ n^2+n by omega) (realizing_bits s n)
      exact lt_of_le_of_lt up (by linarith)
    · have eq := false_head hs (Bool.eq_false_iff.mpr one)
      subst s
      have hz (j : ℕ) : reverseHistory (realizingPattern (fun _ => false)) j = fun _ => false := by
        funext i; simp [reverseHistory, realizingPattern]
      exact .of_forall fun j => by simpa only [boundaryValues, Function.comp_apply, z, hz] using hy
  · have grow : Tendsto (fun n : ℕ => (n+1)^2) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp; nlinarith) tendsto_id
    have conv : Tendsto (fun n : ℕ => historyValue hp (reverseHistory z ((n+1)^2))) atTop
        (𝓝 (historyValue hp s)) := by
      rw [Metric.tendsto_nhds]
      intro ε pos
      filter_upwards [tiny.eventually_lt_const pos] with n hn
      exact (value_at_realizing_ends hp s n).trans_lt hn
    exact (MapClusterPt.of_comp (u:=boundaryValues hp z) grow conv.mapClusterPt).le_limsup high

/-- A period of 2k bits, consisting of k zeros and a reversed k-bit prefix. -/
def periodicHistoryPattern (s : ShellWord) (k j : ℕ) : Bool :=
  let i := j % (2*k)
  if k ≤ i then s (2*k-1-i) else false

private lemma periodic_bits (s : ShellWord) {k : ℕ} (q u : ℕ)
    (lo : q*(2*k) ≤ u) (hi : u < q*(2*k)+2*k) :
    periodicHistoryPattern s k u =
      if q*(2*k)+k ≤ u then s (q*(2*k)+2*k-1-u) else false := by
  let a := q*(2*k)
  have split : u-a+a = u := Nat.sub_add_cancel lo
  have md : u % (2*k) = u-a := by
    conv_lhs => rw [← split]
    rw [show a = q*(2*k) from rfl, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  simp only [periodicHistoryPattern, md]
  dsimp [a]
  split_ifs <;> first | rfl | (congr 1; omega)

private lemma periodic_end_prefix (s : ShellWord) (q k : ℕ) :
    ∀ i < k, reverseHistory (periodicHistoryPattern s k) (q*(2*k)+2*k) i = s i := by
  apply block_match (by omega)
  intro j lo hi
  have d : q*(2*k)+k ≤ j := by omega
  rw [periodic_bits s q j (by omega) hi, ite_eq_left d]

/-- A period of length 2k gives an attainable boundary maximum within p⁻ᵏ.
The same period works for every radix. -/
theorem periodicHistoryPattern_error (s : ShellWord) (hs : SuffixMaximal s) {k : ℕ} (hk : 0 < k)
    {p : ℕ} (hp : 1 < p) :
    |limsup (fun j => historyValue hp (reverseHistory (periodicHistoryPattern s k) j)) atTop -
      historyValue hp s| ≤ ((p:ℝ)^k)⁻¹ := by
  let z := periodicHistoryPattern s k
  have low := boundary_low hp z
  have high := boundary_high hp z
  have upper : limsup (boundaryValues hp z) atTop ≤ historyValue hp s + ((p:ℝ)^k)⁻¹ := by
    apply limsup_le_of_le low
    by_cases one : s 0 = true
    · filter_upwards [eventually_gt_atTop 0] with J hJ
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ.ne'
      let q := j / (2*k)
      have lo : q*(2*k) ≤ j := Nat.div_mul_le_self ..
      have hi : j < q*(2*k)+2*k := by
        have e := Nat.mod_add_div j (2*k)
        have r := Nat.mod_lt j (by omega : 0 < 2*k)
        rw [Nat.mul_comm (2*k) (j/(2*k))] at e
        dsimp [q]; omega
      exact block_upper hp hs one lo hi le_rfl (periodic_bits s q)
    · have eq := false_head hs (Bool.eq_false_iff.mpr one)
      subst s
      have hz (j : ℕ) : reverseHistory z j = fun _ => false := by
        funext i; simp [reverseHistory, z, periodicHistoryPattern]
      exact .of_forall fun j => by simp [boundaryValues, hz, zero_historyValue]
  have lower : historyValue hp s - ((p:ℝ)^k)⁻¹ ≤ limsup (boundaryValues hp z) atTop := by
    apply le_limsup_of_frequently_le _ high
    rw [frequently_atTop]
    intro q
    let a := q*(2*k)
    have qa : q ≤ a := Nat.le_mul_of_pos_right q (by omega)
    refine ⟨a+2*k, by omega, ?_⟩
    have err := (abs_le.mp (historyValue_prefix hp k (periodic_end_prefix s q k))).1
    change _ ≤ historyValue hp (reverseHistory z (a+2*k))
    linarith
  exact abs_le.mpr ⟨by change _ ≤ limsup (boundaryValues hp z) atTop - _; linarith,
    by change limsup (boundaryValues hp z) atTop - _ ≤ _; linarith⟩

/-- The only words with false first bit are zero. The one followed by zeros
realizes the exact lower edge of the positive spectrum. -/
theorem least_positive_historyValue {p : ℕ} (hp : 1 < p) :
    IsLeast {x : ℝ | 0 < x ∧ ∃ s : ShellWord, SuffixMaximal s ∧ historyValue hp s = x}
      (((p:ℝ)-1)/p) := by
  let u : ShellWord := fun i => decide (i=0)
  have one : u 0 = true := rfl
  have su : SuffixMaximal u := by
    intro h
    cases h with
    | zero => exact fun _ _ => le_rfl
    | succ h => exact false_before_true (by simp [u]) one
  have val : historyValue hp u = ((p:ℝ)-1)/p := by
    rw [historyValue_step, one, show (fun i => u (i+1)) = fun _ => false by funext i; simp [u],
      zero_historyValue]
    simp
  have pr : (1:ℝ) < p := by exact_mod_cast hp
  refine ⟨⟨div_pos (sub_pos.mpr pr) (by positivity), u, su, val⟩, ?_⟩
  rintro x ⟨pos, s, hs, rfl⟩
  by_cases h : s 0 = true
  · rw [historyValue_step hp s, h]
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (historyValue_bounds hp _).1) (by positivity)
  · rw [false_head hs (Bool.eq_false_iff.mpr h), zero_historyValue] at pos
    exact (lt_irrefl _ pos).elim

/-- The chronological bit encoding of zero phases. -/
def zeroPattern (c : ℕ → ℤ) : ShellWord := fun j => decide (c j = 0)

/-- Actual shell densities are the radix values of the reverse histories. -/
theorem zeroDensity_eq_historyValue {p : ℕ} (hp : 1 < p) (c : ℕ → ℤ) (j : ℕ) :
    zeroDensity p c (p^j) = historyValue hp (reverseHistory (zeroPattern c) j) := by
  obtain ⟨base, step⟩ := zeroDensity_boundary_recurrence hp c
  induction j with
  | zero =>
    rw [pow_zero, base, show reverseHistory (zeroPattern c) 0 = fun _ => false by
      funext i; simp [reverseHistory], zero_historyValue]
  | succ j ih =>
    rw [step, ih, historyValue_step hp (reverseHistory _ (j+1)),
      shift_history _ 1 _ (by omega)]
    simp [reverseHistory, zeroPattern]

/-- The actual all-prefix discrepancy is the largest limiting reverse-history value. -/
theorem limsup_discrepancy_eq_history_limsup {b p C : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) :
    limsup (radixDiscrepancy b (value b p c)) atTop =
      limsup (fun j => historyValue hp.one_lt (reverseHistory (zeroPattern c) j)) atTop := by
  simp only [limsup_discrepancy_eq_zeroDensity hb hp cop c cap, limsup_zeroDensity_eq_boundary hp.one_lt,
    zeroDensity_eq_historyValue hp.one_lt]

/-- A discrepancy is attainable by a bounded signed phase sequence if and only
if it is the extreme-digit value of a word dominating all its suffixes. -/
theorem attainable_discrepancy_iff {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (cop : b.Coprime p)
    (x : ℝ) :
    (∃ (c : ℕ → ℤ) (C : ℕ), (∀ j, (c j).natAbs ≤ C) ∧
      limsup (radixDiscrepancy b (value b p c)) atTop = x) ↔
    ∃ s : ShellWord, SuffixMaximal s ∧ historyValue hp.one_lt s = x := by
  constructor
  · rintro ⟨c, C, cap, rfl⟩
    obtain ⟨s, _, hs, _, lim⟩ := exists_maximal_limit_history (zeroPattern c)
    exact ⟨s, hs, ((limsup_discrepancy_eq_history_limsup hb hp cop c cap).trans (lim hp.one_lt)).symm⟩
  · rintro ⟨s, hs, rfl⟩
    let c (j : ℕ) : ℤ := if realizingPattern s j then 0 else 1
    have cap (j : ℕ) : (c j).natAbs ≤ 1 := by dsimp [c]; split <;> decide
    refine ⟨c, 1, cap, ?_⟩
    rw [limsup_discrepancy_eq_history_limsup hb hp cop c cap, show zeroPattern c = realizingPattern s by
      funext j; simp [c, zeroPattern]]
    exact realizingPattern_limsup s hs hp.one_lt

/-- A rational cycle maximum with a stated error bound for each admissible target word. -/
theorem cycleMaximum_approximates_historyValue {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (s : ShellWord) (hs : SuffixMaximal s) {k : ℕ} (hk : 0 < k) :
    let c (j : ℕ) : ℤ := if periodicHistoryPattern s k j then 0 else 1
    |(cycleMaximum p (2*k) c : ℝ) - historyValue hp.one_lt s| ≤ ((p:ℝ)^k)⁻¹ := by
  intro c
  have cap (j : ℕ) : (c j).natAbs ≤ 1 := by dsimp [c]; split <;> decide
  have per (j : ℕ) : c (j+2*k) = c j := by simp [c, periodicHistoryPattern]
  rw [← periodic_discrepancy hb hp cop (by omega) c cap per, limsup_discrepancy_eq_history_limsup hb hp cop c cap,
    show zeroPattern c = periodicHistoryPattern s k by funext j; simp [zeroPattern, c]]
  exact periodicHistoryPattern_error s hs hk hp.one_lt

/-- The attainable spectrum is compact, also at the ambiguous binary endpoints. -/
theorem isCompact_historySpectrum {p : ℕ} (hp : 1 < p) :
    IsCompact {x : ℝ | ∃ s : ShellWord, SuffixMaximal s ∧ historyValue hp s = x} := by
  have closed : IsClosed {s | SuffixMaximal s} := by
    have eq : {s | SuffixMaximal s} = ⋂ h : ℕ, {s : ShellWord |
        historyValue (p:=3) (by decide) (fun i => s (i+h)) ≤ historyValue (p:=3) (by decide) s} := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, SuffixMaximal]
      exact forall_congr' fun _ => ⟨historyValue_mono _, wordLE_of_ternary_le⟩
    rw [eq]
    exact isClosed_iInter fun h => isClosed_le ((continuous_historyValue _).comp
      (continuous_pi fun i => continuous_apply (i+h))) (continuous_historyValue _)
  exact closed.isCompact.image (continuous_historyValue hp)

private lemma value_lt_of_more_bits {p : ℕ} (hp : 1 < p) {s t : ShellWord}
    (le : ∀ i, s i ≤ t i) {j : ℕ} (sj : s j = false) (tj : t j = true) :
    historyValue hp s < historyValue hp t := by
  apply Summable.tsum_lt_tsum (i:=j) _ _ Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm
  · intro i
    unfold Real.ofDigitsTerm
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h := le i
    cases f : s i <;> cases g : t i <;> simp_all [extremeDigit, Bool.le_iff_imp]
  · simp only [Real.ofDigitsTerm, sj, tj, extremeDigit, Bool.false_eq_true, ite_false, ite_true,
      Nat.cast_zero, zero_mul]
    have hd : 0 < p-1 := by omega
    positivity

private def truncatedWord (s : ShellWord) (k : ℕ) : ShellWord :=
  fun i => if i < k then s i else false

private lemma truncated_maximal {s : ShellWord} (hs : SuffixMaximal s) (k : ℕ) :
    SuffixMaximal (truncatedWord s k) := by
  intro h n pre
  by_cases nh : n+h < k
  · have nk : n < k := by omega
    simp only [truncatedWord, ite_eq_left nh, ite_eq_left nk]
    apply hs h n
    intro i hi
    simpa [truncatedWord, show i < k by omega, show i+h < k by omega] using pre i hi
  · simp [truncatedWord, nh, Bool.false_le]

private lemma periodic_gt_terminating {p : ℕ} (hp : 1 < p) {s : ShellWord} {k : ℕ}
    (hk : 0 < k) (one : s 0 = true) (tail : ∀ i, k ≤ i → s i = false) :
    historyValue hp s < limsup (boundaryValues hp (periodicHistoryPattern s k)) atTop := by
  let z := periodicHistoryPattern s k
  let w : ShellWord := fun i => if i = 2*k then true else s i
  have greater : historyValue hp s < historyValue hp w :=
    value_lt_of_more_bits hp (fun i => by by_cases hi : i = 2*k <;> simp [w, hi, Bool.le_true])
      (j:=2*k) (tail _ (by omega)) (by simp [w])
  apply greater.trans_le
  apply le_limsup_of_frequently_le _ (boundary_high hp z)
  rw [frequently_atTop]
  intro N
  let a := (N+1)*(2*k)
  have enough : N+1 ≤ a := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨a+2*k, by omega, ?_⟩
  have prefixEq : ∀ i < k, reverseHistory z (a+2*k) i = s i := periodic_end_prefix s (N+1) k
  have extra : reverseHistory z (a+2*k) (2*k) = true := by
    have ae : a = N*(2*k)+2*k := Nat.succ_mul ..
    have d : N*(2*k)+k ≤ a-1 := by omega
    rw [reverseHistory, ite_eq_left (by omega), show a+2*k-1-2*k = a-1 by omega,
      show z (a-1) = _ from periodic_bits s N _ (by omega) (by omega), ite_eq_left d,
      show N*(2*k)+2*k-1-(a-1) = 0 by omega, one]
  apply historyValue_mono hp
  intro i _
  by_cases hi : i < k
  · simp [w, show i ≠ 2*k by omega, prefixEq i hi]
  · by_cases eq : i = 2*k
    · simp [w, eq, extra]
    · simp [w, eq, tail i (by omega), Bool.false_le]

/-- Every positive spectral point is an accumulation point. For each k ≥ 1
there is a distinct attainable value within p⁻ᵏ of it. -/
theorem exists_distinct_nearby_historyValue {p : ℕ} (hp : 1 < p) {s : ShellWord}
    (hs : SuffixMaximal s) (pos : 0 < historyValue hp s) {k : ℕ} (hk : 0 < k) :
    ∃ t, SuffixMaximal t ∧ historyValue hp t ≠ historyValue hp s ∧
      |historyValue hp t - historyValue hp s| ≤ ((p:ℝ)^k)⁻¹ := by
  by_cases term : ∀ i, k ≤ i → s i = false
  · have one : s 0 = true := by
      by_contra h
      rw [false_head hs (Bool.eq_false_iff.mpr h), zero_historyValue] at pos
      exact lt_irrefl _ pos
    obtain ⟨t, _, ht, _, lim⟩ := exists_maximal_limit_history (periodicHistoryPattern s k)
    refine ⟨t, ht, ?_, ?_⟩
    · exact ((lim hp) ▸ periodic_gt_terminating hp hk one term).ne'
    · rw [← lim hp]
      exact periodicHistoryPattern_error s hs hk hp
  · push Not at term
    obtain ⟨j, hj, bit⟩ := term
    refine ⟨truncatedWord s k, truncated_maximal hs k, ?_,
      historyValue_prefix hp k (fun i hi => by simp [truncatedWord, hi])⟩
    exact (value_lt_of_more_bits hp (fun i => by by_cases hi : i < k <;> simp [truncatedWord, hi, Bool.false_le])
      (j:=j) (by simp [truncatedWord, Nat.not_lt.mpr hj]) (by simpa using bit)).ne

end NormalityChecker.SignedPhases
