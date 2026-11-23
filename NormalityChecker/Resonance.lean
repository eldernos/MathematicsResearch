module

public import NormalityChecker.Basic

public section

open Filter Finset
open scoped Topology

namespace NormalityChecker

private abbrev q (j : ℕ) : ℕ := 3 ^ j
private noncomputable abbrev half : ℝ := 1 / 2

/-- A pair of terms from the expansions of `T₁` and `2 T₂` in the conversation. -/
noncomputable def pairTerm (j : ℕ) : ℝ :=
  (half ^ q j + half ^ (2 * q j)) / (q j : ℝ)

noncomputable def resonantSum : ℝ := ∑' j, pairTerm j

/-- The numerator of each shifted pair supplies all the required factors of three. -/
theorem pair_divisibility (j : ℕ) : (3 : ℤ) ^ (j + 1) ∣ 2 ^ (3 ^ j : ℕ) + 1 := by
  induction j with
  | zero => norm_num [q]
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    let a : ℤ := 2 ^ q j
    change a + 1 = 3 ^ (j + 1) * c at hc
    have ha : a + 1 = 3 * (3 ^ j * c) := by rw [hc, pow_succ]; ring
    let w : ℤ := 3 ^ j * c
    have he : a = 3 * w - 1 := by dsimp [w]; linarith
    refine ⟨c * (3 * w ^ 2 - 3 * w + 1), ?_⟩
    rw [pow_succ 3 j, pow_mul]
    change a ^ 3 + 1 = _
    calc
      a ^ 3 + 1 = (a + 1) * (3 * (3 * w ^ 2 - 3 * w + 1)) := by rw [he]; ring
      _ = _ := by rw [hc, pow_succ 3 (j + 1)]; ring

private lemma shifted_pair_integer {j n : ℕ} (hn : 2 * q j ≤ n) :
    ∃ z : ℤ, (2 : ℝ) ^ n * pairTerm j = z := by
  have hd : (3 : ℤ) ^ j ∣ 2 ^ q j + 1 :=
    (pow_dvd_pow 3 (Nat.le_succ j)).trans (pair_divisibility j)
  obtain ⟨c, hc⟩ := hd
  have hc' : (2 : ℝ) ^ q j + 1 = (q j : ℝ) * c := by exact_mod_cast hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨2 ^ d * c, ?_⟩
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [pairTerm, pow_add, show 2 * q j = q j + q j by omega, pow_add,
    one_div_pow, one_div_pow, pow_add]
  field_simp
  exact hc'

private lemma pow_gap (s i : ℕ) : q s + i ≤ q (i + s) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.succ_add]
    change q s + (i + 1) ≤ 3 ^ ((i + s) + 1)
    rw [pow_succ]
    have : 0 < q (i + s) := by positivity
    change q s + (i + 1) ≤ q (i + s) * 3
    omega

/-- Even after shifting, all the uninserted pairs are dominated by a geometric series. -/
private lemma tail_term_le (s i n : ℕ) (hn : n ≤ q s) :
    (2 : ℝ) ^ n * pairTerm (i + s) ≤ (2 / (q s : ℝ)) * half ^ i := by
  let Q := q (i + s)
  have hgap : n + i ≤ Q := (Nat.add_le_add_right hn i).trans (pow_gap s i)
  have hq : (q s : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show q s ≤ Q by
    have := pow_gap s i; dsimp [Q]; omega)
  have hQ : (0 : ℝ) < Q := by dsimp [Q, q]; positivity
  have hsmall : half ^ (2 * Q) ≤ half ^ Q :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hdec : half ^ Q ≤ half ^ (n + i) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap
  have hterm : pairTerm (i + s) ≤ (2 * half ^ (n + i)) / (q s : ℝ) := by
    change (half ^ Q + half ^ (2 * Q)) / (Q : ℝ) ≤ _
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) hq
  calc
    _ ≤ (2 : ℝ) ^ n * ((2 * half ^ (n + i)) / (q s : ℝ)) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = _ := by rw [pow_add, one_div_pow]; field_simp

private lemma summable_scaled_pair (s n : ℕ) (hn : n ≤ q s) :
    Summable (fun i => (2 : ℝ) ^ n * pairTerm (i + s)) :=
  .of_nonneg_of_le (fun i => by unfold pairTerm; positivity)
    (fun i => tail_term_le s i n hn)
    ((summable_geometric_of_lt_one (r := half) (by norm_num) (by norm_num)).mul_left _)

private lemma pair_summable : Summable pairTerm := by
  simpa using summable_scaled_pair 0 0 (by decide)

/-- The Stoneham-type component indexed by `m` in the shared conversation. -/
@[expose] noncomputable def component (m : ℕ) : ℝ :=
  ∑' j : ℕ, (1/2 : ℝ) ^ (m * 3 ^ j) / ((m : ℝ) * (3 : ℝ)^j)

theorem resonantSum_eq_components : resonantSum = component 1 + 2 * component 2 := by
  let f (j : ℕ) := half ^ q j / (q j : ℝ)
  let g (j : ℕ) := 2 * (half ^ (2 * q j) / (2 * (q j : ℝ)))
  have he (j : ℕ) : pairTerm j = f j + g j := by
    dsimp [pairTerm, f, g, q]; ring
  have hf : Summable f := .of_nonneg_of_le (fun i => by dsimp [f]; positivity)
    (fun i => by rw [he]; apply le_add_of_nonneg_right; dsimp [g]; positivity) pair_summable
  have hg : Summable g := .of_nonneg_of_le (fun i => by dsimp [g]; positivity)
    (fun i => by rw [he]; apply le_add_of_nonneg_left; dsimp [f]; positivity) pair_summable
  unfold resonantSum
  simp_rw [he]
  rw [hf.tsum_add hg]
  simp [f, g, q, component, tsum_mul_left]

private lemma tail_bound (s n : ℕ) (hn : n ≤ q s) :
    (∑' i, (2 : ℝ) ^ n * pairTerm (i + s)) ≤ 4 / (q s : ℝ) := by
  calc
    _ ≤ ∑' i : ℕ, (2 / (q s : ℝ)) * half ^ i :=
      (summable_scaled_pair s n hn).tsum_le_tsum (fun i => tail_term_le s i n hn)
        ((summable_geometric_of_lt_one (r := half) (by norm_num) (by norm_num)).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

/-- Throughout this interval of starting positions the next two binary digits are zero. -/
theorem resonant_zero_block {k n : ℕ} (hk : 2 ≤ k) (hlo : 2 * 3 ^ k ≤ n)
    (hhi : n < 3 * 3 ^ k) : shift 2 resonantSum n < 1 / 4 := by
  have hupper : n ≤ q (k + 1) := by change n ≤ 3 ^ (k + 1); rw [pow_succ]; omega
  have hinter : ∀ j ∈ range (k + 1), ∃ z : ℤ, (2 : ℝ) ^ n * pairTerm j = z := by
    intro j hj
    apply shifted_pair_integer
    have hjk : j ≤ k := by simpa using mem_range.mp hj
    exact (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hjk)).trans hlo
  choose z hz using hinter
  let Z : ℤ := ∑ j ∈ (range (k + 1)).attach, z j.1 j.2
  have hsum : (∑ j ∈ range (k + 1), (2 : ℝ) ^ n * pairTerm j) = Z := by
    simp only [Z, Int.cast_sum, ← hz]
    exact (sum_attach (range (k+1)) (fun j => (2 : ℝ) ^ n * pairTerm j)).symm
  let tail := ∑' i, (2 : ℝ) ^ n * pairTerm (i + (k + 1))
  have hsplit : (2 : ℝ) ^ n * resonantSum = Z + tail := by
    rw [← hsum, resonantSum, ← tsum_mul_left]
    exact ((pair_summable.mul_left ((2 : ℝ) ^ n)).sum_add_tsum_nat_add (k + 1)).symm
  have hnonneg : 0 ≤ tail := tsum_nonneg (fun i => by unfold pairTerm; positivity)
  have hpow : 27 ≤ q (k + 1) := Nat.pow_le_pow_right (n := 3) (by decide) (show 3 ≤ k + 1 by omega)
  have hlt : tail < 1 / 4 := by
    apply (tail_bound _ _ hupper).trans_lt
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (q (k + 1) : ℝ))]
    have : (27 : ℝ) ≤ (q (k + 1) : ℝ) := by exact_mod_cast hpow
    linarith
  simpa [shift, hsplit, Int.fract_eq_self.mpr ⟨hnonneg, (show tail < 1 by linarith)⟩] using hlt

/-- The paired positive series in the conversation fails binary normality. -/
theorem resonantSum_not_normal : ¬ NormalIn 2 resonantSum := by
  apply not_normal_of_frequent_excess (k := 2) (m := 0) (δ := 1/12)
    (by decide) (by decide) (by norm_num)
  rw [frequently_atTop]
  intro M
  let k := M + 2
  let Q := q k
  have hbig := pow_gap 0 k
  refine ⟨3 * Q, by dsimp [Q, k] at *; simpa using (show M ≤ 3 * q (M + 2) by omega), ?_⟩
  have hsub : Ico (2 * Q) (3 * Q) ⊆ (range (3 * Q)).filter
      (fun i => 0 ≤ shift 2 resonantSum i ∧ shift 2 resonantSum i < 1 / 4) := by
    intro i hi
    obtain ⟨hl, hu⟩ := mem_Ico.mp hi
    exact mem_filter.mpr ⟨mem_range.mpr hu, Int.fract_nonneg _,
      resonant_zero_block (k := k) (by dsimp [k]; omega) hl hu⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Ico, show 3 * Q - 2 * Q = Q by omega] at hcard
  norm_num [frequency]
  rw [le_div_iff₀ (by dsimp [Q, q]; positivity)]
  linarith [Nat.cast_le (α := ℝ).mpr hcard]

theorem components_not_binary_normal : ¬ NormalIn 2 (component 1 + 2 * component 2) :=
  resonantSum_eq_components ▸ resonantSum_not_normal

end NormalityChecker
