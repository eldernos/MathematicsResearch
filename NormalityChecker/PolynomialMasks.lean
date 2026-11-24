module

public import NormalityChecker.LocalizedMesh
public import NormalityChecker.LocalizedClearing
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-! Reduced denominators for polynomial weights on masked finite prime supports. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.PolynomialMasks

/-- Integer evaluation at a nonnegative index. -/
abbrev sample (G : ℤ[X]) (m : ℕ) : ℤ := G.eval (m : ℤ)

/-- The shifted rational prefix on a finite set of retained positive indices.
The caller supplies indices at most `n`. -/
def shiftedPrefix (b t n : ℕ) (G : ℤ[X]) (A : Finset ℕ) : ℚ :=
  ∑ m ∈ A, (b : ℚ) ^ (n - m) * (sample G m : ℚ) / (m : ℚ) ^ t

/-- Cancel the order of vanishing at zero before testing the denominator. -/
theorem prefix_cancel (b r t n : ℕ) (G : ℤ[X]) (A : Finset ℕ)
    (positive : ∀ m ∈ A, 0 < m) :
    shiftedPrefix b (r + t) n (X ^ r * G) A = shiftedPrefix b t n G A := by
  apply sum_congr rfl
  intro m hm
  simp only [sample, eval_mul, eval_pow, eval_X, Int.cast_mul, Int.cast_pow, Int.cast_natCast, pow_add]
  field_simp [(positive m hm).ne']

private lemma norm_pow {p : ℕ} [Fact p.Prime] (x : ℚ) (n : ℕ) :
    padicNorm p (x ^ n) = (padicNorm p x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

private lemma norm_nat {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    padicNorm p (m : ℚ) = ((p : ℚ) ^ (m.factorization p))⁻¹ := by
  rw [padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hm.ne'), padicValRat.of_nat,
    zpow_neg, zpow_natCast, Nat.factorization_def _ hp]

private lemma eval_error {p : ℕ} [Fact p.Prime] (G : ℤ[X]) (m : ℕ) :
    padicNorm p ((sample G m : ℚ) - (sample G 0 : ℚ)) ≤ padicNorm p (m : ℚ) := by
  obtain ⟨z, hz⟩ : (m : ℤ) ∣ sample G m - sample G 0 := by
    simpa [sample] using sub_dvd_eval_sub (m : ℤ) 0 G
  have eqn : (sample G m : ℚ) - (sample G 0 : ℚ) = (m : ℚ) * z := by exact_mod_cast hz
  rw [eqn, padicNorm.mul]
  exact mul_le_of_le_one_right (padicNorm.nonneg _) (padicNorm.of_int _)

/-- On the first cell after a retained power, the whole prefix has the exact
local norm of the leading term, for any mask and any polynomial degree.
The threshold is equivalent to `k > v_p(G(0))` for a nonzero constant term. -/
theorem first_cell_norm {b p t n k : ℕ} (hp : p.Prime) (unit : ¬ p ∣ b) (ht : 0 < t)
    (G : ℤ[X]) (A : Finset ℕ) (hit : p ^ k ∈ A)
    (indices : ∀ m ∈ A, 0 < m ∧ m ≤ n) (cell : n < 2 * p ^ k)
    (late : ((p : ℚ) ^ k)⁻¹ < padicNorm p (sample G 0 : ℚ)) :
    padicNorm p (shiftedPrefix b t n G A) = padicNorm p (sample G 0 : ℚ) * (p : ℚ) ^ (k * t) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  let α := padicNorm p (sample G 0 : ℚ)
  let w (m : ℕ) := (b : ℚ) ^ (n - m) * (sample G m : ℚ) / (m : ℚ) ^ (u + 1)
  have pp : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have ppos := zero_lt_one.trans pp
  have unitNorm := (padicNorm.nat_eq_one_iff b).mpr unit
  have weight (m : ℕ) (hm : 0 < m) :
      padicNorm p (w m) = padicNorm p (sample G m : ℚ) * ((p : ℚ) ^ (m.factorization p)) ^ (u + 1) := by
    simp only [w, padicNorm.div, padicNorm.mul, norm_pow, unitNorm, one_pow, one_mul,
      norm_nat hp hm, inv_pow, div_inv_eq_mul]
  have topNorm : padicNorm p (p ^ k : ℕ) = ((p : ℚ) ^ k)⁻¹ := by
    simp [norm_pow, padicNorm.padicNorm_p_of_prime, inv_pow]
  have leading : padicNorm p (sample G (p ^ k) : ℚ) = α := by
    have small := (eval_error (p := p) G (p ^ k)).trans_lt (topNorm.trans_lt late)
    rw [show (sample G (p ^ k) : ℚ) =
        (sample G 0 : ℚ) + ((sample G (p ^ k) : ℚ) - (sample G 0 : ℚ)) by ring,
      padicNorm.add_eq_max_of_ne small.ne', max_eq_left small.le]
  have top : padicNorm p (w (p ^ k)) = α * ((p : ℚ) ^ k) ^ (u + 1) := by
    simpa [hp.factorization_pow, leading, α] using weight (p ^ k) (pow_pos hp.pos _)
  have dominates (m : ℕ) (hm : m ∈ A) (hne : m ≠ p ^ k) :
      padicNorm p (w m) < padicNorm p (w (p ^ k)) := by
    obtain ⟨pos, bound⟩ := indices m hm
    have level : m.factorization p < k := by
      by_contra! h
      obtain ⟨a, ha⟩ := (hp.pow_dvd_iff_le_factorization pos.ne').mpr h
      have powerPos := pow_pos hp.pos k
      have aSmall : a < 2 := by
        apply (Nat.mul_lt_mul_left powerPos).mp
        simpa [← ha, Nat.mul_comm 2] using bound.trans_lt cell
      interval_cases a <;> simp_all
    let V := (p : ℚ) ^ (m.factorization p)
    let U := (p : ℚ) ^ k
    have vp : 0 < V := pow_pos ppos _
    have up : 0 < U := pow_pos ppos _
    have vu : V < U := pow_lt_pow_right₀ pp level
    have ap : 0 < α := (inv_pos.mpr up).trans late
    have boundEval : padicNorm p (sample G m : ℚ) ≤ max α V⁻¹ := by
      calc
        _ = padicNorm p ((sample G 0 : ℚ) + ((sample G m : ℚ) - (sample G 0 : ℚ))) := by congr 1; ring
        _ ≤ _ := padicNorm.nonarchimedean
        _ ≤ max α V⁻¹ := max_le_max_left _ ((eval_error G m).trans_eq (norm_nat hp pos))
    rw [weight m pos, top]
    apply (mul_le_mul_of_nonneg_right boundEval (pow_nonneg vp.le _)).trans_lt
    rw [max_mul_of_nonneg _ _ (pow_nonneg vp.le _), max_lt_iff]
    constructor
    · exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ vu vp.le (Nat.succ_ne_zero u)) ap
    · change V⁻¹ * V ^ (u + 1) < α * U ^ (u + 1)
      have scale : 1 < α * U := (inv_lt_iff_one_lt_mul₀ up).mp late
      calc V⁻¹ * V ^ (u + 1) = V ^ u := by rw [pow_succ']; field_simp
           _ ≤ U ^ u := pow_le_pow_left₀ vp.le vu.le _
           _ < (α * U) * U ^ u := lt_mul_of_one_lt_left (pow_pos up _) scale
           _ = α * U ^ (u + 1) := by rw [pow_succ']; ring
  have ultra : IsNonarchimedean (padicNorm p) := fun _ _ => padicNorm.nonarchimedean
  rw [shiftedPrefix, ultra.apply_sum_eq_of_lt w padicNorm.neg hit dominates, top, pow_mul]

/-- The exact exponent in the reduced denominator. The numerator's constant
term can absorb a fixed number of powers of the chosen prime. -/
theorem first_cell_den_exponent {b p t n k : ℕ} (hp : p.Prime) (unit : ¬ p ∣ b) (ht : 0 < t)
    (G : ℤ[X]) (nonzero : sample G 0 ≠ 0) (A : Finset ℕ) (hit : p ^ k ∈ A)
    (indices : ∀ m ∈ A, 0 < m ∧ m ≤ n) (cell : n < 2 * p ^ k)
    (late : (sample G 0).natAbs.factorization p < k) :
    (shiftedPrefix b t n G A).den.factorization p = k * t - (sample G 0).natAbs.factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  let x := shiftedPrefix b t n G A
  let v := (sample G 0).natAbs.factorization p
  have pp : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have ppos := zero_lt_one.trans pp
  have constant : padicNorm p (sample G 0 : ℚ) = ((p : ℚ) ^ v)⁻¹ := by
    dsimp only [v]
    rw [padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast nonzero), padicValRat.of_int,
      zpow_neg, zpow_natCast, padicValInt, Nat.factorization_def _ hp]
  have threshold : ((p : ℚ) ^ k)⁻¹ < padicNorm p (sample G 0 : ℚ) := by
    rw [constant]
    exact (inv_lt_inv₀ (pow_pos ppos _) (pow_pos ppos _)).mpr (pow_lt_pow_right₀ pp late)
  have vk : v < k * t := late.trans_le (Nat.le_mul_of_pos_right k ht)
  have normX : padicNorm p x = (p : ℚ) ^ (k * t - v) := by
    rw [first_cell_norm hp unit ht G A hit indices cell threshold, constant,
      pow_sub₀ _ ppos.ne' vk.le, inv_mul_eq_div, div_eq_mul_inv]
  have big : 1 < padicNorm p x := normX ▸ one_lt_pow₀ pp (Nat.sub_ne_zero_of_lt vk)
  have den : p ∣ x.den := by
    by_contra h
    have bound := Localized.norm_le_prime_part hp x
    rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero] at bound
    exact big.not_ge bound
  have num : padicNorm p (x.num : ℚ) = 1 := (padicNorm.int_eq_one_iff _).mpr (fun h =>
    Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h))
      den x.reduced)
  have cross := congrArg (padicNorm p) (Rat.den_mul_eq_num x)
  rw [padicNorm.mul, norm_nat hp x.pos, normX, num, inv_mul_eq_div,
    div_eq_one_iff_eq (pow_pos ppos _).ne'] at cross
  exact (pow_right_injective₀ ppos pp.ne') cross.symm

/-- After the base factors clear, the reduced denominator divides a fixed smooth
modulus, uniformly in the polynomial and the retained subset. -/
theorem clean_denominator {b c D t n : ℕ} (hb : 0 < b) (hc : 0 < c)
    (S A : Finset ℕ) (support : ∀ q ∈ S, q ∣ b * c) (size : n ≤ 2 ^ D)
    (indices : ∀ m ∈ A, m ∈ Nat.factoredNumbers S ∧ m + D * t ≤ n) (G : ℤ[X]) :
    (shiftedPrefix b t n G A).den ∣ c ^ (D * t) := by
  let L := c ^ (D * t)
  apply (Rat.den_sum_dvd_lcm_den ..).trans
  apply Finset.lcm_dvd
  intro m hm
  obtain ⟨smooth, age⟩ := indices m hm
  have div := LocalizedSupport.cofactor_dvd (Nat.mul_pos hb hc) support smooth (by omega : m ≤ 2 ^ D)
  have div' := pow_dvd_pow_of_dvd div t
  rw [← pow_mul, mul_pow, mul_comm] at div'
  have cleared : m ^ t ∣ L * b ^ (n - m) :=
    div'.trans (Nat.mul_dvd_mul_left _ (pow_dvd_pow b (by omega)))
  obtain ⟨a, ha⟩ := cleared
  have cross : (L : ℚ) * (b : ℚ) ^ (n - m) = (m : ℚ) ^ t * a := by exact_mod_cast ha
  have eqn : (b : ℚ) ^ (n - m) * (sample G m : ℚ) / (m : ℚ) ^ t =
      Rat.divInt ((a : ℤ) * sample G m) L := by
    rw [Rat.divInt_eq_div]
    push_cast
    field_simp [smooth.1, show L ≠ 0 from (pow_pos hc _).ne']
    linear_combination (sample G m : ℚ) * cross
  change ((b : ℚ) ^ (n - m) * (sample G m : ℚ) / (m : ℚ) ^ t).den ∣ L
  rw [eqn]
  exact_mod_cast Rat.den_dvd ((a : ℤ) * sample G m) L

/-- Exact count of positions certified by a finite selection of powers, at any
cutoff, including a cutoff in the middle of a retained first cell. -/
theorem window_count {p : ℕ} (hp : 2 ≤ p) (E : Finset ℕ) (N : ℕ) :
    ((range N).filter (fun n => ∃ k ∈ E, p ^ k ≤ n ∧ n < 2 * p ^ k)).card =
      ∑ k ∈ E, (min N (2 * p ^ k) - p ^ k) := by
  let I (k : ℕ) := Ico (p ^ k) (min N (2 * p ^ k))
  have eqn : (range N).filter (fun n => ∃ k ∈ E, p ^ k ≤ n ∧ n < 2 * p ^ k) =
      E.biUnion I := by
    ext n
    simp only [I, mem_filter, mem_range, mem_biUnion, mem_Ico, lt_min_iff]
    grind
  have ordered {j k : ℕ} (h : j < k) : 2 * p ^ j ≤ p ^ k := by
    calc 2 * p ^ j ≤ p * p ^ j := Nat.mul_le_mul_right _ hp
         _ = p ^ (j + 1) := (pow_succ' ..).symm
         _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) h
  rw [eqn, card_biUnion]
  · simp [I, Nat.card_Ico]
  · intro j _ k _ ne
    apply disjoint_left.mpr
    intro n hj hk
    obtain ⟨jlo, jhi⟩ := mem_Ico.mp hj
    obtain ⟨klo, khi⟩ := mem_Ico.mp hk
    rcases lt_or_gt_of_ne ne with h | h
    · exact ((lt_min_iff.mp jhi).2.trans_le (ordered h)).not_ge klo
    · exact ((lt_min_iff.mp khi).2.trans_le (ordered h)).not_ge jlo

/-- Polynomially growing signed weights are uniformly small after a sufficiently
long gap. The constant depends only on the geometric ratio and degree. -/
theorem polynomial_gap_tail {q : ℝ} (hq : 0 < q) (small : q < 1) (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : ℕ → ℝ) (C : ℝ), 0 ≤ C →
      (∀ m, |a m| ≤ C * ((m : ℝ) + 1) ^ d) → ∀ n g : ℕ,
      (∀ j < g, a (n + j) = 0) →
      |∑' j : ℕ, a (n + j) * q ^ j| ≤ C * ((n : ℝ) + g + 1) ^ d * q ^ g * K := by
  let w (j : ℕ) := ((j : ℝ) + 1) ^ d * q ^ j
  have moment := summable_pow_mul_geometric_of_norm_lt_one d (by simpa [Real.norm_eq_abs, abs_of_pos hq] : ‖q‖ < 1)
  have hw : Summable w := by
    convert (((summable_nat_add_iff 1).mpr moment).mul_right q⁻¹) using 1
    ext j
    simp [w, pow_succ, hq.ne', mul_assoc]
  refine ⟨∑' j, w j, tsum_nonneg (fun j => by dsimp [w]; positivity), ?_⟩
  intro a C hC bound n g gap
  have each (j : ℕ) : |a (n + (j + g)) * q ^ (j + g)| ≤
      (C * ((n : ℝ) + g + 1) ^ d * q ^ g) * w j := by
    rw [abs_mul, abs_of_pos (pow_pos hq _), pow_add]
    have base : ((n + (j + g) : ℕ) : ℝ) + 1 ≤ ((n : ℝ) + g + 1) * (j + 1) := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (Nat.cast_nonneg (α := ℝ) g),
        mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (Nat.cast_nonneg (α := ℝ) n)]
    have estimate := (bound (n + (j + g))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) base d) hC)
    apply (mul_le_mul_of_nonneg_right estimate (by positivity : 0 ≤ q ^ j * q ^ g)).trans_eq
    rw [mul_pow]; dsimp [w]; ring
  have major := hw.mul_left (C * ((n : ℝ) + g + 1) ^ d * q ^ g)
  have tail : Summable (fun j : ℕ => a (n + (j + g)) * q ^ (j + g)) :=
    major.of_norm_bounded (by simpa only [Real.norm_eq_abs] using each)
  have total : Summable (fun j : ℕ => a (n + j) * q ^ j) := (summable_nat_add_iff g).mp tail
  have head : ∑ j ∈ range g, a (n + j) * q ^ j = 0 := sum_eq_zero (fun j hj => by rw [gap j (mem_range.mp hj), zero_mul])
  have split := total.sum_add_tsum_nat_add g
  simp only [head, zero_add] at split
  rw [← split, ← tsum_mul_left]
  apply le_trans ?_
    (tail.abs.tsum_le_tsum each major)
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm tail.norm

end NormalityChecker.PolynomialMasks
