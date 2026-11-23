module

public import NormalityChecker.Resonance
public import Mathlib.Data.Int.ModEq

@[expose] public section
open Finset
namespace NormalityChecker

/-- Removing the fixed factor 1/m leaves the same ternary denominators for every index. -/
noncomputable def insertionTerm (m j : ℕ) : ℝ :=
  (1/2:ℝ)^(m*3^j)/(3:ℝ)^j

private lemma inserted_integer (m j n : ℕ) (h : m*3^j ≤ n) :
    ∃ z : ℤ, (2:ℝ)^n * insertionTerm m j -
        (-1:ℝ)^m*2^n/(3:ℝ)^j = z := by
  have hmod : (2:ℤ)^(3^j:ℕ) ≡ -1 [ZMOD (3:ℤ)^j] := by
    apply Int.modEq_iff_dvd.mpr
    have hd := (pow_dvd_pow (3:ℤ) (Nat.le_succ j)).trans (pair_divisibility j)
    convert hd.neg_right using 1; ring
  have he := (hmod.pow m).mul_right ((-1:ℤ)^m)
  have hs : (-1:ℤ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  rw [hs, ← pow_mul, mul_comm (3^j) m] at he
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  have H := (he.mul_left ((2:ℤ)^d)).dvd
  obtain ⟨z,hz⟩ := H
  have hz' : (2:ℝ)^d*1-2^d*(2^(m*3^j)*(-1)^m) = (3:ℝ)^j*z := by exact_mod_cast hz
  refine ⟨z, ?_⟩
  rw [insertionTerm,pow_add,one_div_pow]
  field_simp
  linear_combination hz'

/-- Shifted prefix of one component, modulo an integer. Only its last ternary
denominator remains after summing the simplified geometric progression. -/
theorem insertion_prefix (m J n : ℕ) (h : m*3^J ≤ n+1) :
    ∃ z : ℤ, (2:ℝ)^(n+1)*(∑ j ∈ range (J+1), insertionTerm m j) +
      (-1:ℝ)^m*2^n/(3:ℝ)^J = z := by
  have ht (j : ℕ) (hj : j ∈ range (J+1)) := inserted_integer m j (n+1)
    ((Nat.mul_le_mul_left m (Nat.pow_le_pow_right (by decide : 0<3)
      (show j≤J by have := mem_range.mp hj; omega))).trans h)
  choose z hz using ht
  let Z : ℤ := ∑ j ∈ (range (J+1)).attach, z j.1 j.2
  have hsum : ∑ j ∈ range (J+1), ((2:ℝ)^(n+1)*insertionTerm m j -
        (-1:ℝ)^m*2^(n+1)/(3:ℝ)^j) = Z := by
    simp only [Z, Int.cast_sum, ← hz]
    exact (sum_attach _ _).symm
  have geom (J : ℕ) : (∑ j ∈ range (J+1), (-1:ℝ)^m*2^(n+1)/(3:ℝ)^j) +
      (-1:ℝ)^m*2^n/(3:ℝ)^J = (-1:ℝ)^m*2^n*3 := by
    induction J with
    | zero => simp [pow_succ]; ring
    | succ J ih =>
      rw [sum_range_succ, ← ih, pow_succ (3:ℝ) J, pow_succ (2:ℝ) n]
      ring
  refine ⟨Z + (-1)^m*2^n*3, ?_⟩
  push_cast
  rw [sum_sub_distrib, ← mul_sum] at hsum
  linarith [geom J]

private lemma index_growth {m : ℕ} (hm : 0<m) (J i : ℕ) :
    m*3^J+i ≤ m*3^(i+J) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.succ_add,pow_succ,← Nat.mul_assoc]
    have : 0<m*3^(i+J) := by positivity
    omega

private lemma insertion_majorant {m : ℕ} (hm : 0<m) (J i n : ℕ) (hn : n≤m*3^J) :
    (2:ℝ)^n*insertionTerm m (i+J) ≤ (1/(3:ℝ)^J)*(1/2:ℝ)^i := by
  have hi : n+i ≤ m*3^(i+J) := (Nat.add_le_add_right hn i).trans (index_growth hm J i)
  have hd : (3:ℝ)^J ≤ 3^(i+J) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1) hi
  unfold insertionTerm
  calc
    _ ≤ (2:ℝ)^n*((1/2:ℝ)^(n+i)/3^J) := by gcongr
    _ = _ := by rw [pow_add, one_div_pow]; field_simp

private lemma ins_summable {m : ℕ} (hm : 0<m) : Summable (insertionTerm m) :=
  .of_nonneg_of_le (fun _ => by unfold insertionTerm; positivity) (fun i => by
    simpa using insertion_majorant hm 0 i 0 (by omega))
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num))

private lemma scaled_component (m : ℕ) (hm : 0<m) :
    (m:ℝ)*component m = ∑' j, insertionTerm m j := by
  rw [component, ← tsum_mul_left]
  apply tsum_congr; intro j; unfold insertionTerm; field_simp

/-- Uniform through the very last starting position before the next insertion. -/
theorem component_orbit_approx {m J n : ℕ} (hm : 0<m)
    (hlo : m*3^J ≤ n+1) (hhi : n+1 ≤ m*3^(J+1)) :
    ∃ z : ℤ, |(2:ℝ)^(n+1)*((m:ℝ)*component m) +
      (-1:ℝ)^m*2^n/(3:ℝ)^J - z| ≤ 2/(3:ℝ)^(J+1) := by
  obtain ⟨z,hz⟩ := insertion_prefix m J n hlo
  refine ⟨z, ?_⟩
  have hs := (ins_summable hm).mul_left ((2:ℝ)^(n+1))
  let tail (i : ℕ) := (2:ℝ)^(n+1)*insertionTerm m (i+(J+1))
  have he : (2:ℝ)^(n+1)*((m:ℝ)*component m) + (-1:ℝ)^m*2^n/(3:ℝ)^J - z =
      ∑' i, tail i := by
    rw [scaled_component m hm, ← tsum_mul_left, ← hs.sum_add_tsum_nat_add (J+1), ← mul_sum, ← hz]
    dsimp [tail]; ring
  rw [he, abs_of_nonneg (tsum_nonneg fun i => by dsimp [tail,insertionTerm]; positivity)]
  calc
    _ ≤ ∑' i : ℕ, (1/(3:ℝ)^(J+1))*(1/2:ℝ)^i :=
      ((summable_nat_add_iff (J+1)).mpr hs).tsum_le_tsum
        (fun i => insertion_majorant hm (J+1) i (n+1) hhi)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
    _ = _ := by rw [tsum_mul_left,tsum_geometric_two]; ring

/-- Adding the one-component estimates with integer weights preserves a single
integer error term even when some weights are negative. -/
theorem finite_orbit_approx (M : Finset ℕ) (c : ℕ → ℤ) (J : ℕ → ℕ) (n : ℕ)
    (hm : ∀ m ∈ M, 0<m) (hl : ∀ m ∈ M, m*3^(J m) ≤ n+1)
    (hu : ∀ m ∈ M, n+1 ≤ m*3^(J m+1)) :
    ∃ z : ℤ, |(2:ℝ)^(n+1)*(∑ m ∈ M, (c m:ℝ)*((m:ℝ)*component m)) +
        2^n*(∑ m ∈ M, (c m:ℝ)*(-1:ℝ)^m/(3:ℝ)^(J m)) - z| ≤
      ∑ m ∈ M, |(c m:ℝ)| *(2/(3:ℝ)^(J m+1)) := by
  choose z hz using fun m (h : m ∈ M) => component_orbit_approx (hm m h) (hl m h) (hu m h)
  let Z := ∑ m ∈ M.attach, c m.1 * z m.1 m.2
  refine ⟨Z, ?_⟩
  let E (m : {a // a ∈ M}) := (2:ℝ)^(n+1)*((m.val:ℝ)*component m.val) +
      (-1:ℝ)^m.val*2^n/(3:ℝ)^(J m.val) - z m.val m.property
  have he : (2:ℝ)^(n+1)*(∑ m ∈ M, (c m:ℝ)*((m:ℝ)*component m)) +
      2^n*(∑ m ∈ M, (c m:ℝ)*(-1:ℝ)^m/(3:ℝ)^(J m)) - Z =
      ∑ m ∈ M.attach, (c m.val:ℝ)* E m := by
    rw [← sum_attach M (fun m => (c m:ℝ)*((m:ℝ)*component m)),
      ← sum_attach M (fun m => (c m:ℝ)*(-1:ℝ)^m/(3:ℝ)^(J m))]
    simp only [Z,Int.cast_sum,Int.cast_mul,mul_sum,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl; intro m _; dsimp [E]; ring
  rw [he, ← sum_attach M (fun m => |(c m:ℝ)| *(2/(3:ℝ)^(J m+1)))]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum; intro m _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hz m.val m.property) (abs_nonneg _)

end NormalityChecker
