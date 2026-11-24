module

public import NormalityChecker.ParameterTwoSquareProfile
public import NormalityChecker.ArithmeticCertificate

/-! Base-`b` normality of the positive-index Stoneham square with parameter two. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ParameterTwoSquare

private lemma den_range {b n : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hn : 0 < n)
    (hk : 2 ≤ Nat.log 2 n) :
    ∃ e, (pre b n).den = 2^e ∧ Nat.log 2 n - 1 ≤ e ∧ e ≤ 2*Nat.log 2 n := by
  have h := (exact_profile hb odd).2 _ hk n (Nat.pow_log_le_self _ hn.ne')
    (Nat.lt_pow_succ_log_self (by decide) _)
  split_ifs at h <;> exact ⟨_, h, by omega, by omega⟩

/-- In every odd radix at least three the parameter-two Stoneham square is normal. -/
theorem square_normal : SquareNormality := by
  intro b hb odd
  apply normal_of_arithmetic_certificate (c:=2) (B:=2) (L:=2) (by omega) (by decide)
    (by decide) _ (pre b) (shifted_tail (by omega))
    (fixed_support_orbit_estimate (by omega) (by decide) odd.coprime_two_right) 6
  intro u hu M η pos
  have dec := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)).const_mul 32
  simp only [mul_zero] at dec
  filter_upwards [eventually_ge_atTop (max M 2), dec.eventually_le_const pos] with k hk small
  let B := 2^k
  let S := ((range (2*(k+1))) ×ˢ range (2*(k+1))).image (fun v => location v.1 v.2)
  let E := insertionBlocks S B (u*B)
  have bp : 0 < B := pow_pos (by decide) _
  have cnt : S.card ≤ (2*(k+1))^2 := by simpa [S, pow_two] using
    (card_image_le (s:=(range (2*(k+1))) ×ˢ range (2*(k+1))) (f:=fun v => location v.1 v.2))
  have exp : (4 : ℕ)^(k+1) = 2^(2*(k+1)) := by rw [pow_mul]; rfl
  have cover (i j : ℕ) (h : location i j < 4^(k+1)) : location i j ∈ S := by
    rw [exp] at h
    have a := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp ((Nat.le_add_right ..).trans_lt h)
    have c := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp ((Nat.le_add_left ..).trans_lt h)
    exact mem_image.mpr ⟨(i,j), mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,rfl⟩
  refine ⟨E, ?_, ?_⟩
  · have bound := (card_insertionBlocks S B (u*B)).trans (Nat.mul_le_mul_left 2 cnt)
    have kr : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have price : (E.card : ℝ) ≤ 32*(k : ℝ)^2 := by
      have bd : (E.card : ℝ) ≤ 2*(2*((k : ℝ)+1))^2 := by exact_mod_cast bound
      exact bd.trans (by nlinarith [sq_nonneg ((k : ℝ)-1)])
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at small
    exact price.trans small
  · intro l hl good
    let n := (u*B+l)*B
    have un : 1 ≤ u := (mem_Ico.mp hu).1
    have uu : u < 4 := (mem_Ico.mp hu).2
    have lo : 2^(2*k) ≤ n := by
      rw [Nat.mul_comm 2 k, pow_mul, pow_two]
      apply Nat.mul_le_mul_right
      exact (Nat.le_mul_of_pos_left B un).trans (Nat.le_add_right ..)
    have hi : n+B ≤ 4^(k+1) := by
      have eqn : B*B = 4^k := by rw [← mul_pow]; rfl
      calc n+B = (u*B+l+1)*B := by dsimp [n]; ring
           _ ≤ ((u+1)*B)*B := by apply Nat.mul_le_mul_right; rw [Nat.add_mul,one_mul]; change l<B at hl; omega
           _ = (u+1)*(B*B) := Nat.mul_assoc ..
           _ ≤ 4*(B*B) := Nat.mul_le_mul_right _ uu
           _ = _ := by rw [eqn,pow_succ']
    have low := Nat.le_log_of_pow_le (by decide : 1<2) lo
    have np := (pow_pos (by decide : 0<2) _).trans_le lo
    have top : Nat.log 2 n < 2*(k+1) := Nat.log_lt_of_lt_pow np.ne' (by rw [← exp]; omega)
    obtain ⟨e, den, lower, upper⟩ := den_range hb odd np (by omega)
    change M ≤ (pre b n).den ∧ _ ∧ _ ∧ _
    refine ⟨den ▸ ((by omega : M ≤ e).trans (Nat.lt_pow_self (by decide : 1<2)).le),
      ⟨e,den ▸ dvd_rfl⟩, ?_, ?_⟩
    · change (pre b n).den ≤ (2^k)^6
      rw [den, ← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · intro i hi'
      change pre b (n+i) = (b : ℚ)^i * pre b n
      apply follows (by omega)
      intro a c gt
      by_contra! inc
      have gap := insertionBlocks_free bp good (cover a c (by change i<B at hi'; omega)) (by
        rw [Nat.add_mul,one_mul]
        change location a c < n+B
        change i<B at hi'
        omega)
      change location a c + B ≤ n at gap
      omega

end NormalityChecker.ParameterTwoSquare
