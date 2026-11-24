import NormalityChecker.CorrectedStrides
import NormalityChecker.DiagonalStep

/-! Rational identities for the corrected-numerator research note. -/
namespace NormalityChecker.PhaseThirteen

open CorrectedStrides

/-- A fixed beta correction turns the stride displacement into one beta value. -/
theorem corrected_step (a : ℤ) (ha : a ≠ 1) (m r : ℕ) :
    corrected a (m+1) r - a * corrected a m r =
      (-1 : ℚ)^r / ((a : ℚ)-1)^r * logDifference r m := by
  have nz : (a : ℚ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ha)
  induction r with
  | zero => simp [corrected, raw, difference_zero]
  | succ r ih =>
    rw [corrected, corrected, ← difference_step]
    simp only [pow_succ]
    linear_combination (norm := (field_simp [nz]; ring)) ih

private theorem phase_model (m r s : ℕ) :
    model (6*m) r s = 2 * corrected 4 (3*m) r - corrected (-8) (2*m) s := by
  have two : 6*m/2 = 3*m := by omega
  have three : 6*m/3 = 2*m := by omega
  simp [model, mulTwo, mulThree, two, three, show 6*m%2=0 by omega,
    show 6*m%3=0 by omega, pow_mul]

/-- Six binary positions give three positive-radix steps and two signed-radix steps. -/
theorem six_step (m r s : ℕ) :
    model (6*(m+1)) r s - 64 * model (6*m) r s =
      2 * ((-1:ℚ)^r / 3^r) * (16 * logDifference r (3*m) +
        4 * logDifference r (3*m+1) + logDifference r (3*m+2)) +
      (7 * logDifference s (2*m) + logDifference (s+1) (2*m)) / 9^s := by
  rw [phase_model, phase_model, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
  have positive (i : ℕ) := corrected_step 4 (by decide) i r
  have negative (i : ℕ) := corrected_step (-8) (by decide) i s
  norm_num at positive negative
  have signed : (-1:ℚ)^s / (-9:ℚ)^s = 1 / 9^s := by
    rw [← div_pow, ← one_div_pow]
    norm_num
  rw [← difference_step]
  simp only [signed] at negative
  linear_combination (norm := ring_nf)
    32 * positive (3*m) + 8 * positive (3*m+1) + 2 * positive (3*m+2)
    + 8 * negative (2*m) - negative (2*m+1)

private theorem beta_strictAnti (r : ℕ) : StrictAnti (logDifference r) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have pos : 0 < logDifference (r+1) n := by unfold logDifference; positivity
  linarith [difference_step r n]

/-- For even positive-stride order, the actual six-position increments decrease strictly. -/
theorem six_step_strictAnti (r s : ℕ) (hr : Even r) :
    StrictAnti (fun m => model (6*(m+1)) r s - 64 * model (6*m) r s) := by
  intro m n h
  dsimp only
  rw [six_step, six_step, hr.neg_one_pow]
  have two : 2*m < 2*n := by omega
  have first : 3*m < 3*n := by omega
  have second : 3*m+1 < 3*n+1 := by omega
  have third : 3*m+2 < 3*n+2 := by omega
  have p : (0:ℚ) < 2 * (1 / 3^r) := by positivity
  apply add_lt_add
  · apply mul_lt_mul_of_pos_left _ p
    linarith [beta_strictAnti r first, beta_strictAnti r second, beta_strictAnti r third]
  · apply div_lt_div_of_pos_right _ (by positivity)
    linarith [beta_strictAnti s two, beta_strictAnti (s+1) two]

/-- The three-position determinant is positive for an orbit with decreasing increments. -/
theorem positive_determinant (b : ℚ) (hb : 1 < b) (z : ℕ → ℚ)
    (dec : StrictAnti (fun n => z (n+1) - b*z n)) (n : ℕ)
    {h k : ℕ} (hh : 0 < h) (hk : h < k) :
    0 < (b^k-1)*(z (n+h)-b^h*z n) - (b^h-1)*(z (n+k)-b^k*z n) := by
  let f (j : ℕ) := z (n+j+1) - b*z (n+j)
  let d (j : ℕ) := z (n+j) - b^j*z n
  have step (j : ℕ) : d (j+1) = b*d j + f j := by
    simp only [d, f, ← Nat.add_assoc, pow_succ]
    ring
  let margin (j : ℕ) := (b-1)*d j - (b^j-1)*f j
  have improve (j : ℕ) (old : 0 ≤ margin j) : 0 < margin (j+1) := by
    have drop : 0 < f j - f (j+1) := sub_pos.mpr (dec (show n+j < n+(j+1) by omega))
    have pos := mul_pos (sub_pos.mpr (one_lt_pow₀ hb (Nat.succ_ne_zero j))) drop
    have scaled := mul_nonneg (by linarith : 0 ≤ b) old
    dsimp only [margin] at scaled ⊢
    rw [step, pow_succ]
    rw [pow_succ] at pos
    linarith only [pos, scaled]
  have bound (j : ℕ) : 0 ≤ margin j := by
    induction j with
    | zero => simp [margin, d]
    | succ j ih => exact (improve j ih).le
  have slopes : StrictAnti (fun j : ℕ => d (j+1)/(b^(j+1)-1)) := by
    apply strictAnti_nat_of_succ_lt
    intro j
    rw [div_lt_div_iff₀ (sub_pos.mpr (one_lt_pow₀ hb (by omega)))
      (sub_pos.mpr (one_lt_pow₀ hb (by omega))), step (j+1), pow_succ b (j+1)]
    have pos := improve j (bound j)
    dsimp only [margin] at pos
    linarith only [pos]
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have cmp := slopes (show h < k by omega)
  dsimp only at cmp
  rw [div_lt_div_iff₀ (sub_pos.mpr (one_lt_pow₀ hb (by omega)))
    (sub_pos.mpr (one_lt_pow₀ hb (by omega)))] at cmp
  change 0 < (b^(k+1)-1)*d (h+1) - (b^(h+1)-1)*d (k+1)
  linarith only [cmp]

/-- The integer cleared in the cross-prime argument has a positive rational factor. -/
theorem six_determinant (r s n : ℕ) (hr : Even r) {h k : ℕ} (hh : 0 < h) (hk : h < k) :
    0 < ((64:ℚ)^k-1) * (model (6*(n+h)) r s - 64^h * model (6*n) r s) -
      ((64:ℚ)^h-1) * (model (6*(n+k)) r s - 64^k * model (6*n) r s) :=
  positive_determinant 64 (by norm_num) (fun m => model (6*m) r s)
    (six_step_strictAnti r s hr) n hh hk

def diagonal (n : ℕ) : ℚ := logShadow n n

def diagonalStep (n : ℕ) : ℚ := diagonal (n+1) - 2 * diagonal n

/-- The ratio used to telescope the diagonal model, as a division-free identity. -/
theorem diagonal_step_ratio (n : ℕ) :
    (4*(n:ℚ)+6)*diagonalStep (n+1) = -((n:ℚ)+1)*diagonalStep n := by
  have step (j : ℕ) := logShadow_diagonal_step j
  change ∀ j, diagonalStep j * (2*(2*(j:ℚ)+1)*j.centralBinom) = (-1:ℚ)^j*3 at step
  have first := step n
  have second := step (n+1)
  have cb := congrArg (fun k : ℕ => (k:ℚ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at cb second
  rw [pow_succ] at second
  have mult : (2*(n:ℚ)+1)*n.centralBinom ≠ 0 := by positivity [Nat.centralBinom_pos n]
  apply mul_left_cancel₀ mult
  linear_combination (norm := ring_nf)
    (n+1:ℚ)/2 * (first + second) - (2*(n:ℚ)+3)*diagonalStep (n+1)*cb

/-- A consecutive triple lies on an affine function of the doubling progression
at an upper-band prime precisely when its residual factor vanishes there. -/
theorem diagonal_three (n : ℕ) :
    (4*(n:ℚ)+6)*(diagonal (n+2)-3*diagonal (n+1)+2*diagonal n) =
      -(5*(n:ℚ)+7)*diagonalStep n := by
  have hr := diagonal_step_ratio n
  unfold diagonalStep at *
  linear_combination hr

end NormalityChecker.PhaseThirteen
