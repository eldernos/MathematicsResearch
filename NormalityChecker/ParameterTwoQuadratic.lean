module

public import NormalityChecker.ParameterTwoQuadraticLimit
public import NormalityChecker.ParameterTwoSquareProfile

/-! Reduced upper-shell denominators of the positive-index Stoneham quadratic.
The use of norms includes an exact zero in the cancellation factor. -/
@[expose] public noncomputable section
open Finset Filter
open NormalityChecker.ParameterTwoSquare
namespace NormalityChecker.ParameterTwoQuadratic

def linearPrefix (b n : ℕ) : ℚ :=
  (b : ℚ)^n * ∑ i ∈ range (Nat.log 2 n), term b i

def «prefix» (b n : ℕ) (A B C₀ : ℤ) : ℚ :=
  A * pre b n + B * linearPrefix b n + C₀ * (b : ℚ)^n

def kappa (b : ℕ) (A B : ℤ) : ℚ_[2] :=
  -(2*A+B+2*A*intercept b) / (2*A*slope b)

/-- On any nonempty shell the reduced denominator of the linear prefix divides
`2^k`. Its integer numerator at that common denominator is supplied as well. -/
theorem linear_form {b n k : ℕ} (hb : 0 < b) (lo : 2^k ≤ n) (hi : n < 2^(k+1)) :
    linearPrefix b n = (((b : ℤ)^(n-2^k) * axisNumerator b k : ℤ) : ℚ) / 2^k := by
  have h := clear_axis hb k
  rw [weighted_eq] at h
  rw [linearPrefix, Nat.log_eq_of_pow_le_of_lt_pow lo hi, eq_div_iff (by positivity)]
  push_cast
  rw [← h, pow_sub₀ _ (by exact_mod_cast hb.ne') lo]
  field_simp

theorem prefix_dyadic {b n k : ℕ} (hb : 0 < b) (lo : 2^k ≤ n) (hi : n < 2^(k+1))
    (A B C₀ : ℤ) : ∃ D : ℕ, («prefix» b n A B C₀).den ∣ 2^D := by
  have lin : (linearPrefix b n).den ∣ 2^k := by
    rw [linear_form hb lo hi]
    let u := (b : ℤ)^(n-2^k) * axisNumerator b k
    exact_mod_cast (show (((u : ℚ) / ((2^k : ℤ) : ℚ)).den : ℤ) ∣ (2^k : ℤ) by
      rw [Rat.intCast_div_eq_divInt]; exact Rat.den_dvd ..)
  obtain ⟨d, hd⟩ := dyadic hb n
  have coeff (c : ℤ) (x : ℚ) : ((c : ℚ)*x).den ∣ x.den := by simpa using Rat.mul_den_dvd (c : ℚ) x
  have hc : (C₀ * (b : ℚ)^n).den = 1 := by exact_mod_cast Rat.den_intCast (C₀ * (b : ℤ)^n)
  use d+k
  rw [«prefix», pow_add]
  refine (Rat.add_den_dvd ..).trans ?_
  rw [hc, mul_one]
  exact (Rat.add_den_dvd ..).trans (Nat.mul_dvd_mul ((coeff ..).trans hd) ((coeff ..).trans lin))

theorem dyadic_den_eq_norm {x : ℚ} {D : ℕ} (hx : x.den ∣ 2^D) :
    (x.den : ℝ) = max 1 ‖(x : ℚ_[2])‖ := by
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx
  have form := congrArg (fun y : ℚ => (y : ℚ_[2])) (Rat.num_div_den x)
  push_cast at form
  rw [← form, he]
  push_cast
  rw [norm_div, norm_pow, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p:=2)]
  cases e with
  | zero => simp [max_eq_left (Padic.norm_int_le_one (p:=2) x.num)]
  | succ e =>
    have hc := x.reduced
    rw [he, Nat.coprime_pow_right_iff (by omega)] at hc
    have hu : ‖(x.num : ℚ_[2])‖ = 1 := by
      rw [← norm_natAbs, Padic.norm_natCast_eq_one_iff]; exact hc.symm
    rw [hu, inv_pow, div_inv_eq_mul, one_mul, max_eq_right (by exact one_le_pow₀ (by norm_num))]

private lemma upper_square {b n j : ℕ} (mid : 3*2^j ≤ n) (hi : n < 2^(j+2)) :
    pre b n = (b : ℚ)^n * ((∑ i ∈ range (j+1), term b i)^2 - (term b j)^2) := by
  have lo : 2^(j+1) ≤ n := by rw [pow_succ]; omega
  rw [pre, Nat.log_eq_of_pow_le_of_lt_pow lo hi]
  congr 1
  have cell {i l : ℕ} (hi' : i < j+1) (hl : l < j+1) :
      (if location i l ≤ n then term b i * term b l else 0) =
      term b i * term b l - (if i = j ∧ l = j then term b j ^ 2 else 0) := by
    have le {t : ℕ} (ht : t < j+1) : 2^(t+1) ≤ 2^(j+1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have lt {t : ℕ} (ht : t < j) : 2^(t+1) ≤ 2^j := Nat.pow_le_pow_right (by decide) ht
    by_cases eqi : i = j <;> by_cases eql : l = j
    · subst i; subst l
      have h : ¬location j j ≤ n := by dsimp [location]; rw [pow_succ (2 : ℕ) (j+1)] at hi; omega
      simp [h, sq]
    all_goals
      have h : location i l ≤ n := by
        dsimp [location]
        first
        | have h₁ := lt (show i < j by omega); have h₂ := le hl; rw [pow_succ] at h₂; omega
        | have h₁ := lt (show l < j by omega); have h₂ := le hi'; rw [pow_succ] at h₂; omega
      rw [ite_eq_left h]
      simp [eqi, eql]
  unfold boxSum
  calc
    _ = ∑ i ∈ range (j+1), ∑ l ∈ range (j+1),
        (term b i * term b l - if i=j ∧ l=j then term b j^2 else 0) :=
      sum_congr rfl fun _ hi' => sum_congr rfl fun _ hl => cell (mem_range.mp hi') (mem_range.mp hl)
    _ = _ := by simp [sum_sub_distrib, ite_and, ← mul_sum, ← sum_mul, sq]

private lemma term_eq (b j : ℕ) : (term b j : ℚ_[2]) = delta b j + ((2 : ℚ_[2])^(j+1))⁻¹ := by
  simp [term, delta, div_eq_mul_inv, mul_comm]
  ring

private lemma axis_eq (b k : ℕ) : (∑ i ∈ range k, (term b i : ℚ_[2])) =
    1 + (∑ i ∈ range k, delta b i) - ((2 : ℚ_[2])^k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ, ih, term_eq, pow_succ]
    field_simp
    ring

private lemma norm_of_integral_difference {x y : ℚ_[2]} (h : ‖x+y‖ ≤ 1) :
    max 1 ‖x‖ = max 1 ‖y‖ := by
  by_cases hy : 1 < ‖y‖
  · rw [Padic.norm_eq_of_norm_add_lt_right (h.trans_lt hy)]
  · have h' := Padic.nonarchimedean (x+y) (-y)
    simp only [add_neg_cancel_right, norm_neg] at h'
    rw [max_eq_left (h'.trans (max_le h (le_of_not_gt hy))), max_eq_left (le_of_not_gt hy)]

private lemma error_integral {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (A : ℤ) (j : ℕ) :
    ‖2 * (A : ℚ_[2]) * (cancellation b j - ((j+1 : ℕ) : ℚ_[2]) * slope b - intercept b) /
      (2 : ℚ_[2])^(j+1)‖ ≤ 1 := by
  rw [norm_div, norm_pow, norm_mul, norm_mul,
    show ‖(2 : ℚ_[2])‖ = 1/2 from by simpa using Padic.norm_p (p:=2)]
  apply (div_le_one (by positivity)).mpr
  have hd := delta_zero_norm_lt_one odd
  calc
    _ ≤ (1/2 * 1) * ((1/2 : ℝ)^j * 1) := by
      gcongr
      · exact Padic.norm_int_le_one _
      · refine (affine_error_le hb odd _).trans ?_
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hd.le
    _ = _ := by ring

/-- Exact reduced denominator on the entire closed-left upper half shell,
with `k=j+1`. If the shell index equals `kappa`, the norm vanishes and
the reduced denominator is one. -/
theorem upper_denominator {b n j : ℕ} (hb : 3 ≤ b) (odd : Odd b)
    (mid : 3*2^j ≤ n) (hi : n < 2^(j+2)) (A B C₀ : ℤ) (hA : A ≠ 0) :
    ((«prefix» b n A B C₀).den : ℝ) =
      max 1 ((2 : ℝ)^(j+1) * ‖2 * (A : ℚ_[2]) * slope b * (((j+1 : ℕ) : ℚ_[2]) - kappa b A B)‖) := by
  have lo : 2^(j+1) ≤ n := by rw [pow_succ]; omega
  obtain ⟨_, hd⟩ := prefix_dyadic (by omega : 0 < b) lo hi A B C₀
  rw [dyadic_den_eq_norm hd]
  let H := 1 + ∑ i ∈ range (j+1), delta b i
  let U : ℚ_[2] := A*(H^2-delta b j^2)+B*H+C₀
  let V : ℚ_[2] := 2*A*slope b*(((j+1 : ℕ) : ℚ_[2])-kappa b A B)
  let E := cancellation b j - ((j+1 : ℕ) : ℚ_[2])*slope b - intercept b
  let x : ℚ_[2] := U - (2*A+B+2*A*cancellation b j)/2^(j+1)
  have shifted : («prefix» b n A B C₀ : ℚ_[2]) = (b : ℚ_[2])^n * x := by
    rw [«prefix», linearPrefix, Nat.log_eq_of_pow_le_of_lt_pow lo hi, upper_square mid hi]
    push_cast
    rw [axis_eq, term_eq]
    dsimp [x, U, H, cancellation]
    field_simp
    ring
  have sl : slope b ≠ 0 := norm_ne_zero_iff.mp (by rw [slope_norm hb odd]; exact norm_ne_zero_iff.mpr (delta_zero_ne hb))
  have hn : (A : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr hA
  have id : x + V/2^(j+1) = U - 2*A*E/2^(j+1) := by
    dsimp [x, V, E, kappa]
    field_simp
    ring
  have dl (i : ℕ) : ‖delta b i‖ ≤ 1 := by rw [delta_norm hb odd]; exact (delta_zero_norm_lt_one odd).le
  have HH : ‖H‖ ≤ 1 := (Padic.nonarchimedean _ _).trans
    (max_le (by simp) (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => dl i)))
  have add {u v : ℚ_[2]} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖u+v‖ ≤ 1 :=
    (Padic.nonarchimedean _ _).trans (max_le hu hv)
  have mul {u v : ℚ_[2]} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖u*v‖ ≤ 1 := by
    rw [norm_mul]; exact (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans (by simpa using hv)
  have sub {u v : ℚ_[2]} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖u-v‖ ≤ 1 := by
    simpa only [sub_eq_add_neg] using add hu (show ‖-v‖ ≤ 1 by simpa)
  have uu : ‖U‖ ≤ 1 := add (add (mul (Padic.norm_int_le_one A)
    (sub (by simpa only [sq] using mul HH HH) (by simpa only [sq] using mul (dl j) (dl j))))
    (mul (Padic.norm_int_le_one B) HH)) (Padic.norm_int_le_one C₀)
  have same := norm_of_integral_difference (x:=x) (y:=V/2^(j+1))
    (by rw [id]; exact sub uu (error_integral hb odd A j))
  rw [shifted, norm_mul, norm_pow, radix_norm odd, one_pow, one_mul, same, norm_div, norm_pow,
    show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p:=2), inv_pow, div_inv_eq_mul, mul_comm]

theorem linear_norm {b n k : ℕ} (hb : 0 < b) (odd : Odd b) (hk : 1 ≤ k)
    (lo : 2^k ≤ n) (hi : n < 2^(k+1)) :
    ‖(linearPrefix b n : ℚ_[2])‖ = (2 : ℝ)^k := by
  have ao := axis_odd (b:=b) hk
  have h : ‖(axisNumerator b k : ℚ_[2])‖ = 1 := by
    rw [← norm_natAbs, Padic.norm_natCast_eq_one_iff]; exact ao.natAbs.coprime_two_left
  rw [linear_form hb lo hi]
  push_cast
  rw [norm_div, norm_mul, norm_pow, radix_norm odd, h, norm_pow,
    show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ from Padic.norm_p (p:=2)]
  simp

/-- In the lower half, the square contributes the larger pole as soon as the
displayed inequality holds. Its right side bounds the full linear perturbation. -/
theorem lower_denominator {b n j : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hj : 1 ≤ j)
    (lo : 2^(j+1) ≤ n) (early : n < 3*2^j) (A B C₀ : ℤ)
    (dom : (2 : ℝ)^(j+1) < ‖(A : ℚ_[2])‖ * 2^(j+j)) :
    ((«prefix» b n A B C₀).den : ℝ) = ‖(A : ℚ_[2])‖ * 2^(j+j) := by
  have hi : n < 2^(j+2) := by rw [pow_add]; have := Nat.two_pow_pos j; omega
  have den := (first_half_reduction (by omega : 0 < b) odd hj lo hi early).2
  have gt : 1 < (2 : ℝ)^(j+j) := one_lt_pow₀ (by norm_num) (by omega)
  have sqnorm : ‖(pre b n : ℚ_[2])‖ = (2 : ℝ)^(j+j) := by
    have hd := dyadic_den_eq_norm (x:= pre b n) (D:=j+j) (den ▸ dvd_refl _)
    rw [den] at hd
    push_cast at hd
    rcases max_cases 1 ‖(pre b n : ℚ_[2])‖ with h | h <;> linarith [h.1]
  have lnorm := linear_norm (by omega : 0 < b) odd (by omega : 1 ≤ j+1) lo hi
  have bnd : ‖(B : ℚ_[2])*linearPrefix b n + C₀*(b : ℚ_[2])^n‖ ≤ (2 : ℝ)^(j+1) := by
    apply (Padic.nonarchimedean _ _).trans
    rw [norm_mul, norm_mul, norm_pow, radix_norm odd, one_pow, mul_one, lnorm]
    exact max_le (mul_le_of_le_one_left (by positivity) (Padic.norm_int_le_one _))
      ((Padic.norm_int_le_one _).trans (one_le_pow₀ (by norm_num)))
  have ha : ‖(A : ℚ_[2]) * pre b n‖ = ‖(A : ℚ_[2])‖ * 2^(j+j) := by rw [norm_mul,sqnorm]
  have small : ‖(B : ℚ_[2])*linearPrefix b n + C₀*(b : ℚ_[2])^n‖ < ‖(A : ℚ_[2])*pre b n‖ :=
    ha ▸ bnd.trans_lt dom
  obtain ⟨_, hd⟩ := prefix_dyadic (by omega : 0 < b) lo hi A B C₀
  rw [dyadic_den_eq_norm hd, «prefix»]
  push_cast
  rw [add_assoc, Padic.add_eq_max_of_ne small.ne', max_eq_left small.le, ha,
    max_eq_right ((one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))).trans dom.le)]

/-- The lower-half threshold is uniform in the cutoff and in the perturbing
linear and constant integer coefficients. -/
theorem eventually_lower_denominator {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (A : ℤ) (hA : A ≠ 0) :
    ∀ᶠ j : ℕ in Filter.atTop, ∀ n : ℕ, 2^(j+1) ≤ n → n < 3*2^j → ∀ B C₀ : ℤ,
      ((«prefix» b n A B C₀).den : ℝ) = ‖(A : ℚ_[2])‖ * 2^(j+j) := by
  have tend := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℝ))).const_mul_atTop
    (norm_pos_iff.mpr (Int.cast_ne_zero.mpr hA : (A : ℚ_[2]) ≠ 0))
  filter_upwards [tend.eventually_gt_atTop 2, Filter.eventually_ge_atTop 1] with j hj jpos n lo hi B C₀
  apply lower_denominator hb odd jpos lo hi
  rw [pow_succ, pow_add]
  change 2 < ‖(A : ℚ_[2])‖ * 2^j at hj
  nlinarith [mul_lt_mul_of_pos_right hj (show 0 < (2 : ℝ)^j by positivity)]

end NormalityChecker.ParameterTwoQuadratic
