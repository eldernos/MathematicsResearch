module

public import NormalityChecker.Dilation

/-! Finite translation estimates for sums along radix orbits. -/
@[expose] public section
open Finset
open scoped ComplexConjugate
namespace NormalityChecker

private lemma shift_sum_error (f : ℕ → ℂ) (unit : ∀ i, ‖f i‖=1) (T r : ℕ) :
    ‖(∑ n∈range T, f (n+r)) - ∑ n∈range T, f n‖ ≤ 2*r := by
  have id := congrArg (fun t : ℕ => ∑ i∈range t, f i) (Nat.add_comm T r)
  simp only [sum_range_add] at id
  have eqn : (∑ n∈range T, f (n+r)) - ∑ n∈range T, f n = (∑ i∈range r, f (T+i)) - ∑ i∈range r,f i := by
    simp_rw [Nat.add_comm _ r]; linear_combination -id
  rw [eqn]; apply (norm_sub_le ..).trans
  have a := norm_sum_le (range r) (fun i => f (T+i)); have b := norm_sum_le (range r) f
  simp only [unit,sum_const,card_range,nsmul_eq_mul,mul_one] at a b; linarith

/-- A finite van der Corput estimate with stride `v`. Only correlations of
strictly ordered pairs are needed. All sums use the same unpadded interval. -/
theorem stride_cancellation (f : ℕ → ℂ) (unit : ∀ n, ‖f n‖=1) {T H v : ℕ} (hH : 0<H)
    {η : ℝ} (pos : 0<η) (size : 1 ≤ (H:ℝ)*η^2) (edge : 2*(H:ℝ)*v ≤ η*T)
    (corr : ∀ a t : ℕ, a<t → t<H → ‖∑ n∈range T, f (n+t*v)*conj (f (n+a*v))‖ ≤ η^2*T) :
    ‖∑ n∈range T, f n‖ ≤ (3*η)*T := by
  let G (n : ℕ) := ∑ t∈range H, f (n+t*v)
  let C (a t : ℕ) := ∑ n∈range T, f (n+t*v)*conj (f (n+a*v))
  have symm (a t : ℕ) : ‖C a t‖=‖C t a‖ := by
    have eqn : conj (C a t)=C t a := by simp [C,mul_comm]
    rw [← eqn,Complex.norm_conj]
  have diag (a : ℕ) : C a a = (T:ℂ) := by simp [C,Complex.mul_conj,Complex.normSq_eq_norm_sq,unit]
  have each (a t : ℕ) (ha : a<H) (ht : t<H) : (C a t).re ≤ (if a=t then (T:ℝ) else 0) + η^2*T := by
    apply (Complex.re_le_norm _).trans
    rcases lt_trichotomy a t with h|rfl|h
    · simpa [h.ne] using corr a t h ht
    · simp [diag]; positivity
    · rw [symm]; simpa [h.ne'] using corr t a h ha
  have energyId : (∑ n∈range T, ‖G n‖^2) = ∑ a∈range H, ∑ t∈range H,(C a t).re := by
    have eqn : (∑ n∈range T, G n*conj (G n))=∑ a∈range H, ∑ t∈range H,C a t := by
      simp only [G,C,map_sum,mul_sum,sum_mul]
      rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]
    simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,← Complex.ofReal_sum,Complex.ofReal_re,Complex.re_sum] using congrArg Complex.re eqn
  have energy : (∑ n∈range T, ‖G n‖^2) ≤ (H:ℝ)*T + H*(H*(η^2*T)) := by
    rw [energyId]; apply (sum_le_sum (fun a ha => sum_le_sum (fun t ht => each a t (mem_range.mp ha) (mem_range.mp ht)))).trans_eq
    simp [sum_add_distrib, add_comm]
    rw [sum_congr rfl (fun x hx => ite_eq_left (mem_range.mp hx))]; simp [add_comm]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (range T) (fun _ => (1:ℝ)) (fun i => ‖G i‖)
  simp only [one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one] at cs
  have se := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun i _ => norm_nonneg _))).mpr (norm_sum_le (range T) G)
  have small : ‖∑ n∈range T,G n‖ ≤ 2*(H:ℝ)*η*T := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    apply (se.trans cs).trans ((mul_le_mul_of_nonneg_left energy (Nat.cast_nonneg T)).trans _)
    nlinarith only [mul_le_mul_of_nonneg_right size (show 0 ≤ (H:ℝ)*T^2 by positivity),sq_nonneg ((H:ℝ)*η*T)]
  let S := ∑ n∈range T, f n
  have eqn : (∑ n∈range T,G n)-(H:ℂ)*S=∑ t∈range H, ((∑ n∈range T, f (n+t*v))-S) := by
    simp only [G,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]; rw [sum_comm]
  have near : ‖(∑ n∈range T,G n)-(H:ℂ)*S‖ ≤ (H:ℝ)*(η*T) := by
    rw [eqn]; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _ => η*(T:ℝ)) ?_).trans_eq (by simp))
    intro t ht; apply (shift_sum_error f unit T (t*v)).trans
    push_cast; have le : (t:ℝ)≤H := by exact_mod_cast (mem_range.mp ht).le
    exact (show 2*((t:ℝ)*v) ≤ 2*(H:ℝ)*v by rw [← mul_assoc]; gcongr).trans edge
  have tri := norm_sub_le (∑ n∈range T,G n) ((∑ n∈range T,G n)-(H:ℂ)*S)
  rw [sub_sub_cancel,norm_mul,Complex.norm_natCast] at tri
  apply (mul_le_mul_iff_right₀ (by exact_mod_cast hH : 0<(H:ℝ))).mp
  linarith only [tri,near,small]

end NormalityChecker
