module

public import NormalityChecker.RationalWeights
public import NormalityChecker.RadixTelescoping
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Dense polynomial-weighted power intervals and their sparse boundary expansions. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker

/-- The polynomial antidifference exists inside the same degree bound. -/
theorem exists_radix_antidifference {b s : ℕ} (hb : 2≤b) (P : ℚ[X]) (hp : P≠0) (deg : P.natDegree<s) :
    ∃ H : ℚ[X], H≠0 ∧ H.natDegree<s ∧ ∀ n : ℚ, P.eval n=H.eval n-H.eval (n+1)/b := by
  let V := degreeLT ℚ s
  let D : V →ₗ[ℚ] V := LinearMap.id - (b:ℚ)⁻¹ • (taylorLinearEquiv (1:ℚ) s).toLinearMap
  have formula (f : V) : ((D f:V):ℚ[X]) = (f:ℚ[X])-(b:ℚ)⁻¹ • taylor 1 (f:ℚ[X]) := rfl
  have bp : (1:ℚ)<b := by exact_mod_cast (show 1<b by omega)
  have inject : Function.Injective D := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro f hf; apply Subtype.ext
    have eqn := congrArg Subtype.val hf
    rw [formula] at eqn
    have e : (f:ℚ[X])=C (b:ℚ)⁻¹ *taylor 1 (f:ℚ[X]) := by simpa only [smul_eq_C_mul,ZeroMemClass.coe_zero,sub_eq_zero] using eqn
    have lead := congrArg leadingCoeff e
    rw [leadingCoeff_mul,leadingCoeff_C,leadingCoeff_taylor] at lead
    change (f:ℚ[X])=0
    apply leadingCoeff_eq_zero.mp
    field_simp [(zero_lt_one.trans bp).ne'] at lead; nlinarith only [lead,bp,mul_self_nonneg ((f:ℚ[X]).leadingCoeff)]))
  let p : V := ⟨P,mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast deg))⟩
  obtain ⟨f,hf⟩ := LinearMap.injective_iff_surjective.mp inject p
  have eqn : (f:ℚ[X])-(b:ℚ)⁻¹ • taylor 1 (f:ℚ[X])=P := (formula f).symm.trans (congrArg Subtype.val hf)
  have nz : (f:ℚ[X])≠0 := fun e => hp (by simpa [e] using eqn.symm)
  refine ⟨f,nz,(natDegree_lt_iff_degree_lt nz).mpr (mem_degreeLT.mp f.prop),fun n => ?_⟩
  rw [← eqn,eval_sub,smul_eq_C_mul,eval_mul,eval_C,taylor_eval]; ring

/-- Geometric weights on power intervals turn any absolutely summable
antidifference into two boundary contributions. Indices start at one. -/
theorem power_interval_boundaries {c : ℕ} (hc : 1<c) {C : ℝ} (hC : 1≤C) (F : ℕ → ℝ) (summ : Summable F) :
    (∑' i : ℕ, (C^Nat.log c (i+1))⁻¹*(F (i+1)-F (i+2))) =
      C*F 1+(1-C)*∑' j : ℕ, (C^j)⁻¹*F (c^j) := by
  let a (j : ℕ) := (C^j)⁻¹
  have small (j : ℕ) : ‖a j‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [a]; positivity)]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hC)
  have weight {g : ℕ → ℝ} (conv : Summable g) (k : ℕ → ℕ) : Summable (fun i => a (k i)*g i) :=
    Summable.of_norm_bounded conv.norm (fun i => (norm_mul ..).le.trans (mul_le_of_le_one_left (norm_nonneg _) (small _)))
  have h := radix_plateau_regroup hc a (fun n => F n-F (n+1))
    (weight (((summable_nat_add_iff 1).mpr summ).sub ((summable_nat_add_iff 2).mpr summ)) _)
  rw [h]
  let w (j : ℕ) := a j*F (c^j)
  have conv : Summable w := weight (summ.comp_injective (Nat.pow_right_injective hc)) id
  have step (j : ℕ) : a j*(∑ n ∈ Ico (c^j) (c^(j+1)), (F n-F (n+1))) = w j-C*w (j+1) := by
    have H := sum_Ico_sub (fun i => -F i) (Nat.pow_le_pow_right hc.le (Nat.le_succ j))
    simp only [neg_sub_neg] at H; rw [H]; dsimp [w,a]; rw [pow_succ C]; field_simp [(zero_lt_one.trans_le hC).ne']
  simp_rw [step]
  rw [conv.tsum_sub (((summable_nat_add_iff 1).mpr conv).mul_left C),tsum_mul_left]
  have cut := conv.sum_add_tsum_nat_add 1
  simp only [sum_range_one,show w 0=F 1 by simp [w,a]] at cut
  change (∑' j,w j)-C*(∑' j,w (j+1))=C*F 1+(1-C)*(∑' j,w j)
  linarith only [congrArg (C * ·) cut]

private lemma summable_poly_radix {b : ℕ} (hb : 2≤b) (H : ℚ[X]) :
    Summable (fun n : ℕ => ((H.eval (n:ℚ):ℚ):ℝ)/(b:ℝ)^n) := by
  have bp : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have hr : ‖(b:ℝ)⁻¹‖<1 := by rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (zero_lt_one.trans bp))]; exact inv_lt_one_of_one_lt₀ bp
  simp only [eval_eq_sum_range,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,sum_div]
  apply summable_sum; intro i _
  convert (summable_pow_mul_geometric_of_norm_lt_one i hr).mul_left (H.coeff i:ℝ) using 1
  funext n; rw [inv_pow]; ring

/-- A dense coefficient sequence with a supplied antidifference only needs the
values of that antidifference at the endpoints of the power intervals. -/
theorem dense_boundary_identity {b c s : ℕ} (hc : 2≤c) (P H : ℕ → ℚ)
    (step : ∀ n, P n=H n-H (n+1)/b) (summ : Summable (fun n : ℕ => (H n:ℝ)/(b:ℝ)^n)) :
    (∑' i : ℕ, (P (i+1):ℝ) / (c:ℝ)^(s*Nat.log c (i+1)) / (b:ℝ)^(i+1)) =
      (c:ℝ)^s*(H 1:ℝ)/b + (1-(c:ℝ)^s)*
        ∑' j : ℕ, (H (c^j):ℝ) / ((c:ℝ)^j)^s / (b:ℝ)^(c^j) := by
  let F (n : ℕ) := (H n:ℝ)/(b:ℝ)^n
  have formula := power_interval_boundaries (c:=c) hc (C:=(c:ℝ)^s) (one_le_pow₀ (by exact_mod_cast (show 1≤c by omega))) F summ
  calc _ = ∑' i : ℕ, (((c:ℝ)^s)^Nat.log c (i+1))⁻¹*(F (i+1)-F (i+2)) := by
         apply tsum_congr; intro i; rw [step]; dsimp only [F]; push_cast
         rw [pow_succ (b:ℝ) (i+1),pow_mul]; ring_nf
       _ = _ := formula.trans (by dsimp only [F]; rw [pow_one]; congr 1
                                  · ring
                                  · congr 1; apply tsum_congr; intro j; rw [pow_right_comm]; ring)

/-- Dense sums with a rational polynomial weight on every digit, regrouped as a
single geometric support. The displayed sparse sum includes the `j=0` term. -/
theorem dense_polynomial_identity {b c s : ℕ} (hb : 2≤b) (hc : 2≤c) (P H : ℚ[X])
    (step : ∀ n : ℚ, P.eval n = H.eval n - H.eval (n+1)/b) :
    (∑' i : ℕ, ((P.eval ((i:ℚ)+1):ℚ):ℝ) / (c:ℝ)^(s*Nat.log c (i+1)) / (b:ℝ)^(i+1)) =
      (c:ℝ)^s*((H.eval 1:ℚ):ℝ)/b + (1-(c:ℝ)^s)*
        ∑' j : ℕ, ((H.eval ((c:ℚ)^j):ℚ):ℝ) / ((c:ℝ)^j)^s / (b:ℝ)^(c^j) := by
  simpa using dense_boundary_identity (b:=b) (s:=s) hc (fun n => P.eval (n:ℚ)) (fun n => H.eval (n:ℚ))
    (fun n => by simpa using step (n:ℚ)) (summable_poly_radix hb H)

/-- Polynomial agreement is only required at the powers of `c`. This also
accepts antidifferences that follow different formulas on residue classes. -/
theorem normal_of_polynomial_boundaries {b c s : ℕ} (hb : 2≤b) (hc : 2≤c) (cop : b.Coprime c)
    (P F : ℕ → ℚ) (H : ℚ[X]) (hn : H≠0) (hd : H.natDegree<s)
    (step : ∀ n, P n=F n-F (n+1)/b) (summ : Summable (fun n : ℕ => (F n:ℝ)/(b:ℝ)^n))
    (boundary : ∀ j : ℕ, F (c^j)=H.eval ((c:ℚ)^j)) :
    NormalIn b (∑' i : ℕ, (P (i+1):ℝ) / (c:ℝ)^(s*Nat.log c (i+1)) / (b:ℝ)^(i+1)) := by
  let d : Localized.Composite.Generators := ⟨b,b,c,hb,hb,hc,cop,1,by simp⟩
  have norm := d.axis_rational_normal H hn hd
  rw [dense_boundary_identity hc P F step summ,add_comm]
  simp_rw [boundary]
  let D : ℤ := 1-(c:ℤ)^s
  let r : ℚ := (c:ℚ)^s*F 1/b
  have dn : D≠0 := by
    have h := one_lt_pow₀ (by exact_mod_cast hc : (1:ℤ)<c) (by omega : s≠0)
    dsimp [D]; omega
  convert (normal_add_rat_iff hb _ r).mpr ((normal_mul_int_iff hb dn _).mpr norm) using 2 <;> simp [r,D,d]

/-- Every nonzero rational polynomial of degree strictly less than `s` gives a
normal dense expansion for coprime `b,c ≥ 2`. -/
theorem dense_polynomial_normal {b c s : ℕ} (hb : 2≤b) (hc : 2≤c) (cop : b.Coprime c)
    (P : ℚ[X]) (hp : P≠0) (deg : P.natDegree<s) :
    NormalIn b (∑' i : ℕ, ((P.eval ((i:ℚ)+1):ℚ):ℝ) / (c:ℝ)^(s*Nat.log c (i+1)) / (b:ℝ)^(i+1)) := by
  obtain ⟨H,hn,hd,step⟩ := exists_radix_antidifference hb P hp deg
  simpa using normal_of_polynomial_boundaries hb hc cop (fun n => P.eval (n:ℚ)) (fun n => H.eval (n:ℚ)) H hn hd
    (fun n => by simpa using step (n:ℚ)) (summable_poly_radix hb H) (fun j => by simp)

/-- The boundary calculation for the changing binary coefficients in the review.
The index `j+1` omits the initial power `3^0`. -/
theorem dense_linear_ternary_identity :
    (∑' i : ℕ, ((i:ℝ)+1)/3^(2*Nat.log 3 (i+1))/2^(i+1)) =
      2-16*∑' j : ℕ, ((3:ℝ)^(j+1)+1)/3^(2*(j+1))/2^(3^(j+1):ℕ) := by
  let H : ℚ[X] := 2*X+2
  let F (n : ℕ) := ((H.eval (n:ℚ):ℚ):ℝ)/2^n
  let w (j : ℕ) := ((3:ℝ)^j+1)/3^(2*j)/2^(3^j:ℕ)
  have sumF : Summable F := summable_poly_radix (b:=2) (by decide) H
  have hs : Summable w := Summable.of_norm_bounded (sumF.comp_injective (Nat.pow_right_injective (by decide : 2≤3))).norm (by
    intro j; dsimp [F,w,H]; push_cast; simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    push_cast; rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    gcongr; apply (div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ)≤3))).trans; linarith [show (0:ℝ)≤3^j by positivity])
  have cut := hs.sum_add_tsum_nat_add 1
  simp only [sum_range_one,show w 0=1 by norm_num [w]] at cut
  have step (n : ℚ) : (X:ℚ[X]).eval n = H.eval n-H.eval (n+1)/2 := by simp [H]; ring
  have formula := dense_polynomial_identity (b:=2) (c:=3) (s:=2) (by decide) (by decide) X H step
  have boundary : (∑' j : ℕ, ((H.eval ((3:ℚ)^j):ℚ):ℝ)/((3:ℝ)^j)^2/2^(3^j:ℕ)) = 2*∑' j,w j := by
    rw [← tsum_mul_left]; apply tsum_congr; intro j; simp [H,w,pow_mul,pow_right_comm]; ring
  norm_num only [eval_X,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Nat.cast_ofNat] at formula
  rw [formula,boundary,← cut]; norm_num [H]; ring

/-- The same expansion has limiting frequency `2^(-k)` for every binary word
of positive length `k`. -/
theorem dense_linear_ternary_normal : NormalIn 2
    (∑' i : ℕ, ((i:ℝ)+1)/3^(2*Nat.log 3 (i+1))/2^(i+1)) := by
  simpa using dense_polynomial_normal (b:=2) (c:=3) (s:=2) (by decide) (by decide) (by decide) X X_ne_zero (by simp)

/-- Nonzero periodic coefficients can give exact cancellation on every plateau.
The coefficient is one at even positions and minus one half at odd positions. -/
theorem periodic_plateau_zero (s : ℕ) :
    (∑' i : ℕ, (if (i+1)%2=0 then (1:ℝ) else -1/2) / 3^(s*Nat.log 3 (i+1)) / 2^(i+1)) = 0 := by
  let F (n : ℕ) : ℚ := if n%2=0 then 1 else 0
  let a (n : ℕ) : ℚ := if n%2=0 then 1 else -1/2
  have step (n : ℕ) : a n=F n-F (n+1)/2 := by
    dsimp [a,F]; split_ifs <;> norm_num <;> omega
  have summ : Summable (fun n : ℕ => (F n:ℝ)/2^n) := by
    apply Summable.of_norm_bounded (summable_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num))
    intro n; dsimp [F]; split_ifs <;> simp [abs_of_nonneg]
  have cut (j : ℕ) : F (3^j)=0 := by
    have odd := Nat.odd_iff.mp ((by decide : Odd 3).pow (n:=j)); simp [F,odd]
  have h := dense_boundary_identity (b:=2) (s:=s) (by decide : 2≤3) a F step summ
  simp_rw [cut] at h; simpa [F,a,apply_ite] using h

end NormalityChecker
