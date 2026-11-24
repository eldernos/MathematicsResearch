module

public import NormalityChecker.HigherOrderPrincipal
public import NormalityChecker.LocalizedMesh
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.NumberTheory.Multiplicity

/-! Uniform detection of the largest surviving local order by finite differences. -/
@[expose] public section
noncomputable section
open Finset Filter Polynomial
open scoped Topology fwdDiff
namespace NormalityChecker.LocalizedSupport
variable {p : ℕ} [hp : Fact p.Prime]

private def differenceWeight (h j : ℕ) : ℤ := (-1)^(h-j) * h.choose j

private lemma difference_pow (h j : ℕ) :
    ∑ i ∈ range (h+1), (differenceWeight h i : ℤ_[p]) * (i:ℤ_[p])^j =
      (Δ_[(1:ℤ_[p])]^[h] (fun x : ℤ_[p] => x^j)) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [differenceWeight,zsmul_eq_mul]

/-- Taking the `h`th difference at stride `a` isolates coefficient `h`
modulo the next power of the stride. -/
theorem stride_coefficient_identity (Q : (ℤ_[p])[X]) (u : ℤ_[p]) (h a : ℕ)
    (values : ∀ j ≤ h, Q.eval ((a*j:ℕ):ℤ_[p]) = u^(a*j)) :
    ∃ E : ℤ_[p], (u^a-1)^h =
      (a:ℤ_[p])^h * Q.coeff h * h.factorial + (a:ℤ_[p])^(h+1) * E := by
  choose tail ht using fun j : ℕ => eval_split Q (h+1) ((a*j:ℕ):ℤ_[p])
  refine ⟨∑ j ∈ range (h+1), (differenceWeight h j : ℤ_[p])*(j:ℤ_[p])^(h+1)*tail j, ?_⟩
  have val (j : ℕ) (hj : j ∈ range (h+1)) :
      (differenceWeight h j : ℤ_[p])*(u^a)^j =
        (∑ i ∈ range (h+1), Q.coeff i*(a:ℤ_[p])^i *
          ((differenceWeight h j : ℤ_[p])*(j:ℤ_[p])^i)) +
        (a:ℤ_[p])^(h+1)*((differenceWeight h j : ℤ_[p])*(j:ℤ_[p])^(h+1)*tail j) := by
    rw [← pow_mul, ← values j (by simpa using mem_range.mp hj), ht, mul_add, mul_sum]
    push_cast
    simp only [mul_pow]
    congr 1
    · apply sum_congr rfl; intro i _; ring
    · ring
  have expansion : (u^a-1)^h =
      ∑ j ∈ range (h+1), (differenceWeight h j : ℤ_[p])*(u^a)^j := by
    rw [sub_eq_add_neg,add_pow]
    apply sum_congr rfl; intro i _
    simp only [differenceWeight,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
    ring
  rw [expansion,sum_congr rfl val,sum_add_distrib,sum_comm, ← mul_sum]
  congr 1
  simp_rw [← mul_sum,difference_pow]
  rw [sum_range_succ, sum_eq_zero (fun j hj =>
    by rw [fwdDiff_iter_pow_eq_zero_of_lt (mem_range.mp hj),Pi.zero_apply,mul_zero]),
    zero_add, fwdDiff_iter_eq_factorial, Pi.natCast_apply]
  ring

/-- Lifting the exponent for the actual principal unit at a stride divisible by
`p-1`. The torsion factor disappears exactly. -/
private lemma stride_norm {b : ℕ} (hb : 2 ≤ b) (cop : b.Coprime p) (odd : Odd p)
    {w z : ℤ_[p]} (hw : ‖w‖=1) (fixed : w^p=w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p])*(1+(p:ℚ_[p])*z)) (a : ℕ) :
    ‖(1+(p:ℤ_[p])*z)^((p-1)*p^a)-1‖ =
      ((p:ℝ)⁻¹)^(multiplicity p (b^(p-1)-1) + a) := by
  let m := b^(p-1)
  have pm : 0 < p-1 := Nat.sub_pos_of_lt hp.out.one_lt
  have mgt : 1 < m := one_lt_pow₀ (by omega : 1 < b) pm.ne'
  have dvd : p ∣ m-1 := by
    have h := Nat.ModEq.pow_totient cop
    rw [Nat.totient_prime hp.out] at h
    exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ m)).mp h.symm
  have ndiv : ¬ p ∣ m := hp.out.coprime_iff_not_dvd.mp (cop.symm.pow_right _)
  have normW : (w:ℚ_[p])^(p-1) = 1 := by
    have wn : (w:ℚ_[p]) ≠ 0 := by
      have := (PadicInt.norm_coe w).trans hw
      exact norm_ne_zero_iff.mp (this.trans_ne one_ne_zero)
    apply mul_right_cancel₀ wn
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le, one_mul]
    exact congrArg (fun x : ℤ_[p] => (x:ℚ_[p])) fixed
  have powerU : (1+(p:ℚ_[p])*z)^((p-1)*p^a) = ((m^(p^a):ℕ):ℚ_[p])⁻¹ := by
    have eqn := congrArg (fun x : ℚ_[p] => x^((p-1)*p^a)) factor
    rw [mul_pow,pow_mul (w:ℚ_[p]),normW,one_pow,one_mul] at eqn
    simpa [m, pow_mul, inv_pow] using eqn.symm
  let M := m^(p^a)
  have Mgt : 1 < M := one_lt_pow₀ mgt (pow_ne_zero _ hp.out.ne_zero)
  have normM : ‖(M:ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr
    ((cop.symm.pow_right _).pow_right _)
  have normsub : ‖(M:ℚ_[p])⁻¹-1‖ = ‖((M-1:ℕ):ℚ_[p])‖ := by
    have ne : (M:ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have eqn : (M:ℚ_[p])⁻¹-1 = -(((M:ℚ_[p])-1) / M) := by field_simp; ring
    rw [eqn,norm_neg,norm_div,normM,div_one,Nat.cast_sub Mgt.le,Nat.cast_one]
  have val := Nat.multiplicity_pow_sub_pow odd mgt dvd ndiv (pow_ne_zero a hp.out.ne_zero)
  have vp : multiplicity p (p^a) = a := Nat.multiplicity_prime_pow (p:=p) a
  rw [one_pow, vp] at val
  rw [← PadicInt.norm_coe]
  push_cast
  rw [powerU,normsub,Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (by omega : M-1 ≠ 0)),
    Padic.valuation_natCast]
  change (p:ℝ)^(-(multiplicity p (m^(p^a)-1):ℤ)) = _
  rw [val,zpow_neg,zpow_natCast,inv_pow]

/-- All coefficients needed at fixed order are bounded away from zero uniformly
in the digit position. Finite differences avoid a choice of a p-adic logarithm. -/
theorem principal_coefficients_bounded {b : ℕ} (hb : 2 ≤ b) (cop : b.Coprime p) (odd : Odd p)
    {w z : ℤ_[p]} (hw : ‖w‖=1) (fixed : w^p=w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p])*(1+(p:ℚ_[p])*z)) (s : ℕ) :
    ∃ C N : ℕ, ∀ n ≥ N, ∀ h ≤ s, ((p:ℝ)⁻¹)^C ≤ ‖(principalPolynomial z n).coeff h‖ := by
  let v := multiplicity p (b^(p-1)-1)
  let a := v*s+1
  let stride := (p-1)*p^a
  let u : ℤ_[p] := 1 + p*z
  let q := (p:ℝ)⁻¹
  have qp : 0 < q := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have qlt : q < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have uval : ‖u^stride-1‖ = q^(v+a) := stride_norm hb cop odd hw fixed factor a
  have aval : ‖(stride:ℤ_[p])‖ = q^a := by
    dsimp only [stride]
    rw [Nat.cast_mul,Nat.cast_pow,norm_mul,norm_pow, PadicInt.norm_p]
    have hu : ‖((p-1:ℕ):ℤ_[p])‖ = 1 := by
      rw [← PadicInt.norm_coe,PadicInt.coe_natCast,Padic.norm_natCast_p_sub_one]
    rw [hu,one_mul]
  refine ⟨(v+a)*s,stride*s,fun n hn h hs => ?_⟩
  let Q := principalPolynomial z n
  obtain ⟨e, eqn⟩ := stride_coefficient_identity Q u h stride (fun j hj =>
    principalPolynomial_eval z ((Nat.mul_le_mul_left stride (hj.trans hs)).trans hn))
  have err : ‖(stride:ℤ_[p])^(h+1)*e‖ < ‖u^stride-1‖^h := by
    rw [norm_mul,norm_pow,aval,uval,← pow_mul,← pow_mul]
    refine (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one e)).trans_lt ?_
    apply pow_lt_pow_right_of_lt_one₀ qp qlt
    have vh := Nat.mul_le_mul_left v hs
    dsimp [a] at *
    nlinarith only [vh]
  have bound := PadicInt.nonarchimedean ((stride:ℤ_[p])^h*Q.coeff h*(h.factorial:ℤ_[p]))
    ((stride:ℤ_[p])^(h+1)*e)
  rw [← eqn, norm_pow] at bound
  have main := (le_max_iff.mp bound).resolve_right (not_le.mpr err)
  rw [norm_mul,norm_mul] at main
  have cap : ‖(stride:ℤ_[p])^h‖ * ‖Q.coeff h‖ * ‖(h.factorial:ℤ_[p])‖ ≤ ‖Q.coeff h‖ :=
    (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)).trans
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))
  rw [uval,← pow_mul] at main
  exact (pow_le_pow_of_le_one qp.le qlt.le (Nat.mul_le_mul_left _ hs)).trans (main.trans cap)


private lemma sum_norm_cap {ι : Type*} (V : Finset ι) {f : ι → ℚ_[p]} {R : ℝ}
    (pos : 0 ≤ R) (bound : ∀ j ∈ V, ‖f j‖ ≤ R) : ‖∑ j ∈ V, f j‖ ≤ R := by
  classical
  induction V using Finset.induction_on with
  | empty => simpa
  | insert j V out ih =>
    rw [sum_insert out]
    exact (Padic.nonarchimedean _ _).trans (max_le (bound j (mem_insert_self ..))
      (ih (fun _ h => bound _ (mem_insert_of_mem h))))

/-- Outside the small nonzero moment sets, the largest surviving order gives a
growing divisor bound for the actual shifted denominator. All constants are
uniform over real points of every sufficiently late digit interval. -/
theorem dominant_order_denominator {b s : ℕ} (hb : 2 ≤ b) (cop : b.Coprime p) (odd : Odd p)
    {S : Finset ℕ} (outside : p ∉ S) {w z : ℤ_[p]} (hw : ‖w‖=1) (fixed : w^p=w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p])*(1+(p:ℚ_[p])*z)) :
    ∃ C N : ℕ, ∀ {n k L d : ℕ} {t : ℝ}, N ≤ n → C+L < k → n < p^(k+1) →
      ⌊t*(p:ℝ)^k⌋₊ = n → 0 < d → d ≤ s →
      ((p:ℝ)⁻¹)^L ≤ ‖phaseMoment S w d t‖ →
      (∀ j, d < j → j ≤ s → phaseMoment S w j t = 0) →
      p^(k-(C+L)) ≤ (powerShifted b s (insert p S) n).den := by
  obtain ⟨C,N,coeff⟩ := principal_coefficients_bounded hb cop odd hw fixed factor s
  refine ⟨C,N,?_⟩
  intro n k L d t hn hk top cut dp ds lower higher
  obtain ⟨e, he⟩ := phase_prefix_identity outside fixed factor top cut (s:=s)
  let Q := principalPolynomial z n
  let R := (p:ℝ)^k
  let a := ((p:ℝ)⁻¹)^(C+L)
  have pp : (1:ℝ) < p := by exact_mod_cast hp.out.one_lt
  have Rp : 0 < R := by dsimp [R]; positivity
  have R1 : 1 ≤ R := one_le_pow₀ pp.le
  have ap : 0 < a := by dsimp [a]; positivity
  have scale : a*R = (p:ℝ)^(k-(C+L)) := by
    dsimp [a,R]
    have eqn : (p:ℝ)^k = (p:ℝ)^(C+L) * (p:ℝ)^(k-(C+L)) := by
      rw [← pow_add]; congr 1; omega
    rw [inv_pow,eqn]; field_simp
  have big : 1 < a*R := scale ▸ one_lt_pow₀ pp (by omega)
  let f (h : ℕ) : ℚ_[p] := (Q.coeff h : ℚ_[p]) *
    ((phaseMoment S w (s-h) t : ℚ_[p]) / ((p:ℚ_[p])^(s-h))^k)
  have term (h : ℕ) : ‖f h‖ = ‖Q.coeff h‖ * ‖phaseMoment S w (s-h) t‖ * R^(s-h) := by
    dsimp [f,R]
    rw [norm_mul,norm_div,norm_pow,norm_pow,Padic.norm_p,PadicInt.norm_coe,PadicInt.norm_coe]
    simp only [inv_pow,div_eq_mul_inv,inv_inv]
    rw [← pow_mul, Nat.mul_comm (s-h) k,pow_mul]; ring
  let h := s-d
  have deg : s-h=d := by dsimp [h]; omega
  have hm : h ∈ range s := mem_range.mpr (by dsimp [h]; omega)
  have main : a*R^d ≤ ‖f h‖ := by
    rw [term,deg]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [show a = ((p:ℝ)⁻¹)^C * ((p:ℝ)⁻¹)^L from pow_add ..]
    exact mul_le_mul (coeff n hn h (Nat.sub_le ..)) lower (by positivity) (norm_nonneg _)
  let V := (range s).erase h
  have rest : ‖∑ j ∈ V, f j‖ ≤ R^(d-1) := by
    apply sum_norm_cap _ (by positivity)
    intro j hj
    rw [term]
    rcases lt_or_gt_of_ne (ne_of_mem_erase hj) with lt|gt
    · rw [higher _ (by dsimp [h] at lt; omega) (Nat.sub_le ..),norm_zero,mul_zero,zero_mul]
      positivity
    · have cap := (mul_le_of_le_one_right (norm_nonneg (Q.coeff j))
          (PadicInt.norm_le_one (phaseMoment S w (s-j) t))).trans (PadicInt.norm_le_one _)
      exact (mul_le_of_le_one_left (by positivity) cap).trans
        (pow_le_pow_right₀ R1 (by dsimp [h] at gt; omega))
  have residual : ‖(∑ j ∈ V, f j) + (e:ℚ_[p])‖ ≤ R^(d-1) :=
    (Padic.nonarchimedean ..).trans (max_le rest (by
      rw [PadicInt.norm_coe]
      exact (PadicInt.norm_le_one _).trans (one_le_pow₀ R1)))
  have strict : R^(d-1) < a*R^d := by
    have eqn : a*R^d = (a*R)*R^(d-1) := by
      rw [mul_assoc, ← pow_succ',Nat.sub_add_cancel dp]
    rw [eqn]
    exact lt_mul_of_one_lt_left (pow_pos Rp _) big
  have val : ‖(powerPartial b s (insert p S) n : ℚ_[p])‖ = ‖f h‖ := by
    change (powerPartial b s (insert p S) n : ℚ_[p]) = (∑ j ∈ range s, f j) + e at he
    rw [he, ← add_sum_erase _ f hm,add_assoc,Padic.add_eq_max_of_ne (ne_of_gt (residual.trans_lt
      (strict.trans_le main))),max_eq_left (residual.trans (strict.le.trans main))]
  let P := powerShifted b s (insert p S) n
  have shiftNorm : ‖(P:ℚ_[p])‖ = ‖f h‖ := by
    simp only [P,powerShifted,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,norm_mul,norm_pow,
      Padic.norm_natCast_eq_one_iff.mpr cop.symm,one_pow,one_mul,val]
  have den : ‖(P:ℚ_[p])‖ ≤ (P.den:ℝ) := by
    rw [Padic.eq_padicNorm]
    exact_mod_cast Localized.padicNorm_le_den hp.out P
  have pbound : (p:ℝ)^(k-(C+L)) ≤ P.den := by
    rw [← scale]
    exact (mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ R1 dp) ap.le).trans
      (main.trans (shiftNorm ▸ den))
  exact_mod_cast pbound

end NormalityChecker.LocalizedSupport
