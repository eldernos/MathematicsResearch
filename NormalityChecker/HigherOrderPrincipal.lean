module

public import NormalityChecker.LocalizedCertificate
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Order.Floor.Semifield

/-! Finite principal-unit interpolation for prime-restricted polylogarithms. -/
@[expose] public section
noncomputable section
open Finset Polynomial
namespace NormalityChecker.LocalizedSupport

variable {p : ℕ} [hp : Fact p.Prime]

private lemma residue_zero (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/-- The Teichmüller factorization of the inverse radix, with an explicit
principal unit of the form `1 + p*z`. -/
theorem inverse_radix_factors {b : ℕ} (cop : b.Coprime p) :
    ∃ w z : ℤ_[p], w^p = w ∧ ‖w‖ = 1 ∧
      (b : ℚ_[p])⁻¹ = (w : ℚ_[p]) * (1 + (p : ℚ_[p]) * z) := by
  have unit : IsUnit (b : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr cop.symm)
  let a : ℤ_[p] := ↑unit.unit⁻¹
  have ab : a * b = 1 := by
    change ↑unit.unit⁻¹ * (b : ℤ_[p]) = 1
    simpa only [unit.unit_spec] using unit.unit.inv_mul
  let F : (ℤ_[p])[X] := X ^ p - X
  have value (x : ℤ_[p]) : F.aeval x = x^p-x := by simp [F]
  have deriv (x : ℤ_[p]) : F.derivative.aeval x = (p:ℤ_[p])*x^(p-1)-1 := by
    simp [F, Polynomial.derivative_X_pow]
  have dernorm (x : ℤ_[p]) : ‖F.derivative.aeval x‖ = 1 := by
    by_contra hn
    have h := (PadicInt.norm_lt_one_iff_dvd _).mp
      (lt_of_le_of_ne (PadicInt.norm_le_one _) hn)
    have z := (residue_zero _).mpr h
    simp [deriv] at z
  have hF : ‖F.aeval a‖ < ‖F.derivative.aeval a‖^2 := by
    rw [dernorm,one_pow,PadicInt.norm_lt_one_iff_dvd,← residue_zero,value]
    simp [ZMod.pow_card]
  obtain ⟨w,root,close,_,_⟩ := hensels_lemma hF
  rw [dernorm] at close
  have rw0 := (residue_zero _).mpr ((PadicInt.norm_lt_one_iff_dvd _).mp close)
  have rwa' : PadicInt.toZMod w = PadicInt.toZMod a := sub_eq_zero.mp (by simpa using rw0)
  have wu : IsUnit w := by
    apply PadicInt.isUnit_iff.mpr
    by_contra hn
    have z := (residue_zero _).mpr ((PadicInt.norm_lt_one_iff_dvd _).mp
      (lt_of_le_of_ne (PadicInt.norm_le_one _) hn))
    have hu := congrArg PadicInt.toZMod ab
    simp [← rwa', z] at hu
  obtain ⟨v,hv⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp close
  refine ⟨w, -(↑wu.unit⁻¹ * v), sub_eq_zero.mp ((value w).symm.trans root),
    PadicInt.isUnit_iff.mp wu, ?_⟩
  have eqn : w * (1 + p * -(↑wu.unit⁻¹ * v)) = a := by
    have inv : w * ↑wu.unit⁻¹ = 1 := by simpa only [wu.unit_spec] using wu.unit.mul_inv
    calc _ = w - (w * ↑wu.unit⁻¹) * (p*v) := by ring
         _ = a := by rw [inv,one_mul,← hv]; abel
  have abs' := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) ab
  have e := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) eqn
  push_cast at abs' e ⊢
  exact (inv_eq_of_mul_eq_one_left abs').trans e.symm

/-- The factorial denominators in Newton interpolation are absorbed by `p^j`. -/
def newtonWeight (j : ℕ) : ℤ_[p] :=
  ((p : ℚ_[p])^j / j.factorial).lift (by
    have pos : (0:ℝ) < p := by exact_mod_cast hp.out.pos
    rw [norm_div, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)), Padic.valuation_natCast,
      div_le_one (zpow_pos pos _)]
    apply zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le)
    exact neg_le_neg (by exact_mod_cast multiplicity_factorial_le p j))

/-- An integral interpolation polynomial for the first `N+1` powers of a principal unit. -/
def principalPolynomial (z : ℤ_[p]) (N : ℕ) : (ℤ_[p])[X] :=
  ∑ j ∈ range (N+1), C (newtonWeight j * z^j) * descPochhammer _ j

theorem principalPolynomial_eval (z : ℤ_[p]) {m N : ℕ} (hm : m ≤ N) :
    (principalPolynomial z N).eval (m : ℤ_[p]) = (1 + p*z)^m := by
  apply Subtype.ext
  rw [principalPolynomial,eval_finsetSum, PadicInt.coe_sum]
  simp only [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, PadicInt.coe_mul,
    PadicInt.coe_pow, PadicInt.coe_natCast, newtonWeight, PadicInt.coe_lift,
    PadicInt.coe_add, PadicInt.coe_one]
  rw [add_comm (1:ℚ_[p]), add_pow]
  simp only [one_pow, mul_one, mul_pow]
  have reduce (j : ℕ) : (p:ℚ_[p])^j / j.factorial * (z:ℚ_[p])^j *
      (j.factorial * (m.choose j : ℚ_[p])) =
      ((p:ℚ_[p])^j * (z:ℚ_[p])^j) * m.choose j := by
    field_simp [Nat.factorial_ne_zero]
  simp_rw [reduce]
  symm
  apply sum_subset (range_mono (Nat.succ_le_succ hm))
  intro j _ hj
  simp [Nat.choose_eq_zero_of_lt (show m < j by simpa using hj)]


lemma eval_split (Q : (ℤ_[p])[X]) (s : ℕ) (m : ℤ_[p]) :
    ∃ e : ℤ_[p], Q.eval m = (∑ h ∈ range s, Q.coeff h * m^h) + m^s * e := by
  refine ⟨∑ i ∈ range (Q.natDegree+1), Q.coeff (s+i) * m^i, ?_⟩
  rw [Polynomial.eval_eq_sum_range' (n:=s+(Q.natDegree+1)) (by omega),sum_range_add,mul_sum]
  simp only [pow_add,mul_left_comm]

/-- A frozen moment before reordering by powers of the selected prime. -/
def frozenMoment (A : Finset ℕ) (w : ℤ_[p]) (d n : ℕ) : ℚ_[p] :=
  ∑ m ∈ indices A n, (w:ℚ_[p])^m / (m:ℚ_[p])^d

/-- The finite Newton polynomial gives the exact prefix modulo integral terms.
Only powers corresponding to orders 1 through `s` occur. -/
theorem principal_prefix_identity {b n s : ℕ} (A : Finset ℕ) (w z : ℤ_[p])
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p]) * (1 + (p:ℚ_[p]) * z)) :
    ∃ e : ℤ_[p], (powerPartial b s A n : ℚ_[p]) =
      (∑ h ∈ range s, ((principalPolynomial z n).coeff h : ℚ_[p]) * frozenMoment A w (s-h) n) + e := by
  classical
  let Q := principalPolynomial z n
  choose rem eqn using fun m : ℕ => eval_split Q s (m:ℤ_[p])
  refine ⟨∑ m ∈ indices A n, w^m * rem m, ?_⟩
  simp only [powerPartial, Rat.cast_sum, frozenMoment, mul_sum, PadicInt.coe_sum]
  rw [sum_comm, ← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  have mn := (mem_indices.mp hm).1
  have m0 : (m:ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (mem_indices.mp hm).2.1
  have em := eqn m
  rw [show Q.eval (m:ℤ_[p]) = _ from principalPolynomial_eval z mn] at em
  have em' := congrArg (fun x : ℤ_[p] => (x:ℚ_[p])) em
  simp only [PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_one, PadicInt.coe_mul,
    PadicInt.coe_natCast, PadicInt.coe_sum] at em'
  have bh : ∀ h ∈ range s, (m:ℚ_[p])^h * (m:ℚ_[p])^(s-h) = (m:ℚ_[p])^s := by
    intro h hh
    rw [← pow_add]; congr 1; have := mem_range.mp hh; omega
  simp only [powerWeight,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
    PadicInt.coe_mul,PadicInt.coe_pow]
  change 1 / ((m:ℚ_[p])^s * (b:ℚ_[p])^m) = _
  rw [one_div,mul_inv_rev,← inv_pow,factor,mul_pow,em']
  rw [mul_add, add_mul, mul_sum, sum_mul]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro h hh
    rw [← bh h hh]
    field_simp
    ring
  · field_simp

/-- The signed unit weight is constant on a `p`-power orbit. -/
lemma fixed_frobenius (w : ℤ_[p]) (fixed : w^p = w) (j : ℕ) : w^(p^j) = w := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,pow_mul,ih,fixed]

/-- Cofactor row with its integral unit inverses. The argument is the upper
bound on the cofactor, before multiplication by the power of `p`. -/
def momentRow (S : Finset ℕ) (w : ℤ_[p]) (d cut : ℕ) : ℤ_[p] :=
  ∑ r ∈ indices S cut, w^r * ((r:ℤ_[p]).inv)^d

private lemma row_coe {S : Finset ℕ} (outside : p ∉ S) (w : ℤ_[p]) (d cut : ℕ) :
    (momentRow S w d cut : ℚ_[p]) = ∑ r ∈ indices S cut, (w:ℚ_[p])^r / (r:ℚ_[p])^d := by
  rw [momentRow,PadicInt.coe_sum]
  apply sum_congr rfl
  intro r hr
  have hu := PadicInt.norm_natCast_eq_one_iff.mpr (hp.out.factoredNumbers_coprime outside (mem_indices.mp hr).2)
  have eqn := congrArg (fun x : ℤ_[p] => (x:ℚ_[p])) (PadicInt.inv_mul hu)
  simp only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at eqn
  have inv := (inv_eq_of_mul_eq_one_left eqn).symm
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, inv, inv_pow, div_eq_mul_inv]

/-- Infinite normalized moment at a real phase. -/
def phaseMoment (S : Finset ℕ) (w : ℤ_[p]) (d : ℕ) (t : ℝ) : ℤ_[p] :=
  ∑' i : ℕ, ((p:ℤ_[p])^d)^i * momentRow S w d ⌊t*(p:ℝ)^i⌋₊

private lemma weighted_rows_summable {d : ℕ} (hd : 0 < d) (v : ℕ → ℤ_[p]) :
    Summable (fun i : ℕ => ((p:ℤ_[p])^d)^i * v i) := by
  have small : ‖(p:ℤ_[p])^d‖ < 1 := by
    rw [norm_pow,PadicInt.norm_p]
    apply pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)) hd.ne'
  apply (summable_geometric_of_lt_one (norm_nonneg _) small).of_norm_bounded
  intro i
  rw [norm_mul,norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

lemma phaseMoment_tail (S : Finset ℕ) (w : ℤ_[p]) {d : ℕ} (hd : 0 < d) (t : ℝ) (k : ℕ) :
    ∃ e : ℤ_[p], phaseMoment S w d t =
      (∑ i ∈ range k, ((p:ℤ_[p])^d)^i * momentRow S w d ⌊t*(p:ℝ)^i⌋₊) +
        ((p:ℤ_[p])^d)^k * e := by
  let v (i : ℕ) := momentRow S w d ⌊t*(p:ℝ)^i⌋₊
  refine ⟨∑' i : ℕ, ((p:ℤ_[p])^d)^i * v (i+k), ?_⟩
  rw [phaseMoment, ← (weighted_rows_summable hd v).sum_add_tsum_nat_add k,
    ← (weighted_rows_summable hd (fun i => v (i+k))).tsum_mul_left]
  congr 1
  apply tsum_congr
  intro i
  rw [pow_add]; ring

/-- At all real points giving the same integer prefix, the frozen rational
moment is the scaled infinite phase moment up to a `p`-adic integer. -/
theorem frozenMoment_phase {S : Finset ℕ} (outside : p ∉ S) (w : ℤ_[p]) (fixed : w^p = w)
    {k n d : ℕ} (hd : 0 < d) (top : n < p^(k+1)) {t : ℝ} (cut : ⌊t*(p:ℝ)^k⌋₊ = n) :
    ∃ e : ℤ_[p], (phaseMoment S w d t : ℚ_[p]) / ((p:ℚ_[p])^d)^k =
      frozenMoment (insert p S) w d n + e := by
  obtain ⟨e,he⟩ := phaseMoment_tail S w hd t (k+1)
  refine ⟨(p:ℤ_[p])^d * e, ?_⟩
  have pp : (p:ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hsum := sum_layers hp.out outside n k top (fun m : ℕ => (w:ℚ_[p])^m / (m:ℚ_[p])^d)
  rw [← sum_range_reflect (fun j => ∑ r ∈ indices S (n/p^j), (w:ℚ_[p])^(p^j*r) /
    ((p^j*r:ℕ):ℚ_[p])^d) (k+1)] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  rw [he, PadicInt.coe_add, PadicInt.coe_sum, add_div, frozenMoment,hsum, sum_div]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro i hi
    have ik : i ≤ k := by simpa using mem_range.mp hi
    have ex : i + (k-i) = k := by omega
    have coord : ⌊t*(p:ℝ)^i⌋₊ = n/p^(k-i) := by
      rw [← cut,← Nat.floor_div_natCast, Nat.cast_pow,← ex, Nat.add_sub_cancel_left,pow_add]
      congr 1
      field_simp [hp.out.ne_zero]
    rw [coord,PadicInt.coe_mul, row_coe outside,mul_sum,sum_div]
    apply sum_congr rfl
    intro r hr
    have wf := congrArg (fun x : ℤ_[p] => (x:ℚ_[p])) (fixed_frobenius w fixed (k-i))
    simp only [PadicInt.coe_pow] at wf ⊢
    rw [pow_mul,wf]
    push_cast
    have peq : ((p:ℚ_[p])^d)^k = ((p:ℚ_[p])^i)^d * ((p:ℚ_[p])^(k-i))^d := by
      rw [← mul_pow, ← pow_add, ex, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [peq]
    have hr0 := (mem_indices.mp hr).2.1
    rw [← pow_mul, Nat.mul_comm d i, pow_mul]
    field_simp [pp, hr0]
    ring
  · push_cast
    rw [pow_succ]
    field_simp

/-- The local identity at every real phase in a digit position. Its finite
coefficients are integral and are shared by all the orders at this cutoff. -/
theorem phase_prefix_identity {S : Finset ℕ} (outside : p ∉ S) {b n s k : ℕ}
    {w z : ℤ_[p]} (fixed : w^p = w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p]) * (1 + (p:ℚ_[p])*z))
    (top : n < p^(k+1)) {t : ℝ} (cut : ⌊t*(p:ℝ)^k⌋₊ = n) :
    ∃ e : ℤ_[p], (powerPartial b s (insert p S) n : ℚ_[p]) =
      (∑ h ∈ range s, ((principalPolynomial z n).coeff h : ℚ_[p]) *
        ((phaseMoment S w (s-h) t : ℚ_[p]) / ((p:ℚ_[p])^(s-h))^k)) + e := by
  obtain ⟨E, he⟩ := principal_prefix_identity (n:=n) (s:=s) (insert p S) w z factor
  have each (h : ℕ) (hh : h < s) := frozenMoment_phase outside w fixed
    (d:=s-h) (by omega) top cut
  classical
  let r (h : ℕ) := if hh : h < s then (each h hh).choose else 0
  refine ⟨E - ∑ h ∈ range s, (principalPolynomial z n).coeff h * r h, ?_⟩
  rw [he,PadicInt.coe_sub,PadicInt.coe_sum]
  have id := sum_congr (s₁:=range s) rfl fun h hh =>
    (show ((principalPolynomial z n).coeff h : ℚ_[p]) *
       ((phaseMoment S w (s-h) t : ℚ_[p]) / ((p:ℚ_[p])^(s-h))^k) =
       ((principalPolynomial z n).coeff h : ℚ_[p])*frozenMoment (insert p S) w (s-h) n +
       (((principalPolynomial z n).coeff h*r h:ℤ_[p]):ℚ_[p]) by
      rw [(each h (mem_range.mp hh)).choose_spec, mul_add]
      simp [r,mem_range.mp hh])
  rw [id, sum_add_distrib]
  abel

/-- Simultaneous zeros clear the off-radix prime at every order and every point
of the digit interval, independently of recent insertions. -/
theorem prime_cleared_of_phase_zeros {S : Finset ℕ} (outside : p ∉ S) {b n s k : ℕ}
    {w z : ℤ_[p]} (fixed : w^p = w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p]) * (1 + (p:ℚ_[p])*z))
    (top : n < p^(k+1)) {t : ℝ} (cut : ⌊t*(p:ℝ)^k⌋₊ = n)
    (zeros : ∀ d, 0 < d → d ≤ s → phaseMoment S w d t = 0) :
    p.Coprime (powerShifted b s (insert p S) n).den := by
  obtain ⟨e, he⟩ := phase_prefix_identity outside fixed factor top cut (s:=s)
  have zsum : ∀ h ∈ range s, phaseMoment S w (s-h) t = 0 :=
    fun h hh => zeros _ (Nat.sub_pos_of_lt (mem_range.mp hh)) (Nat.sub_le ..)
  rw [sum_eq_zero (fun h hh => by rw [zsum h hh,PadicInt.coe_zero,zero_div,mul_zero]), zero_add] at he
  have shiftEq : (powerShifted b s (insert p S) n : ℚ_[p]) = (((b:ℤ_[p])^n*e:ℤ_[p]) : ℚ_[p]) := by
    simp only [powerShifted,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,he,PadicInt.coe_mul,
      PadicInt.coe_pow,PadicInt.coe_natCast]
  apply PadicInt.norm_natCast_eq_one_iff.mp
  apply PadicInt.isUnit_iff.mp
  apply PadicInt.isUnit_den
  rw [shiftEq,PadicInt.norm_coe]
  exact PadicInt.norm_le_one _

end NormalityChecker.LocalizedSupport
