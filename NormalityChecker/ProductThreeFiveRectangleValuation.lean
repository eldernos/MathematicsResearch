module

public import NormalityChecker.ProductThreeFiveRectangles
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.Taylor

/-! The ternary valuation of the opposite quinary numerator on a full rectangle. -/

@[expose] public section

open Finset Polynomial
namespace NormalityChecker.ProductThreeFive

-- At X = -1/2 this is the negative of the one-axis sum with its powers of five cleared.
private noncomputable def blockPoly : ℕ → ℤ[X]
  | 0 => 0
  | s+1 => C 5 * blockPoly s + X^(5^(s+1) : ℕ)

private lemma block_add (a b : ℕ) (x : ℤ) :
    (blockPoly (a+b)).eval x =
      5^b * (blockPoly a).eval x + (blockPoly b).eval (x^(5^a : ℕ)) := by
  induction b with
  | zero => simp [blockPoly]
  | succ b ih =>
    rw [← Nat.add_assoc]
    simp only [blockPoly]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, ih]
    rw [show a+b+1=a+(b+1) by omega, pow_add (5:ℕ) a (b+1), pow_mul, pow_succ (5:ℤ)]
    ring

private lemma eval_congr {x y m : ℤ} (h : x ≡ y [ZMOD m]) (P : ℤ[X]) :
    P.eval x ≡ P.eval y [ZMOD m] := by
  apply Int.modEq_of_dvd
  exact h.dvd.trans (sub_dvd_eval_sub _ _ _)

-- The derivative at 1 is s * 5^s. All s terms give the same contribution.
private lemma block_derivative (s : ℕ) :
    (blockPoly s).derivative.eval 1 = (s:ℤ)*5^s := by
  induction s with
  | zero => simp [blockPoly]
  | succ s ih =>
    simp only [blockPoly, derivative_add, derivative_C_mul, derivative_X_pow, eval_add,
      eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, ih, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_succ]
    ring

private lemma block_stable {s : ℕ} {m x y : ℤ} (hs : 3 ∣ s) (hm : 3 ∣ m)
    (hx : x ≡ 1 [ZMOD 3]) (hy : x ≡ y [ZMOD m]) :
    (blockPoly s).eval x ≡ (blockPoly s).eval y [ZMOD 3*m] := by
  have deriv := eval_congr hx (blockPoly s).derivative
  rw [block_derivative] at deriv
  have van : (3:ℤ) ∣ (blockPoly s).derivative.eval x := by
    apply Int.modEq_zero_iff_dvd.mp
    exact deriv.trans ((dvd_mul_of_dvd_left (by exact_mod_cast hs : (3:ℤ) ∣ s) _).modEq_zero_int)
  obtain ⟨c, hc⟩ := (blockPoly s).exists_mul_sq_add_linear_part_eq_eval_add x (y-x)
  rw [show x+(y-x)=y by ring] at hc
  apply Int.modEq_of_dvd
  rw [← hc]
  ring_nf
  obtain ⟨u, hu⟩ := hy.dvd
  obtain ⟨v, hv⟩ := van
  obtain ⟨w, hw⟩ := hm
  refine ⟨c*w*u^2+v*u, ?_⟩
  have ey : y = x + m*u := by linarith only [hu]
  rw [ey,hv,hw]; ring

private lemma pow_three_lift {x : ℤ} (hx : x ≡ 1 [ZMOD 3]) (t : ℕ) :
    x^(3^t : ℕ) ≡ 1 [ZMOD 3^(t+1)] := by
  induction t with
  | zero => simpa using hx
  | succ t ih =>
    obtain ⟨z, hz⟩ := Int.modEq_iff_add_fac.mp ih.symm
    rw [pow_succ (3:ℕ), pow_mul, hz, pow_succ (3:ℤ) (t+1)]
    apply Int.modEq_of_dvd
    refine ⟨-(z + 3^(t+1)*z^2 + 3^(2*t+1)*z^3), ?_⟩
    rw [show 2*t+1=t+t+1 by omega]
    simp only [pow_succ, pow_add]
    ring

private abbrev span (t : ℕ) := 2*3^t

private lemma five_step (t : ℕ) : (5:ℤ)^span t ≡ 1 [ZMOD 3^(t+1)] := by
  simpa only [span,pow_mul] using pow_three_lift (x:=5^2) (by decide) t

private lemma shift_step {x : ℤ} (hx : x ≡ 1 [ZMOD 3]) (t r : ℕ) :
    x^(5^(r*span t) : ℕ) ≡ x [ZMOD 3^(t+2)] := by
  have e := (five_step t).pow r
  simp only [← pow_mul, one_pow] at e
  rw [Nat.mul_comm] at e
  have ev : (1:ℕ) ≡ 5^(r*span t) [MOD 3^(t+1)] := by
    exact_mod_cast e.symm
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by decide))).mp ev
  have positive : 0 < (5:ℕ)^(r*span t) := by positivity
  have sub : 5^(r*span t) = 1+3^(t+1)*k := by omega
  rw [sub,pow_add x,pow_mul x,pow_one]
  simpa only [one_pow,mul_one] using ((pow_three_lift hx (t+1)).pow k).mul_left x

private lemma base_two {x : ℤ} (hx : x ≡ 4 [ZMOD 9]) :
    (blockPoly 2).eval x ≡ 3 [ZMOD 9] :=
  (eval_congr hx _).trans (by simp only [blockPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero]; decide)

set_option exponentiation.threshold 16000 in
private lemma base_six {x : ℤ} (hx : x ≡ 4 [ZMOD 9]) :
    (blockPoly 6).eval x ≡ 9 [ZMOD 27] := by
  have stable := block_stable (s:=6) (by decide) (m:=9) (by decide)
    (x:=4) (by decide) hx.symm
  apply stable.symm.trans
  simp only [blockPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
  decide

-- Concatenate equal-length blocks. The two hypotheses account separately for
-- the new power of five on the old block and the changed binary argument.
private lemma repeat_blocks {s : ℕ} {M x B : ℤ}
    (scale : 5^s * B ≡ B [ZMOD M])
    (shift : ∀ r : ℕ, (blockPoly s).eval (x^(5^(r*s) : ℕ)) ≡ B [ZMOD M]) (u : ℕ) :
    (blockPoly (u*s)).eval x ≡ u*B [ZMOD M] := by
  induction u with
  | zero => simp [blockPoly]
  | succ u ih =>
    rw [Nat.succ_mul,block_add,Nat.cast_succ,add_mul,one_mul]
    apply Int.ModEq.add _ (shift u)
    apply (ih.mul_left _).trans
    simpa only [mul_left_comm (5^s : ℤ)] using scale.mul_left u

private lemma scale_unit {a B m d : ℤ} (h : a ≡ 1 [ZMOD m]) (v : d ∣ B) :
    a*B ≡ B [ZMOD m*d] := by
  obtain ⟨c, hc⟩ := h.dvd
  obtain ⟨e,rfl⟩ := v
  apply Int.modEq_of_dvd
  exact ⟨c*e, by linear_combination d*e*hc⟩

private lemma single_block (t : ℕ) {x : ℤ} (hx : x ≡ 4 [ZMOD 9]) :
    (blockPoly (span t)).eval x ≡ 3^(t+1) [ZMOD 3^(t+2)] := by
  have hx₃ : x ≡ 1 [ZMOD 3] := (hx.of_dvd (by decide : (3:ℤ)∣9)).trans (by decide)
  induction t with
  | zero => exact base_two hx
  | succ t ih =>
    by_cases z : t=0
    · subst t; exact base_six hx
    let s := span t
    let B := (blockPoly s).eval x
    have power9 : (9:ℤ) ∣ 3^(t+1) := pow_dvd_pow 3 (by omega : 2≤t+1)
    have div9 : (9:ℤ) ∣ B := Int.modEq_zero_iff_dvd.mp
      ((ih.of_dvd (power9.trans (pow_dvd_pow _ (by omega : t+1≤t+2)))).trans power9.modEq_zero_int)
    have scale : (5:ℤ)^s*B ≡ B [ZMOD 3^(t+3)] := by
      simpa only [show t+3=t+1+2 by omega, pow_add (3:ℤ) (t+1) 2, show (3:ℤ)^2=9 by decide] using
        scale_unit (five_step t) div9
    have ds : 3 ∣ s := dvd_mul_of_dvd_right (dvd_pow_self _ z) _
    have shift (r : ℕ) : (blockPoly s).eval (x^(5^(r*s) : ℕ)) ≡ B [ZMOD 3^(t+3)] := by
      simpa only [pow_succ' (3:ℤ) (t+2)] using
        (block_stable ds (dvd_pow_self 3 (by omega : t+2 ≠ 0)) hx₃ (shift_step hx₃ t r).symm).symm
    have triple := repeat_blocks scale shift 3
    have lifted : (blockPoly (3*s)).eval x ≡ 3*3^(t+1) [ZMOD 3^(t+3)] := by
      apply triple.trans
      simpa only [Nat.cast_ofNat, pow_succ' (3:ℤ) (t+2), B, s] using ih.mul_left' (c:=3)
    rw [show span (t+1) = 3*s by dsimp [s,span]; rw [pow_succ]; ring,
        pow_succ' (3:ℤ) (t+1)]
    exact lifted

private lemma multiple_blocks (t u : ℕ) {x : ℤ} (hx : x ≡ 4 [ZMOD 9]) :
    (blockPoly (u*span t)).eval x ≡ u*3^(t+1) [ZMOD 3^(t+2)] := by
  have hx₃ : x ≡ 1 [ZMOD 3] := (hx.of_dvd (by decide : (3:ℤ) ∣ 9)).trans (by decide)
  apply repeat_blocks
  · simpa only [pow_succ (3:ℤ) (t+1)] using
      scale_unit (five_step t) (dvd_pow_self 3 (by omega : t+1 ≠ 0))
  · intro r
    apply single_block t
    exact ((shift_step hx₃ t r).of_dvd (pow_dvd_pow 3 (by omega : 2≤t+2))).trans hx


private lemma crossNum_succ {a : ℕ} (ha : 0<a) (s : ℕ) :
    crossNum a (s+1) = a*2^(a^(s+1)-a^s)*crossNum a s + 1 := by
  rw [crossNum, sum_range_succ, crossNum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro i hi
    have h : i+1 ≤ s := mem_range.mp hi
    have h₁ := Nat.pow_le_pow_right ha h
    have h₂ := Nat.pow_le_pow_right ha (Nat.le_succ s)
    change a^s ≤ a^(s+1) at h₂
    simp only [crossTerm, show s+1-(i+1)=s-(i+1)+1 by omega,
      show a^(s+1)-a^(i+1)=(a^(s+1)-a^s)+(a^s-a^(i+1)) by omega,
      pow_succ a (s-(i+1)), pow_add (2:ℕ)]
    ring
  · simp [crossTerm]

private lemma binary_clear {m x : ℤ} (unit : 2*x ≡ -1 [ZMOD m]) (s : ℕ) :
    2^(5^s : ℕ)*(blockPoly s).eval x ≡ -(crossNum 5 s : ℤ) [ZMOD m] := by
  induction s with
  | zero => simp [blockPoly,crossNum]
  | succ s ih =>
    let e := (5:ℕ)^(s+1)-5^s
    have h : (5:ℕ)^(s+1) = e+5^s := (Nat.sub_add_cancel (Nat.pow_le_pow_right (by decide : 0<5) (Nat.le_succ s))).symm
    have newTerm := unit.pow (5^(s+1) : ℕ)
    rw [mul_pow, ((by decide : Odd (5:ℕ)).pow (n:=s+1)).neg_one_pow] at newTerm
    rw [blockPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X, mul_add,
      show (2:ℤ)^(5^(s+1) : ℕ)*(5*(blockPoly s).eval x) =
        (5*2^e)*(2^(5^s : ℕ)*(blockPoly s).eval x) by
          nth_rw 1 [h]; rw [pow_add]; ring]
    rw [crossNum_succ (by decide : 0<5)]
    push_cast
    convert (ih.mul_left (5*2^e)).add newTerm using 1; ring

/-- The first nonzero ternary digit at even length, including its unit
coefficient. Here the length is twice a power of three times u. -/
theorem crossNum_five_even_residue (t u : ℕ) :
    crossNum 5 (u*(2*3^t)) ≡ u*3^(t+1) [MOD 3^(t+2)] := by
  let L := u*span t
  obtain ⟨x,hx⟩ := (show Odd (3:ℤ) by decide).pow (n:=t+2)
  have fac : (3:ℤ)^(t+2) = 9*3^t := by rw [pow_add]; ring
  have x₉ : x ≡ 4 [ZMOD 9] := by rw [fac] at hx; unfold Int.ModEq; omega
  have unit : 2*x ≡ -1 [ZMOD 3^(t+2)] := by
    apply Int.modEq_of_dvd
    exact ⟨-1, by linarith only [hx]⟩
  have h₁ := binary_clear unit L
  have h₂ := (multiple_blocks t u x₉).mul_left (2^(5^L : ℕ))
  have binary : (2:ℤ)^(5^L : ℕ) ≡ -1 [ZMOD 3] := by
    simpa only [((by decide : Odd (5:ℕ)).pow (n:=L)).neg_one_pow] using
      (show (2:ℤ) ≡ -1 [ZMOD 3] by decide).pow (5^L : ℕ)
  have h₃ : (2:ℤ)^(5^L : ℕ)*(u*3^(t+1)) ≡ -(u*3^(t+1)) [ZMOD 3^(t+2)] := by
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm, neg_mul, mul_neg, one_mul] using
      (binary.mul_right' (c:=3^(t+1))).mul_left u
  have con := (h₁.symm.trans (h₂.trans h₃)).neg
  simp only [neg_neg] at con
  exact_mod_cast con

private lemma odd_cross {L : ℕ} (h : L%2 ≠ 0) : ¬ 3 ∣ crossNum 5 L := by
  let u := L/2
  have len : L=u*2+1 := by dsimp [u]; omega
  have d := crossNum_five_even_residue 0 u
  have d₀ : 3 ∣ crossNum 5 (u*2) := Nat.modEq_zero_iff_dvd.mp
    ((d.of_dvd (by decide : 3 ∣ 3^(0+2))).trans ((dvd_mul_left 3 u).modEq_zero_nat))
  rw [len,crossNum_succ (by decide : 0<5)]
  have dvd := dvd_mul_of_dvd_right d₀ (5*2^(5^(u*2+1)-5^(u*2)))
  omega

/-- The ternary cancellation depth is zero for odd lengths and one plus the
ternary valuation of the length for positive even lengths. -/
theorem crossNum_five_ternary_valuation {L : ℕ} (hL : 0<L) :
    (crossNum 5 L).factorization 3 = if L%2=0 then 1+L.factorization 3 else 0 := by
  split_ifs with parity
  · let m := L/2
    let t := m.factorization 3
    let u := ordCompl[3] m
    have hm : m ≠ 0 := by dsimp [m]; omega
    have hu : ¬3 ∣ u := Nat.not_dvd_ordCompl Nat.prime_three hm
    have len₂ : L=2*m := by dsimp [m]; omega
    have decomp : 3^t*u=m := Nat.ordProj_mul_ordCompl_eq_self m 3
    have len : L=u*(2*3^t) := by rw [len₂, ← decomp]; ring
    have residue := crossNum_five_even_residue t u
    rw [← len] at residue
    have low : 3^(t+1) ∣ crossNum 5 L := Nat.modEq_zero_iff_dvd.mp
      ((residue.of_dvd (pow_dvd_pow 3 (by omega : t+1≤t+2))).trans (dvd_mul_left _ _).modEq_zero_nat)
    have high : ¬3^(t+2) ∣ crossNum 5 L := by
      intro h
      have dh := Nat.modEq_zero_iff_dvd.mp (residue.symm.trans h.modEq_zero_nat)
      rw [pow_succ, mul_comm u, Nat.mul_dvd_mul_iff_left (by positivity)] at dh
      exact hu dh
    have nz : crossNum 5 L ≠ 0 := fun e => high (e ▸ dvd_zero _)
    have lo := (Nat.prime_three.pow_dvd_iff_le_factorization nz).mp low
    have hi := mt (Nat.prime_three.pow_dvd_iff_le_factorization nz).mpr high
    have val : L.factorization 3=t := by
      rw [len₂,Nat.factorization_mul (by decide) hm,Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3 ∣ 2),zero_add]
    omega
  · exact Nat.factorization_eq_zero_of_not_dvd (odd_cross parity)


/-- The same valuation for the rational opposite-axis sum before clearing
the binary and quinary units. -/
theorem opposite_quinary_ternary_valuation {L : ℕ} (hL : 0<L) :
    padicValRat 3 (∑ j ∈ range L, 1 / ((5:ℚ)^(j+1)*2^(5^(j+1) : ℕ))) =
      if L%2=0 then 1+(L.factorization 3 : ℤ) else 0 := by
  let D := (5:ℕ)^L * 2^(5^L : ℕ)
  have hd : 0<D := by dsimp [D]; positivity
  have hu : ¬3 ∣ D := fun h => (Nat.prime_three.dvd_mul.mp h).elim
    (fun e => (by decide : ¬3 ∣ 5) (Nat.prime_three.dvd_of_dvd_pow e))
    (fun e => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow e))
  have nz : crossNum 5 L ≠ 0 := by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
    rw [crossNum_succ (by decide : 0<5)]; omega
  have eqn : (∑ j ∈ range L, 1 / ((5:ℚ)^(j+1)*2^(5^(j+1) : ℕ))) =
      (crossNum 5 L:ℚ) / D := by
    rw [eq_div_iff (by exact_mod_cast hd.ne'),sum_mul,crossNum,Nat.cast_sum]
    apply sum_congr rfl
    intro j hj
    have le : j+1 ≤ L := mem_range.mp hj
    have a := Nat.sub_add_cancel le
    have b := Nat.sub_add_cancel (Nat.pow_le_pow_right (by decide : 0<5) le)
    dsimp only [D,crossTerm]
    push_cast
    field_simp
    have A : (5:ℚ)^(L-(j+1))*5^(j+1)=5^L := by rw [← pow_add,a]
    have B : (2:ℚ)^(5^L-5^(j+1) : ℕ)*2^(5^(j+1) : ℕ)=2^(5^L : ℕ) := by rw [← pow_add,b]
    rw [← A,← B]; ring
  rw [eqn,padicValRat.div (by exact_mod_cast nz) (by exact_mod_cast hd.ne'),
    padicValRat.of_nat,padicValRat.of_nat,Nat.multiplicity_eq_factorization Nat.prime_three,
    Nat.multiplicity_eq_factorization Nat.prime_three,Nat.factorization_eq_zero_of_not_dvd hu,
    crossNum_five_ternary_valuation hL]
  split <;> simp

/-- The full rectangle retains the entire ternary shell power except for
the ternary valuation of the opposite quinary numerator. -/
theorem rectangle_ternary_retained {n K L : ℕ} (hk : Nat.log 3 n = K)
    (hl : Nat.log 5 n = L) (full : 3^K+5^L ≤ n) (hK : 0<K) (hL : 0<L) :
    3^(K-(if L%2=0 then 1+L.factorization 3 else 0)) ∣ (pre n).den := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have newTerm := crossNum_succ (by decide : 0<3) k
  have unit : ¬3 ∣ crossNum 3 (k+1) := by
    rw [newTerm]
    have h := dvd_mul_of_dvd_left (dvd_mul_right 3 (2^(3^(k+1)-3^k))) (crossNum 3 k)
    omega
  have nz₃ : crossNum 3 (k+1) ≠ 0 := fun e => unit (e ▸ dvd_zero _)
  have nz₅ : crossNum 5 L ≠ 0 := by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
    rw [crossNum_succ (by decide : 0<5)]; omega
  have val : (commonNum n).factorization 3 = (crossNum 5 L).factorization 3 := by
    rw [rectangle_factor hk hl full, Nat.factorization_mul (mul_ne_zero (by positivity) nz₃) nz₅,
      Nat.factorization_mul (by positivity) nz₃, Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd unit, Nat.factorization_eq_zero_of_not_dvd
        (fun d => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow d))]
    omega
  have nz : commonNum n ≠ 0 := by
    rw [rectangle_factor hk hl full]; exact mul_ne_zero (mul_ne_zero (by positivity) nz₃) nz₅
  have eqn := (reduced_info (S:=commonNum n) (x:=pre n)
    (show 0 < 3^(k+1)*5^L by positivity) (by
      simpa [hk,hl,mul_assoc,mul_comm,mul_left_comm] using commonNum_eq n)).2
  have dvd : 3^(k+1) ∣ commonNum n*(pre n).den := by rw [eqn,mul_assoc]; exact dvd_mul_right ..
  have exp := (Nat.prime_three.pow_dvd_iff_le_factorization (mul_ne_zero nz (pre n).pos.ne')).mp dvd
  rw [Nat.factorization_mul nz (pre n).pos.ne', Finsupp.add_apply, val,
    crossNum_five_ternary_valuation hL] at exp
  exact (Nat.prime_three.pow_dvd_iff_le_factorization (pre n).pos.ne').mpr (by omega)

/-- Uniform denominator growth on full rectangles, including those that fail
both first-precision tests. Every rectangle beyond the cutoff retains 3^M. -/
theorem rectangle_denominator_growth {n M : ℕ} (late : 5^(2*M+2) ≤ n)
    (full : 3^Nat.log 3 n + 5^Nat.log 5 n ≤ n) : 3^M ∣ (pre n).den := by
  let K := Nat.log 3 n
  let L := Nat.log 5 n
  have lbound : 2*M+2 ≤ L := Nat.le_log_of_pow_le (by decide) late
  have order : L ≤ K := Nat.log_anti_left (by decide) (by decide : 3≤5)
  have upper : 3^L.factorization 3 ≤ L := Nat.le_of_dvd (by omega)
    ((Nat.prime_three.pow_dvd_iff_le_factorization (by omega : L≠0)).mpr le_rfl)
  have growth (v : ℕ) : 2*v+1 ≤ 3^v := by
    induction v with
    | zero => decide
    | succ v ih => rw [pow_succ]; omega
  have := growth (L.factorization 3)
  apply (pow_dvd_pow 3 (show M ≤ K-(if L%2=0 then 1+L.factorization 3 else 0) by
    split <;> omega)).trans
  exact rectangle_ternary_retained rfl rfl full (by omega) (by omega)

end NormalityChecker.ProductThreeFive
