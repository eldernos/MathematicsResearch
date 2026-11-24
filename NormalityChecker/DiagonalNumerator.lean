module

public import NormalityChecker.DiagonalStep
public import NormalityChecker.ShadowCancellations

/-! Repetition bounds for the actual step-normalized diagonal logarithm numerator. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.DiagonalNumerator

/-- Integer numerator with the factorial clearing the recurrence denominators. -/
def scaled : ℕ → ℤ
  | 0 => 0
  | n+1 => -2*(2*(n:ℤ)+3)*(2*scaled n+3*n.factorial)

/-- This recurrence measures the given diagonal rational, including its numerator. -/
theorem scaled_eq (n : ℕ) :
    (scaled n : ℚ) = n.factorial * (-1:ℚ)^n * (2*(2*(n:ℚ)+1)*n.centralBinom) *
      logShadow n n := by
  induction n with
  | zero => simp [scaled, logShadow, logPrefix]
  | succ n ih =>
    have cb := Nat.succ_mul_centralBinom_succ n
    have cbq := congrArg (fun v : ℕ => (v:ℚ)) cb
    push_cast at cbq
    have st := logShadow_diagonal_step n
    have sg : (-1:ℚ)^n * (-1:ℚ)^n = 1 := by rw [← mul_pow]; norm_num
    simp only [scaled,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_add,Int.cast_natCast,
      Nat.factorial_succ,pow_succ,Nat.cast_succ,Nat.cast_mul,ih]
    linear_combination (norm := ring_nf)
      (n.factorial:ℚ)*(-1:ℚ)^n*2*(2*(n:ℚ)+3)*logShadow (n+1) (n+1)*cbq +
      (n.factorial:ℚ)*(-1:ℚ)^n*2*(2*(n:ℚ)+3)*st +
      6*(n.factorial:ℚ)*(2*(n:ℚ)+3)*sg

variable (p : ℕ) [Fact p.Prime]

/-- For n < p, the factorial is a unit. -/
def residue (n : ℕ) : ZMod p := (scaled n : ZMod p) / n.factorial

theorem residue_step {n : ℕ} (hn : n+1<p) :
    ((n:ZMod p)+1)*residue p (n+1) = -2*(2*(n:ZMod p)+3)*(2*residue p n+3) := by
  have hfac : (n.factorial:ZMod p) ≠ 0 := fun h =>
    (Fact.out : p.Prime).dvd_factorial.mp ((ZMod.natCast_eq_zero_iff ..).mp h) |>.not_gt (by omega)
  have hs : ((n:ZMod p)+1) ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact fun h => Nat.not_dvd_of_pos_of_lt (by omega) hn ((ZMod.natCast_eq_zero_iff ..).mp h)
  simp only [residue, scaled, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Int.cast_mul,
    Int.cast_neg, Int.cast_ofNat, Int.cast_add, Int.cast_natCast]
  field_simp

private noncomputable def denPoly : ℕ → (ZMod p)[X]
  | 0 => 1
  | j+1 => (X+C (j:ZMod p)+1)*denPoly j

private noncomputable def numPoly (c : ZMod p) : ℕ → (ZMod p)[X]
  | 0 => C c
  | j+1 => C (-2)*(C 2*(X+C (j:ZMod p))+C 3)*(C 2*numPoly c j+C 3*denPoly p j)

private lemma iterate {n h : ℕ} {c : ZMod p} (hn : n+h<p) (start : residue p n=c) :
    (denPoly p h).eval (n:ZMod p)*residue p (n+h)=(numPoly p c h).eval (n:ZMod p) := by
  induction h with
  | zero => simpa [denPoly,numPoly] using start
  | succ j ih =>
    have prev := ih (by omega)
    have step := residue_step p (n:=n+j) (by omega)
    push_cast at step
    simp only [denPoly,numPoly,eval_mul,eval_add,eval_X,eval_C,eval_one]
    linear_combination (denPoly p j).eval (n:ZMod p)*step -
      4*(2*((n:ZMod p)+j)+3)*prev

private lemma degrees (c : ZMod p) (h : ℕ) :
    (denPoly p h).natDegree≤h ∧ (numPoly p c h).natDegree≤h := by
  induction h with
  | zero => simp [denPoly,numPoly]
  | succ j ih =>
    have lin : (X+C (j:ZMod p)).natDegree≤1 := natDegree_add_le_of_degree_le natDegree_X_le (by simp)
    have a : (X+C (j:ZMod p)+1).natDegree≤1 := natDegree_add_le_of_degree_le lin (by simp)
    have b : (C (-2)*(C 2*(X+C (j:ZMod p))+C 3)).natDegree≤1 :=
      (natDegree_C_mul_le ..).trans (natDegree_add_le_of_degree_le ((natDegree_C_mul_le ..).trans lin) (by simp))
    constructor
    · exact (natDegree_mul_le_of_le a ih.1).trans (by omega)
    · exact (natDegree_mul_le_of_le b (natDegree_add_le_of_degree_le
        ((natDegree_C_mul_le ..).trans ih.2) ((natDegree_C_mul_le ..).trans ih.1))).trans (by omega)

private lemma unit {m : ℕ} (hm : 0<m) (hp : m<p) : (m:ZMod p)≠0 :=
  fun h => Nat.not_dvd_of_pos_of_lt hm hp ((ZMod.natCast_eq_zero_iff ..).mp h)

private lemma obstruction_ne (c : ZMod p) {h : ℕ} (big : 3<p) (pos : 0<h) (short : 2*h<p) :
    numPoly p c h-C c*denPoly p h ≠ 0 := by
  have two : (2:ZMod p)≠0 := by exact_mod_cast unit p (by decide : 0<2) (by omega)
  have three : (3:ZMod p)≠0 := by exact_mod_cast unit p (by decide : 0<3) big
  intro eqn
  have evalAt (x : ZMod p) := congrArg (fun P : (ZMod p)[X] => P.eval x) eqn
  simp only [eval_sub,eval_mul,eval_C,eval_zero,sub_eq_zero] at evalAt
  by_cases cz : c=0
  · subst c
    have denZero (j : ℕ) : (denPoly p (j+1)).eval (-1)=0 := by
      induction j with
      | zero => simp [denPoly]
      | succ j ih => rw [denPoly,eval_mul,ih,mul_zero]
    have numUnit (j : ℕ) (small : 2*(j+1)<p) : (numPoly p 0 (j+1)).eval (-1)≠0 := by
      induction j with
      | zero =>
        simp only [numPoly,denPoly,eval_mul,eval_add,eval_X,eval_C,eval_one,Nat.cast_zero]
        convert mul_ne_zero (neg_ne_zero.mpr two) three using 1; ring
      | succ j ih =>
        have odd := unit p (m:=2*(j+1)+1) (by omega) (by omega)
        push_cast at odd
        rw [numPoly]
        simp only [eval_add,eval_C,eval_X,eval_mul,denZero,mul_zero,add_zero]
        apply mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two) ?_) (mul_ne_zero two (ih (by omega)))
        convert odd using 1; push_cast; ring
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    exact numUnit j short (by simpa using evalAt (-1))
  · let x : ZMod p := -(h:ZMod p)-1/2
    have dx (j : ℕ) (hj : j≤h) : (denPoly p j).eval x≠0 := by
      induction j with
      | zero => simp [denPoly]
      | succ i ih =>
        simp only [denPoly,eval_mul,eval_add,eval_X,eval_C,eval_one]
        apply mul_ne_zero _ (ih (by omega))
        have u := unit p (m:=2*(h-(i+1))+1) (by omega) (by omega)
        push_cast [Nat.cast_sub (by omega : i+1≤h)] at u
        intro bad; apply u; dsimp [x] at bad
        field_simp at bad
        linear_combination -bad
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    have nz := mul_ne_zero cz (dx (j+1) le_rfl)
    apply nz; rw [← evalAt x]
    simp only [numPoly,eval_mul,eval_add,eval_C,eval_X]
    have v : 2*(x+(j:ZMod p))+3=0 := by dsimp [x]; push_cast; field_simp; ring
    rw [v,mul_zero,zero_mul]

/-- Any specified residue repeats at a given short gap at most h times. -/
theorem paired_residues {h : ℕ} (big : 3<p) (pos : 0<h) (short : 2*h<p) (c : ZMod p) :
    ((range p).filter (fun n => n+h<p ∧ residue p n=c ∧ residue p (n+h)=c)).card≤h := by
  classical
  let U := (range p).filter (fun n => n+h<p ∧ residue p n=c ∧ residue p (n+h)=c)
  let W := numPoly p c h-C c*denPoly p h
  have inj : Set.InjOn (fun n : ℕ => (n:ZMod p)) (U:Set ℕ) := by
    intro a ha b hb eqn; have e := congrArg ZMod.val eqn
    simpa [ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp ha).1),
      ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp hb).1)] using e
  change U.card≤h; rw [← card_image_of_injOn inj]
  have bd := degrees p c h
  apply (Polynomial.card_le_degree_of_subset_roots (p:=W) ?_).trans
    (by simpa using natDegree_sub_le_of_le bd.2 ((natDegree_C_mul_le c (denPoly p h)).trans bd.1))
  intro x hx; obtain ⟨n,hn,rfl⟩ := mem_image.mp (Finset.mem_val.mp hx)
  obtain ⟨_,lo,a,b⟩ := mem_filter.mp hn
  apply (Polynomial.mem_roots (obstruction_ne p c big pos short)).mpr
  simp only [Polynomial.IsRoot,eval_sub,eval_mul,eval_C,sub_eq_zero]
  rw [← iterate p lo a,b,mul_comm]

end NormalityChecker.DiagonalNumerator
