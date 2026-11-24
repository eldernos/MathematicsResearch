module

public import NormalityChecker.DiagonalNumerator

/-! Factorial Taylor numerators of e, their periodic residues and short returns. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.FactorialNumerators

def numerator : ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1)*numerator n+1

/-- Denominator before reduction is n!, and the recurrence gives the exact numerator. -/
theorem taylor_sum (n : ℕ) :
    (numerator n:ℚ)/n.factorial=∑ j∈range (n+1), (1:ℚ)/j.factorial := by
  induction n with
  | zero => simp [numerator]
  | succ n ih =>
    rw [sum_range_succ,←ih,numerator,Nat.factorial_succ]; push_cast
    field_simp [Nat.factorial_ne_zero]

theorem periodic_residue (q n : ℕ) : (numerator (q+n):ZMod q)=numerator n := by
  induction n with
  | zero =>
    cases q with
    | zero => rfl
    | succ k => simp [numerator, Nat.cast_add]
  | succ n ih =>
    rw [←Nat.add_assoc,numerator,numerator]; push_cast; simp [ih]

private noncomputable def lag (p : ℕ) : ℕ → (ZMod p)[X]
  | 0 => 0
  | h+1 => (X+C ((h:ZMod p)+1))*lag p h+1

private lemma lag_degree (p h : ℕ) : (lag p (h+1)).natDegree≤h := by
  induction h with
  | zero => simp [lag]
  | succ h ih =>
    rw [lag]
    apply natDegree_add_le_of_degree_le _ (by simp)
    exact (natDegree_mul_le_of_le (show (X+C ((↑(h+1):ZMod p)+1)).natDegree≤1 by
      exact natDegree_add_le_of_degree_le natDegree_X_le (by simp)) ih).trans (by omega)

private lemma lag_eval (p n h : ℕ) (zero : (numerator n:ZMod p)=0) :
    (numerator (n+h):ZMod p)=(lag p h).eval (n:ZMod p) := by
  induction h with
  | zero => simpa [lag] using zero
  | succ h ih =>
    rw [←Nat.add_assoc,numerator,lag]; push_cast
    rw [ih]; simp; ring

/-- In one residue period modulo p there are at most h−1 repeated zeros at gap h,
including pairs that cross the end of the period. -/
theorem paired_zeros {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ((range p).filter (fun n => (numerator n:ZMod p)=0 ∧
      (numerator (n+(h+1)):ZMod p)=0)).card≤h := by
  let : Fact p.Prime := ⟨hp⟩
  classical
  let E := (range p).filter (fun n => (numerator n:ZMod p)=0 ∧ (numerator (n+(h+1)):ZMod p)=0)
  have inj : Set.InjOn (fun n : ℕ => (n:ZMod p)) E := by
    intro a ha b hb eqn
    simpa [ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp ha).1),
      ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp hb).1)] using congrArg ZMod.val eqn
  have mon : lag p (h+1) ≠ 0 := by
    intro eqn; have val := congrArg (fun f : (ZMod p)[X] => f.eval (-((h:ZMod p)+1))) eqn
    rw [lag,eval_add,eval_mul,eval_add,eval_X,eval_C,neg_add_cancel,zero_mul,zero_add,eval_one,eval_zero] at val
    exact one_ne_zero val
  change E.card≤h; rw [←card_image_of_injOn inj]
  apply (Polynomial.card_le_degree_of_subset_roots (p:=lag p (h+1)) ?_).trans (lag_degree p h)
  intro x hx; obtain ⟨n,hn,rfl⟩ := mem_image.mp (Finset.mem_val.mp hx)
  obtain ⟨_,a,b⟩ := mem_filter.mp hn
  exact (Polynomial.mem_roots mon).mpr (by simpa only [Polynomial.IsRoot,←lag_eval p n (h+1) a] using b)

end NormalityChecker.FactorialNumerators
