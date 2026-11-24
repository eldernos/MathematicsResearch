module

public import NormalityChecker.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite counting estimate for the limitation of polynomial-denominator models. -/
@[expose] public section
open Finset
namespace NormalityChecker

/-- Among words in an alphabet of size `a`, words with at most `k` occurrences
of the distinguished symbol have total count at most `(2*a-1)^j / 2^(j-k)`.
For orbit models each symbol records two consecutive radix digits. -/
theorem few_symbol_words {a : ℕ} (d : Fin a) (j k : ℕ) :
    ((univ : Finset (Fin j → Fin a)).filter (fun w => (univ.filter (fun i => w i=d)).card≤k)).card *
      2^(j-k) ≤ (2*a-1)^j := by
  classical
  let weight (x : Fin a) : ℕ := if x=d then 1 else 2
  let words := (univ : Finset (Fin j → Fin a)).filter (fun w => (univ.filter (fun i => w i=d)).card≤k)
  have one : ∑ x : Fin a, weight x=2*a-1 := by
    have split := card_filter_add_card_filter_not (s:=univ) (fun x : Fin a => x=d)
    simp only [filter_eq',mem_univ,ite_true,card_singleton,card_univ,Fintype.card_fin] at split
    simp only [weight,sum_ite,filter_eq',mem_univ,ite_true,sum_const,nsmul_eq_mul,card_singleton]
    push_cast
    omega
  have total : (∑ w : Fin j → Fin a, ∏ i,weight (w i))=(2*a-1)^j := by
    rw [← one,sum_pow']; simp
  have each (w : Fin j → Fin a) (hw : w∈words) : 2^(j-k)≤∏ i,weight (w i) := by
    have count := (mem_filter.mp hw).2
    have split := card_filter_add_card_filter_not (s:=univ) (fun i : Fin j => w i=d)
    simp only [card_univ,Fintype.card_fin] at split
    simp only [weight,prod_ite,prod_const_one,one_mul,prod_const]
    apply Nat.pow_le_pow_right (by decide); omega
  calc _ = ∑ _w∈words, 2^(j-k) := by simp [words]
       _ ≤ ∑ w∈words, ∏ i,weight (w i) := sum_le_sum each
       _ ≤ ∑ w : Fin j → Fin a, ∏ i,weight (w i) := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
       _ = _ := total

end NormalityChecker
