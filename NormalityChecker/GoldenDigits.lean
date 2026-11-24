module

public import NormalityChecker.GoldenOrbit

/-! An executable parity readout from the occupied Fibonacci indices. -/
@[expose] public section
open Finset Real
open scoped goldenRatio
namespace NormalityChecker

private theorem fib_mod_two : ∀ j : ℕ, Nat.fib j % 2 = if j%3=0 then 0 else 1
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j+3 => by
    have step : Nat.fib (j+3)%2 = Nat.fib j%2 := by
      rw [Nat.fib_add_two (n:=j+1),Nat.fib_add_two (n:=j)]; omega
    simpa using step.trans (fib_mod_two j)

private theorem fib_sum_parity (S : Finset ℕ) :
    (∑ j∈S,Nat.fib (j+1)) % 2 = (S.filter (fun j => j%3≠2)).card % 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S fresh ih =>
    rw [sum_insert fresh,filter_insert]
    have p := fib_mod_two (a+1)
    by_cases ha : a%3=2
    · rw [ite_eq_right (not_not_intro ha),Nat.add_mod,ih]
      rw [ite_eq_left (by omega : (a+1)%3=0)] at p
      simp [p]
    · have h : a∉S.filter (fun j => j%3≠2) := fun h => fresh (mem_filter.mp h).1
      rw [ite_eq_left ha,card_insert_of_notMem h,Nat.add_mod,ih]
      rw [ite_eq_right (by omega : (a+1)%3≠0)] at p
      rw [p]; omega

/-- Binary readout on positive integer input: count occupied indices other
than `2 mod 3` and toggle the parity for an even least index. -/
def goldenFibReadout (M : ℕ) : ℕ :=
  ((M.zeckendorf.toFinset.filter (fun i => i%3≠2)).card + (if Even (leastFibIndex M) then 1 else 0)) % 2

/-- The finite parity calculation recovers the integer part modulo two. -/
theorem golden_floor_mod_two {M : ℕ} (hm : 0<M) :
    ⌊(M:ℝ)*φ⌋%2=(goldenFibReadout M:ℤ) := by
  rw [golden_floor_zeckendorf hm]; unfold goldenFibReadout
  have h := fib_sum_parity M.zeckendorf.toFinset
  split_ifs <;> omega

/-- Fractional bit `n` (starting at zero) follows from the Zeckendorf
representation of the integer `2^(n+1)`. -/
theorem golden_bit_readout (n : ℕ) : binaryBit φ n = decide (goldenFibReadout (2^(n+1))=1) := by
  let x := (2:ℝ)^n*φ
  have model := golden_floor_mod_two (M:=2^(n+1)) (by positivity)
  push_cast at model; rw [pow_succ,mul_right_comm] at model
  change ⌊x*2⌋%2=_ at model
  have whole := Int.fract_add_floor x
  have h0 := Int.fract_nonneg x; have h1 := Int.fract_lt_one x
  change decide (1/2≤Int.fract x) = _
  by_cases high : 1/2≤Int.fract x
  · have fld : ⌊x*2⌋=2*⌊x⌋+1 := by
      apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith
    rw [fld] at model; rw [decide_eq_true high,decide_eq_true (show goldenFibReadout (2^(n+1))=1 by omega)]
  · have fld : ⌊x*2⌋=2*⌊x⌋ := by
      apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith
    rw [fld] at model; rw [decide_eq_false high,decide_eq_false (show goldenFibReadout (2^(n+1))≠1 by omega)]

end NormalityChecker
