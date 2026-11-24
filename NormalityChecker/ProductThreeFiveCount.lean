module

public import NormalityChecker.ProductThreeFivePrefix

/-! The cost of canceled top columns, including the unfinished last shell. -/
@[expose] public section
open Finset
namespace NormalityChecker.ProductThreeFive

/-- A one charges a position where the quinary column test gives no information. -/
def columnCost (n : ℕ) : ℕ :=
  if Nat.log 3 (n-5^Nat.log 5 n)%4=0 then 1 else 0

private def cost (y : ℕ) : ℕ := if Nat.log 3 y%4=0 then 1 else 0
private def count (t : ℕ) := ∑ y ∈ range t, cost y

private lemma cost_one {k y : ℕ} (lo : 81^k ≤ y) (hi : y < 3*81^k) : cost y = 1 := by
  have base : 3^(4*k) = 81^k := by rw [pow_mul]; rfl
  have eqn := Nat.log_eq_of_pow_le_of_lt_pow (base.le.trans lo)
    (by simpa [pow_succ',base] using hi : y<3^(4*k+1))
  simp [cost,eqn]

private lemma cost_zero {k y : ℕ} (lo : 3*81^k ≤ y) (hi : y < 81*81^k) : cost y = 0 := by
  have base : 3^(4*k)=81^k := by rw [pow_mul]; rfl
  have lower := Nat.le_log_of_pow_le (by decide : 1<3)
    (by simpa [pow_succ',base] using lo : 3^(4*k+1) ≤ y)
  have upper := Nat.log_lt_of_lt_pow (ne_of_gt ((by positivity : 0<3*81^k).trans_le lo))
    (by rw [pow_add,base,mul_comm]; exact hi : y<3^(4*k+4))
  simp only [cost,ite_eq_right (by omega : Nat.log 3 y%4 ≠ 0)]

private lemma count_extend {t u c : ℕ} (le : t≤u) (h : ∀ y, t≤y → y<u → cost y=c) :
    count u = count t + (u-t)*c := by
  have eqn : u=t+(u-t) := by omega
  unfold count
  conv_lhs => rw [eqn,sum_range_add]
  have V := sum_congr (s₁:=range (u-t)) (s₂:=range (u-t)) rfl
    (fun i hi => h (t+i) (by omega) (by have := mem_range.mp hi; omega))
  rw [V]; simp

private lemma count_at_power (k : ℕ) : 40*count (81^k)=81^k+39 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have first := count_extend (t:=81^k) (u:=3*81^k) (by omega)
      (fun _ lo hi => cost_one lo hi)
    have next := count_extend (t:=3*81^k) (u:=81*81^k) (by omega)
      (fun _ lo hi => cost_zero lo hi)
    rw [pow_succ']; omega

/-- At an arbitrary truncation of a quinary shell, the proportion charged is at
most 27/40 up to a constant of less than one position. -/
private lemma count_partial (t : ℕ) : 40*count t ≤ 27*t+39 := by
  by_cases ht : t=0
  · simp [ht,count]
  let k := Nat.log 81 t
  have lo := Nat.pow_log_le_self 81 ht
  have hi := Nat.lt_pow_succ_log_self (by decide : 1<81) t
  change 81^k ≤ t at lo
  change t < 81^(k+1) at hi
  rw [pow_succ'] at hi
  have base := count_at_power k
  by_cases short : t ≤ 3*81^k
  · have H := count_extend lo (c:=1) (fun _ low high => cost_one low (high.trans_le short))
    omega
  · have first := count_extend (t:=81^k) (u:=3*81^k) (by omega) (fun _ low high => cost_one low high)
    have next := count_extend (t:=3*81^k) (u:=t) (by omega) (fun _ low high => cost_zero low (high.trans hi))
    omega

private lemma shell_count (l t : ℕ) (ht : t≤4*5^l) :
    (∑ i ∈ range (5^l+t), columnCost i) = (∑ i ∈ range (5^l), columnCost i)+count t := by
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i hi
  have ilt := mem_range.mp hi
  have h := Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right (5^l) i)
    (by rw [pow_succ']; omega : 5^l+i<5^(l+1))
  simp [columnCost,cost,h]

private lemma full_shells (l : ℕ) :
    40*(∑ n ∈ range (5^l), columnCost n) ≤ 27*5^l+39*l+13 := by
  induction l with
  | zero => decide
  | succ l ih =>
    have h := shell_count l (4*5^l) le_rfl
    have short := count_partial (4*5^l)
    rw [pow_succ',show 5*5^l=5^l+4*5^l by omega,h]
    omega

/-- Finite-prefix bound for the union of all intervals on which the
top quinary column cancels. It includes the very first, empty column. -/
theorem column_cost_bound (N : ℕ) :
    40*(∑ n ∈ range N, columnCost n) ≤ 27*N+39*Nat.log 5 N+52 := by
  by_cases hz : N=0
  · simp [hz]
  let l := Nat.log 5 N
  have lo : 5^l≤N := Nat.pow_log_le_self _ hz
  have hi : N<5^(l+1) := Nat.lt_pow_succ_log_self (by decide) _
  rw [pow_succ'] at hi
  have h := shell_count l (N-5^l) (by omega)
  have prev := full_shells l
  have partial' := count_partial (N-5^l)
  rw [Nat.add_sub_of_le lo] at h
  rw [h]; change _ ≤ 27*N+39*l+52
  omega

end NormalityChecker.ProductThreeFive
