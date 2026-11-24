module

public import NormalityChecker.CyclotomicTest
public import NormalityChecker.CyclotomicDistribution

@[expose] public section
open Finset Polynomial
namespace NormalityChecker

/-- Literal equality of the new binary, p=3 cell test and the original
arithmetic obstruction, including families with zero coefficients. -/
theorem binary_cyclotomic_cell (M : Finset ℕ) (a : ℕ → ℚ) (u : ℕ) :
    cyclotomic (orderOf (2:ZMod 3)) ℚ ∣ cellPolynomial 3 u M a ↔ resonanceCoefficient M a u=0 := by
  have d : orderOf (2:ZMod 3)=2 := (residueOrder_eq (b:=2) (p:=3) (by decide)).symm.trans (by decide)
  rw [d,cyclotomic_two,show X+(1:ℚ[X])=X-C (-1:ℚ) by simp,dvd_iff_isRoot,IsRoot.def]
  simp only [cellPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  have e : (∑ m∈M, cellWeight 3 u a m*(-1:ℚ)^m)=resonanceCoefficient M a u := by
    apply sum_congr rfl; intro m _; unfold cellWeight radixDepth depth; ring
  rw [e]

theorem cyclotomicTest_binary_eq (M : Finset ℕ) (a : ℕ → ℚ) (hm : ∀ m∈M,0<m) :
    cyclotomicNormalTest 2 3 M a=binaryNormalTest M a := by
  apply Bool.eq_iff_iff.mpr
  rw [cyclotomicNormalTest_correct (by decide) (by decide) (by decide) M a hm,binaryNormalTest_correct hm]
  rfl

/-- Whenever b is 1 modulo p, all positive-weight nonempty families are normal. -/
theorem positive_sum_of_order_one {b p : ℕ} [Fact p.Prime] (hb : 1<b) (ho : Odd p)
    (hbc : b.Coprime p) (hone : (b:ZMod p)=1) (M : Finset ℕ) (a : ℕ → ℚ)
    (hM : M.Nonempty) (hm : ∀ m∈M,0<m) (ha : ∀ m∈M,0<a m) : NormalIn b (radixSum b p M a) := by
  let S := max 1 (M.sup id)
  apply (cyclotomic_normal_iff hb ho hbc (S:=S) (by dsimp [S]; omega) M a
    (fun m h => ⟨hm m h,(Finset.le_sup (f:=id) h).trans (le_max_right ..)⟩)).mpr
  intro u _ H
  rw [hone,orderOf_one,cyclotomic_one, ← C_1,dvd_iff_isRoot,IsRoot.def] at H
  simp only [cellPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,one_pow,mul_one] at H
  have hp := (Fact.out (p:=p.Prime)).pos
  exact (sum_pos (fun m h => by dsimp [cellWeight]; positivity [hm m h,ha m h]) hM).ne' H

theorem decimal_positive_normal (M : Finset ℕ) (a : ℕ → ℚ) (hM : M.Nonempty)
    (hm : ∀ m∈M,0<m) (ha : ∀ m∈M,0<a m) : NormalIn 10 (radixSum 10 3 M a) :=
  positive_sum_of_order_one (by decide) (by decide) (by decide) (by decide) M a hM hm ha

/-- A three-term resonance coming from a primitive cube root. -/
theorem seventh_triple_not_normal :
    ¬NormalIn 2 (radixComponent 2 7 1 + 2*radixComponent 2 7 2 + 3*radixComponent 2 7 3) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let M : Finset ℕ := {1,2,3}
  let a (m : ℕ) : ℚ := m
  have H := cyclotomicNormalTest_correct (b:=2) (p:=7) (by decide) (by decide) (by decide) M a (by simp [M])
  have test : cyclotomicNormalTest 2 7 M a=false := by dsimp [M,a]; decide +kernel
  rw [test] at H
  simpa [M,a,radixSum,add_assoc,add_comm,add_left_comm] using H.not

/-- Two different endpoint sequences for the same scaled orbit have
different limiting atom weights. -/
theorem seventh_triple_masses :
    resonanceMass 2 7 3 {1,2,3} (fun m => m)=2/9 ∧
    resonanceMass 2 7 7 {1,2,3} (fun m => m)=2/3 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  simp only [resonanceMass, ← resonanceWitnesses_eq (b:=2) (p:=7) (by decide)]
  decide +kernel

/-- Both weak limits for the explicit three-component example. -/
theorem seventh_triple_distributions (f : C(AddCircle (1:ℝ),ℂ)) :
    let x := radixComponent 2 7 1 + 2*radixComponent 2 7 2 + 3*radixComponent 2 7 3
    let A := Weyl.cMean (fun n => (2:ℝ)^n*(6*x)) f
    Filter.Tendsto (fun k : ℕ => A (3*7^k)) Filter.atTop (nhds (7/9*Weyl.cInt f+2/9*f 0)) ∧
      Filter.Tendsto (fun k : ℕ => A (7^(k+1))) Filter.atTop (nhds (1/3*Weyl.cInt f+2/3*f 0)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let M : Finset ℕ := {1,2,3}
  let a (m : ℕ) : ℚ := m
  have scale : radixDilation 7 M a=6 := by norm_num [radixDilation,weightDen,M,a]
  have hx : radixSum 2 7 M a=radixComponent 2 7 1 + 2*radixComponent 2 7 2 + 3*radixComponent 2 7 3 := by
    norm_num [M,a,radixSum]; ring
  have H₃ := cyclotomic_distribution (b:=2) (p:=7) (S:=3) (by decide) (by decide) (by decide) (by decide)
    M a (by simp [M]) f
  have H₇ := cyclotomic_distribution (b:=2) (p:=7) (S:=7) (by decide) (by decide) (by decide) (by decide)
    M a (by simp [M]) f
  simp only [scale,hx] at H₃ H₇
  rw [show resonanceMass 2 7 3 M a=2/9 from seventh_triple_masses.1] at H₃
  rw [show resonanceMass 2 7 7 M a=2/3 from seventh_triple_masses.2] at H₇
  constructor
  · convert H₃ using 2; push_cast; ring
  · simpa only [pow_succ' 7,Nat.cast_ofNat, Rat.cast_div,Rat.cast_ofNat,show (1:ℂ)-2/3=1/3 by norm_num] using H₇

end NormalityChecker
