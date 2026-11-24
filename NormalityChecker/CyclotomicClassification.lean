module

public import NormalityChecker.CyclotomicFourier
public import NormalityChecker.FiniteClassification
public import NormalityChecker.FourierTest

@[expose] public section
open Finset Filter Polynomial Classical
open scoped Topology
namespace NormalityChecker

def radixDepth (p u m : ℕ) := Nat.log p (u/m)

def cellWeight (p u : ℕ) (a : ℕ → ℚ) (m : ℕ) := (a m/m)/(p:ℚ)^radixDepth p u m

noncomputable def cellPolynomial (p u : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) : ℚ[X] :=
  ∑ m ∈ M, C (cellWeight p u a m)*X^m

noncomputable def radixSum (b p : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) :=
  ∑ m ∈ M, (a m:ℝ)*radixComponent b p m

def radixDilation (p : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) := (p-1)*weightDen M a

noncomputable def resonantCells (b p S : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) :=
  (Ico S (p*S)).filter fun u => cyclotomic (orderOf (b:ZMod p)) ℚ ∣ cellPolynomial p u M a

private lemma scaled_eq {p : ℕ} (hp : 1<p) (b : ℕ) (M : Finset ℕ) (a : ℕ → ℚ)
    (hm : ∀ m∈M, 0<m) :
    (radixDilation p M a:ℝ)*radixSum b p M a = CyclotomicCell.scaled b p M (integerWeight M a) := by
  simp only [radixDilation, Nat.cast_mul,Nat.cast_sub hp.le,Nat.cast_one,CyclotomicCell.scaled,radixSum,mul_assoc,mul_sum]
  apply sum_congr rfl; intro m h
  have he : (integerWeight M a m:ℝ)=(weightDen M a:ℝ)*((a m:ℝ)/m) := by exact_mod_cast integerWeight_spec M a m h
  rw [he]; field_simp [Nat.ne_of_gt (hm m h)]

private lemma scaled_value {p : ℕ} [Fact p.Prime] (w : ℤ_[p]) (M : Finset ℕ) (a : ℕ → ℚ) (u : ℕ) :
    let j := radixDepth p u
    let E := M.sup j
    (CyclotomicCell.value M (integerWeight M a) j E w:ℚ_[p]) =
      (weightDen M a:ℚ_[p])*(p:ℚ_[p])^E*(cellPolynomial p u M a).aeval (w:ℚ_[p]) := by
  dsimp only; unfold CyclotomicCell.value cellPolynomial
  simp only [PadicInt.coe_sum,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast,PadicInt.coe_natCast]
  simp only [map_sum,map_mul,map_pow,aeval_C,aeval_X,mul_sum]
  apply sum_congr rfl; intro m h
  have he : (integerWeight M a m:ℚ_[p])=(weightDen M a:ℚ_[p])*((a m:ℚ_[p])/m) := by
    exact_mod_cast integerWeight_spec M a m h
  have hp := Fact.out (p:=p.Prime)
  rw [he]; unfold cellWeight; simp only [map_div₀,map_natCast,map_pow, eq_ratCast]
  have e := Nat.sub_add_cancel (Finset.le_sup (f:=radixDepth p u) h)
  conv_rhs => rw [← e, pow_add]
  field_simp [hp.ne_zero]

private theorem cyclotomic_character {b p S : ℕ} [Fact p.Prime] (hb : 1<b) (ho : Odd p) (hbc : b.Coprime p)
    (M : Finset ℕ) (a : ℕ → ℚ) (hm : ∀ m∈M, 0<m ∧ m≤S)
    (h : ℤ) (hh : h≠0) (u : ℕ) (hu : u∈Ico S (p*S)) :
    RadixCellCancellation p (fun n => phase (h*((b:ℝ)^n * ((radixDilation p M a:ℝ)*radixSum b p M a))) -
      (if u ∈ resonantCells b p S M a then 1 else 0)) u := by
  classical
  have hp := Fact.out (p:=p.Prime)
  obtain ⟨w,hw,hred⟩ := exists_inverse_lift b hbc
  let j := radixDepth p u
  let E := M.sup j
  have bounds (m : ℕ) (h : m∈M) : m*p^(j m)≤u ∧ u+1≤m*p^(j m+1) := by
    have hmu := (hm m h).2.trans (mem_Ico.mp hu).1
    have hm' := (hm m h).1
    have hd := Nat.div_pos hmu hm'
    constructor
    · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm').mp (Nat.pow_log_le_self _ hd.ne')
    · have H := (Nat.div_lt_iff_lt_mul hm').mp (Nat.lt_pow_succ_log_self hp.one_lt (u/m))
      rw [mul_comm m]; exact H
  have hd := Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one ((ZMod.isUnit_iff_coprime b p).mpr hbc).ne_zero)
    (show 0<p-1 by have := hp.one_lt; omega)
  have eqn : CyclotomicCell.value M (integerWeight M a) j E w=0 ↔ u∈resonantCells b p S M a := by
    rw [resonantCells,mem_filter,and_iff_right hu,← lift_eval_zero_iff hd w hw,
      ← PadicInt.coe_eq_zero,scaled_value]
    have hD : (weightDen M a:ℚ_[p])≠0 := by exact_mod_cast (weightDen_pos M a).ne'
    simp [hp.ne_zero,hD]
  rw [scaled_eq hp.one_lt b M a (fun m h => (hm m h).1)]
  simpa only [eqn] using CyclotomicCell.character hb ho hbc w (inverse_lift_precision w hw hred hbc)
    M (integerWeight M a) j (E:=E) (fun m h => (hm m h).1) (fun m h => (bounds m h).1)
    (fun m h => (bounds m h).2) (fun m h => Finset.le_sup h) h hh

/-- The exact nonconstant Fourier coefficients at the ends of complete scales. -/
theorem cyclotomic_fourier_limit {b p S : ℕ} [Fact p.Prime] (hb : 1<b) (ho : Odd p)
    (hbc : b.Coprime p) (hS : 0<S) (M : Finset ℕ) (a : ℕ → ℚ) (hm : ∀ m∈M, 0<m ∧ m≤S)
    (h : ℤ) (hh : h≠0) :
    Tendsto (fun k => mean (fun n => phase (h*((b:ℝ)^n*((radixDilation p M a:ℝ)*radixSum b p M a)))) (S*p^k))
      atTop (𝓝 (((resonantCells b p S M a).card:ℂ)/(((p:ℂ)-1)*S))) := by
  classical
  have H := mean_at_scale (Fact.out (p:=p.Prime)).one_lt hS _
    (fun u => if u∈resonantCells b p S M a then (1:ℂ) else 0) (cyclotomic_character hb ho hbc M a hm h hh)
  convert H using 3
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  congr 2
  ext u
  simp [resonantCells,and_assoc]; tauto

/-- Necessary and sufficient cyclotomic divisibility test, for every odd prime
parameter coprime to the integer base. -/
theorem cyclotomic_normal_iff {b p S : ℕ} [Fact p.Prime] (hb : 1<b) (ho : Odd p)
    (hbc : b.Coprime p) (hS : 0<S) (M : Finset ℕ) (a : ℕ → ℚ) (hm : ∀ m∈M, 0<m ∧ m≤S) :
    NormalIn b (radixSum b p M a) ↔ ∀ u∈Ico S (p*S),
      ¬ cyclotomic (orderOf (b:ZMod p)) ℚ ∣ cellPolynomial p u M a := by
  classical
  have hp := Fact.out (p:=p.Prime)
  have hD : 0<radixDilation p M a := Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (weightDen_pos ..)
  rw [← normal_mul_nat_iff hb hD]
  constructor
  · intro hn u hu hr
    have grow : Tendsto (fun k : ℕ => S*p^k) atTop atTop := tendsto_atTop_mono
      (fun k => Nat.le_mul_of_pos_left _ hS) (tendsto_pow_atTop_atTop_of_one_lt hp.one_lt)
    have eqn := tendsto_nhds_unique (cyclotomic_fourier_limit hb ho hbc hS M a hm 1 one_ne_zero)
      ((fourier_of_normal hn 1 one_ne_zero).comp grow)
    have hcard := Finset.card_pos.mpr (show (resonantCells b p S M a).Nonempty from ⟨u,mem_filter.mpr ⟨hu,hr⟩⟩)
    exact (div_ne_zero (by exact_mod_cast hcard.ne') (mul_ne_zero
      (sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)) (by exact_mod_cast hS.ne'))) eqn
  · intro H
    apply normal_of_fourier hb
    intro h hh
    apply mean_zero_of_radix_cells hp.one_lt hS
    intro u hu
    simpa [resonantCells,H u hu] using cyclotomic_character hb ho hbc M a hm h hh u hu

end NormalityChecker
