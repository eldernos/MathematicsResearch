module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.SModEq.Pow
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Tactic

public section
open Polynomial
namespace NormalityChecker

variable {p : ℕ} [Fact p.Prime]

private lemma norm_lt_one_iff_reduce (x : ℤ_[p]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton,
    ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]

/-- Lift the inverse residue of the base to its unique order-d branch. -/
theorem exists_inverse_lift (b : ℕ) (hbc : b.Coprime p) :
    ∃ w : ℤ_[p], IsPrimitiveRoot w (orderOf (b:ZMod p)) ∧
      PadicInt.toZMod w = (b:ZMod p)⁻¹ := by
  let d := orderOf (b:ZMod p)
  have hp := Fact.out (p:=p.Prime)
  have hb : (b:ZMod p)≠0 := ((ZMod.isUnit_iff_coprime b p).mpr hbc).ne_zero
  have hdvd := ZMod.orderOf_dvd_card_sub_one hb
  have hd : 0<d := Nat.pos_of_dvd_of_pos hdvd (by have := hp.one_lt; omega)
  have hdlt : d<p := (Nat.le_of_dvd (by have := hp.one_lt; omega : 0<p-1) hdvd).trans_lt (Nat.sub_lt hp.pos (by decide))
  have hd₀ : (d:ZMod p)≠0 := by
    rw [ne_eq,ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hd hdlt
  let a : ℤ_[p] := ((b:ZMod p)⁻¹.val : ℕ)
  have ha : PadicInt.toZMod a = (b:ZMod p)⁻¹ := by simp [a]
  let F : ℤ[X] := X^d-1
  have valF (x : ℤ_[p]) : F.aeval x = x^d-1 := by simp [F]
  have der : F.derivative.aeval a = (d:ℤ_[p])*a^(d-1) := by simp [F,derivative_X_pow]
  have valNorm : ‖F.aeval a‖<1 := by
    rw [norm_lt_one_iff_reduce,valF,map_sub,map_pow,map_one,ha, inv_pow,pow_orderOf_eq_one,inv_one,sub_self]
  have derNorm : ‖F.derivative.aeval a‖=1 := by
    apply le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt ?_)
    rw [norm_lt_one_iff_reduce,der,map_mul,map_natCast,map_pow,ha]
    exact mul_ne_zero hd₀ (pow_ne_zero _ (inv_ne_zero hb))
  obtain ⟨w,hw,hnear,_⟩ := hensels_lemma (F:=F) (a:=a) (by simpa [derNorm] using valNorm)
  have hred : PadicInt.toZMod w = (b:ZMod p)⁻¹ := by
    rw [derNorm,norm_lt_one_iff_reduce,map_sub,sub_eq_zero,ha] at hnear; exact hnear
  refine ⟨w,⟨sub_eq_zero.mp ((valF w).symm.trans hw),fun l hl => ?_⟩,hred⟩
  have h := congrArg PadicInt.toZMod hl
  simp only [map_pow,hred,map_one,inv_pow,inv_eq_one] at h
  exact orderOf_dvd_of_pow_eq_one h

/-- The inverse Teichmüller lift cancels each inserted radix power at the
precision of its denominator. -/
theorem inverse_lift_precision {b : ℕ} (w : ℤ_[p])
    (hw : IsPrimitiveRoot w (orderOf (b:ZMod p))) (hred : PadicInt.toZMod w=(b:ZMod p)⁻¹)
    (hbc : b.Coprime p) (j : ℕ) :
    (p:ℤ_[p])^j ∣ ((b:ℤ_[p])^(p^j)*w-1) := by
  have hp := Fact.out (p:=p.Prime)
  have hb : (b:ZMod p)≠0 := ((ZMod.isUnit_iff_coprime b p).mpr hbc).ne_zero
  have wp : w^p=w := by
    have e := (hw.pow_eq_one_iff_dvd _).mpr (ZMod.orderOf_dvd_card_sub_one hb)
    calc w^p = w^(p-1+1) := by rw [Nat.sub_add_cancel hp.one_le]
         _ = w := by rw [pow_succ,e,one_mul]
  have iter (j : ℕ) : w^(p^j)=w := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ,pow_mul,ih,wp]
  let I : Ideal ℤ_[p] := Ideal.span {(p:ℤ_[p])}
  have h : (b:ℤ_[p])*w ≡ 1 [SMOD I] := by
    dsimp only [I]; rw [SModEq.sub_mem, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,RingHom.mem_ker]
    simp [hred,hb]
  have H := h.pow_pow_add_one (show (p:ℤ_[p]) ∈ I from Ideal.subset_span (by simp)) j
  dsimp only [I] at H
  rw [SModEq.sub_mem,one_pow,mul_pow,iter,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at H
  exact (pow_dvd_pow _ (Nat.le_succ _)).trans H

theorem lift_eval_zero_iff {d : ℕ} (hd : 0<d) (w : ℤ_[p]) (hw : IsPrimitiveRoot w d) (P : ℚ[X]) :
    P.aeval (w:ℚ_[p])=0 ↔ cyclotomic d ℚ ∣ P := by
  have h : IsPrimitiveRoot (w:ℚ_[p]) d := hw.map_of_injective (f:=algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective
  have : NeZero (d:ℚ) := ⟨by exact_mod_cast hd.ne'⟩
  rw [h.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hd)]
  exact ⟨fun h => minpoly.dvd _ _ h,fun ⟨q,hq⟩ => by rw [hq,map_mul,minpoly.aeval,zero_mul]⟩

end NormalityChecker
