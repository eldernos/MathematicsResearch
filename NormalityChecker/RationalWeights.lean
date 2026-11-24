module

public import NormalityChecker.PolynomialLayers
public import Mathlib.RingTheory.Localization.Integral

/-! Proper rational weights with a monomial denominator on mixed or single-axis supports. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker

/-- A nonzero signed integer multiplier preserves and reflects normality. -/
theorem normal_mul_int_iff {b : ℕ} (hb : 2≤b) {D : ℤ} (hD : D≠0) (x : ℝ) :
    NormalIn b ((D:ℝ)*x) ↔ NormalIn b x := by
  have forwards (y : ℝ) (H : NormalIn b y) : NormalIn b ((D:ℝ)*y) := by
    apply normal_of_fourier hb; intro h hh
    simpa only [Int.cast_mul,mul_left_comm,mul_comm,mul_assoc] using fourier_of_normal H (h*D) (mul_ne_zero hh hD)
  refine ⟨fun H => ?_,forwards x⟩
  apply (normal_mul_nat_iff hb (pow_pos (Int.natAbs_pos.mpr hD) 2) x).mp
  have eqn : ((D.natAbs^2:ℕ):ℝ)*x=(D:ℝ)*(D*x) := by rw [Nat.cast_pow,← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,sq_abs]; ring
  rw [eqn]; exact forwards _ H

namespace Localized.Composite.Generators
variable (d : Generators)

noncomputable def rationalValue (keep : ℕ × ℕ → Bool) (P : ℚ[X]) (s : ℕ) :=
  ∑' v : ℕ × ℕ, if keep v then ((P.eval (d.idx v:ℚ):ℚ):ℝ) / (d.idx v:ℝ)^s / (d.b:ℝ)^d.idx v else 0

/-- Clear a fixed rational denominator and cancel the common power of `X`
before testing large layers. Both operations work with any fixed mask. -/
private theorem lift_reduced (keep : ℕ × ℕ → Bool)
    (reduced : ∀ G : ℤ[X], sample G 0≠0 → ∀ r : ℕ, G.natDegree<r → NormalIn d.b (d.weightedValue keep G r))
    (P : ℚ[X]) (hp : P≠0) {s : ℕ} (deg : P.natDegree<s) : NormalIn d.b (d.rationalValue keep P s) := by
  let t := P.rootMultiplicity 0
  obtain ⟨F,fac,unit⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  change P=(_)^t*F at fac
  simp only [map_zero,sub_zero] at fac unit
  have f0 : F.eval 0≠0 := by simpa [X_dvd_iff,coeff_zero_eq_eval_zero] using unit
  have fn : F≠0 := fun h => f0 (by simp [h])
  have sumdeg : P.natDegree=t+F.natDegree := by rw [fac,natDegree_mul (pow_ne_zero _ X_ne_zero) fn,natDegree_X_pow]
  let G := IsLocalization.integerNormalization (nonZeroDivisors ℤ) F
  obtain ⟨D,hD,mapG⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) F
  change G.map _=D • F at mapG
  have dn : D≠0 := nonZeroDivisors.ne_zero hD
  have eval (m : ℕ) : (sample G m:ℚ) = D*F.eval (m:ℚ) := by
    have h := congrArg (Polynomial.eval (m:ℚ)) mapG
    rw [eval_smul, zsmul_eq_mul] at h
    convert h using 1
    exact (eval_map_apply (p:=G) (algebraMap ℤ ℚ) (m:ℤ)).symm
  have g0 : sample G 0≠0 := by
    have h := eval 0; simp only [Nat.cast_zero] at h
    intro hz; rw [hz,Int.cast_zero] at h
    exact (mul_ne_zero (by exact_mod_cast dn : (D:ℚ)≠0) f0) h.symm
  have gd : G.natDegree≤F.natDegree := by
    rw [← natDegree_map_eq_of_injective (Int.cast_injective (α:=ℚ)) (p:=G) (f:=algebraMap ℤ ℚ),mapG]; exact natDegree_smul_le ..
  have normal := reduced G g0 (s-t) (by omega)
  apply (normal_mul_int_iff d.hb dn _).mp
  convert normal using 2
  unfold rationalValue weightedValue
  rw [← tsum_mul_left]; apply tsum_congr; intro v
  by_cases h : keep v
  · simp only [h,ite_true,numerator]
    have he := congrArg (fun y : ℚ => (y:ℝ)) (eval (d.idx v))
    push_cast at he
    rw [he,fac,eval_mul,eval_pow,eval_X]; push_cast
    conv_lhs => rw [show s=t+(s-t) by omega,pow_add]
    field_simp [(d.positive v).ne']
  · simp [numerator,h]

/-- All nonzero proper rational weights `P(m)/m^s` on `m=q^a c^j`, including
finite signed rational combinations of localized polylogarithmic orders. -/
theorem mixed_rational_normal (P : ℚ[X]) (hp : P≠0) {s : ℕ} (deg : P.natDegree<s) :
    NormalIn d.b (∑' v : ℕ × ℕ, ((P.eval (d.idx v:ℚ):ℚ):ℝ) / (d.idx v:ℝ)^s / (d.b:ℝ)^d.idx v) := by
  simpa only [rationalValue,ite_true] using d.lift_reduced (fun _ => true) (fun G h _ deg => d.mixed_normal_reduced G h deg) P hp deg

/-- Infinite restrictions of the geometric axis preserve normality. No bound on
successive gaps of the selected exponents is required. -/
theorem restricted_axis_normal (mask : ℕ → Bool) (unbounded : ∀ J : ℕ, ∃ j≥J, mask j=true)
    (P : ℚ[X]) (hp : P≠0) {s : ℕ} (deg : P.natDegree<s) :
    NormalIn d.b (∑' j : ℕ, if mask j then ((P.eval ((d.c:ℚ)^j):ℚ):ℝ) / ((d.c:ℝ)^j)^s / (d.b:ℝ)^(d.c^j) else 0) := by
  have H := d.lift_reduced (fun v => (v.1==0) && mask v.2) (fun G h _ deg => d.axis_normal_reduced mask unbounded G h deg) P hp deg
  convert H using 2
  let f (v : ℕ × ℕ) := if (v.1==0) && mask v.2 then ((P.eval (d.idx v:ℚ):ℚ):ℝ) / (d.idx v:ℝ)^s / (d.b:ℝ)^d.idx v else 0
  have inj : Function.Injective (fun j : ℕ => (0,j) : ℕ → ℕ × ℕ) := fun _ _ h => congrArg Prod.snd h
  have cover : Function.support f ⊆ Set.range (fun j : ℕ => ((0:ℕ),j)) := by
    intro v hv
    by_cases h0 : v.1=0
    · exact ⟨v.2, Prod.ext h0.symm rfl⟩
    · exact False.elim (hv (by simp [f,h0]))
  have eqn := inj.tsum_eq cover
  simpa [rationalValue,f,idx,index] using eqn

/-- A single geometric support, used for the boundary terms of dense sums. -/
theorem axis_rational_normal (P : ℚ[X]) (hp : P≠0) {s : ℕ} (deg : P.natDegree<s) :
    NormalIn d.b (∑' j : ℕ, ((P.eval ((d.c:ℚ)^j):ℚ):ℝ) / ((d.c:ℝ)^j)^s / (d.b:ℝ)^(d.c^j)) := by
  simpa using d.restricted_axis_normal (fun _ => true) (fun J => ⟨J,le_rfl,rfl⟩) P hp deg

end Localized.Composite.Generators
end NormalityChecker
