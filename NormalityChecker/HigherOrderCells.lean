module

public import NormalityChecker.HigherOrderPrincipal
public import NormalityChecker.PersistentRegion
public import Mathlib.LinearAlgebra.SModEq.Pow

/-! Reduction of the infinite local moments to the checker's finite residues. -/
@[expose] public section
noncomputable section
open Finset
namespace NormalityChecker.LocalizedSupport
variable {p : ℕ} [hp : Fact p.Prime]

private lemma reduce_principal (z : ℤ_[p]) (l : ℕ) :
    PadicInt.toZModPow (l+1) ((1+(p:ℤ_[p])*z)^(p^l)) = 1 := by
  let I : Ideal ℤ_[p] := Ideal.span {(p:ℤ_[p])}
  have congr : (1 + p*z : ℤ_[p]) ≡ 1 [SMOD I] := by
    rw [SModEq.sub_mem]
    apply Ideal.mem_span_singleton.mpr
    use z
    ring
  have raised := congr.pow_pow_add_one (Ideal.subset_span (by simp : (p:ℤ_[p]) ∈ ({(p:ℤ_[p])}:Set ℤ_[p]))) l
  rw [SModEq.sub_mem,one_pow,Ideal.span_singleton_pow] at raised
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker,map_sub,map_one,sub_eq_zero] at raised
  exact raised

/-- Every inverse-radix Teichmüller factor reduces to the checker's canonical lift. -/
theorem reduce_inverse_radix {b : ℕ} {w z : ℤ_[p]} (fixed : w^p = w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p])*(1+(p:ℚ_[p])*z)) (cop : b.Coprime p) (l : ℕ) :
    PadicInt.toZModPow (l+1) w = inverseLift b p l l := by
  let φ := PadicInt.toZModPow (p:=p) (l+1)
  have bn : b ≠ 0 := by rintro rfl; simp [hp.out.ne_one] at cop
  have mul : (b:ℤ_[p])*(w*(1+p*z)) = 1 := by
    apply Subtype.ext
    change (b:ℚ_[p])*((w:ℚ_[p])*(1+(p:ℚ_[p])*z)) = 1
    rw [← factor,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr bn)]
  have modEq := congrArg φ mul
  simp only [map_mul,map_natCast,map_one] at modEq
  have bu := (ZMod.isUnit_iff_coprime b (p^(l+1))).mpr (cop.pow_right _)
  have inv : (b:ZMod (p^(l+1)))⁻¹ = φ w * φ (1+p*z) := by
    apply bu.mul_right_inj.mp
    rw [ZMod.mul_inv_of_unit _ bu, modEq]
  change φ w = ((b:ZMod (p^(l+1)))⁻¹)^(p^l)
  rw [inv,mul_pow,← map_pow,← map_pow, fixed_frobenius w fixed,
    show φ ((1+(p:ℤ_[p])*z)^(p^l)) = 1 from reduce_principal z l,mul_one]

/-- The exact finite-checker residue is the reduction of the infinite moment
at every real phase, including thresholds belonging to the right-hand cell. -/
theorem phaseMoment_reduction {S : Finset ℕ} (outside : p ∉ S) (w : ℤ_[p])
    {d : ℕ} (hd : 0 < d) (t : ℝ) (l : ℕ) :
    PadicInt.toZModPow (l+1) (phaseMoment S w d t) =
      powerCellResidue d p l S (PadicInt.toZModPow (l+1) w) ⌊t*(p:ℝ)^l⌋₊ := by
  let φ := PadicInt.toZModPow (p:=p) (l+1)
  have zero : (p:ZMod (p^(l+1)))^(l+1) = 0 := by exact_mod_cast ZMod.natCast_self (p^(l+1))
  have vanish : ((p:ZMod (p^(l+1)))^d)^(l+1) = 0 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, zero, zero_pow hd.ne']
  obtain ⟨e,eqn⟩ := phaseMoment_tail S w hd t (l+1)
  rw [eqn, map_add,map_mul,map_pow,map_pow,map_natCast,vanish,zero_mul,add_zero,map_sum]
  unfold powerCellResidue
  apply sum_congr rfl
  intro i hi
  have il : i ≤ l := by simpa using mem_range.mp hi
  have ex : i + (l-i) = l := by omega
  have coord : ⌊t*(p:ℝ)^i⌋₊ = ⌊t*(p:ℝ)^l⌋₊ / p^(l-i) := by
    rw [← Nat.floor_div_natCast, Nat.cast_pow, ← ex, Nat.add_sub_cancel_left, pow_add]
    congr 1; field_simp [hp.out.ne_zero]
  rw [map_mul,momentRow,map_sum,mul_sum,coord]
  apply sum_congr rfl
  intro r hr
  have hrp := hp.out.factoredNumbers_coprime outside (mem_indices.mp hr).2
  have unit := (ZMod.isUnit_iff_coprime r (p^(l+1))).mpr (hrp.symm.pow_right _)
  have inv : φ (r:ℤ_[p]).inv = (r:ZMod (p^(l+1)))⁻¹ := by
    apply unit.mul_right_inj.mp
    rw [ZMod.mul_inv_of_unit _ unit, ← map_natCast φ r, ← map_mul,
      PadicInt.mul_inv (PadicInt.norm_natCast_eq_one_iff.mpr hrp),map_one]
  simp only [map_pow,map_natCast,map_mul]
  change _ * (φ w^r * φ (r:ℤ_[p]).inv^d) = _
  rw [inv,mul_pow, ← pow_mul, Nat.mul_comm d i,pow_mul]
  ring

/-- A failed level is equivalently a zero reduction of the moment. -/
theorem failedRegion_iff_phaseReduction_zero {b d : ℕ} {S : Finset ℕ} (outside : p ∉ S)
    (hd : 0 < d) {w z : ℤ_[p]} (fixed : w^p = w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p])*(1+(p:ℚ_[p])*z)) (cop : b.Coprime p)
    {t : ℝ} (ht : t ∈ Set.Ico 1 (p:ℝ)) (l : ℕ) :
    t ∈ failedRegion b d p l S ↔ PadicInt.toZModPow (l+1) (phaseMoment S w d t) = 0 := by
  let q := p^l
  have qpos : (0:ℝ) < q := by exact_mod_cast pow_pos hp.out.pos l
  have qeq : (q:ℝ) = (p:ℝ)^l := Nat.cast_pow p l
  let u := ⌊t*(q:ℝ)⌋₊
  have nonneg : 0 ≤ t*q := mul_nonneg (le_trans zero_le_one ht.1) qpos.le
  have inside : u ∈ Ico q (p*q) := by
    apply mem_Ico.mpr
    constructor
    · apply Nat.le_floor
      nlinarith only [mul_le_mul_of_nonneg_right ht.1 qpos.le]
    · apply (Nat.floor_lt nonneg).mpr
      push_cast
      exact mul_lt_mul_of_pos_right ht.2 qpos
  rw [phaseMoment_reduction outside w hd, reduce_inverse_radix fixed factor cop, ← qeq]
  constructor
  · intro mem
    obtain ⟨v,hv,lo,hi⟩ := Set.mem_iUnion₂.mp mem
    have lv := (div_le_iff₀ qpos).mp lo
    have hv' := (lt_div_iff₀ qpos).mp hi
    have eqn : u = v := Nat.floor_eq_iff nonneg |>.mpr ⟨lv,hv'⟩
    change powerCellResidue d p l S _ u = 0
    rw [eqn]
    exact (mem_filter.mp hv).2
  · intro zero
    apply Set.mem_iUnion₂.mpr
    refine ⟨u,mem_filter.mpr ⟨inside,zero⟩,?_,?_⟩
    · exact (div_le_iff₀ qpos).mpr (Nat.floor_le nonneg)
    · exact (lt_div_iff₀ qpos).mpr (Nat.lt_floor_add_one _)

/-- On the phase interval, simultaneous failure through every precision is exactly
the zero condition on the infinite moment. -/
theorem persistent_iff_phaseMoment_zero {b d : ℕ} {S : Finset ℕ} (outside : p ∉ S)
    (hd : 0 < d) {w z : ℤ_[p]} (fixed : w^p = w)
    (factor : (b:ℚ_[p])⁻¹ = (w:ℚ_[p])*(1+(p:ℚ_[p])*z)) (cop : b.Coprime p)
    {t : ℝ} (ht : t ∈ Set.Ico 1 (p:ℝ)) :
    t ∈ persistentRegion b d p S ↔ phaseMoment S w d t = 0 := by
  have each := failedRegion_iff_phaseReduction_zero outside hd fixed factor cop ht
  simp only [persistentRegion,Set.mem_iInter,each]
  constructor
  · intro h
    apply PadicInt.ext_of_toZModPow.mp
    intro l
    cases l with
    | zero =>
      have : Subsingleton (ZMod (p^0)) := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim ..
    | succ l => simpa using h l
  · intro h l; simp [h]

end NormalityChecker.LocalizedSupport
