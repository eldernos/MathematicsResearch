module

public import NormalityChecker.CyclotomicCell
public import NormalityChecker.CellLimits

@[expose] public section
open Finset Filter Classical
open scoped Topology
namespace NormalityChecker.CyclotomicCell

variable {b p : ℕ} [Fact p.Prime]

/-- The normalized sum of the modeled characters, after subtracting its cell
limit. A nonzero p-adic coefficient contributes a fixed power of p to h. -/
private lemma orbit (hb : 1<b) (ho : Odd p) (hbc : b.Coprime p) (v : ℤ_[p])
    (u E : ℕ) (h : ℤ) (hh : h≠0) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∃ A : ℤ,
    (A:ZMod (p^(k+E))) = PadicInt.toZModPow (k+E) ((b:ℤ_[p])^(u*p^k)*v) ∧
    ∀ T≤p^k, ‖∑ i ∈ range T, (phase ((h:ℝ)*A*(b:ℝ)^i/(p:ℝ)^(k+E)) -
      (if v=0 then 1 else 0))‖ ≤ ε*(p:ℝ)^k := by
  classical
  have hp := Fact.out (p:=p.Prime)
  by_cases hv : v=0
  · subst v; exact .of_forall fun k => ⟨0,by simp,by simp [phase, mul_nonneg hε.le (pow_nonneg (Nat.cast_nonneg _) _)]⟩
  let V := v.valuation
  have h' : h*(p:ℤ)^V ≠ 0 := mul_ne_zero hh (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  let U := PadicInt.unitCoeff hv
  have bunit : IsUnit (b:ℤ_[p]) := PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
    hbc.symm)
  have H := (tendsto_add_atTop_nat E).eventually (stoneham_orbit_small hb hp.one_lt ho hbc _ h'
    (ε/(p:ℝ)^E) (by positivity [hp.pos]))
  filter_upwards [H,eventually_gt_atTop 0] with k H hk
  let t := k+E
  let π := PadicInt.toZModPow (p:=p) t
  let z := π ((b:ℤ_[p])^(u*p^k)*(U:ℤ_[p]))
  have hz : z.val.Coprime p := by
    apply Nat.Coprime.of_dvd_right (dvd_pow_self p (by dsimp [t]; omega : t≠0))
    apply (ZMod.isUnit_iff_coprime ..).mp
    rw [ZMod.natCast_zmod_val]; exact (((bunit.pow _).mul U.isUnit).map π)
  refine ⟨(z.val:ℤ)*(p:ℤ)^V,?_,fun T hT => ?_⟩
  · change _ = π (_ * v)
    conv_rhs => rw [PadicInt.unitCoeff_spec hv,← mul_assoc,map_mul,map_pow,map_natCast]
    push_cast; rw [ZMod.natCast_zmod_val]
  · have hT' : T≤p^(k+E) := hT.trans (Nat.pow_le_pow_right hp.pos (by omega))
    have sum := H z.val hz T hT'
    simp only [hv,ite_false,sub_zero, Int.cast_mul,Int.cast_pow,Int.cast_natCast] at sum ⊢
    convert sum using 1
    · congr 2; funext i; congr 1; ring
    · rw [pow_add]; field_simp [hp.ne_zero]

/-- Each nonzero frequency has cell mean zero off resonance and one on
resonance, uniformly over partial cells after scaling by p-1. -/
theorem character (hb : 1<b) (ho : Odd p) (hbc : b.Coprime p) (w : ℤ_[p])
    (hw : ∀ j : ℕ, (p:ℤ_[p])^j ∣ (b:ℤ_[p])^(p^j)*w-1)
    (M : Finset ℕ) (c : ℕ → ℤ) (j : ℕ → ℕ) {u E : ℕ}
    (hm : ∀ m ∈ M, 0<m) (hl : ∀ m ∈ M, m*p^(j m)≤u)
    (hu : ∀ m ∈ M, u+1≤m*p^(j m+1)) (hE : ∀ m ∈ M, j m≤E)
    (h : ℤ) (hh : h≠0) :
    RadixCellCancellation p (fun n => phase (h*((b:ℝ)^n * scaled b p M c)) -
      (if value M c j E w=0 then 1 else 0)) u := by
  classical
  let v := -value M c j E w
  let B := ∑ m ∈ M, |(c m:ℝ)|
  let L : ℂ := if v=0 then 1 else 0
  intro ε hε
  have hp := Fact.out (p:=p.Prime)
  have err : Tendsto (fun k : ℕ => 2*Real.pi*|(h:ℝ)| *B/(p:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=2*Real.pi*|(h:ℝ)| *B)).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp.one_lt : (1:ℝ)<p)))
  filter_upwards [orbit hb ho hbc v u E h hh (ε/2) (half_pos hε),
    err.eventually_lt_const (half_pos hε)] with k H hsmall T hT
  obtain ⟨A,hA,hbound⟩ := H
  let f (i : ℕ) := phase (h*((b:ℝ)^(u*p^k+i)*scaled b p M c))
  let g (i : ℕ) := phase ((h:ℝ)*A*(b:ℝ)^i/(p:ℝ)^(k+E))
  have point (i : ℕ) (hi : i∈range T) : ‖(f i-L)-(g i-L)‖ ≤ ε/2 := by
    obtain ⟨z,hz⟩ := model hb w hw M c j hm hl hu hE k i ((mem_range.mp hi).trans_le hT) A
      (by simpa [v] using hA)
    rw [sub_sub_sub_cancel_right]
    have hzphase : phase ((h*z:ℤ):ℝ)=1 := by simpa [phase,mul_comm] using Complex.exp_int_mul_two_pi_mul_I (h*z)
    change ‖phase _-phase _‖ ≤ _
    rw [← mul_one (phase ((h:ℝ)*A*(b:ℝ)^i/(p:ℝ)^(k+E))), ← hzphase, ← phase_add]
    apply (phase_sub_le _ _).trans
    rw [show (h:ℝ)*((b:ℝ)^(u*p^k+i)*scaled b p M c) - (h*A*(b:ℝ)^i/(p:ℝ)^(k+E)+((h*z:ℤ):ℝ)) =
      h*((b:ℝ)^(u*p^k+i)*scaled b p M c-A*(b:ℝ)^i/(p:ℝ)^(k+E)-z) by push_cast; ring, abs_mul, ← mul_assoc]
    apply (mul_le_mul_of_nonneg_left hz (by positivity)).trans
    simpa [B,mul_div_assoc] using hsmall.le
  have diff : ‖(∑ i ∈ range T, (f i-L)) - ∑ i ∈ range T, (g i-L)‖ ≤ (ε/2)*(p:ℝ)^k := by
    rw [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans ((sum_le_sum point).trans ?_)
    simp only [sum_const,card_range,nsmul_eq_mul]; rw [mul_comm]; gcongr; exact_mod_cast hT
  have tri := norm_add_le ((∑ i ∈ range T, (f i-L)) - ∑ i ∈ range T, (g i-L)) (∑ i ∈ range T, (g i-L))
  rw [sub_add_cancel] at tri
  have hg : ‖∑ i ∈ range T, (g i-L)‖ ≤ ε/2*(p:ℝ)^k := hbound T hT
  have : ‖∑ i ∈ range T, (f i-L)‖ ≤ ε*(p:ℝ)^k := by linarith
  simpa only [f,L,v,neg_eq_zero] using this

end NormalityChecker.CyclotomicCell
