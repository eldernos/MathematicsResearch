module

public import NormalityChecker.MaskGrid

/-! Extreme discrepancy under integer dilation of a radix orbit. -/
@[expose] public section
open Finset
namespace NormalityChecker.AlternateBase

/-- Each interval in the dilated orbit lifts to D disjoint intervals. -/
theorem discrepancy_dilation {D : ℕ} (pos : 0<D) (B : ℕ) (x : ℝ) (N : ℕ) :
    radixDiscrepancy B (D*x) N ≤ D*radixDiscrepancy B x N := by
  classical
  change sSup {v | ∃ a t : ℝ, 0≤a ∧ a<t ∧ t≤1 ∧ v=|frequency (shift B (D*x)) a t N-(t-a)|} ≤ _
  refine csSup_le ?_ ?_
  · exact ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩
  rintro _ ⟨a,t,ha,at',ht,rfl⟩
  let l (i : ℕ) := ((i:ℝ)+a)/D
  let h (i : ℕ) := ((i:ℝ)+t)/D
  have dp : (0:ℝ)<D := by exact_mod_cast pos
  have point (n : ℕ) :
      (if a≤shift B (D*x) n ∧ shift B (D*x) n<t then (1:ℝ) else 0) =
        ∑ i ∈ range D, if l i ≤ shift B x n ∧ shift B x n < h i then 1 else 0 := by
    let y := (B:ℝ)^n*x
    let s := Int.fract y
    let j := ⌊(D:ℝ)*s⌋₊
    have sp : 0≤s := Int.fract_nonneg _
    have dm : 0≤(D:ℝ)*s := mul_nonneg dp.le sp
    have exactShift : shift B (D*x) n = Int.fract ((D:ℝ)*s) := by
      change Int.fract ((B:ℝ)^n*(D*x)) = _
      have e : (B:ℝ)^n*(D*x) = D*s + ((D:ℤ)*⌊y⌋:ℤ) := by
        change _ = D*(y-(⌊y⌋:ℝ))+((D:ℤ)*⌊y⌋:ℤ)
        rw [Int.cast_mul,Int.cast_natCast]; dsimp only [y]; ring
      rw [e,Int.fract_add_intCast]
    have jmem : j∈range D := mem_range.mpr (Nat.floor_lt dm |>.mpr (by
      simpa only [mul_one] using mul_lt_mul_of_pos_left (Int.fract_lt_one y) dp))
    have rem : Int.fract ((D:ℝ)*s)=(D:ℝ)*s-j := by
      change _ = _ - (⌊(D:ℝ)*s⌋₊:ℝ)
      rw [natCast_floor_eq_intCast_floor dm]; rfl
    have fiber (i : ℕ) : l i≤s ∧ s<h i ↔
        i=j ∧ a≤Int.fract ((D:ℝ)*s) ∧ Int.fract ((D:ℝ)*s)<t := by
      simp only [l,h,div_le_iff₀ dp,lt_div_iff₀ dp,rem]
      constructor
      · rintro ⟨lo,up⟩
        have eqn : ⌊(D:ℝ)*s⌋₊=i := (Nat.floor_eq_iff dm).mpr ⟨by linarith,by linarith⟩
        change j=i at eqn
        exact ⟨eqn.symm,by rw [eqn]; linarith,by rw [eqn]; linarith⟩
      · rintro ⟨rfl,lo,up⟩
        constructor <;> linarith
    rw [exactShift]
    change _ = ∑ i ∈ range D, if l i≤s ∧ s<h i then (1:ℝ) else 0
    simp_rw [fiber]
    rw [sum_eq_single_of_mem j jmem (fun i _ neq => by simp [neq])]
    simp
  have sumfreq : frequency (shift B (D*x)) a t N =
      ∑ i ∈ range D, frequency (shift B x) (l i) (h i) N := by
    simp only [frequency,← sum_div]
    congr 1
    have e := sum_congr (s₁:=range N) rfl (fun n _ => point n)
    rw [sum_comm (s:=range N) (t:=range D)] at e
    simpa only [sum_boole] using e
  have widths : (∑ i ∈ range D, (h i-l i)) = t-a := by
    simp only [l,h,← sub_div,add_sub_add_left_eq_sub,sum_const,card_range,nsmul_eq_mul]
    field_simp
  rw [sumfreq,← widths,← sum_sub_distrib]
  calc _ ≤ ∑ i ∈ range D, |frequency (shift B x) (l i) (h i) N-(h i-l i)| := by
            simpa [Real.norm_eq_abs] using norm_sum_le (range D)
              (fun i => frequency (shift B x) (l i) (h i) N-(h i-l i))
       _ ≤ ∑ _ ∈ range D, radixDiscrepancy B x N := by
            apply sum_le_sum; intro i hi
            have bound : (i:ℝ)+1≤D := by exact_mod_cast mem_range.mp hi
            exact PolynomialMasks.interval_le_radix x (by dsimp [l]; positivity)
              ((div_lt_div_iff_of_pos_right dp).mpr (by linarith))
              ((div_le_one dp).mpr (by linarith))
       _ = _ := by simp

end NormalityChecker.AlternateBase
