module

public import NormalityChecker.Linearization
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section
open Finset
namespace NormalityChecker

private lemma char_norm {m : ℕ} [NeZero m] (v : ZMod m) :
    ‖ZMod.stdAddChar v‖ = 1 := Circle.norm_coe _

private lemma char_nat {m : ℕ} [NeZero m] (v : ℕ) :
    ZMod.stdAddChar (v : ZMod m) = Complex.exp (2*Real.pi*Complex.I*v/m) := by
  simpa using ZMod.stdAddChar_coe (N:=m) (v:ℤ)

private lemma chord_lower {m v : ℕ} [NeZero m] (hv : 0<v) (hm : v<m) :
    4*min (v:ℝ) (m-v:ℝ)/(m:ℝ) ≤ ‖ZMod.stdAddChar (v : ZMod m) - 1‖ := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast hv.trans hm
  let x := Real.pi*(v:ℝ)/m
  have hx : 0≤x := by dsimp [x]; positivity
  have hπ : x ≤ Real.pi := by
    dsimp [x]; rw [div_le_iff₀ hm0]; gcongr
  have hv' : (v:ℝ) ≤ m := by exact_mod_cast hm.le
  have hexp : 2*(Real.pi:ℂ)*Complex.I*v/m = Complex.I*((2*x:ℝ):ℂ) := by
    dsimp [x]; push_cast; ring
  rw [char_nat, hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show 2*x/2=x by ring, abs_of_nonneg (by positivity [Real.sin_nonneg_of_nonneg_of_le_pi hx hπ])]
  by_cases hh : (v:ℝ) ≤ m-v
  · rw [min_eq_left hh]
    have hx' : x ≤ Real.pi/2 := by dsimp [x]; rw [div_le_iff₀ hm0]; nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh)]
    have h := Real.mul_le_sin hx hx'
    dsimp [x] at h
    field_simp [Real.pi_ne_zero] at h ⊢
    nlinarith [Real.pi_pos]
  · rw [min_eq_right (le_of_not_ge hh)]
    have hx' : Real.pi-x ≤ Real.pi/2 := by
      have hh' : m-v ≤ (v:ℝ) := le_of_not_ge hh
      dsimp [x]; field_simp; nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh')]
    have h := Real.mul_le_sin (sub_nonneg.mpr hπ) hx'
    rw [Real.sin_pi_sub] at h
    dsimp [x] at h
    field_simp [Real.pi_ne_zero] at h ⊢
    nlinarith [Real.pi_pos]

private lemma geometric_bound {m : ℕ} [NeZero m] (x : ZMod m) (hx : 0 < x.val) (T : ℕ) :
    ‖∑ t ∈ range T, (ZMod.stdAddChar x)^t‖ ≤
      (m:ℝ)/2*((x.val:ℝ)⁻¹+((m:ℝ)-x.val)⁻¹) := by
  let v := x.val
  have hv : v<m := x.val_lt
  have hv0 : (0:ℝ)<v := by exact_mod_cast hx
  have huv : (0:ℝ)<m-v := sub_pos.mpr (by exact_mod_cast hv)
  have hm : (0:ℝ)<m := by linarith
  let d := min (v:ℝ) (m-v:ℝ)
  have hd : 0<d := lt_min hv0 huv
  have H := chord_lower hx hv
  rw [ZMod.natCast_zmod_val] at H
  let S := ‖∑ t ∈ range T, (ZMod.stdAddChar x)^t‖
  have hS : S*(4*d/m) ≤ 2 := by
    apply (mul_le_mul_of_nonneg_left H (norm_nonneg _)).trans
    change ‖_‖*‖_‖ ≤ _
    rw [← norm_mul, geom_sum_mul]
    simpa [norm_pow, char_norm, one_add_one_eq_two] using norm_sub_le (ZMod.stdAddChar x ^ T) 1
  have hS' : S ≤ (m:ℝ)/2*d⁻¹ := by
    rw [← div_eq_mul_inv,le_div_iff₀ hd]
    have h := (div_le_iff₀ hm).mp (by simpa [mul_div_assoc] using hS : S*(4*d)/m ≤ 2)
    linarith
  apply hS'.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total (v:ℝ) (m-v:ℝ) with h | h
  · rw [show d=(v:ℝ) from min_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  · rw [show d=(m-v:ℝ) from min_eq_right h]; exact le_add_of_nonneg_left (by positivity)

private lemma harmonic_image_bound {P m : ℕ} (v : ℕ → ℕ)
    (hinj : Set.InjOn v (range P)) (hv : ∀ i < P, 0 < v i ∧ v i < m) :
    ∑ i ∈ range P, ((v i:ℝ)⁻¹) ≤ 1+Real.log m := by
  have H : ∑ i ∈ range P, ((v i:ℝ)⁻¹) ≤ ∑ j ∈ Icc 1 m, (j:ℝ)⁻¹ := by
    apply sum_le_sum_of_injOn (g:= fun j : ℕ => (j:ℝ)⁻¹) v hinj _ (fun _ _ => le_rfl) (fun _ _ _ => by positivity)
    intro j hj; obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact mem_Icc.mpr ⟨(hv i (mem_range.mp hi)).1,(hv i (mem_range.mp hi)).2.le⟩
  exact H.trans (by simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log m)

private lemma sum_rectangle {E : Type*} [AddCommMonoid E] (f : ℕ → E) (L T : ℕ) :
    ∑ n ∈ range (L*T), f n = ∑ u ∈ range L, ∑ t ∈ range T, f (u+L*t) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Nat.mul_succ, sum_range_add,ih]
    simp_rw [sum_range_succ]
    rw [sum_add_distrib]
    simp [add_comm]

/-- Uniform in the multiplier and length. The multiplier is a unit modulo three.
The modulus exponent is (s+1)+(d+1); the stride exponent is s+1. -/
theorem incomplete_orbit_bound (d s A N : ℕ) (hds : d ≤ s) (hA : ¬ 3 ∣ A) :
    let m : ℕ := 3^(d+1)
    let q := 3^((s+1)+(d+1))
    ‖∑ n ∈ range N, ZMod.stdAddChar ((A:ZMod q)*2^n)‖ ≤
      (2*3^s:ℕ) + (3^(s-d):ℕ)*(m:ℝ)*(1+Real.log m) := by
  let m := 3^(d+1)
  let q := 3^((s+1)+(d+1))
  let L := 2*3^s
  let P := 2*3^d
  let B := 3^(s-d)
  have : NeZero m := ⟨by dsimp [m]; positivity⟩
  have : NeZero q := ⟨by dsimp [q]; positivity⟩
  have hL : 0 < L := by dsimp [L]; positivity
  have hLP : P*B = L := by
    dsimp [P,B,L]; rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hds]
  obtain ⟨c,hc,hlin⟩ := stride_linearization s ((s+1)+(d+1)) (by omega)
  have hc3 : ¬ 3 ∣ c := by omega
  let F (n : ℕ) := ZMod.stdAddChar ((A:ZMod q)*2^n)
  let X (u : ℕ) : ZMod m := ((A*2^u*c:ℕ):ZMod m)
  have row (u t : ℕ) : F (u+L*t) = F u * (ZMod.stdAddChar (X u))^t := by
    have hz := (ZMod.natCast_eq_natCast_iff _ _ q).mpr (hlin t)
    push_cast at hz
    have hbase : ZMod.stdAddChar (((A*2^u*c)*3^(s+1):ℕ):ZMod q) = ZMod.stdAddChar (X u) := by
      dsimp only [X]; rw [char_nat, char_nat]
      congr 1
      dsimp [q,m]; push_cast; field_simp; ring
    dsimp only [F]; rw [pow_add, show (2:ZMod q)^(L*t)=_ from hz,
      show (A:ZMod q)*(2^u*(1+t*c*3^(s+1))) =
        (A:ZMod q)*2^u + t • (((A*2^u*c)*3^(s+1):ℕ):ZMod q) by push_cast; rw [nsmul_eq_mul]; ring,
      AddChar.map_add_eq_mul,AddChar.map_nsmul_eq_pow,hbase]
  have groupBound (w T : ℕ) :
      ∑ i ∈ range P, ‖∑ t ∈ range T, F ((w+i)+L*t)‖ ≤ (m:ℝ)*(1+Real.log m) := by
    let v (i : ℕ) := (X (w+i)).val
    have hunit (n : ℕ) : IsUnit (X n) := by
      apply (ZMod.isUnit_iff_coprime _ _).mpr
      apply Nat.Coprime.pow_right
      apply Nat.Coprime.symm
      apply Nat.prime_three.coprime_iff_not_dvd.mpr
      simp only [Nat.prime_three.dvd_mul]
      exact fun h => h.elim (fun h => h.elim hA (fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h))) hc3
    have hv (i : ℕ) : 0<v i ∧ v i<m := by
      refine ⟨Nat.pos_of_ne_zero ?_, (X _).val_lt⟩
      intro h
      have hn : Nontrivial (ZMod m) := by
        have : Fact (1<m) := ⟨by dsimp [m]; exact one_lt_pow₀ (by decide) (by omega)⟩
        infer_instance
      exact (hunit (w+i)).ne_zero ((ZMod.val_injective m) (by simpa [v] using h))
    have hi : Set.InjOn v (range P) := by
      intro i hi j hj he
      have e := (ZMod.val_injective m) he
      have e' (i : ℕ) : X (w+i) = X w * (2:ZMod m)^i := by dsimp [X]; push_cast; rw [pow_add]; ring
      rw [e' i,e' j] at e
      apply pow_injOn_Iio_orderOf (x:=(2:ZMod m)) _ _ ((hunit w).mul_left_cancel e)
      · simpa [m,orderOf_two_three_pow,P] using mem_range.mp hi
      · simpa [m,orderOf_two_three_pow,P] using mem_range.mp hj
    have hi' : Set.InjOn (fun i => m-v i) (range P) := by
      intro i hi₁ j hj₁ he; apply hi hi₁ hj₁
      have := hv i; have := hv j; dsimp at he; omega
    have H₁ := harmonic_image_bound v hi (fun i _ => hv i)
    have H₂ := harmonic_image_bound (m:=m) (fun i => m-v i) hi' (fun i _ => by have := hv i; omega)
    calc
      _ ≤ ∑ i ∈ range P, (m:ℝ)/2*((v i:ℝ)⁻¹+((m-v i:ℕ):ℝ)⁻¹) := by
        apply sum_le_sum; intro i _
        simp_rw [row, ← mul_sum, norm_mul, show ‖F (w+i)‖ = 1 from char_norm _, one_mul]
        rw [Nat.cast_sub (hv i).2.le]
        exact geometric_bound (X (w+i)) (hv i).1 T
      _ = (m:ℝ)/2*((∑ i ∈ range P, (v i:ℝ)⁻¹)+ ∑ i ∈ range P, ((m-v i:ℕ):ℝ)⁻¹) := by
        rw [← sum_add_distrib,mul_sum]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (add_le_add H₁ H₂) (Nat.cast_nonneg (α:=ℝ) m)]
  let T := N/L
  let R := N%L
  have hN : L*T+R = N := Nat.div_add_mod _ _
  change ‖∑ n ∈ range N, F n‖ ≤ (L:ℝ)+(B:ℝ)*m*(1+Real.log m)
  rw [← hN,sum_range_add]
  apply (norm_add_le _ _).trans
  have H : ‖∑ n ∈ range (L*T), F n‖ ≤ (B:ℝ)*m*(1+Real.log m) := by
    rw [sum_rectangle]
    apply (norm_sum_le _ _).trans
    rw [← hLP, sum_rectangle, sum_comm]
    calc
      _ ≤ ∑ _b ∈ range B, (m:ℝ)*(1+Real.log m) := by
        apply sum_le_sum; intro b _
        simpa only [hLP,add_comm] using groupBound (P*b) T
      _ = _ := by simp; ring
  have HR : ‖∑ n ∈ range R, F (L*T+n)‖ ≤ (L:ℝ) := by
    apply (norm_sum_le _ _).trans
    simp only [F,char_norm,sum_const,card_range,nsmul_eq_mul,mul_one]
    exact_mod_cast (Nat.mod_lt N hL).le
  linarith

/-- The square-root/logarithm estimate for every starting exponent and every length. -/
theorem incomplete_orbit_interval {k : ℕ} (hk : 2 ≤ k) (A u N : ℕ) (hA : ¬ 3 ∣ A) :
    ‖∑ n ∈ range N, ZMod.stdAddChar ((A:ZMod (3^k))*2^(u+n))‖ ≤
      5*Real.sqrt ((3:ℝ)^k)*(1+Real.log ((3:ℝ)^k)) := by
  let d := k/2-1
  let s := (k+1)/2-1
  let m : ℕ := 3^(d+1)
  have hds : d ≤ s := by dsimp [d,s]; omega
  have hsd : s ≤ d+1 := by dsimp [d,s]; omega
  have he : s+1+(d+1)=k := by dsimp [d,s]; omega
  have hu : ¬ 3 ∣ A*2^u := fun h => (Nat.prime_three.dvd_mul.mp h).elim hA
    (fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h))
  have H := incomplete_orbit_bound d s (A*2^u) N hds hu
  dsimp only at H
  rw [he] at H
  have Hz : (∑ n ∈ range N, ZMod.stdAddChar ((A:ZMod (3^k))*2^(u+n))) =
      ∑ n ∈ range N, ZMod.stdAddChar (((A*2^u:ℕ):ZMod (3^k))*2^n) := by
    apply sum_congr rfl; intro n _
    push_cast; rw [pow_add,mul_assoc]
  rw [Hz]
  apply H.trans
  have hB : (3:ℕ)^(s-d) ≤ 3 := by simpa using Nat.pow_le_pow_right (n:=3) (by decide) (show s-d ≤ 1 by omega)
  have hL : 3^s ≤ m := Nat.pow_le_pow_right (by decide) hsd
  have hsq : (m:ℝ) ≤ Real.sqrt ((3:ℝ)^k) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    dsimp [m]; push_cast; rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (show (d+1)*2 ≤ k by omega)
  have hlog : Real.log m ≤ Real.log ((3:ℝ)^k) := by
    apply Real.log_le_log (by dsimp [m]; positivity)
    dsimp [m]; push_cast; exact pow_le_pow_right₀ (by norm_num) (show d+1 ≤ k by omega)
  have hl0 : 0 ≤ Real.log ((3:ℝ)^k) := Real.log_nonneg (one_le_pow₀ (by norm_num))
  have hm0 : 0 ≤ Real.log m := Real.log_nonneg (by dsimp [m]; push_cast; exact one_le_pow₀ (by norm_num))
  have b' : ((3^(s-d):ℕ):ℝ) ≤ 3 := by exact_mod_cast hB
  have l' : ((2*3^s:ℕ):ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hL
  change ((2*3^s:ℕ):ℝ) + ((3^(s-d):ℕ):ℝ)*(m:ℝ)*(1+Real.log m) ≤ _
  have H' : ((3^(s-d):ℕ):ℝ)*(m:ℝ)*(1+Real.log m) ≤ 3*Real.sqrt ((3:ℝ)^k)*(1+Real.log ((3:ℝ)^k)) := by gcongr
  nlinarith [mul_nonneg (Real.sqrt_nonneg ((3:ℝ)^k)) hl0]

end NormalityChecker
