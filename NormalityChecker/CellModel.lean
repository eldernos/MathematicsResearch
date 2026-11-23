module

public import NormalityChecker.Insertion
public import NormalityChecker.ScaleTransfer
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section
open Finset Filter
open scoped Topology ComplexConjugate
namespace NormalityChecker

private lemma orbit_relative_error :
    Tendsto (fun q : ℝ => 5*((1+Real.log q)/Real.sqrt q)) atTop (𝓝 0) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  simp only [← Real.sqrt_eq_rpow] at hlog
  have hi : Tendsto (fun q : ℝ => 1/Real.sqrt q) atTop (𝓝 0) := by
    simpa [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  simpa [add_div] using (tendsto_const_nhds (x:=(5:ℝ))).mul (hi.add hlog)

private lemma model_nat {A : ℕ} (hA : A≠0) (E : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ u T : ℕ,
      ‖∑ i ∈ range T, phase ((A:ℝ)*2^(u+i)/(3:ℝ)^(k+E))‖ ≤ ε*(3:ℝ)^k := by
  let v := A.factorization 3
  let B := A/3^v
  have hB : ¬ 3 ∣ B := Nat.not_dvd_ordCompl Nat.prime_three hA
  have he : 3^v*B=A := Nat.ordProj_mul_ordCompl_eq_self A 3
  have hpow : Tendsto (fun k : ℕ => (3:ℝ)^(k+E-v)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp
      ((tendsto_sub_atTop_nat v).comp (tendsto_add_atTop_nat E))
  have small := (orbit_relative_error.comp hpow).eventually_lt_const (div_pos hε (by positivity : (0:ℝ)<3^E))
  filter_upwards [small,eventually_ge_atTop (v+2)] with k hk hv u T
  let j := k+E-v
  have hj : j+v=k+E := by dsimp [j]; omega
  have hq : (0:ℝ)<3^j := by positivity
  have H := incomplete_orbit_interval (k:=j) (by dsimp [j]; omega) B u T hB
  have e (i : ℕ) : phase ((A:ℝ)*2^(u+i)/(3:ℝ)^(k+E)) =
      ZMod.stdAddChar ((B:ZMod (3^j))*2^(u+i)) := by
    have C := ZMod.stdAddChar_coe (N:=3^j) ((B:ℤ)*2^(u+i))
    push_cast at C
    rw [C,phase]
    congr 1
    rw [← he, ← hj, pow_add]; push_cast; field_simp; ring
  simp_rw [e]
  apply H.trans
  change 5*((1+Real.log ((3:ℝ)^j))/Real.sqrt ((3:ℝ)^j)) < ε/3^E at hk
  have H' := mul_le_mul_of_nonneg_right hk.le hq.le
  have hs := Real.sq_sqrt hq.le
  have hqle : (3:ℝ)^j ≤ 3^(k+E) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ = 5*((1+Real.log ((3:ℝ)^j))/Real.sqrt ((3:ℝ)^j))*3^j := by
      field_simp [Real.sqrt_ne_zero'.mpr hq]; rw [hs]
    _ ≤ _ := H'
    _ ≤ (ε/3^E)*3^(k+E) := mul_le_mul_of_nonneg_left hqle (by positivity)
    _ = _ := by rw [pow_add]; field_simp

private lemma phase_neg (t : ℝ) : phase (-t) = conj (phase t) := by
  rw [phase,phase, ← Complex.exp_conj]
  push_cast; simp; ring_nf; rw [map_ofNat]

theorem fixed_multiplier_orbit {A : ℤ} (hA : A≠0) (E : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ u T : ℕ,
      ‖∑ i ∈ range T, phase ((A:ℝ)*2^(u+i)/(3:ℝ)^(k+E))‖ ≤ ε*(3:ℝ)^k := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg A
  · simpa using model_nat (A:=a) (by simpa using hA) E ε hε
  · filter_upwards [model_nat (A:=a) (by simpa using hA) E ε hε] with k H u T
    simpa only [Int.cast_neg,Int.cast_natCast, neg_mul,neg_div,phase_neg,← map_sum,Complex.norm_conj] using H u T

/-- Integer numerator of the cell phase with a common power of three cleared. -/
def cellNumerator (M : Finset ℕ) (c : ℕ → ℤ) (j : ℕ → ℕ) (E : ℕ) : ℤ :=
  ∑ m ∈ M, c m*(-1)^m*3^(E-j m)

/-- A single modular orbit approximates the entire finite sum on a scale cell. -/
theorem cell_orbit_approx {u E : ℕ} (M : Finset ℕ) (c : ℕ → ℤ) (j : ℕ → ℕ)
    (hm : ∀ m ∈ M, 0<m) (hl : ∀ m ∈ M, m*3^(j m) ≤ u)
    (hu : ∀ m ∈ M, u+1 ≤ m*3^(j m+1)) (hE : ∀ m ∈ M, j m ≤ E)
    (k i : ℕ) (hi : i < 3^k) :
    let n := u*3^k+i
    ∃ z : ℤ, |(2:ℝ)^(n+1)*(∑ m ∈ M, (c m:ℝ)*((m:ℝ)*component m)) +
      2^n*((cellNumerator M c j E:ℝ)/(3:ℝ)^(k+E)) - z| ≤
      (∑ m ∈ M, |(c m:ℝ)| *2)/(3:ℝ)^k := by
  let n := u*3^k+i
  let C := cellNumerator M c j E
  let B := ∑ m ∈ M, |(c m:ℝ)| *2
  have H' := finite_orbit_approx M c (fun m => k+j m) n hm (fun m hm => by
    dsimp [n]; rw [pow_add]; nlinarith [Nat.mul_le_mul_right (3^k) (hl m hm)]) (fun m hm => by
    dsimp [n]; rw [show k+j m+1=k+(j m+1) by omega,pow_add 3 k (j m+1)]; nlinarith [Nat.mul_le_mul_right (3^k) (hu m hm)])
  obtain ⟨z,hz⟩ := H'
  have he : (∑ m ∈ M, (c m:ℝ)*(-1:ℝ)^m/(3:ℝ)^(k+j m)) = C/(3:ℝ)^(k+E) := by
    dsimp [C,cellNumerator]; push_cast; rw [sum_div]
    apply sum_congr rfl; intro m hm
    have he' : E= j m+(E-j m) := (Nat.add_sub_of_le (hE m hm)).symm
    conv_rhs => rw [show k+E=(k+j m)+(E-j m) by omega,pow_add]
    field_simp
  rw [he] at hz
  have HB : (∑ m ∈ M, |(c m:ℝ)| *(2/(3:ℝ)^(k+j m+1))) ≤ B/(3:ℝ)^k := by
    dsimp [B]; rw [sum_div]
    apply sum_le_sum; intro m _
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨z,hz.trans HB⟩

/-- The insertion depths are constant offsets from the scale k throughout a cell.
The last inequality allows the next insertion at the upper endpoint. -/
theorem cell_cancellation {u E : ℕ} (M : Finset ℕ) (c : ℕ → ℤ) (j : ℕ → ℕ)
    (hm : ∀ m ∈ M, 0<m) (hl : ∀ m ∈ M, m*3^(j m) ≤ u)
    (hu : ∀ m ∈ M, u+1 ≤ m*3^(j m+1)) (hE : ∀ m ∈ M, j m ≤ E)
    (hC : cellNumerator M c j E ≠ 0) (h : ℤ) (hh : h≠0) :
    CellCancellation (fun n => phase (h*((2:ℝ)^(n+1)*
      (∑ m ∈ M, (c m:ℝ)*((m:ℝ)*component m))))) u := by
  let F := ∑ m ∈ M, (c m:ℝ)*((m:ℝ)*component m)
  let C := cellNumerator M c j E
  let B := ∑ m ∈ M, |(c m:ℝ)| *2
  intro ε hε
  have hc := fixed_multiplier_orbit (neg_ne_zero.mpr (mul_ne_zero hh hC)) E (ε/2) (half_pos hε)
  have err : Tendsto (fun k : ℕ => 2*Real.pi*|(h:ℝ)| *B/(3:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=2*Real.pi*|(h:ℝ)| *B)).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3)))
  filter_upwards [hc, err.eventually_lt_const (half_pos hε)] with k H hsmall T hT
  let q := 3^k
  let f (n : ℕ) := phase (h*((2:ℝ)^(n+1)*F))
  let g (n : ℕ) := phase (((-(h*C):ℤ):ℝ)*2^n/(3:ℝ)^(k+E))
  have point (i : ℕ) (hi : i<T) : ‖f (u*q+i) - g (u*q+i)‖ ≤ ε/2 := by
    let n := u*q+i
    obtain ⟨z,hz'⟩ := cell_orbit_approx M c j hm hl hu hE k i (hi.trans_le hT)
    have hzphase : phase (((h*z:ℤ):ℝ)) = 1 := by
      simpa [phase,mul_comm] using Complex.exp_int_mul_two_pi_mul_I (h*z)
    let y := ((-(h*C):ℤ):ℝ)*2^n/(3:ℝ)^(k+E)
    change ‖phase (h*(2^(n+1)*F)) - phase y‖ ≤ _
    rw [← mul_one (phase y), ← hzphase, ← phase_add]
    apply (phase_sub_le _ _).trans
    have he' : (h:ℝ)*(2^(n+1)*F) - (y+((h*z:ℤ):ℝ)) =
        h*(2^(n+1)*F+2^n*(C/(3:ℝ)^(k+E))-z) := by dsimp [y]; push_cast; ring
    rw [he', abs_mul, ← mul_assoc]
    apply (mul_le_mul_of_nonneg_left hz' (by positivity)).trans
    simpa [mul_div_assoc] using hsmall.le
  change ‖∑ i ∈ range T, f (u*q+i)‖ ≤ _
  have hdiff : ‖(∑ i ∈ range T, f (u*q+i)) - ∑ i ∈ range T, g (u*q+i)‖ ≤ (ε/2)*(3:ℝ)^k := by
    rw [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ range T, ε/2 := sum_le_sum (fun i hi => point i (mem_range.mp hi))
      _ ≤ _ := by simp only [sum_const,card_range,nsmul_eq_mul]; rw [mul_comm]; gcongr; exact_mod_cast hT
  have H' := norm_add_le ((∑ i ∈ range T, f (u*q+i)) - ∑ i ∈ range T, g (u*q+i))
    (∑ i ∈ range T, g (u*q+i))
  rw [sub_add_cancel] at H'
  have Hg : ‖∑ i ∈ range T, g (u*q+i)‖ ≤ ε/2*(3:ℝ)^k := H (u*q) T
  linarith

end NormalityChecker
