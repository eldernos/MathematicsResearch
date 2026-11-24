module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.LSeries.WeakPNT
public import Mathlib.Tactic

@[expose] public section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace NormalityChecker
namespace LogTwoForm

/-- The classical auxiliary integral uses this positive kernel on (1,2). -/
private noncomputable def kernel (x : ℝ) := (x-1)*(2-x)/x
private noncomputable def integrand (m i j : ℕ) (x : ℝ) := (kernel x)^m * x^i * (2/x)^j / x
private noncomputable def moment (m i j : ℕ) := ∫ x in (1:ℝ)..2, integrand m i j x

private lemma continuous_integrand (m i j : ℕ) {a b : ℝ} (ha : 0<a) :
    ContinuousOn (integrand m i j) (Icc a b) := by
  have hx : ∀ x∈Icc a b, x≠0 := fun x h => (ha.trans_le h.1).ne'
  unfold integrand kernel; fun_prop (disch := assumption)

private lemma integrable (m i j : ℕ) : IntervalIntegrable (integrand m i j) volume 1 2 :=
  (continuous_integrand m i j (by norm_num : (0:ℝ)<1)).intervalIntegrable_of_Icc (by norm_num)

private lemma kernel_bounds (x : ℝ) (hx : x∈Icc 1 2) : 0≤kernel x ∧ kernel x≤1/4 := by
  obtain ⟨hl,hr⟩ := hx
  unfold kernel; constructor
  · positivity [sub_nonneg.mpr hl,sub_nonneg.mpr hr]
  · rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (x-3/2)]

private lemma moment_bounds (m : ℕ) :
    (1/6:ℝ)*(1/18:ℝ)^m ≤ moment m 0 0 ∧ moment m 0 0 ≤ (1/4:ℝ)^m := by
  let f := integrand m 0 0
  have hi := integrable m 0 0
  have lo := integral_mono_on (μ:=volume) (a:=(4/3:ℝ)) (b:=(5/3:ℝ)) (f:=fun _ => (1/2:ℝ)*(1/18:ℝ)^m)
    (g:=f) (by norm_num) intervalIntegrable_const
    ((continuous_integrand m 0 0 (by norm_num : (0:ℝ)<4/3)).intervalIntegrable_of_Icc (by norm_num)) (by
      intro x hx
      obtain ⟨hl,hr⟩ := hx
      have hpos : 0<x := by linarith
      have HK : (1/18:ℝ) ≤ kernel x := by
        rw [kernel,le_div_iff₀ hpos]
        have h := mul_le_mul (show 1/3≤x-1 by linarith) (show 1/3≤2-x by linarith)
          (by norm_num : (0:ℝ)≤1/3) (by linarith : 0≤x-1)
        linarith
      dsimp [f,integrand]; rw [le_div_iff₀ hpos]
      have H := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/18) HK m
      nlinarith [mul_le_mul_of_nonneg_right (show x≤2 by linarith) (by positivity : (0:ℝ)≤(1/18:ℝ)^m)])
  have nonneg (x : ℝ) (hx : x∈Ioc 1 2) : 0≤f x := by
    obtain ⟨h,_⟩ := kernel_bounds x ⟨hx.1.le,hx.2⟩
    dsimp [f,integrand]; positivity [hx.1.le]
  have sub := integral_mono_interval (μ:=volume) (f:=f) (by norm_num : (1:ℝ)≤4/3) (by norm_num : (4/3:ℝ)≤5/3)
    (by norm_num : (5/3:ℝ)≤2) ((ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall nonneg)) hi
  have upper := integral_mono_on (μ:=volume) (a:=(1:ℝ)) (b:=2) (f:=f) (g:=fun _ => (1/4:ℝ)^m)
    (by norm_num) hi intervalIntegrable_const (by
      intro x hx
      obtain ⟨h0,h1⟩ := kernel_bounds x hx
      dsimp [f,integrand]; rw [div_le_iff₀ (by linarith [hx.1])]
      simp only [pow_zero,mul_one]
      exact (pow_le_pow_left₀ h0 h1 _).trans (le_mul_of_one_le_right (by positivity) hx.1))
  rw [intervalIntegral.integral_const] at lo upper
  change _ ≤ (∫ x in (1:ℝ)..2, f x) ∧ _
  constructor
  · exact (show (1/6:ℝ)*(1/18:ℝ)^m = (5/3-4/3:ℝ) • ((1/2:ℝ)*(1/18:ℝ)^m) by simp only [smul_eq_mul]; ring) ▸ lo.trans sub
  · change (∫ x in (1:ℝ)..2, f x) ≤ _
    norm_num at upper ⊢; exact upper

private lemma moment_step (m i j : ℕ) : moment (m+1) i j =
    3*moment m i j - moment m (i+1) j - moment m i (j+1) := by
  unfold moment
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub ((integrable m i j).const_mul 3) (integrable m (i+1) j),
    ← intervalIntegral.integral_sub (((integrable m i j).const_mul 3).sub (integrable m (i+1) j)) (integrable m i (j+1))]
  apply intervalIntegral.integral_congr; intro x hx; dsimp only
  have hpos : 0<x := by rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx; linarith [hx.1]
  simp only [integrand,kernel,pow_succ]; field_simp; ring

/-- The elementary integrals for unequal indices have denominator dividing |i-j|. -/
private lemma base_pos_gap (i j : ℕ) (h : j < i) : moment 0 i j =
    ((2:ℝ)^i-2^j)/(i-j) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_lt h
  have he : i=j+(k+1) := by omega
  rw [he]
  have eqn : moment 0 (j+(k+1)) j = ∫ x in (1:ℝ)..2, (2:ℝ)^j*x^k := by
    apply intervalIntegral.integral_congr; intro x hx; dsimp only
    rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
    have hpos : 0<x := by linarith [hx.1]
    simp only [integrand,pow_zero,one_mul,pow_add x j,pow_succ x k,div_pow]; field_simp
  rw [eqn, intervalIntegral.integral_const_mul,integral_pow,pow_add (2:ℝ) j]; push_cast; field_simp; ring

private lemma base_neg_gap (i j : ℕ) (h : i < j) : moment 0 i j = moment 0 j i := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_lt h
  have he : j=i+(k+1) := by omega
  rw [he]
  let t : ℤ := -(k:ℤ)-2
  have eqn : moment 0 i (i+(k+1)) = ∫ x in (1:ℝ)..2, (2:ℝ)^(i+(k+1))*x^t := by
    apply intervalIntegral.integral_congr; intro x hx; dsimp only
    rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
    have hpos : 0<x := by linarith [hx.1]
    rw [show t=-((k+2:ℕ):ℤ) by dsimp [t]; ring,zpow_neg,zpow_natCast]
    simp only [integrand,pow_zero,one_mul,div_pow,pow_add]; field_simp
  rw [eqn,base_pos_gap _ _ (by omega),intervalIntegral.integral_const_mul,integral_zpow (Or.inr ⟨by dsimp [t]; omega,by norm_num⟩)]
  rw [show t+1=-((k+1:ℕ):ℤ) by dsimp [t]; ring,zpow_neg,zpow_natCast]
  dsimp [t]; push_cast; simp only [one_zpow,pow_add]
  have hn : -(k:ℝ)-2+1≠0 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hp : (i:ℝ)+(k+1)-i≠0 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  field_simp [hn,hp]; ring

private lemma base_equal (i : ℕ) : moment 0 i i = (2:ℝ)^i * Real.log 2 := by
  have e : moment 0 i i= ∫ x in (1:ℝ)..2, (2:ℝ)^i*(1/x) := by
    apply intervalIntegral.integral_congr; intro x hx; dsimp only
    rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
    have hpos : 0<x := by linarith [hx.1]
    simp [integrand,div_pow]; field_simp
  rw [e,intervalIntegral.integral_const_mul,integral_one_div_of_pos (by norm_num) (by norm_num),div_one]

private lemma offdiag_integer (L i j : ℕ) (h : j < i) (hi : i≤L) :
    ∃ B : ℤ, (Nat.lcmUpto L:ℝ)*moment 0 i j = B := by
  have hd : i-j ∣ Nat.lcmUpto L := Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  obtain ⟨q,hq⟩ := hd
  refine ⟨(q:ℤ)*((2:ℤ)^i-2^j),?_⟩
  have he : (Nat.lcmUpto L:ℝ)=((i:ℝ)-j)*q := by rw [hq,Nat.cast_mul,Nat.cast_sub h.le]
  rw [he,base_pos_gap _ _ h]; push_cast
  have hn : (i:ℝ)-j≠0 := sub_ne_zero.mpr (by exact_mod_cast h.ne')
  field_simp

/-- Clearing all moments at level L with one lcm produces a linear form in log 2. -/
private lemma coefficients (L m i j : ℕ) (h : m+i+j≤L) :
    ∃ A B : ℤ, (Nat.lcmUpto L:ℝ)*moment m i j = Nat.lcmUpto L*A*Real.log 2+B ∧
      |(A:ℝ)|≤(5:ℝ)^m*2^L := by
  induction m generalizing i j with
  | zero =>
    rcases lt_trichotomy i j with hlt|rfl|hgt
    · obtain ⟨B,hB⟩ := offdiag_integer L j i hlt (by omega)
      exact ⟨0,B,by simpa [base_neg_gap i j hlt] using hB,by simp⟩
    · refine ⟨(2:ℤ)^i,0,?_,?_⟩
      · rw [base_equal]; push_cast; ring
      · simpa [abs_of_pos] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : i≤L))
    · obtain ⟨B,hB⟩ := offdiag_integer L i j hgt (by omega)
      exact ⟨0,B,by simpa using hB,by simp⟩
  | succ m ih =>
    obtain ⟨A,B,e,hA⟩ := ih i j (by omega)
    obtain ⟨C,D,g,hC⟩ := ih (i+1) j (by omega)
    obtain ⟨U,V,f,hU⟩ := ih i (j+1) (by omega)
    refine ⟨3*A-C-U,3*B-D-V,?_,?_⟩
    · rw [moment_step]; push_cast; linear_combination 3*e-g-f
    · push_cast; rw [pow_succ]
      obtain ⟨a,a'⟩ := abs_le.mp hA
      obtain ⟨c,c'⟩ := abs_le.mp hC
      obtain ⟨u,u'⟩ := abs_le.mp hU
      apply abs_le.mpr; constructor <;> linarith

private lemma lcm_upper : ∀ᶠ m : ℕ in atTop, (Nat.lcmUpto m:ℝ)≤3^m := by
  have h3 : 1<Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  filter_upwards [Nat.tendsto_log_lcmUpto_div_atTop.eventually_lt_const h3,eventually_gt_atTop 0] with m hm hm'
  apply le_of_lt
  apply (Real.log_lt_log_iff (by exact_mod_cast Nat.lcmUpto_pos m) (by positivity)).mp
  rw [Real.log_pow]
  have := (div_lt_iff₀ (show (0:ℝ)<m by exact_mod_cast hm')).mp hm
  linarith

private lemma half_integer (s : ℝ) (hr : s≤1/2) (z : ℤ) : s ≤ |s-z| := by
  by_cases h : z≤0
  · have h' : (z:ℝ)≤0 := by exact_mod_cast h
    exact (show s≤s-z by linarith).trans (le_abs_self _)
  · have h' : (1:ℝ)≤z := by exact_mod_cast (show 1≤z by omega)
    exact (show s≤ -(s-z) by linarith).trans (neg_le_abs _)

/-- An unconditional dyadic approximation bound obtained from the auxiliary
integrals. All sufficiently late shifts stay at least 2^(-32n) from integers. -/
theorem dyadic_separation :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℤ, (1/2:ℝ)^(32*n) ≤ |(2:ℝ)^n*Real.log 2-z| := by
  have grow : Tendsto (fun n : ℕ => 4*n) atTop atTop := tendsto_atTop_mono
    (fun n => Nat.le_mul_of_pos_left n (by decide : 0<4)) tendsto_id
  have small := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : 0≤2*(3/4:ℝ)^4) (by norm_num : 2*(3/4:ℝ)^4<1)).eventually_lt_const (by norm_num : (0:ℝ)<1/2)
  filter_upwards [grow.eventually lcm_upper,small,eventually_ge_atTop 3] with n hL hsmall hn z
  let m := 4*n
  let D : ℝ := Nat.lcmUpto m
  let q : ℝ := 2^n
  let s := q*D*moment m 0 0
  have hD : 0<D := by dsimp [D]; exact_mod_cast Nat.lcmUpto_pos m
  have hq : 0<q := by dsimp [q]; positivity
  obtain ⟨lo,hi⟩ := moment_bounds m
  have hI : 0≤moment m 0 0 := (by positivity : 0≤(1/6:ℝ)*(1/18)^m).trans lo
  have upper : s≤1/2 := by
    calc
      s ≤ q*(3:ℝ)^m*(1/4:ℝ)^m := by dsimp only [s]; gcongr
      _ = (2*(3/4:ℝ)^4)^n := by dsimp [q,m]; rw [mul_pow,← pow_mul,mul_assoc,← mul_pow]; norm_num
      _ ≤ _ := hsmall.le
  obtain ⟨A,B,form,hA⟩ := coefficients m m 0 0 (by omega)
  let e := q*Real.log 2-z
  let Z : ℤ := (2:ℤ)^n*B+(Nat.lcmUpto m:ℤ)*A*z
  have eqn : s-Z=D*A*e := by
    dsimp [s,Z,e,D,q]; push_cast
    linear_combination (2:ℝ)^n*form
  have dist := half_integer s upper Z
  rw [eqn,abs_mul,abs_mul,abs_of_pos hD] at dist
  have loss : q*moment m 0 0 ≤ |(A:ℝ)| *|e| := by
    apply (mul_le_mul_iff_right₀ hD).mp; dsimp [s] at dist; linarith
  have hsix : 6≤q := by
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn
    change (6:ℝ)≤2^n; norm_num at this; linarith
  have he : (1/18:ℝ)^m ≤ (10:ℝ)^m*|e| := by
    rw [show (10:ℝ)^m=5^m*2^m by rw [← mul_pow]; norm_num]
    calc
      _ ≤ q*((1/6:ℝ)*(1/18)^m) := by nlinarith [mul_le_mul_of_nonneg_right hsix (by positivity : 0≤(1/18:ℝ)^m)]
      _ ≤ q*moment m 0 0 := mul_le_mul_of_nonneg_left lo hq.le
      _ ≤ _ := loss
      _ ≤ _ := mul_le_mul_of_nonneg_right hA (abs_nonneg e)
  have he' : (1/180:ℝ)^m≤|e| := by
    rw [show (1/180:ℝ)=(1/18)/10 by norm_num,div_pow,div_le_iff₀ (by positivity)]
    simpa [mul_comm] using he
  apply le_trans _ he'
  change (1/2:ℝ)^(32*n)≤(1/180:ℝ)^(4*n)
  rw [show 32*n=8*(4*n) by ring,pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) _

end LogTwoForm
end NormalityChecker
