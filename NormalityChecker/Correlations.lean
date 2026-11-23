module

public import NormalityChecker.LogTwo
public import NormalityChecker.Analysis.Weyl
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker

theorem logPrefix_steps (n r : ℕ) :
    logPrefix (n+r) - 2^r * logPrefix n =
      ∑ i ∈ range r, (2:ℚ)^(r-1-i)/((n:ℚ)+i+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_succ, logPrefix, pow_succ', sum_range_succ]
    have he : (∑ i ∈ range r, (2:ℚ)^(r+1-1-i)/((n:ℚ)+i+1)) =
        2 * ∑ i ∈ range r, (2:ℚ)^(r-1-i)/((n:ℚ)+i+1) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have := mem_range.mp hi
      rw [show r+1-1-i = (r-1-i)+1 by omega,pow_succ']; ring
    rw [he, ← ih]
    simp; ring

theorem logPrefix_steps_bounds (n r : ℕ) :
    0 ≤ logPrefix (n+r) - 2^r * logPrefix n ∧
    logPrefix (n+r) - 2^r * logPrefix n ≤ (2^r-1)/((n:ℚ)+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_succ, logPrefix, pow_succ']
    push_cast
    have h : 1/((n:ℚ)+r+1) ≤ 1/(n+1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α:=ℚ) r])
    constructor
    · linarith [ih.1, (by positivity : (0:ℚ) ≤ 1/((n:ℚ)+r+1))]
    · have hd : (2*2^r-1)/((n:ℚ)+1) = 2*((2^r-1)/(n+1))+1/(n+1) := by ring
      rw [hd]; linarith [ih.2]

/-- The complex character at a real phase measured in turns. -/
noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x:ℂ))

private lemma phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp [phase, mul_add, Complex.exp_add]

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := by simp [phase, Complex.norm_exp]

private lemma phase_sub_le (x y : ℝ) : ‖phase x - phase y‖ ≤ 2*Real.pi*|x-y| := by
  have he : phase x - phase y = phase y * (phase (x-y)-1) := by
    rw [mul_sub_one, ← phase_add, add_sub_cancel]
  rw [he, norm_mul, norm_phase, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*Real.pi*(x-y))
  convert h using 1
  · unfold phase; push_cast; ring_nf
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]

/-- A fixed-lag joint character is controlled by the single frequency h+2^r g. -/
theorem logPrefix_lag_character_bound (n r : ℕ) (h g : ℤ) :
    ‖phase (h*(logPrefix n:ℝ)) * phase (g*(logPrefix (n+r):ℝ)) -
      phase (((h:ℝ)+2^r*g)*(logPrefix n:ℝ))‖ ≤
      2*Real.pi*|(g:ℝ)| *((2^r-1)/((n:ℝ)+1)) := by
  rw [← phase_add]
  apply (phase_sub_le _ _).trans
  have e : (h:ℝ)*logPrefix n + g*logPrefix (n+r) - (h+2^r*g)*logPrefix n =
      g*((logPrefix (n+r):ℝ)-2^r*logPrefix n) := by ring
  obtain ⟨hl,hu⟩ := logPrefix_steps_bounds n r
  have hl' : 0 ≤ (logPrefix (n+r):ℝ)-2^r*logPrefix n := by exact_mod_cast hl
  have hu' : (logPrefix (n+r):ℝ)-2^r*logPrefix n ≤ (2^r-1)/((n:ℝ)+1) := by exact_mod_cast hu
  rw [e, abs_mul, abs_of_nonneg hl', ← mul_assoc]
  exact mul_le_mul_of_nonneg_left hu' (by positivity)

private noncomputable def mean (f : ℕ → ℂ) (N : ℕ) := (∑ n ∈ range N, f n)/(N:ℂ)

private lemma mean_sub (f g : ℕ → ℂ) (N : ℕ) :
    mean (fun n => f n-g n) N = mean f N - mean g N := by simp [mean, sum_sub_distrib, sub_div]

private lemma mean_zero (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (mean f) atTop (𝓝 0) := by
  unfold mean
  simpa [div_eq_inv_mul, Complex.real_smul] using hf.cesaro_smul

private lemma mean_shift_zero (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ = 1)
    (hf : Tendsto (mean f) atTop (𝓝 0)) :
    Tendsto (mean (fun n => f (n+1))) atTop (𝓝 0) := by
  have he (N : ℕ) : mean (fun n => f (n+1)) N - mean f N = (f N-f 0)/(N:ℂ) := by
    rw [← mean_sub, mean, sum_range_sub]
  have small : Tendsto (fun N : ℕ => (f N-f 0)/(N:ℂ)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_const_div_atTop_nhds_zero_nat 2)
    intro N
    rw [norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa [hb, one_add_one_eq_two] using norm_sub_le (f N) (f 0)
  simpa using ((small.congr fun n => (he n).symm).add hf)

private lemma mean_phase (u : ℕ → ℝ) (h : ℤ) :
    Weyl.fourierMean u h = mean (fun n => phase (h*u n)) := by
  funext N
  simp only [Weyl.fourierMean, mean, phase, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]

private lemma phase_fract (h : ℤ) (x : ℝ) : phase (h*Int.fract x) = phase (h*x) := by
  have hz (z : ℤ) : phase z = 1 := by simpa [phase, mul_comm] using Complex.exp_int_mul_two_pi_mul_I z
  rw [show (h:ℝ)*x = h*Int.fract x + ((h*⌊x⌋ : ℤ):ℝ) by
    push_cast; rw [← mul_add, Int.fract_add_floor], phase_add, hz, mul_one]

/-- Odd signed frequencies suffice for the exact doubling orbit. -/
theorem binary_normal_of_odd_fourier (x : ℝ)
    (ho : ∀ h : ℤ, Odd h → Tendsto (Weyl.fourierMean (fun n => 2^n*x) h) atTop (𝓝 0)) :
    NormalIn 2 x := by
  have allFreq (h : ℤ) (hh : h ≠ 0) :
      Tendsto (Weyl.fourierMean (shift 2 x) h) atTop (𝓝 0) := by
    obtain ⟨v,m,hm,he⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hh)
    let a : ℤ := h.sign*m
    have ha : Odd a := (Int.odd_sign_iff.mpr hh).mul (by exact_mod_cast hm)
    have he' : h = 2^v*a := by rw [← h.sign_mul_natAbs, he]; push_cast; dsimp [a]; ring
    rw [mean_phase]
    change Tendsto (mean (fun n => phase (h*Int.fract ((2:ℝ)^n*x)))) atTop (𝓝 0)
    simp_rw [phase_fract]
    rw [he']
    clear he he'
    induction v with
    | zero => simpa [mean_phase] using ho a ha
    | succ v ih =>
      have H := mean_shift_zero _ (fun n => norm_phase _) ih
      apply H.congr
      intro N
      apply congrArg (fun f => mean f N)
      funext n
      push_cast; rw [pow_succ (2:ℝ) v, pow_succ (2:ℝ) n]; ring_nf
  have H := Weyl.equidistributed_of_weyl (shift 2 x) (fun _ =>
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) allFreq
  refine ⟨by decide, fun k m _ hm => ?_⟩
  have hd : (0:ℝ)<2^k := by positivity
  have he : ((m:ℝ)+1)/2^k - m/2^k = 1/2^k := by ring
  unfold frequency
  simpa [Weyl.visitCount, Set.mem_Ico, he] using
    H (m/2^k) ((m+1)/2^k) (by positivity) (by gcongr; linarith)
      ((div_le_one hd).mpr (by exact_mod_cast (show m+1 ≤ 2^k from hm)))

/-- One can test odd frequencies on the exact rational prefixes themselves. -/
theorem logTwo_normal_of_odd_prefix_fourier
    (ho : ∀ h : ℤ, Odd h →
      Tendsto (Weyl.fourierMean (fun n => (logPrefix n:ℝ)) h) atTop (𝓝 0)) :
    NormalIn 2 (Real.log 2) := by
  apply binary_normal_of_odd_fourier
  intro h hh
  rw [mean_phase]
  let f (n : ℕ) := phase (h*((2:ℝ)^n*Real.log 2))
  let g (n : ℕ) := phase (h*(logPrefix n:ℝ))
  have small : Tendsto (fun n => f n-g n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have H := (tendsto_const_nhds (x:=2*Real.pi*|(h:ℝ)|)).mul logTwo_shift_error_tendsTo_zero
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using H)
    intro n
    apply (phase_sub_le _ _).trans_eq
    rw [← mul_sub,abs_mul,abs_of_nonneg (logTwo_tail_bounds n).1]; ring
  have HG : Tendsto (mean g) atTop (𝓝 0) := by simpa [mean_phase,g] using ho h hh
  simpa [mean_sub] using (mean_zero _ small).add HG

end NormalityChecker
