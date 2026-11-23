module

public import NormalityChecker.Dilation
public import NormalityChecker.ScaleTransfer
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Convergence of overlapping radix-word frequencies forces cancellation
of each nonzero Fourier frequency of the shifted real number. -/
theorem fourier_of_normal {b : ℕ} {x : ℝ} (hn : NormalIn b x) (h : ℤ) (hh : h≠0) :
    Tendsto (mean (fun n => phase (h*((b:ℝ)^n*x)))) atTop (𝓝 0) := by
  classical
  have hb := hn.1
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpow : Tendsto (fun k : ℕ => (b:ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hb)
  have grow : Tendsto (fun k : ℕ => b^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hb
  obtain ⟨k,hk,hk',hk₀⟩ := ((hpow.eventually_gt_atTop (4*Real.pi*|(h:ℝ)| /ε)).and
    ((grow.eventually_gt_atTop h.natAbs).and (eventually_gt_atTop 0))).exists
  let q := b^k
  have hq : 0<q := pow_pos (by omega) _
  let : NeZero q := ⟨hq.ne'⟩
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hχ : (h:ZMod q)≠0 := by
    intro e
    exact hh (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp e)
      (by simpa using hk'))
  let u := shift b x
  let a (n : ℕ) := ⌊u n*q⌋₊
  have huni (n : ℕ) : 0≤u n ∧ u n<1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have ha (n : ℕ) : a n < q := (Nat.floor_lt (mul_nonneg (huni n).1 hqr.le)).mpr
    (by simpa using (mul_lt_mul_of_pos_right (huni n).2 hqr))
  have bin (n m : ℕ) : a n=m ↔ (m:ℝ)/q ≤ u n ∧ u n < (m+1)/q := by
    rw [div_le_iff₀ hqr,lt_div_iff₀ hqr]; exact Nat.floor_eq_iff (mul_nonneg (huni n).1 hqr.le)
  let χ (z : ZMod q) := ZMod.stdAddChar ((h:ZMod q)*z)
  have integral : ∑ z : ZMod q, χ z = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hχ)
  let g (n : ℕ) := χ (a n : ZMod q)
  have weight (z : ZMod q) : Tendsto (fun N => (χ z)*
      ((frequency u (z.val/q) ((z.val+1)/q) N : ℝ):ℂ)) atTop (𝓝 (χ z*(1/(q:ℂ)))) := by
    have hz := hn.2 k z.val hk₀ (ZMod.val_lt z)
    simpa [u,q] using (tendsto_const_nhds (x:=χ z)).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hz)
  have sumzero := tendsto_finsetSum univ fun z _ => weight z
  rw [← sum_mul,integral,zero_mul] at sumzero
  have hg : Tendsto (mean g) atTop (𝓝 0) := by
    apply sumzero.congr
    intro N
    have decomp (z : ZMod q) : χ z * ((frequency u (z.val/q) ((z.val+1)/q) N : ℝ):ℂ) =
        (∑ i ∈ range N, if (a i : ZMod q)=z then χ z else 0)/(N:ℂ) := by
      unfold frequency; push_cast
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      have eqn (i : ℕ) : ((a i:ZMod q)=z) ↔ a i=z.val := by
        rw [← (ZMod.val_injective q).eq_iff, ZMod.val_natCast_of_lt (ha i)]
      simp_rw [eqn,bin]
      ring
    simp_rw [decomp]
    rw [← sum_div,sum_comm]; simp [mean,g]
  let f (n : ℕ) := phase (h*((b:ℝ)^n*x))
  have err (n : ℕ) : ‖f n-g n‖ ≤ ε/2 := by
    have ech := ZMod.stdAddChar_coe (N:=q) (h*(a n:ℤ))
    push_cast at ech
    have e : g n = phase (h*((a n:ℝ)/q)) := by
      change ZMod.stdAddChar ((h:ZMod q)*(a n:ZMod q)) = _
      rw [ech,phase]; push_cast; ring_nf
    have fe : f n = phase (h*u n) := (phase_fract h _).symm
    rw [fe,e]
    apply (phase_sub_le _ _).trans
    obtain ⟨lo,hi⟩ := (bin n (a n)).mp rfl
    rw [← mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr lo),← mul_assoc]
    have hd : u n-(a n:ℝ)/q ≤ 1/q := by rw [add_div] at hi; linarith
    apply (mul_le_mul_of_nonneg_left hd (by positivity)).trans
    rw [mul_one_div,div_le_iff₀ hqr]
    have bound := (div_lt_iff₀ hε).mp hk
    dsimp [q]; push_cast; linarith
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ((tendsto_zero_iff_norm_tendsto_zero.mp hg).eventually_lt_const (half_pos hε))
  refine ⟨max 1 N₀,fun N hN => ?_⟩
  have hN' : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one ((le_max_left ..).trans hN))
  have dist : ‖mean f N-mean g N‖ ≤ ε/2 := by
    rw [mean,mean,← sub_div,← sum_sub_distrib,norm_div,Complex.norm_natCast, div_le_iff₀ hN']
    apply (norm_sum_le _ _).trans ((sum_le_sum (fun i _ => err i)).trans_eq ?_)
    simp [mul_comm]
  have tri := norm_add_le (mean f N-mean g N) (mean g N)
  rw [sub_add_cancel] at tri
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  change ‖mean f N‖ < ε
  linarith [hN₀ N ((le_max_right ..).trans hN)]

/-- Fourier characterization of normality for any approximation to the shifted orbit. -/
theorem normalIn_iff_prefix_fourier {b : ℕ} (hb : 2≤b) (x : ℝ) (u : ℕ → ℝ)
    (he : Tendsto (fun n => (b:ℝ)^n*x - u n) atTop (𝓝 0)) :
    NormalIn b x ↔ ∀ h : ℤ, h≠0 → Tendsto (Weyl.fourierMean u h) atTop (𝓝 0) := by
  constructor
  · intro hn h hh
    apply (fourierMean_zero_iff_of_error he h).mp
    simpa [mean_phase] using fourier_of_normal hn h hh
  · intro hu
    apply normal_of_fourier hb
    intro h hh
    simpa [mean_phase] using (fourierMean_zero_iff_of_error he h).mpr (hu h hh)

theorem binary_normal_iff_odd_prefix_fourier (x : ℝ) (u : ℕ → ℝ)
    (he : Tendsto (fun n => 2^n*x-u n) atTop (𝓝 0)) :
    NormalIn 2 x ↔ ∀ h : ℤ, Odd h → Tendsto (Weyl.fourierMean u h) atTop (𝓝 0) := by
  constructor
  · intro hn h hh
    apply (normalIn_iff_prefix_fourier (by decide) x u he).mp hn h
    rintro rfl; exact (by decide : ¬ Odd (0:ℤ)) hh
  · intro H
    exact binary_normal_of_odd_fourier x (fun h hh => (fourierMean_zero_iff_of_error he h).mpr (H h hh))

/-- Normality is invariant under multiplication by a positive integer, even
when that integer shares factors with the base. -/
theorem normal_mul_nat_iff {b D : ℕ} (hb : 2≤b) (hD : 0<D) (x : ℝ) :
    NormalIn b ((D:ℝ)*x) ↔ NormalIn b x := by
  constructor
  · intro H
    apply normal_of_dilated_fourier hb x D hD
    intro h hh
    simpa only [mul_left_comm (D:ℝ)] using fourier_of_normal H h hh
  · intro H
    apply normal_of_fourier hb
    intro h hh
    simpa only [Int.cast_mul,Int.cast_natCast,mul_assoc,mul_left_comm,mul_comm] using
      fourier_of_normal H (h*D) (mul_ne_zero hh (by exact_mod_cast hD.ne'))

/-- Translation by a rational preserves normality in every integer radix. -/
theorem normal_add_rat_iff {b : ℕ} (hb : 2≤b) (x : ℝ) (q : ℚ) :
    NormalIn b (x+(q:ℝ)) ↔ NormalIn b x := by
  rw [← normal_mul_nat_iff hb q.pos (x+q), ← normal_mul_nat_iff hb q.pos x]
  have hq : (q.den:ℝ)*(q:ℝ) = q.num := by rw [Rat.cast_def]; field_simp
  rw [mul_add,hq]
  have shifts : shift b ((q.den:ℝ)*x+q.num) = shift b ((q.den:ℝ)*x) := by
    funext n
    have h : (b:ℝ)^n*q.num=((b:ℤ)^n*q.num:ℤ) := by push_cast; rfl
    simp only [shift,mul_add,h,Int.fract_add_intCast]
  simp only [NormalIn,shifts]

private theorem lag_difference_error {b : ℕ} (hb : 2≤b) (x : ℝ) (u : ℕ → ℝ)
    (he : Tendsto (fun n => (b:ℝ)^n*x-u n) atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun n => (b:ℝ)^n*((b^r-1:ℕ)*x)-(u (n+r)-u n)) atTop (𝓝 0) := by
  have H := (he.comp (tendsto_add_atTop_nat r)).sub he
  rw [sub_zero] at H
  apply H.congr
  intro n
  simp only [Function.comp_apply,pow_add,Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 0<b)),
    Nat.cast_pow, Nat.cast_one]
  ring

/-- Differences at any one fixed positive lag characterize normality for every
radix expansion admitting a vanishing-error prefix approximation. -/
theorem normalIn_iff_lag_differences {b : ℕ} (hb : 2≤b) (x : ℝ) (u : ℕ → ℝ)
    (he : Tendsto (fun n => (b:ℝ)^n*x-u n) atTop (𝓝 0)) {r : ℕ} (hr : 0<r) :
    NormalIn b x ↔ UniformModOne (fun n => u (n+r)-u n) := by
  let D := b^r-1
  have hD : 0<D := Nat.sub_pos_of_lt (one_lt_pow₀ hb hr.ne')
  exact (normal_mul_nat_iff hb hD x).symm.trans
    (normalIn_iff_uniform_approx hb _ _ (lag_difference_error hb x u he r))

/-- Binary normality of log 2 is equivalent to cancellation at all odd signed
frequencies of its exact rational recurrence. -/
theorem logTwo_normal_iff_odd_prefix_fourier :
    NormalIn 2 (Real.log 2) ↔ ∀ h : ℤ, Odd h →
      Tendsto (Weyl.fourierMean (fun n => (logPrefix n:ℝ)) h) atTop (𝓝 0) :=
  binary_normal_iff_odd_prefix_fourier _ _ logTwo_shift_error_tendsTo_zero

/-- At any chosen fixed positive lag, odd-frequency correlations between
separated rational prefixes give an equivalent test for binary normality. -/
theorem logTwo_normal_iff_lag_fourier {r : ℕ} (hr : 0<r) :
    NormalIn 2 (Real.log 2) ↔ ∀ h : ℤ, Odd h →
      Tendsto (Weyl.fourierMean (fun n => (logPrefix (n+r):ℝ)-logPrefix n) h) atTop (𝓝 0) := by
  have hD : 0<2^r-1 := Nat.sub_pos_of_lt (one_lt_pow₀ (by decide : 1<(2:ℕ)) hr.ne')
  exact (normal_mul_nat_iff (by decide) hD _).symm.trans (binary_normal_iff_odd_prefix_fourier _ _
    (lag_difference_error (by decide) _ _ logTwo_shift_error_tendsTo_zero r))

/-- One fixed odd frequency with a persistent bias along a subsequence is
necessary and sufficient for binary nonnormality of log 2. -/
theorem logTwo_not_normal_iff_odd_bias :
    ¬ NormalIn 2 (Real.log 2) ↔ ∃ h : ℤ, Odd h ∧ ∃ δ : ℝ, 0<δ ∧
      ∃ᶠ N in atTop, δ ≤ ‖Weyl.fourierMean (fun n => (logPrefix n:ℝ)) h N‖ := by
  rw [logTwo_normal_iff_odd_prefix_fourier]
  simp only [Metric.tendsto_nhds,dist_zero_right,not_forall,not_eventually,not_lt,exists_prop]

/-- An equivalent block estimate uniform in the endpoint of each dyadic interval. -/
theorem logTwo_normal_iff_dyadic_lag_cancellation {r : ℕ} (hr : 0<r) :
    NormalIn 2 (Real.log 2) ↔ ∀ h : ℤ, Odd h →
      RadixCellCancellation 2 (fun n => phase (h*((logPrefix (n+r):ℝ)-logPrefix n))) 1 := by
  rw [logTwo_normal_iff_lag_fourier hr]
  simp_rw [mean_phase,mean_zero_iff_dyadic_cells]

end NormalityChecker
