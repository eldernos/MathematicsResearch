module

public import NormalityChecker.Correlations
public import Mathlib.Data.Fintype.Pigeonhole

@[expose] public section
open Finset Filter
open scoped Topology ComplexConjugate
namespace NormalityChecker

private lemma shifted_mean_error (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖=1) (l : ℕ) :
    Tendsto (fun N => mean (fun n => f (n+l)) N - mean f N) atTop (𝓝 0) := by
  have he (N : ℕ) : (∑ n ∈ range N, f (n+l)) - ∑ n ∈ range N, f n =
      (∑ i ∈ range l, f (N+i)) - ∑ i ∈ range l, f i := by
    have H := congrArg (fun t : ℕ => ∑ i ∈ range t, f i) (Nat.add_comm N l)
    simp only [sum_range_add] at H
    simpa only [add_comm _ l] using (show (∑ n ∈ range N, f (l+n)) - ∑ n ∈ range N, f n =
      (∑ i ∈ range l, f (N+i)) - ∑ i ∈ range l, f i by linear_combination -H)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_const_div_atTop_nhds_zero_nat (2*(l:ℝ)))
  intro N; rw [mean,mean, ← sub_div,he,norm_div,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (norm_sub_le _ _).trans
  have h₁ := norm_sum_le (range l) (fun i => f (N+i))
  have h₂ := norm_sum_le (range l) f
  simp only [hb,sum_const,card_range,nsmul_eq_mul,mul_one] at h₁ h₂
  linarith

private lemma norm_mean_sq {f : ℕ → ℂ} {N : ℕ} (hN : 0<N) :
    ‖mean f N‖^2 ≤ (∑ i ∈ range N, ‖f i‖^2)/(N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1:ℝ)) (fun i => ‖f i‖)
  simp only [one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one] at h
  have h' := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun i _ => norm_nonneg _))).mpr (norm_sum_le (range N) f)
  rw [mean,norm_div,Complex.norm_natCast,div_pow,div_le_div_iff₀ (by positivity) hn]
  nlinarith [mul_le_mul_of_nonneg_right (h'.trans h) hn.le]

private lemma phase_conj (x : ℝ) : conj (phase x) = phase (-x) := by
  rw [phase,phase, ← Complex.exp_conj]; push_cast; simp; ring_nf; rw [map_ofNat]; ring_nf

/-- To test binary normality one may test all nonzero frequencies after a fixed
positive integer dilation. Shifts having the same residue 2^t modulo D become
asymptotically orthogonal, and their number can be made arbitrarily large. -/
theorem binary_normal_of_dilated_fourier (x : ℝ) (D : ℕ) (hD : 0<D)
    (H : ∀ h : ℤ, h≠0 → Tendsto (mean (fun n => phase (h*((D:ℝ)*(2^n*x))))) atTop (𝓝 0)) :
    NormalIn 2 x := by
  classical
  apply binary_normal_of_odd_fourier
  intro h hh
  have hh0 : h≠0 := by rintro rfl; exact (by decide : ¬ Odd (0:ℤ)) hh
  rw [mean_phase]
  let f (n : ℕ) := phase (h*(2^n*x))
  change Tendsto (mean f) atTop (𝓝 0)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (4/ε^2:ℝ)
  have hK0 : (0:ℝ)<K := lt_trans (by positivity) hK
  have hKe : 4 < (K:ℝ)*ε^2 := (div_lt_iff₀ (by positivity)).mp hK
  have : NeZero D := ⟨hD.ne'⟩
  let v (t : ℕ) := (2:ZMod D)^t
  obtain ⟨y,hy⟩ := Finite.exists_infinite_fiber v
  obtain ⟨S,hS,hcard⟩ := (Set.infinite_coe_iff.mp hy).exists_subset_card_eq K
  let G (n : ℕ) := ∑ t ∈ S, f (n+t)
  have corr (a : ℕ) (ha : a ∈ S) (b : ℕ) (hb : b ∈ S) :
      Tendsto (mean (fun n => f (n+a) * conj (f (n+b)))) atTop
        (𝓝 (if a=b then (1:ℂ) else 0)) := by
    by_cases hab : a=b
    · subst b; simp only [ite_true]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with N hN
      simp [mean,Complex.mul_conj,Complex.normSq_eq_norm_sq,f,norm_phase,hN.ne']
    · rw [ite_eq_right hab]
      have he : (2:ZMod D)^a = 2^b := (hS ha : v a=y).trans (hS hb : v b=y).symm
      have hd : (D:ℤ) ∣ (2:ℤ)^a-2^b := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ D).mp (by push_cast; exact he.symm)
      obtain ⟨w,hw⟩ := hd
      have hw0 : w≠0 := by
        rintro rfl; rw [mul_zero,sub_eq_zero] at hw
        exact hab ((pow_right_injective₀ (by decide : (0:ℤ)<2) (by decide : (2:ℤ)≠1)) hw)
      have hr : (2:ℝ)^a-2^b = (D:ℝ)*w := by exact_mod_cast hw
      apply (H (h*w) (mul_ne_zero hh0 hw0)).congr
      intro N; apply congrArg (fun g => mean g N); funext n
      dsimp only [f]; rw [phase_conj,← phase_add,pow_add,pow_add]
      congr 1; push_cast
      linear_combination -((h:ℝ)*2^n*x)*hr
  have energy : Tendsto (fun N => (∑ n ∈ range N, ‖G n‖^2)/(N:ℝ)) atTop (𝓝 (K:ℝ)) := by
    have H' := tendsto_finsetSum S fun a ha => tendsto_finsetSum S (fun b hb => corr a ha b hb)
    have hlim : (∑ a ∈ S, ∑ b ∈ S, if a=b then (1:ℂ) else 0) = K := by simp [hcard]
    have hc : Tendsto (fun N => ∑ a ∈ S, ∑ b ∈ S, mean (fun n => f (n+a)*conj (f (n+b))) N)
        atTop (𝓝 (K:ℂ)) := by rwa [hlim] at H'
    apply (Complex.continuous_re.continuousAt.tendsto.comp hc).congr
    intro N
    have e : (∑ a ∈ S, ∑ b ∈ S, mean (fun n => f (n+a)*conj (f (n+b))) N) =
        mean (fun n => G n * conj (G n)) N := by
      simp only [mean,G,map_sum,sum_mul,mul_sum,← sum_div]
      congr 1
      conv_lhs => rw [sum_comm]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl; intro i _
      rw [sum_comm]
    rw [Function.comp_apply,e,mean]
    simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_div,Complex.ofReal_re]
  have translates : Tendsto (fun N => mean G N - (K:ℂ)*mean f N) atTop (𝓝 0) := by
    have H' := tendsto_finsetSum S fun a _ => shifted_mean_error f (fun n => norm_phase _) a
    simpa only [sum_const_zero] using H'.congr (fun N => by
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul,hcard]; congr 1
      simp only [mean,G,← sum_div]; rw [sum_comm])
  have Hnear := (tendsto_zero_iff_norm_tendsto_zero.mp translates).eventually_lt_const
    (show 0 < (K:ℝ)*ε/2 by positivity)
  have Henergy := energy.eventually_lt_const (show (K:ℝ) < ((K:ℝ)*ε/2)^2 by
    nlinarith [mul_lt_mul_of_pos_left hKe hK0])
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ((Hnear.and Henergy).and (eventually_gt_atTop 0))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨h₁,h₂⟩,h₃⟩ := hN₀ N hN
  have he := (norm_mean_sq (f:=G) h₃).trans_lt h₂
  have hg : ‖mean G N‖ < (K:ℝ)*ε/2 := (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp he
  have ht := norm_sub_le (mean G N) (mean G N-(K:ℂ)*mean f N)
  rw [sub_sub_cancel,norm_mul,Complex.norm_natCast] at ht
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  apply (mul_lt_mul_iff_right₀ hK0).mp
  linarith

end NormalityChecker
