module

public import NormalityChecker.FirstFrequency
public import NormalityChecker.LogShadow

/-! Complete dyadic shells suffice for a first-frequency discrepancy bound. -/
@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker

/-- A lower mean on complete dyadic shells controls every prefix for a
nonnegative observable. No partial-shell estimate is assumed. -/
theorem dyadic_prefix_lower (f : ℕ → ℝ) (pos : ∀ i, 0≤f i) {e : ℝ} (he : 0≤e)
    (shell : ∀ᶠ k : ℕ in atTop, e*(2:ℝ)^k≤∑ i∈range (2^k),f (2^k+i)) :
    ∃ C : ℝ, ∀ N : ℕ, e*N/2-C ≤ ∑ i∈range N,f i := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp shell
  let F (n : ℕ) := ∑ i∈range n,f i
  have mono : Monotone F := fun a b h => sum_le_sum_of_subset_of_nonneg (range_mono h) (fun n _ _ => pos n)
  have blocks (k : ℕ) (large : K≤k) : e*(2:ℝ)^k-e*2^K≤F (2^k) := by
    induction k,large using Nat.le_induction with
    | base => simpa [F] using sum_nonneg (s:=range (2^K)) (fun n _ => pos n)
    | succ k hk ih =>
      have split : F (2^(k+1))=F (2^k)+∑ i∈range (2^k),f (2^k+i) := by simp [F,pow_succ,mul_two,sum_range_add]
      rw [split,pow_succ]; linarith [hK k hk]
  refine ⟨e*2^K,fun N => ?_⟩
  by_cases large : 2^K≤N
  · let k := Nat.log 2 N
    have hn : N≠0 := (lt_of_lt_of_le (by positivity : 0<2^K) large).ne'
    have a := blocks k (Nat.le_log_of_pow_le (by decide) large)
    have m := mono (Nat.pow_log_le_self 2 hn)
    have hi : (N:ℝ)≤2^k*2 := by exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) N).le.trans_eq (pow_succ 2 k)
    change _≤F N; nlinarith only [a,m,mul_le_mul_of_nonneg_left hi he]
  · have small : (N:ℝ)≤2^K := by exact_mod_cast (le_of_not_ge large)
    have zero := sum_nonneg (s:=range N) (fun n _ => pos n)
    nlinarith only [zero,mul_le_mul_of_nonneg_left small he,mul_nonneg he (Nat.cast_nonneg (α:=ℝ) N)]

/-- One minus the real part of the first Fourier coefficient of the corrected
rational orbit at the start of the complete shell. -/
noncomputable def shadowShellEscape (k : ℕ) : ℝ :=
  let n := 2^k
  escapeAverage (fun i => (2:ℝ)^i*(logShadow n n:ℝ)) n

private lemma shell_transfer (n : ℕ) (i : ℕ) (hi : i≤n) :
    cosineEscape ((2:ℝ)^i*logShadow n n) ≤ cosineEscape ((2:ℝ)^(n+i)*Real.log 2)+2*Real.pi/(n+1) := by
  have tail := logTwo_corrected_tail (n:=n) (r:=n) le_rfl
  have diff := mul_le_mul_of_nonneg_left tail (pow_nonneg (by norm_num : 0≤(2:ℝ)) i)
  have e : |(2:ℝ)^(n+i)*Real.log 2-2^i*logShadow n n|≤1/(n+1) := by
    rw [show (2:ℝ)^(n+i)*Real.log 2-2^i*logShadow n n=2^i*(2^n*Real.log 2-logShadow n n) by rw [pow_add]; ring,abs_mul,abs_of_nonneg (pow_nonneg (by norm_num : 0≤(2:ℝ)) i)]
    apply diff.trans; rw [← mul_div_assoc,one_div_pow,mul_one_div]; gcongr; exact (div_le_one₀ (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) hi)
  let x := (2:ℝ)^(n+i)*Real.log 2
  let y := (2:ℝ)^i*logShadow n n
  have lip := Real.abs_cos_sub_cos_le (2*Real.pi*x) (2*Real.pi*y)
  rw [← mul_sub,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)] at lip
  have upper := (le_abs_self _).trans (lip.trans (mul_le_mul_of_nonneg_left e (by positivity)))
  rw [mul_one_div] at upper; change 1-Real.cos (2*Real.pi*y)≤1-Real.cos (2*Real.pi*x)+_; linarith

/-- A first-frequency deficit on every sufficiently late complete shell gives
an explicit bound on the asymptotic discrepancy of the logarithm. -/
theorem logTwo_discrepancy_of_dyadic_escape {ε : ℝ} (pos : 0<ε)
    (model : ∀ᶠ k : ℕ in atTop, ε≤shadowShellEscape k) :
    asymptoticDiscrepancy (Real.log 2) ≤ max (2/3) (1-ε/8) := by
  let x := Real.log 2
  let f (i : ℕ) := cosineEscape ((2:ℝ)^i*x)
  have nonneg (i : ℕ) : 0≤f i := sub_nonneg.mpr (Real.cos_le_one _)
  have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have den : ε/8≤transitionDensity x := by
    apply le_of_forall_lt_imp_le_of_dense; intro u hu
    let e := max 0 ((ε+8*u)/2)
    have en : 0≤e := le_max_left ..
    have gap : 0<ε-e := sub_pos.mpr (max_lt pos (by linarith))
    have gu : 8*u<e := lt_of_lt_of_le (by linarith : 8*u<(ε+8*u)/2) (le_max_right ..)
    have decay := ((tendsto_one_div_add_atTop_nhds_zero_nat.comp grow).const_mul (2*Real.pi)).eventually_lt_const (show 2*Real.pi*0<ε-e by simpa using gap)
    have shells : ∀ᶠ k : ℕ in atTop, e*(2:ℝ)^k≤∑ i∈range (2^k), f (2^k+i) := by
      filter_upwards [model,decay] with k hk hd
      let n : ℕ := 2^k
      have np : (0:ℝ)<n := by exact_mod_cast pow_pos (by decide : 0<2) k
      change ε≤(∑ i∈range n,cosineEscape (2^i*(logShadow n n:ℝ)))/n at hk
      have orig := (le_div_iff₀ np).mp hk
      have each := sum_le_sum (s:=range n) (fun i hi => shell_transfer n i (mem_range.mp hi).le)
      rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at each
      change 2*Real.pi*(1/((n:ℝ)+1))<ε-e at hd; rw [mul_one_div] at hd
      change _ ≤ ∑ i∈range n,f (n+i); rw [show (2:ℝ)^k=(n:ℝ) by simp [n]]
      change _≤(∑ i∈range n,f (n+i))+_ at each; nlinarith only [orig,each,mul_le_mul_of_nonneg_left hd.le np.le]
    obtain ⟨C,allN⟩ := dyadic_prefix_lower f nonneg en shells
    apply le_liminf_of_le (isCoboundedUnder_ge_of_le _ (fun N => (frequency_bounds (shift 2 x) (1/4) (3/4) N).2))
    have little := (tendsto_const_div_atTop_nhds_zero_nat (C+2)).eventually_lt_const (show 0<e/2-4*u by linarith)
    filter_upwards [little,eventually_gt_atTop 0] with N h hN
    have np : (0:ℝ)<N := by exact_mod_cast hN
    have F := (escapeAverage_transition_bounds x N).2
    change (∑ i∈range N,f i)/N ≤ 2/N+4*transitionFrequency x N at F
    rw [div_le_iff₀ np,add_mul,div_mul_cancel₀ _ np.ne'] at F
    rw [div_lt_iff₀ np] at h; change u≤transitionFrequency x N
    by_contra! bad; nlinarith only [F,h,allN N,mul_lt_mul_of_pos_right bad np]
  exact (sharp_asymptotic_discrepancy x).trans (max_le_max_left _ (sub_le_sub_left den _))

end NormalityChecker
