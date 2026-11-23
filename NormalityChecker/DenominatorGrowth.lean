module

public import NormalityChecker.PrimeCancellation
public import Mathlib.NumberTheory.LSeries.WeakPNT

public section

open Finset Filter Nat Real
open scoped Topology Asymptotics

namespace NormalityChecker

private abbrev num (k : ℕ) := (partialLogTwo k).num.natAbs
private def numeratorProduct (K : ℕ) := ∏ k ∈ Icc 1 K, num k

private lemma product_pos (K : ℕ) : 0 < numeratorProduct K :=
  Finset.prod_pos fun _ hk => partial_num_pos (mem_Icc.mp hk).1

/-- All small-prime powers fit in three copies of the shorter lcm. -/
lemma small_log_bound {n K p : ℕ} (hn : 0 < n) (h : n ≤ K^3)
    (hK : 2 ≤ K) (hp : p.Prime) (hs : p ≤ K^2) :
    p.log n ≤ 3 * p.log (K^2) := by
  let l := p.log (K^2)
  have hl : 0 < l := Nat.log_pos hp.one_lt hs
  have h₁ : K^2 < p^(l+1) := Nat.lt_pow_succ_log_self hp.one_lt _
  have h₂ : n < p^((l+1)*2) := by
    rw [pow_mul]
    have hpow : K^3 ≤ (K^2)^2 := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by decide)
    exact (h.trans hpow).trans_lt (Nat.pow_lt_pow_left h₁ (by decide))
  have := Nat.log_lt_of_lt_pow hn.ne' h₂
  change p.log n ≤ 3*l
  omega

/-- Each prime power in the full lcm is covered by the reduced denominator,
the small-prime allowance, or a short-prefix numerator. -/
private lemma lcm_cover {n K : ℕ} (hn : 0 < n) (hK : 2 ≤ K) (h : n ≤ K^3) :
    lcmUpto n ∣ logDen n * ((lcmUpto (K^2))^3 * numeratorProduct K) := by
  let M := K^2
  let B := lcmUpto M ^ 3
  let P := numeratorProduct K
  have hQ : 0 < logDen n := (logPrefix n).pos
  have hB : 0 < B := pow_pos (lcmUpto_pos _) _
  have hP : 0 < P := product_pos _
  apply (factorization_prime_le_iff_dvd (lcmUpto_ne_zero n) (by positivity)).mp
  intro p hp
  rw [factorization_lcmUpto _ hp, ← hp.pow_dvd_iff_le_factorization (by positivity)]
  by_cases hs : p ≤ M
  · have hd : p^(p.log n) ∣ B := by
      apply (hp.pow_dvd_iff_le_factorization hB.ne').mpr
      simp [B, Nat.factorization_pow, factorization_lcmUpto _ hp, M,
        small_log_bound hn h hK hp hs]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd P) _
  by_cases hpn : p ≤ n
  · have hMp : M < p := by omega
    have hhi : n < p^2 := h.trans_lt ((show K^3 ≤ M^2 by
      dsimp [M]; nlinarith [Nat.pow_le_pow_right (by omega : 0 < K) (show 3 ≤ 4 by decide)]).trans_lt
        (Nat.pow_lt_pow_left hMp (by decide)))
    have he : p.log n = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by simpa using hpn) hhi
    rw [he, pow_one]
    by_cases hdiv : p ∣ logDen n
    · exact dvd_mul_of_dvd_left hdiv _
    have hp2 : p ≠ 2 := by dsimp [M] at hMp; nlinarith
    have he' := prime_cancellation (a := 1) hp hp2 (by decide) (by simpa using hpn) hhi
    simp only [pow_one] at he'
    have hd : p ∣ num (n/p) := by by_contra hnot; exact hdiv (he'.mpr hnot)
    have hk : n/p ∈ Icc 1 K := by
      refine mem_Icc.mpr ⟨Nat.div_pos hpn hp.pos, ?_⟩
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      calc
        n ≤ K^3 := h
        _ = K*M := by dsimp [M]; ring
        _ < (K+1)*p := Nat.mul_lt_mul_of_lt_of_le (by omega) hMp.le hp.pos
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hd.trans (dvd_prod_of_mem num hk)) B) _
  · simp [Nat.log_of_lt (lt_of_not_ge hpn)]

lemma log_lcm_le (m : ℕ) : Real.log (lcmUpto m) ≤ 7*m := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  have hc : Real.log 4 + 4 ≤ 7 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  exact (Chebyshev.psi_le_const_mul_self (by positivity)).trans (mul_le_mul_of_nonneg_right hc (by positivity))

private lemma log_product_le (K : ℕ) : Real.log (numeratorProduct K) ≤ 8*(K:ℝ)^2 := by
  rw [numeratorProduct, Nat.cast_prod, Real.log_prod]
  · calc
      _ ≤ ∑ _k ∈ Icc 1 K, 8*(K:ℝ) := by
        apply sum_le_sum
        intro k hk
        have hk' := mem_Icc.mp hk
        have hpos : (0 : ℝ) < num k := by exact_mod_cast partial_num_pos hk'.1
        have h := Real.log_le_log hpos (show (num k : ℝ) ≤ ((lcmUpto k * 2^k : ℕ) : ℝ) by
          exact_mod_cast partial_num_bound k)
        push_cast at h
        rw [Real.log_mul (by positivity [lcmUpto_pos k]) (by positivity), Real.log_pow] at h
        have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        have hlog : (k:ℝ)*Real.log 2 ≤ k := by nlinarith
        have hle : (k:ℝ) ≤ K := by exact_mod_cast hk'.2
        linarith [log_lcm_le k]
      _ = _ := by simp [Nat.card_Icc]; ring
  · intro k hk
    exact_mod_cast (partial_num_pos (mem_Icc.mp hk).1).ne'

/-- Logarithmic loss of the common denominator when the shifted rational is reduced. -/
@[expose] noncomputable def logLoss (n : ℕ) : ℝ := Real.log ((lcmUpto n : ℝ) / logDen n)

theorem logLoss_nonneg (n : ℕ) : 0 ≤ logLoss n := by
  apply Real.log_nonneg
  rw [one_le_div (show (0:ℝ) < logDen n by exact_mod_cast (logPrefix n).pos)]
  exact_mod_cast Nat.le_of_dvd (lcmUpto_pos n) (logDen_dvd_lcm n)

/-- A finite bound, valid at every positive index with `n ≤ K³`. -/
theorem logLoss_le_of_le_cube {n K : ℕ} (hn : 0 < n) (hK : 2 ≤ K) (h : n ≤ K^3) :
    logLoss n ≤ 29*(K:ℝ)^2 := by
  have hQ : 0 < logDen n := (logPrefix n).pos
  have hD := lcmUpto_pos (K^2)
  have hP := product_pos K
  have hle := Nat.le_of_dvd (by positivity) (lcm_cover hn hK h)
  have h' : (lcmUpto n : ℝ) ≤ (logDen n : ℝ) * ((lcmUpto (K^2) : ℝ)^3 * numeratorProduct K) := by
    exact_mod_cast hle
  have hx : (0 : ℝ) < (lcmUpto n : ℝ) / logDen n := by positivity [lcmUpto_pos n]
  rw [mul_comm (logDen n : ℝ)] at h'
  have H := Real.log_le_log hx ((div_le_iff₀ (by positivity)).mpr h')
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at H
  have hM := log_lcm_le (K^2)
  push_cast at hM
  change Real.log _ ≤ _
  linarith [log_product_le K]

lemma root_cube (x : ℝ) (hx : 0 ≤ x) : (x^(1/3:ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]; norm_num

/-- Explicit constants in the denominator-loss bound. -/
theorem logLoss_le {n : ℕ} (hn : 8 ≤ n) : logLoss n ≤ 116*(n:ℝ)^(2/3:ℝ) := by
  let r := (n:ℝ)^(1/3:ℝ)
  let K := ⌈r⌉₊
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have he : r^3 = n := root_cube _ (by positivity)
  have hr : 1 < r := by
    by_contra! hh
    have := pow_le_pow_left₀ hr0 hh 3
    have hn' : (8:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hKr : r ≤ (K:ℝ) := Nat.le_ceil _
  have hK : 2 ≤ K := by exact_mod_cast (show (1:ℝ) < K by linarith)
  have hnK : n ≤ K^3 := by
    exact_mod_cast (show (n:ℝ) ≤ (K:ℝ)^3 by rw [← he]; exact pow_le_pow_left₀ hr0 hKr _)
  have hKupper : (K:ℝ) ≤ 2*r := by linarith [Nat.ceil_lt_add_one hr0]
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ K) hKupper 2
  have he2 : (n:ℝ)^(2/3:ℝ) = r^2 := by
    dsimp [r]; rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
  rw [he2]
  nlinarith [logLoss_le_of_le_cube (by omega : 0<n) hK hnK]

/-- Quantitative denominator loss in ordinary asymptotic notation. -/
theorem logLoss_isBigO : logLoss =O[atTop] (fun n : ℕ => (n:ℝ)^(2/3:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 116
  filter_upwards [eventually_ge_atTop 8] with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (logLoss_nonneg n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (2/3))] using logLoss_le hn

/-- The reduced denominator has the same exponential growth rate as the full lcm. -/
theorem tendsto_logDen_div : Tendsto (fun n : ℕ => Real.log (logDen n) / n) atTop (𝓝 1) := by
  have hr : (fun n : ℕ => (n:ℝ)^(2/3:ℝ)) =o[atTop] (fun n : ℕ => (n:ℝ)) := by
    apply Asymptotics.isLittleO_of_tendsto (fun n hn => by simp [hn])
    have H := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).comp tendsto_natCast_atTop_atTop
    apply H.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    change (n:ℝ)^(-(1/3):ℝ) = _ / _
    rw [show -(1/3:ℝ) = 2/3-1 by norm_num, Real.rpow_sub (by positivity), Real.rpow_one]
  have HL := (logLoss_isBigO.trans_isLittleO hr).tendsto_div_nhds_zero
  have H := Nat.tendsto_log_lcmUpto_div_atTop.sub HL
  rw [sub_zero] at H
  apply H.congr
  intro n
  have hQ : 0 < logDen n := (logPrefix n).pos
  change Real.log (lcmUpto n) / n - Real.log ((lcmUpto n : ℝ) / logDen n) / n = _
  rw [Real.log_div (by exact_mod_cast (lcmUpto_ne_zero n)) (by exact_mod_cast hQ.ne')]
  ring

/-- Even this exact denominator profile can coexist with convergence to zero. -/
theorem reciprocal_logDen :
    (∀ n, (1 / (logDen n : ℚ)).den = logDen n) ∧
    Tendsto (fun n => 1 / (logDen n : ℝ)) atTop (𝓝 0) := by
  refine ⟨fun n => by rw [one_div, Rat.inv_natCast_den_of_pos (show 0 < logDen n from (logPrefix n).pos)], ?_⟩
  have h : Tendsto (fun n => Real.log (logDen n)) atTop atTop := by
    apply (tendsto_logDen_div.pos_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_mul_cancel₀ _ (by positivity)
  have h' : Tendsto (fun n => (logDen n : ℝ)) atTop atTop := by
    apply (Real.tendsto_exp_atTop.comp h).congr
    intro n
    exact Real.exp_log (Nat.cast_pos.mpr (logPrefix n).pos)
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h'

end NormalityChecker
