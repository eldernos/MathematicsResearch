module

public import NormalityChecker.Polylog
public import NormalityChecker.DenominatorGrowth

@[expose] public section
open Filter Finset Nat Real
open scoped Topology Asymptotics
namespace NormalityChecker.Polylog

private abbrev num (b s k : ℕ) := (partialSum b s k).num.natAbs
private def product (b s K : ℕ) := ∏ k ∈ Icc 1 K, num b s k

private lemma product_pos {b : ℕ} (hb : 0 < b) (s K : ℕ) : 0 < product b s K :=
  Finset.prod_pos fun _ hk => num_pos hb (mem_Icc.mp hk).1

private lemma cover {n K b s : ℕ} (hn : 0 < n) (hK : 2 ≤ K) (h : n ≤ K^3)
    (hb : 2 ≤ b) (hbK : b ≤ K^2) (hs : 0 < s) :
    (lcmUpto n)^s ∣ denominator b s n * ((lcmUpto (K^2))^(3*s) * (product b s K)^s) := by
  let M := K^2
  let B := (lcmUpto M)^(3*s)
  let P := (product b s K)^s
  have hQ : 0 < denominator b s n := (shifted b s n).pos
  have hB : 0 < B := pow_pos (lcmUpto_pos _) _
  have hP : 0 < P := pow_pos (product_pos (by omega) _ _) _
  change _ ∣ denominator b s n * (B*P)
  apply (factorization_prime_le_iff_dvd (pow_ne_zero s (lcmUpto_ne_zero n)) (by positivity)).mp
  intro p hp
  simp only [factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_lcmUpto _ hp]
  rw [← hp.pow_dvd_iff_le_factorization (by positivity)]
  by_cases hsmall : p ≤ M
  · have hd : p^(s*p.log n) ∣ B := by
      apply (hp.pow_dvd_iff_le_factorization hB.ne').mpr
      simp only [B,factorization_pow,Finsupp.smul_apply,smul_eq_mul,factorization_lcmUpto _ hp]
      nlinarith [Nat.mul_le_mul_left s (small_log_bound hn h hK hp hsmall)]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd P) _
  by_cases hpn : p ≤ n
  · have hMp : M < p := by omega
    have hhi : n < p^2 := h.trans_lt ((show K^3 ≤ M^2 by
      dsimp [M]; rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by decide)).trans_lt
        (Nat.pow_lt_pow_left hMp (by decide)))
    have he : p.log n = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by simpa using hpn) hhi
    rw [he,mul_one]
    by_cases hd : p^s ∣ denominator b s n
    · exact dvd_mul_of_dvd_left hd _
    have hpb : ¬ p ∣ b := Nat.not_dvd_of_pos_of_lt (by omega) (hbK.trans_lt hMp)
    have hc := prime_cancellation (a:=1) hp hpb hs (by decide) (by simpa using hpn) hhi
    simp only [one_mul,pow_one] at hc
    have hn' : p ∣ num b s (n/p) := by by_contra hn'; exact hd (hc.mpr hn')
    have hk : n/p ∈ Icc 1 K := by
      refine mem_Icc.mpr ⟨Nat.div_pos hpn hp.pos, ?_⟩
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      calc
        n ≤ K^3 := h
        _ = K*M := by dsimp [M]; ring
        _ < (K+1)*p := Nat.mul_lt_mul_of_lt_of_le (by omega) hMp.le hp.pos
    have hPP : p^s ∣ P := pow_dvd_pow_of_dvd (hn'.trans (dvd_prod_of_mem (num b s) hk)) _
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hPP B) _
  · simp [Nat.log_of_lt (lt_of_not_ge hpn)]

private lemma log_product {b : ℕ} (hb : 2 ≤ b) (s K : ℕ) :
    Real.log (product b s K) ≤ (7*s+b)*(K:ℝ)^2 := by
  rw [product, Nat.cast_prod, Real.log_prod]
  · calc
      _ ≤ ∑ _k ∈ Icc 1 K, (7*(s:ℝ)+b)*K := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hk₁,hk₂⟩ := mem_Icc.mp hk
        have h := Real.log_le_log (by exact_mod_cast num_pos (s:=s) (by omega : 0<b) hk₁ :
            (0:ℝ)<num b s k) (show (num b s k:ℝ) ≤ (((lcmUpto k)^s*b^k:ℕ):ℝ) by exact_mod_cast num_bound hb s k)
        push_cast at h
        rw [Real.log_mul (by positivity [lcmUpto_pos k]) (by positivity), Real.log_pow,Real.log_pow] at h
        have hlog : Real.log b ≤ (b:ℝ) := by linarith [Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<b)]
        calc
          _ ≤ _ := h
          _ ≤ (7*(s:ℝ)+b)*k := by nlinarith [mul_le_mul_of_nonneg_left (log_lcm_le k) (Nat.cast_nonneg (α:=ℝ) s),
              mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) k)]
          _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hk₂) (by positivity)
      _ = _ := by simp [Nat.card_Icc]; ring
  · intro k hk; exact_mod_cast (num_pos (s:=s) (by omega : 0<b) (mem_Icc.mp hk).1).ne'

noncomputable def loss (b s n : ℕ) := Real.log ((lcmUpto n:ℝ)^s / denominator b s n)

theorem loss_nonneg (b s n : ℕ) : 0 ≤ loss b s n := by
  apply Real.log_nonneg
  rw [one_le_div (by exact_mod_cast (shifted b s n).pos : (0:ℝ)<denominator b s n)]
  exact_mod_cast Nat.le_of_dvd (pow_pos (lcmUpto_pos n) s) (denominator_dvd b s n)

private lemma loss_cube {n K b s : ℕ} (hn : 0<n) (hK : 2≤K) (h : n≤K^3)
    (hb : 2≤b) (hbK : b≤K^2) (hs : 0<s) :
    loss b s n ≤ (s:ℝ)*(21+7*s+b)*(K:ℝ)^2 := by
  have hQ : 0 < denominator b s n := (shifted b s n).pos
  have hP := product_pos (by omega : 0<b) s K
  have hD := lcmUpto_pos (K^2)
  have hle := Nat.le_of_dvd (by positivity) (cover hn hK h hb hbK hs)
  have h' : (lcmUpto n:ℝ)^s ≤ (denominator b s n:ℝ)*
      ((lcmUpto (K^2):ℝ)^(3*s)*(product b s K:ℝ)^s) := by exact_mod_cast hle
  rw [mul_comm (denominator b s n:ℝ)] at h'
  have H := Real.log_le_log (by positivity [lcmUpto_pos n] : (0:ℝ)<(lcmUpto n:ℝ)^s/denominator b s n)
    ((div_le_iff₀ (by positivity)).mpr h')
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,Real.log_pow] at H
  have hM := log_lcm_le (K^2)
  push_cast at hM H
  change Real.log _ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hM (show (0:ℝ) ≤ 3*s by positivity),
    mul_le_mul_of_nonneg_left (log_product hb s K) (Nat.cast_nonneg (α:=ℝ) s)]

/-- Explicit loss bound, for a fixed radix and order, beyond a radix-dependent cutoff. -/
theorem loss_le {b s n : ℕ} (hb : 2≤b) (hn : b^3≤n) :
    loss b s n ≤ 4*(s:ℝ)*(21+7*s+b)*(n:ℝ)^(2/3:ℝ) := by
  by_cases hs : s=0
  · simp [hs,loss,denominator_zero_order]
  let r := (n:ℝ)^(1/3:ℝ)
  let K := ⌈r⌉₊
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have he : r^3 = n := root_cube _ (by positivity)
  have hb' : (b:ℝ) ≤ r := by
    apply le_of_not_gt
    intro hh
    have := pow_lt_pow_left₀ hh hr0 (by decide : 3≠0)
    rw [he] at this
    exact this.not_ge (by exact_mod_cast hn)
  have hKr : r ≤ (K:ℝ) := Nat.le_ceil _
  have hbK : b ≤ K := by exact_mod_cast hb'.trans hKr
  have hnK : n ≤ K^3 := by
    exact_mod_cast (show (n:ℝ) ≤ (K:ℝ)^3 by rw [← he]; exact pow_le_pow_left₀ hr0 hKr _)
  have hr1 : (1:ℝ) ≤ r := by
    have : (2:ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hKupper : (K:ℝ) ≤ 2*r := by linarith [Nat.ceil_lt_add_one hr0]
  have hC := loss_cube ((pow_pos (by omega : 0<b) 3).trans_le hn) (hb.trans hbK) hnK hb (hbK.trans (by nlinarith)) (Nat.pos_of_ne_zero hs)
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ K) hKupper 2
  have he2 : (n:ℝ)^(2/3:ℝ) = r^2 := by
    dsimp [r]; rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
  rw [he2]
  nlinarith [mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ s*(21+7*(s:ℝ)+b) by positivity)]

theorem loss_isBigO {b : ℕ} (hb : 2≤b) (s : ℕ) :
    loss b s =O[atTop] (fun n : ℕ => (n:ℝ)^(2/3:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (4*(s:ℝ)*(21+7*s+b))
  filter_upwards [eventually_ge_atTop (b^3)] with n hn
  simpa [Real.norm_eq_abs,abs_of_nonneg (loss_nonneg b s n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (2/3))] using loss_le (s:=s) hb hn

end NormalityChecker.Polylog
