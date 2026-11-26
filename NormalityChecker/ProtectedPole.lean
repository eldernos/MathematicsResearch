module

public import NormalityChecker.SurvivingGrid
public import Mathlib.Data.Nat.Factorization.Basic

/-! # Protected-pole arithmetic for all-prime polynomial normality (Track C1)

Kernel-checked rational denominator and `p`-adic pole-dominance theorems for series of the form
`W = ∑_{k ≥ 1} 1 / (p^(e k) · ℓ_k · b^(n k))`, where `p ∤ b` is a protected prime and `ℓ_k`
enumerates auxiliary off-radix primes:

1. **Auxiliary prime survival (`shifted_prefix_aux_prime_dvd_den`).**
   For every `k ≥ 1`, if `ℓ_k` is prime, coprime to `b`, `p`, and all earlier `ℓ_j` (`1 ≤ j < k`),
   then for every shift `N ≥ n_k`, `ℓ_k` divides the reduced denominator of `b^N U_k`, where
   `U_k = ∑_{1 ≤ j ≤ k} 1 / (p^(e j) · ℓ_j · b^(n j))`.
   (Only the newest prime `ℓ_k` of the prefix `U_k` is covered; that every earlier `ℓ_i` persists
   in later prefixes is a written argument.)

2. **Protected prime-power depth (`shifted_prefix_protected_prime_pow_dvd_den`).**
   If `e` is strictly increasing on `1..k` and `p` does not divide `b` or any `ℓ_j` (`1 ≤ j ≤ k`),
   then for every shift `N ≥ n_k`, `p^(e k)` divides the reduced denominator of `b^N U_k` and
   `p^(e k + 1)` does not.

3. **Truncated polynomial pole dominance (`truncated_poly_pole_dvd_den`).**
   Given `U = u / (p^(e₁) · Q₁)` and `V = v / (p^(e₂) · Q₂)` (`p ∤ u, v, Q₁, Q₂`), an integer
   polynomial `∑_{d ≤ r} a_d X^d` (`a_r ≠ 0`), and a truncation level `1 ≤ l ≤ r`, define
     `F_l(U, V) = ∑_{d=0}^r a_d ∑_{j=0}^{min d l} C(d, j) U^(d - j) V^j`.
   Let `g = padicValNat p (a_r.natAbs * Nat.choose r l)`. Whenever `g < e₁` and `g < e₂ - e₁`,
   the unique leading term `(d, j) = (r, l)` dominates every other term `p`-adically, and
     `p^(l * e₂ + (r - l) * e₁ - g) ∣ (F_l(U, V)).den`.
   For `e_k = k²` this yields protected pole depth `l k² + (r - l)(k - 1)² - O_P(1)` in
   Track C1, the arithmetic core for `SurvivingGrid.stride_order` and `PrimePowerGrid.crt_period_count`.
-/

@[expose] public section

open Finset

namespace NormalityChecker.ProtectedPole

/-! ### Helper lemmas connecting rational denominators and prime powers -/

/-- If `q = num / (p^d * M)` with `p` prime, `M > 0`, and `p^(v+1) ∤ num` (`v ≤ d`),
then `p^(d - v) ∣ q.den`. -/
theorem prime_pow_dvd_rat_den_of_repr {p d v : ℕ} (hp : p.Prime) {num : ℤ} {M : ℕ}
    (hMpos : 0 < M) (hvd : v ≤ d) (hnum : ¬ (p : ℤ) ^ (v + 1) ∣ num)
    {q : ℚ} (hq : q = (num : ℚ) / ((p ^ d * M : ℕ) : ℚ)) :
    p ^ (d - v) ∣ q.den := by
  have hden_ne : ((p ^ d * M : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (pow_pos hp.pos d) hMpos).ne'
  have hcross : (q.num : ℤ) * ((p ^ d * M : ℕ) : ℤ) = num * (q.den : ℤ) := by
    have hq_eq : (q.num : ℚ) / (q.den : ℚ) = (num : ℚ) / ((p ^ d * M : ℕ) : ℚ) := by
      rw [Rat.num_div_den, hq]
    have hqd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hmul : (q.num : ℚ) * ((p ^ d * M : ℕ) : ℚ) = (num : ℚ) * (q.den : ℚ) := by
      rwa [div_eq_div_iff hqd hden_ne] at hq_eq
    exact_mod_cast hmul
  -- Count `p`-factors in `q.den`: if `p^(d - v) ∤ q.den`, then `v_p(q.den) < d - v`,
  -- so `v_p(num * q.den) ≤ v + (d - v - 1) < d ≤ v_p(q.num * p^d * M)`, contradiction.
  by_contra hndvd
  have hlt : q.den.factorization p < d - v := by
    by_contra hge
    push Not at hge
    apply hndvd
    exact (hp.pow_dvd_iff_le_factorization q.den_nz).mpr hge
  have hnum_lt : num.natAbs.factorization p ≤ v := by
    by_contra hgt
    push Not at hgt
    apply hnum
    have hnat : p ^ (v + 1) ∣ num.natAbs := by
      by_cases h0 : num = 0
      · subst h0; simp
      · exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr h0)).mpr (by omega)
    exact Int.natCast_dvd.mpr hnat
  have hnum_ne : num ≠ 0 := by
    intro h0; subst h0; exact hnum (dvd_zero _)
  have hqnum_ne : q.num ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcross
    have : num * (q.den : ℤ) ≠ 0 := mul_ne_zero hnum_ne (by exact_mod_cast q.den_nz)
    exact this hcross.symm
  have habs : q.num.natAbs * (p ^ d * M) = num.natAbs * q.den := by
    have := congrArg Int.natAbs hcross
    simpa [Int.natAbs_mul] using this
  have hfac := congrArg (fun n : ℕ => n.factorization p) habs
  have hL : (q.num.natAbs * (p ^ d * M)).factorization p =
      q.num.natAbs.factorization p + (d + M.factorization p) := by
    rw [Nat.factorization_mul (Int.natAbs_ne_zero.mpr hqnum_ne)
        (Nat.mul_pos (pow_pos hp.pos d) hMpos).ne',
      Nat.factorization_mul (pow_pos hp.pos d).ne' hMpos.ne',
      Finsupp.add_apply, Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same]
  have hR : (num.natAbs * q.den).factorization p =
      num.natAbs.factorization p + q.den.factorization p := by
    rw [Nat.factorization_mul (Int.natAbs_ne_zero.mpr hnum_ne) q.den_nz, Finsupp.add_apply]
  rw [hL, hR] at hfac
  omega

/-- Upper bound on `p`-adic denominator depth: if `q = num / (p^d * M)` with `p ∤ M`,
then `¬ p^(d + 1) ∣ q.den`. -/
theorem not_prime_pow_succ_dvd_rat_den_of_repr {p d : ℕ} (hp : p.Prime) {num : ℤ} {M : ℕ}
    (hM : ¬ p ∣ M)
    {q : ℚ} (hq : q = (num : ℚ) / ((p ^ d * M : ℕ) : ℚ)) :
    ¬ p ^ (d + 1) ∣ q.den := by
  have hdvd : q.den ∣ p ^ d * M := by
    rw [hq]
    have h1 := Rat.den_dvd num (p ^ d * M)
    have hrew : (num : ℚ) / ((p ^ d * M : ℕ) : ℚ) = Rat.divInt num (p ^ d * M) := by
      rw [Rat.divInt_eq_div]; push_cast; rfl
    rw [hrew]
    exact Int.natCast_dvd_natCast.mp (by simpa using h1)
  intro hbig
  have htrans : p ^ (d + 1) ∣ p ^ d * M := hbig.trans hdvd
  rw [pow_succ] at htrans
  have hcancel : p ∣ M := (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos d)).mp htrans
  exact hM hcancel

/-! ### Part 1 & 2: Shifted prefixes of `W = ∑ 1 / (p^(e j) · ℓ_j · b^(n j))` -/

/-- Individual term `1 / (p^(e j) · ℓ_j · b^(n j))` of the protected-pole series `W`. -/
def protectedTerm (b p : ℕ) (e ℓ n : ℕ → ℕ) (j : ℕ) : ℚ :=
  ((p : ℚ) ^ e j * (ℓ j : ℚ) * (b : ℚ) ^ n j)⁻¹

/-- `k`-th prefix `U_k = ∑_{1 ≤ j ≤ k} 1 / (p^(e j) · ℓ_j · b^(n j))`. -/
def protectedPrefix (b p : ℕ) (e ℓ n : ℕ → ℕ) (k : ℕ) : ℚ :=
  ∑ j ∈ Icc 1 k, protectedTerm b p e ℓ n j

private lemma prime_not_dvd_prod {p : ℕ} (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, ¬ p ∣ f i) : ¬ p ∣ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [hp.not_dvd_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with h1 | h2
    · exact hf a (mem_insert_self a s) h1
    · exact ih (fun i hi => hf i (mem_insert_of_mem hi)) h2

/-- **Auxiliary prime survival (Track C1).**
If `ℓ k` is prime and coprime to `b`, `p`, and all earlier `ℓ j` (`1 ≤ j < k`), and
`n j ≤ N` for all `1 ≤ j ≤ k`, then `ℓ k` divides the reduced denominator of `b^N U_k`. -/
theorem shifted_prefix_aux_prime_dvd_den {b p : ℕ} (hb : 0 < b) (hp : 0 < p)
    (e ℓ n : ℕ → ℕ) {k N : ℕ} (hk : 1 ≤ k)
    (hℓ_pos : ∀ j ∈ Icc 1 k, 0 < ℓ j)
    (hℓk_prime : (ℓ k).Prime)
    (hℓk_b : ¬ ℓ k ∣ b)
    (hℓk_p : ¬ ℓ k ∣ p)
    (hℓk_prev : ∀ j ∈ Ico 1 k, ¬ ℓ k ∣ ℓ j)
    (hnN : ∀ j ∈ Icc 1 k, n j ≤ N) :
    ℓ k ∣ ((b : ℚ) ^ N * protectedPrefix b p e ℓ n k).den := by
  let E : ℕ := (Icc 1 k).sup e
  let P_prev : ℕ := ∏ j ∈ Ico 1 k, ℓ j
  let M : ℕ := p ^ E * P_prev
  have hP_pos : 0 < P_prev := Finset.prod_pos (fun j hj =>
    hℓ_pos j (mem_Icc.mpr ⟨(mem_Ico.mp hj).1, (mem_Ico.mp hj).2.le⟩))
  have hM_pos : 0 < M := Nat.mul_pos (pow_pos hp E) hP_pos
  have hℓk_P : ¬ ℓ k ∣ P_prev := prime_not_dvd_prod hℓk_prime (Ico 1 k) ℓ hℓk_prev
  have hℓk_M : ¬ ℓ k ∣ M := by
    intro hdvd
    rcases hℓk_prime.dvd_mul.mp hdvd with h1 | h2
    · exact hℓk_p (hℓk_prime.dvd_of_dvd_pow h1)
    · exact hℓk_P h2
  -- Write `b^N U_k = num / (ℓ k * M)` where `num ≡ b^(N - n k) * p^(E - e k) * P_prev (mod ℓ k)`.
  let cPrev : ℕ → ℤ := fun j =>
    (b : ℤ) ^ (N - n j) * (p : ℤ) ^ (E - e j) * ((P_prev / ℓ j : ℕ) : ℤ)
  let num : ℤ :=
    (ℓ k : ℤ) * (∑ j ∈ Ico 1 k, cPrev j) +
      (b : ℤ) ^ (N - n k) * (p : ℤ) ^ (E - e k) * (P_prev : ℤ)
  have hsplit : Icc 1 k = insert k (Ico 1 k) := by
    ext j; simp only [mem_Icc, mem_insert, mem_Ico]; omega
  have hk_not : k ∉ Ico 1 k := by simp
  have hrepr : (b : ℚ) ^ N * protectedPrefix b p e ℓ n k =
      (num : ℚ) / (((ℓ k) ^ 1 * M : ℕ) : ℚ) := by
    unfold protectedPrefix
    rw [hsplit, Finset.sum_insert hk_not, mul_add, Finset.mul_sum]
    have hM_ne : (M : ℚ) ≠ 0 := by exact_mod_cast hM_pos.ne'
    have hℓk_ne : (ℓ k : ℚ) ≠ 0 := by exact_mod_cast hℓk_prime.pos.ne'
    have hb_ne : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    have hterm_k : (b : ℚ) ^ N * protectedTerm b p e ℓ n k =
        ((b : ℚ) ^ (N - n k) * (p : ℚ) ^ (E - e k) * (P_prev : ℚ)) / ((ℓ k : ℚ) * (M : ℚ)) := by
      unfold protectedTerm
      have hEk : e k ≤ E := Finset.le_sup (f := e) (mem_Icc.mpr ⟨hk, le_rfl⟩)
      have hnk : n k ≤ N := hnN k (mem_Icc.mpr ⟨hk, le_rfl⟩)
      have hpow_b : (b : ℚ) ^ N = (b : ℚ) ^ (N - n k) * (b : ℚ) ^ n k := by
        rw [← pow_add, Nat.sub_add_cancel hnk]
      have hpow_p : (p : ℚ) ^ E = (p : ℚ) ^ (E - e k) * (p : ℚ) ^ e k := by
        rw [← pow_add, Nat.sub_add_cancel hEk]
      have hM_eq : (M : ℚ) = (p : ℚ) ^ E * (P_prev : ℚ) := by unfold M; push_cast; rfl
      rw [hpow_b, hM_eq, hpow_p]
      have hP_ne : (P_prev : ℚ) ≠ 0 := by exact_mod_cast hP_pos.ne'
      field_simp [hb_ne, hp_ne, hℓk_ne, hP_ne]
    have hterm_prev : ∀ j ∈ Ico 1 k,
        (b : ℚ) ^ N * protectedTerm b p e ℓ n j =
          ((ℓ k : ℚ) * (cPrev j : ℚ)) / ((ℓ k : ℚ) * (M : ℚ)) := by
      intro j hj
      unfold protectedTerm cPrev
      have hjIcc : j ∈ Icc 1 k := mem_Icc.mpr ⟨(mem_Ico.mp hj).1, (mem_Ico.mp hj).2.le⟩
      have hEj : e j ≤ E := Finset.le_sup (f := e) hjIcc
      have hnj : n j ≤ N := hnN j hjIcc
      have hℓj_pos : 0 < ℓ j := hℓ_pos j hjIcc
      have hℓj_ne : (ℓ j : ℚ) ≠ 0 := by exact_mod_cast hℓj_pos.ne'
      have hdvd_P : ℓ j ∣ P_prev := Finset.dvd_prod_of_mem ℓ hj
      have hP_eq : ((P_prev / ℓ j : ℕ) : ℚ) * (ℓ j : ℚ) = (P_prev : ℚ) := by
        exact_mod_cast Nat.div_mul_cancel hdvd_P
      have hpow_b : (b : ℚ) ^ N = (b : ℚ) ^ (N - n j) * (b : ℚ) ^ n j := by
        rw [← pow_add, Nat.sub_add_cancel hnj]
      have hpow_p : (p : ℚ) ^ E = (p : ℚ) ^ (E - e j) * (p : ℚ) ^ e j := by
        rw [← pow_add, Nat.sub_add_cancel hEj]
      have hM_eq : (M : ℚ) = (p : ℚ) ^ E * (P_prev : ℚ) := by unfold M; push_cast; rfl
      rw [hpow_b, hM_eq, hpow_p, ← hP_eq]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      have hdiv_ne : ((P_prev / ℓ j : ℕ) : ℚ) ≠ 0 := by
        intro h0
        have : P_prev / ℓ j = 0 := by exact_mod_cast h0
        rw [this, Nat.cast_zero, zero_mul] at hP_eq
        exact (by exact_mod_cast hP_pos.ne' : (P_prev : ℚ) ≠ 0) hP_eq.symm
      field_simp [hb_ne, hp_ne, hℓk_ne, hℓj_ne, hdiv_ne]
    rw [hterm_k, Finset.sum_congr rfl hterm_prev, ← Finset.sum_div, ← Finset.mul_sum, ← add_div]
    simp only [num, pow_one, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_sum]
    ring
  have hnot_dvd : ¬ (ℓ k : ℤ) ^ (0 + 1) ∣ num := by
    rw [zero_add, pow_one]
    intro hdvd
    have hfirst : (ℓ k : ℤ) ∣ (ℓ k : ℤ) * (∑ j ∈ Ico 1 k, cPrev j) := dvd_mul_right _ _
    have hrem : (ℓ k : ℤ) ∣ (b : ℤ) ^ (N - n k) * (p : ℤ) ^ (E - e k) * (P_prev : ℤ) := by
      have hsub := dvd_sub hdvd hfirst
      simpa [num] using hsub
    have hnat : ℓ k ∣ b ^ (N - n k) * p ^ (E - e k) * P_prev := by
      exact_mod_cast hrem
    rcases hℓk_prime.dvd_mul.mp hnat with hbp | hP
    · rcases hℓk_prime.dvd_mul.mp hbp with hb' | hp'
      · exact hℓk_b (hℓk_prime.dvd_of_dvd_pow hb')
      · exact hℓk_p (hℓk_prime.dvd_of_dvd_pow hp')
    · exact hℓk_P hP
  have hd := prime_pow_dvd_rat_den_of_repr hℓk_prime hM_pos (by omega : 0 ≤ 1) hnot_dvd hrepr
  simpa using hd

/-- **Exact protected prime-power depth of `W`'s shifted prefixes (Track C1).**
If `p` is prime, `p ∤ b`, `p ∤ ℓ j` for `1 ≤ j ≤ k`, `e j < e k` for `1 ≤ j < k`, and
`n j ≤ N` for `1 ≤ j ≤ k`, then `p^(e k)` divides the reduced denominator of `b^N U_k`,
and `p^(e k + 1)` does not. -/
theorem shifted_prefix_protected_prime_pow_dvd_den {b p : ℕ} (hb : 0 < b) (hp : p.Prime)
    (e ℓ n : ℕ → ℕ) {k N : ℕ} (hk : 1 ≤ k)
    (hpb : ¬ p ∣ b)
    (hℓ_pos : ∀ j ∈ Icc 1 k, 0 < ℓ j)
    (hpℓ : ∀ j ∈ Icc 1 k, ¬ p ∣ ℓ j)
    (he_max : ∀ j ∈ Ico 1 k, e j < e k)
    (hnN : ∀ j ∈ Icc 1 k, n j ≤ N) :
    p ^ e k ∣ ((b : ℚ) ^ N * protectedPrefix b p e ℓ n k).den ∧
      ¬ p ^ (e k + 1) ∣ ((b : ℚ) ^ N * protectedPrefix b p e ℓ n k).den := by
  let M : ℕ := ∏ j ∈ Icc 1 k, ℓ j
  have hM_pos : 0 < M := Finset.prod_pos (fun j hj => hℓ_pos j hj)
  have hpM : ¬ p ∣ M := prime_not_dvd_prod hp (Icc 1 k) ℓ hpℓ
  let cPrev : ℕ → ℤ := fun j =>
    (b : ℤ) ^ (N - n j) * (p : ℤ) ^ (e k - e j - 1) * ((M / ℓ j : ℕ) : ℤ)
  let num : ℤ :=
    (p : ℤ) * (∑ j ∈ Ico 1 k, cPrev j) + (b : ℤ) ^ (N - n k) * ((M / ℓ k : ℕ) : ℤ)
  have hsplit : Icc 1 k = insert k (Ico 1 k) := by
    ext j; simp only [mem_Icc, mem_insert, mem_Ico]; omega
  have hk_not : k ∉ Ico 1 k := by simp
  have hrepr : (b : ℚ) ^ N * protectedPrefix b p e ℓ n k =
      (num : ℚ) / ((p ^ e k * M : ℕ) : ℚ) := by
    unfold protectedPrefix
    rw [hsplit, Finset.sum_insert hk_not, mul_add, Finset.mul_sum]
    have hb_ne : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have hM_ne : (M : ℚ) ≠ 0 := by exact_mod_cast hM_pos.ne'
    have hterm_k : (b : ℚ) ^ N * protectedTerm b p e ℓ n k =
        ((b : ℚ) ^ (N - n k) * ((M / ℓ k : ℕ) : ℚ)) / ((p : ℚ) ^ e k * (M : ℚ)) := by
      unfold protectedTerm
      have hkIcc : k ∈ Icc 1 k := mem_Icc.mpr ⟨hk, le_rfl⟩
      have hnk : n k ≤ N := hnN k hkIcc
      have hdvd_M : ℓ k ∣ M := Finset.dvd_prod_of_mem ℓ hkIcc
      have hM_eq : ((M / ℓ k : ℕ) : ℚ) * (ℓ k : ℚ) = (M : ℚ) := by
        exact_mod_cast Nat.div_mul_cancel hdvd_M
      have hpow_b : (b : ℚ) ^ N = (b : ℚ) ^ (N - n k) * (b : ℚ) ^ n k := by
        rw [← pow_add, Nat.sub_add_cancel hnk]
      have hℓk_ne : (ℓ k : ℚ) ≠ 0 := by exact_mod_cast (hℓ_pos k hkIcc).ne'
      rw [hpow_b, ← hM_eq]
      have hdiv_ne : ((M / ℓ k : ℕ) : ℚ) ≠ 0 := by
        intro h0
        have : M / ℓ k = 0 := by exact_mod_cast h0
        rw [this, Nat.cast_zero, zero_mul] at hM_eq
        exact hM_ne hM_eq.symm
      field_simp [hb_ne, hp_ne, hℓk_ne, hdiv_ne]
    have hterm_prev : ∀ j ∈ Ico 1 k,
        (b : ℚ) ^ N * protectedTerm b p e ℓ n j =
          ((p : ℚ) * (cPrev j : ℚ)) / ((p : ℚ) ^ e k * (M : ℚ)) := by
      intro j hj
      unfold protectedTerm cPrev
      have hjIcc : j ∈ Icc 1 k := mem_Icc.mpr ⟨(mem_Ico.mp hj).1, (mem_Ico.mp hj).2.le⟩
      have hlt : e j < e k := he_max j hj
      have hnj : n j ≤ N := hnN j hjIcc
      have hdvd_M : ℓ j ∣ M := Finset.dvd_prod_of_mem ℓ hjIcc
      have hM_eq : ((M / ℓ j : ℕ) : ℚ) * (ℓ j : ℚ) = (M : ℚ) := by
        exact_mod_cast Nat.div_mul_cancel hdvd_M
      have hpow_b : (b : ℚ) ^ N = (b : ℚ) ^ (N - n j) * (b : ℚ) ^ n j := by
        rw [← pow_add, Nat.sub_add_cancel hnj]
      have hpow_p : (p : ℚ) ^ e k = (p : ℚ) * (p : ℚ) ^ (e k - e j - 1) * (p : ℚ) ^ e j := by
        rw [← pow_succ', ← pow_add]
        congr 1; omega
      have hℓj_ne : (ℓ j : ℚ) ≠ 0 := by exact_mod_cast (hℓ_pos j hjIcc).ne'
      rw [hpow_b, hpow_p, ← hM_eq]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      have hdiv_ne : ((M / ℓ j : ℕ) : ℚ) ≠ 0 := by
        intro h0
        have : M / ℓ j = 0 := by exact_mod_cast h0
        rw [this, Nat.cast_zero, zero_mul] at hM_eq
        exact hM_ne hM_eq.symm
      field_simp [hb_ne, hp_ne, hℓj_ne, hdiv_ne]
    rw [hterm_k, Finset.sum_congr rfl hterm_prev, ← Finset.sum_div, ← Finset.mul_sum, ← add_div]
    simp only [num, Nat.cast_mul, Nat.cast_pow, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_sum]
    ring
  have hnot_dvd : ¬ (p : ℤ) ^ (0 + 1) ∣ num := by
    rw [zero_add, pow_one]
    intro hdvd
    have hfirst : (p : ℤ) ∣ (p : ℤ) * (∑ j ∈ Ico 1 k, cPrev j) := dvd_mul_right _ _
    have hrem : (p : ℤ) ∣ (b : ℤ) ^ (N - n k) * ((M / ℓ k : ℕ) : ℤ) := by
      have hsub := dvd_sub hdvd hfirst
      simpa [num] using hsub
    have hnat : p ∣ b ^ (N - n k) * (M / ℓ k) := by exact_mod_cast hrem
    rcases hp.dvd_mul.mp hnat with hb' | hm'
    · exact hpb (hp.dvd_of_dvd_pow hb')
    · exact hpM (hm'.trans (Nat.div_dvd_of_dvd (Finset.dvd_prod_of_mem ℓ (mem_Icc.mpr ⟨hk, le_rfl⟩))))
  exact ⟨by simpa using prime_pow_dvd_rat_den_of_repr hp hM_pos (Nat.zero_le _) hnot_dvd hrepr,
    not_prime_pow_succ_dvd_rat_den_of_repr hp hpM hrepr⟩

/-! ### Part 3: Truncated polynomial pole dominance (Track C1) -/

/-- Truncated binomial expansion of `∑_{d ≤ r} a_d (U + V)^d` retaining terms with at most `l`
factors of `V`. -/
def truncatedPoly (a : ℕ → ℤ) (r l : ℕ) (U V : ℚ) : ℚ :=
  ∑ d ∈ range (r + 1), (a d : ℚ) * ∑ j ∈ range (min d l + 1),
    (Nat.choose d j : ℚ) * U ^ (d - j) * V ^ j

/-- **Truncated polynomial pole dominance (Track C1 core).**
Let `U = u / (p^(e₁) · Q₁)` and `V = v / (p^(e₂) · Q₂)` with `p` prime and `p ∤ u, v, Q₁, Q₂`.
For any integer polynomial `∑_{d ≤ r} a_d X^d` with `a_r ≠ 0`, any truncation level `1 ≤ l ≤ r`,
and `g = (a_r.natAbs * Nat.choose r l).factorization p`:
whenever `g < e₁` and `g < e₂ - e₁`, the unique leading term `(d, j) = (r, l)` dominates every
other term `p`-adically, so
`p^(l * e₂ + (r - l) * e₁ - g) ∣ (truncatedPoly a r l U V).den`. -/
theorem truncated_poly_pole_dvd_den {p e₁ e₂ Q₁ Q₂ r l : ℕ} (hp : p.Prime)
    {u v : ℤ} (hu : ¬ (p : ℤ) ∣ u) (hv : ¬ (p : ℤ) ∣ v)
    (hQ₁ : ¬ p ∣ Q₁) (hQ₂ : ¬ p ∣ Q₂) (hQ₁_pos : 0 < Q₁) (hQ₂_pos : 0 < Q₂)
    (hl1 : 1 ≤ l) (hlr : l ≤ r)
    (a : ℕ → ℤ) (har : a r ≠ 0)
    {U V : ℚ}
    (hU : U = (u : ℚ) / ((p ^ e₁ * Q₁ : ℕ) : ℚ))
    (hV : V = (v : ℚ) / ((p ^ e₂ * Q₂ : ℕ) : ℚ))
    (he₁ : ((a r).natAbs * Nat.choose r l).factorization p < e₁)
    (hgap : ((a r).natAbs * Nat.choose r l).factorization p < e₂ - e₁) :
    p ^ (l * e₂ + (r - l) * e₁ - ((a r).natAbs * Nat.choose r l).factorization p) ∣
      (truncatedPoly a r l U V).den := by
  set g : ℕ := ((a r).natAbs * Nat.choose r l).factorization p
  set D : ℕ := l * e₂ + (r - l) * e₁
  set M : ℕ := Q₁ ^ r * Q₂ ^ r
  have hM_pos : 0 < M := Nat.mul_pos (pow_pos hQ₁_pos r) (pow_pos hQ₂_pos r)
  have hpM : ¬ p ∣ M := by
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with h1 | h2
    · exact hQ₁ (hp.dvd_of_dvd_pow h1)
    · exact hQ₂ (hp.dvd_of_dvd_pow h2)
  have he_le : e₁ ≤ e₂ := by omega
  -- For every `(d, j)` with `d ≤ r`, `j ≤ min d l`, `(d, j) ≠ (r, l)`, its pole depth
  -- `j * e₂ + (d - j) * e₁` is at most `D - (g + 1)`.
  have hdepth_le : ∀ d j, d ≤ r → j ≤ min d l → (d, j) ≠ (r, l) →
      j * e₂ + (d - j) * e₁ + (g + 1) ≤ D := by
    intro d j hdr hjl hne
    have hjd : j ≤ d := hjl.trans (min_le_left d l)
    have hjll : j ≤ l := hjl.trans (min_le_right d l)
    by_cases hdr_eq : d = r
    · rw [hdr_eq] at hne hjd ⊢
      have hjlt : j < l := by
        rcases hjll.lt_or_eq with h | h
        · exact h
        · exfalso; exact hne (Prod.ext rfl h)
      -- Difference is `(l - j) * (e₂ - e₁) ≥ e₂ - e₁ ≥ g + 1`.
      have h1 : (l - j) * e₂ + (r - l) * e₁ = (l - j) * (e₂ - e₁) + (l - j) * e₁ + (r - l) * e₁ := by
        have : e₂ = (e₂ - e₁) + e₁ := by omega
        calc (l - j) * e₂ + (r - l) * e₁
            = (l - j) * ((e₂ - e₁) + e₁) + (r - l) * e₁ := by rw [← this]
          _ = (l - j) * (e₂ - e₁) + (l - j) * e₁ + (r - l) * e₁ := by ring
      have h2 : D = j * e₂ + (l - j) * e₂ + (r - l) * e₁ := by
        change l * e₂ + (r - l) * e₁ = _
        have : l = j + (l - j) := by omega
        calc l * e₂ + (r - l) * e₁ = (j + (l - j)) * e₂ + (r - l) * e₁ := by rw [← this]
          _ = j * e₂ + (l - j) * e₂ + (r - l) * e₁ := by ring
      have h3 : (l - j) * e₁ + (r - l) * e₁ = (r - j) * e₁ := by
        rw [← add_mul]; congr 1; omega
      have h4 : g + 1 ≤ (l - j) * (e₂ - e₁) := by
        have hlj : 1 ≤ l - j := by omega
        calc g + 1 ≤ 1 * (e₂ - e₁) := by omega
          _ ≤ (l - j) * (e₂ - e₁) := Nat.mul_le_mul_right _ hlj
      omega
    · have hdlt : d < r := lt_of_le_of_ne hdr hdr_eq
      -- Difference is `(l - j) * (e₂ - e₁) + (r - d) * e₁ ≥ e₁ ≥ g + 1`.
      have hdiff : j * e₂ + (d - j) * e₁ + ((l - j) * (e₂ - e₁) + (r - d) * e₁) = D := by
        change j * e₂ + (d - j) * e₁ + ((l - j) * (e₂ - e₁) + (r - d) * e₁) = l * e₂ + (r - l) * e₁
        zify [hjd, hjll, hlr, he_le, hdr]
        ring
      have hge : g + 1 ≤ (l - j) * (e₂ - e₁) + (r - d) * e₁ := by
        have hrd : 1 ≤ r - d := by omega
        have : e₁ ≤ (r - d) * e₁ := Nat.le_mul_of_pos_left e₁ (by omega)
        omega
      omega
  have hterm_val : ∀ d j, d ≤ r → j ≤ min d l →
      (Nat.choose d j : ℚ) * U ^ (d - j) * V ^ j =
        (((Nat.choose d j : ℤ) * u ^ (d - j) * v ^ j *
            (p : ℤ) ^ (D - (j * e₂ + (d - j) * e₁)) *
            (Q₁ : ℤ) ^ (r - (d - j)) * (Q₂ : ℤ) ^ (r - j) : ℤ) : ℚ) /
          ((p ^ D * M : ℕ) : ℚ) := by
    intro d j hdr hjl
    have hjd : j ≤ d := hjl.trans (min_le_left d l)
    have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have hQ₁_ne : (Q₁ : ℚ) ≠ 0 := by exact_mod_cast hQ₁_pos.ne'
    have hQ₂_ne : (Q₂ : ℚ) ≠ 0 := by exact_mod_cast hQ₂_pos.ne'
    have hdepth : j * e₂ + (d - j) * e₁ ≤ D := by
      by_cases hne : (d, j) = (r, l)
      · rcases Prod.ext_iff.mp hne with ⟨rfl, rfl⟩; exact le_rfl
      · have := hdepth_le d j hdr hjl hne; omega
    rw [hU, hV, div_pow, div_pow]
    push_cast
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have hM_eq : (M : ℚ) = (Q₁ : ℚ) ^ r * (Q₂ : ℚ) ^ r := by unfold M; push_cast; rfl
    have hpow_p : (p : ℚ) ^ D = (p : ℚ) ^ (D - (j * e₂ + (d - j) * e₁)) *
        ((p : ℚ) ^ (e₁ * (d - j)) * (p : ℚ) ^ (e₂ * j)) := by
      rw [← pow_add, ← pow_add]; congr 1
      have : e₁ * (d - j) + e₂ * j = j * e₂ + (d - j) * e₁ := by ring
      omega
    have hpow_Q₁ : (Q₁ : ℚ) ^ r = (Q₁ : ℚ) ^ (r - (d - j)) * (Q₁ : ℚ) ^ (d - j) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have hpow_Q₂ : (Q₂ : ℚ) ^ r = (Q₂ : ℚ) ^ (r - j) * (Q₂ : ℚ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hM_eq, hpow_p, hpow_Q₁, hpow_Q₂]
    field_simp [hp_ne, hQ₁_ne, hQ₂_ne]
  let termInt : ℕ → ℕ → ℤ := fun d j =>
    a d * (Nat.choose d j : ℤ) * u ^ (d - j) * v ^ j *
      (p : ℤ) ^ (D - (j * e₂ + (d - j) * e₁)) *
      (Q₁ : ℤ) ^ (r - (d - j)) * (Q₂ : ℤ) ^ (r - j)
  let num : ℤ := ∑ d ∈ range (r + 1), ∑ j ∈ range (min d l + 1), termInt d j
  have hrepr : truncatedPoly a r l U V = (num : ℚ) / ((p ^ D * M : ℕ) : ℚ) := by
    unfold truncatedPoly
    simp only [num, Int.cast_sum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdr : d ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hd)
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjl : j ≤ min d l := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have htv := hterm_val d j hdr hjl
    rw [htv, ← mul_div_assoc]
    congr 1
    simp only [termInt]
    push_cast
    ring
  -- Separate `(r, l)` from all other terms in `num`.
  have hlead_not_dvd : ¬ (p : ℤ) ^ (g + 1) ∣ termInt r l := by
    have hD_eq : l * e₂ + (r - l) * e₁ = D := rfl
    have hterm_rl : termInt r l =
        a r * (Nat.choose r l : ℤ) * (u ^ (r - l) * v ^ l * (Q₁ : ℤ) ^ (r - (r - l)) * (Q₂ : ℤ) ^ (r - l)) := by
      simp only [termInt, hD_eq, Nat.sub_self, pow_zero, mul_one]
      ring
    rw [hterm_rl]
    intro hdvd
    have hnat : p ^ (g + 1) ∣
        ((a r).natAbs * Nat.choose r l) *
          (u.natAbs ^ (r - l) * v.natAbs ^ l * Q₁ ^ (r - (r - l)) * Q₂ ^ (r - l)) := by
      have h1 := Int.natCast_dvd.mp hdvd
      simpa [Int.natAbs_mul, Int.natAbs_pow, mul_assoc] using h1
    have hcop : Nat.Coprime (p ^ (g + 1))
        (u.natAbs ^ (r - l) * v.natAbs ^ l * Q₁ ^ (r - (r - l)) * Q₂ ^ (r - l)) := by
      refine Nat.Coprime.pow_left _ ?_
      rw [hp.coprime_iff_not_dvd]
      intro hd
      rcases hp.dvd_mul.mp hd with h1 | hQ2'
      · rcases hp.dvd_mul.mp h1 with h2 | hQ1'
        · rcases hp.dvd_mul.mp h2 with hu' | hv'
          · exact hu (Int.natCast_dvd.mpr (hp.dvd_of_dvd_pow hu'))
          · exact hv (Int.natCast_dvd.mpr (hp.dvd_of_dvd_pow hv'))
        · exact hQ₁ (hp.dvd_of_dvd_pow hQ1')
      · exact hQ₂ (hp.dvd_of_dvd_pow hQ2')
    have hdvd_lead : p ^ (g + 1) ∣ ((a r).natAbs * Nat.choose r l) :=
      hcop.dvd_of_dvd_mul_right hnat
    have hpos_lead : (a r).natAbs * Nat.choose r l ≠ 0 :=
      Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr har) (Nat.choose_pos hlr).ne'
    have hle := (hp.pow_dvd_iff_le_factorization hpos_lead).mp hdvd_lead
    omega
  have hother_dvd : ∀ d ∈ range (r + 1), ∀ j ∈ range (min d l + 1), (d, j) ≠ (r, l) →
      (p : ℤ) ^ (g + 1) ∣ termInt d j := by
    intro d hd j hj hne
    have hdr : d ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hd)
    have hjl : j ≤ min d l := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hdep := hdepth_le d j hdr hjl hne
    have hpow_dvd : (p : ℤ) ^ (g + 1) ∣ (p : ℤ) ^ (D - (j * e₂ + (d - j) * e₁)) :=
      pow_dvd_pow (p : ℤ) (by omega)
    unfold termInt
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpow_dvd _) _) _
  have hnum_not_dvd : ¬ (p : ℤ) ^ (g + 1) ∣ num := by
    intro hnum_dvd
    apply hlead_not_dvd
    -- Write `num = termInt r l + rest` where `(p : ℤ)^(g+1) ∣ rest`.
    have hrest : (p : ℤ) ^ (g + 1) ∣ num - termInt r l := by
      have hnum_eq : num - termInt r l =
          (∑ d ∈ (range (r + 1)).erase r, ∑ j ∈ range (min d l + 1), termInt d j) +
            ∑ j ∈ (range (min r l + 1)).erase l, termInt r j := by
        unfold num
        have hr_mem : r ∈ range (r + 1) := mem_range.mpr (Nat.lt_succ_self r)
        have hl_mem : l ∈ range (min r l + 1) := by
          rw [mem_range, min_eq_right hlr]; omega
        rw [← Finset.add_sum_erase _ _ hr_mem]
        rw [← Finset.add_sum_erase _ _ hl_mem]
        ring
      rw [hnum_eq]
      refine dvd_add ?_ ?_
      · refine Finset.dvd_sum (fun d hd => Finset.dvd_sum (fun j hj => ?_))
        have hdr : d ∈ range (r + 1) := mem_of_mem_erase hd
        have hdne : d ≠ r := ne_of_mem_erase hd
        exact hother_dvd d hdr j hj (fun h => hdne (congrArg Prod.fst h))
      · refine Finset.dvd_sum (fun j hj => ?_)
        have hjr : j ∈ range (min r l + 1) := mem_of_mem_erase hj
        have hjne : j ≠ l := ne_of_mem_erase hj
        exact hother_dvd r (mem_range.mpr (Nat.lt_succ_self r)) j hjr
          (fun h => hjne (congrArg Prod.snd h))
    have hsub := dvd_sub hnum_dvd hrest
    simpa using hsub
  have hgD : g ≤ D := by
    have : e₁ ≤ D := by
      have h1 : 1 * e₂ ≤ l * e₂ := Nat.mul_le_mul_right e₂ hl1
      omega
    omega
  exact prime_pow_dvd_rat_den_of_repr hp hM_pos hgD hnum_not_dvd hrepr

end NormalityChecker.ProtectedPole
