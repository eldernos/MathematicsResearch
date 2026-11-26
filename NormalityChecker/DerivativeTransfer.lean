module

public import NormalityChecker.GeneralMassTransfer
public import NormalityChecker.EulerPentagonal

/-! # Derivative transfer for unary series, `b`-coprime unit survival, and carry shift register (Track D3–D4)

Kernel-checked finite and asymptotic theorems supporting `notes/phase21/partitions-and-higher-modular.md`:

1. **General derivative transfer (`derivCoeff`, `derivCoeff_supportCount_le`, `derivCoeff_absMass_le`,
   `derivCoeff_tendsto_one`, `derivCoeff_preserves_discrepancy`):**
   Applying `D^j = (q d/dq)^j` multiplies the `m`-th coefficient by `m^j`, which never enlarges
   support (`S_{D^j a}(X) ≤ S_a(X)`) and multiplies aggregate mass by at most `X^j`. Together with
   `GeneralMassTransfer.poly_mass_sparse_tendsto_one`, every polynomial-mass series with
   `S_a(X) = o(X / log X)` remains in `K_b` under all iterates `D^j` (`j ≥ 0`, `b ≥ 2`).

2. **Direct instantiations (`j ≥ 0`, `b ≥ 2`):**
   - `deriv_eulerPentagonal_discrepancy_tendsto_one` / `preserves_discrepancy` (`D^j E_b ∈ K_b`,
     for the pentagonal series `pentCoeff`; transfer to the Euler product uses Euler's identity).
   - `deriv_eulerCube_discrepancy_tendsto_one` / `preserves_discrepancy` (`D^j E_b^3 ∈ K_b`,
     for Jacobi's triangular series `jacobiCubeCoeff`; transfer uses Jacobi's identity).
   - `deriv_thetaThree_discrepancy_tendsto_one` / `preserves_discrepancy` (`D^j Θ_3(1/b) ∈ K_b`).
   - `eulerSqDeriv_discrepancy_tendsto_one` (`(1/3) D(E_b^3) = E_b^2 · DE_b ∈ K_b`), via the exact
     integer identity `3 * eulerSqDerivCoeff m = derivCoeff 1 jacobiCubeCoeff m`.

3. **Width–density wall Lemma W.1 (`coprimePart_le_natAbs_radixUnit_mul`):**
   For any `b ≥ 2`, nonzero `x y : ℤ`, and any `d : ℕ` with `d ∣ x.natAbs` and `Nat.Coprime d b`,
   `d ≤ (radixUnit b (x * y)).natAbs`. Thus `b`-adic valuations cannot erase `b`-coprime factors
   from multiplicative coefficients.

4. **Carry-window shift register (`carryWindow`, `carryWindow_succ_modEq`):**
   For any `a : ℕ → ℤ` and `b, n, L : ℕ`, the raw window `R̂_{n,L} = ∑_{j=1}^L a(n + j) b^{L - j}`
   satisfies `R̂_{n+1, L} ≡ b · R̂_{n, L} + a(n + L + 1) [ZMOD b^L]`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.DerivativeTransfer

open CoefficientTransfer GeneralMassTransfer EulerPentagonal SharpTranslation

/-! ### Part 1: General `D^j = (q d/dq)^j` coefficient operator and transfer -/

/-- The `j`-th logarithmic derivative operator `(q d/dq)^j` on integer coefficient sequences:
`(derivCoeff j a) m = m^j * a m`. -/
def derivCoeff (j : ℕ) (a : ℕ → ℤ) (m : ℕ) : ℤ := (m : ℤ) ^ j * a m

/-- Applying `D^j` does not enlarge the nonzero support count. -/
theorem derivCoeff_supportCount_le (j : ℕ) (a : ℕ → ℤ) (X : ℕ) :
    supportCount (derivCoeff j a) X ≤ supportCount a X := by
  unfold supportCount
  refine Finset.card_le_card (fun m hm => ?_)
  rw [mem_filter] at hm ⊢
  refine ⟨hm.1, ?_⟩
  intro ha0
  apply hm.2
  simp [derivCoeff, ha0]

/-- Applying `D^j` multiplies aggregate absolute mass up to `X` by at most `X^j`. -/
theorem derivCoeff_absMass_le (j : ℕ) (a : ℕ → ℤ) (X : ℕ) :
    absMass (derivCoeff j a) X ≤ ((X : ℝ) ^ j) * absMass a X := by
  unfold absMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun m hm => ?_)
  have hmX : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast (mem_Icc.mp hm).2
  have hpow : (m : ℝ) ^ j ≤ (X : ℝ) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg m) hmX j
  unfold derivCoeff
  push_cast
  rw [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg m)]
  exact mul_le_mul_of_nonneg_right hpow (abs_nonneg _)

/-- Polynomial mass preservation under `D^j`: `A_a(X) ≤ C (X + 1)^k` implies
`A_{D^j a}(X) ≤ C (X + 1)^(k + j)`. -/
theorem derivCoeff_poly_mass {a : ℕ → ℤ} {C : ℝ} (k j : ℕ)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k) (X : ℕ) :
    absMass (derivCoeff j a) X ≤ C * ((X + 1 : ℕ) : ℝ) ^ (k + j) := by
  have h1 := derivCoeff_absMass_le j a X
  have h2 := hmass X
  have hXle : (X : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hpow : (X : ℝ) ^ j ≤ ((X + 1 : ℕ) : ℝ) ^ j :=
    pow_le_pow_left₀ (Nat.cast_nonneg X) hXle j
  have hmass_nn : 0 ≤ absMass a X := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc absMass (derivCoeff j a) X
      ≤ (X : ℝ) ^ j * absMass a X := h1
    _ ≤ ((X + 1 : ℕ) : ℝ) ^ j * absMass a X :=
        mul_le_mul_of_nonneg_right hpow hmass_nn
    _ ≤ ((X + 1 : ℕ) : ℝ) ^ j * (C * ((X + 1 : ℕ) : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * ((X + 1 : ℕ) : ℝ) ^ (k + j) := by rw [pow_add]; ring

/-- If `a` has polynomial mass and `S_a(X) = o(X / log X)`, then `D^j F_b(a) ∈ K_b` for every
`j ≥ 0` and every radix `b ≥ 2`. -/
theorem derivCoeff_tendsto_one {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (k j : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k)
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b (derivCoeff j a)) N) atTop (𝓝 1) := by
  refine poly_mass_sparse_tendsto_one hb hC (k + j) (derivCoeff_poly_mass k j hmass) ?_
  refine squeeze_zero (fun N => ?_) (fun N => ?_) hsparse
  · have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    positivity
  · have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have hsup : (supportCount (derivCoeff j a) N : ℝ) ≤ (supportCount a N : ℝ) := by
      exact_mod_cast derivCoeff_supportCount_le j a N
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsup hlog_nn) (Nat.cast_nonneg N)

/-- Discrepancy preservation for `D^j F_b(a)` under polynomial mass and `S_a(X) = o(X / log X)`. -/
theorem derivCoeff_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C : ℝ} (hC : 0 ≤ C)
    (k j : ℕ) (hmass : ∀ X : ℕ, absMass a X ≤ C * ((X + 1 : ℕ) : ℝ) ^ k)
    (hsparse : Tendsto (fun N : ℕ => (supportCount a N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0))
    (x : ℝ) :
    Tendsto (fun N : ℕ =>
      radixDiscrepancy b (x + coeffSeries b (derivCoeff j a)) N - radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  refine poly_mass_sparse_preserves_discrepancy hb hC (k + j) (derivCoeff_poly_mass k j hmass) ?_ x
  refine squeeze_zero (fun N => ?_) (fun N => ?_) hsparse
  · have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    positivity
  · have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have hsup : (supportCount (derivCoeff j a) N : ℝ) ≤ (supportCount a N : ℝ) := by
      exact_mod_cast derivCoeff_supportCount_le j a N
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsup hlog_nn) (Nat.cast_nonneg N)

/-! ### Part 2: Sparsity helper `O(√N) · log N / N → 0` and instantiations -/

/-- Elementary asymptotic: `((Nat.sqrt (2 * N) + 1) * log N) / N → 0`. -/
theorem tendsto_sqrt_mul_log_div_self :
    Tendsto (fun N : ℕ => ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa [pow_one, one_mul, add_zero] using h
  have hsqrt_top : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop := by
    rw [tendsto_atTop]
    intro M
    refine eventually_atTop.mpr ⟨Nat.ceil (max M 0 ^ 2), fun N hN => ?_⟩
    have h1 : max M 0 ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    have h2 : max M 0 ≤ Real.sqrt (N : ℝ) := Real.le_sqrt_of_sq_le h1
    exact (le_max_left M 0).trans h2
  have hlog_sqrt : Tendsto (fun N : ℕ => 6 * (Real.log (Real.sqrt (N : ℝ)) / Real.sqrt (N : ℝ)))
      atTop (𝓝 0) := by
    simpa using (hlog_div.comp hsqrt_top).const_mul (6 : ℝ)
  refine squeeze_zero' ?_ ?_ hlog_sqrt
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have hsqrt_le : (Nat.sqrt (2 * N) : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) := by
      have hsq : Nat.sqrt (2 * N) * Nat.sqrt (2 * N) ≤ 2 * N := Nat.sqrt_le (2 * N)
      have hsq_r : ((Nat.sqrt (2 * N) : ℝ)) ^ 2 ≤ 2 * (N : ℝ) := by
        rw [sq]; exact_mod_cast hsq
      exact Real.le_sqrt_of_sq_le hsq_r
    have h1_le_sqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
    have hsqrt2 : Real.sqrt (2 * (N : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    have hnum : ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
      push_cast; linarith
    have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
    have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNr.le
    have hlog_eq : Real.log (N : ℝ) = 2 * Real.log (Real.sqrt (N : ℝ)) := by
      calc Real.log (N : ℝ) = Real.log (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by rw [hsqN]
        _ = 2 * Real.log (Real.sqrt (N : ℝ)) := by rw [Real.log_mul hsqrt_pos.ne' hsqrt_pos.ne']; ring
    calc ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) * Real.log (N : ℝ) / (N : ℝ)
        ≤ (3 * Real.sqrt (N : ℝ)) * Real.log (N : ℝ) / (N : ℝ) := by
          gcongr
      _ = 6 * (Real.log (Real.sqrt (N : ℝ)) / Real.sqrt (N : ℝ)) := by
          rw [hlog_eq]
          field_simp [hNr.ne', hsqrt_pos.ne']
          nlinarith [hsqN]

private lemma tendsto_of_supportCount_le_const_sqrt {a : ℕ → ℤ} (c : ℝ)
    (hsup : ∀ N : ℕ, (supportCount a N : ℝ) ≤ c * ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ)) :
    Tendsto (fun N : ℕ => (supportCount a N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => c * (((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) * Real.log (N : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa using tendsto_sqrt_mul_log_div_self.const_mul c
  refine squeeze_zero (fun N => ?_) (fun N => ?_) hlim
  · have := Real.log_natCast_nonneg N; positivity
  · have hlog_nn := Real.log_natCast_nonneg N
    calc (supportCount a N : ℝ) * Real.log (N : ℝ) / (N : ℝ)
        ≤ (c * ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ)) * Real.log (N : ℝ) / (N : ℝ) := by gcongr; exact hsup N
      _ = c * (((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) * Real.log (N : ℝ) / (N : ℝ)) := by ring

/-- **All derivatives of the Euler pentagonal series lie in `K_b` (Track D4.2).**
For every `j ≥ 0` and every radix `b ≥ 2`, `D_N(D^j E_b; b) → 1`. -/
theorem deriv_eulerPentagonal_discrepancy_tendsto_one {b : ℕ} (hb : 2 ≤ b) (j : ℕ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b (derivCoeff j pentCoeff)) N)
      atTop (𝓝 1) := by
  refine derivCoeff_tendsto_one hb (C := 1) zero_le_one 1 j ?_ ?_
  · intro X
    have h := pentCoeff_absMass_le X
    push_cast; linarith
  · refine tendsto_of_supportCount_le_const_sqrt 2 (fun N => ?_)
    exact_mod_cast pentagonal_supportCount_le N

/-- Discrepancy preservation by `D^j E_b` for every `j ≥ 0`, `b ≥ 2`, `x ∈ ℝ`. -/
theorem deriv_eulerPentagonal_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) (j : ℕ) (x : ℝ) :
    Tendsto (fun N : ℕ =>
      radixDiscrepancy b (x + coeffSeries b (derivCoeff j pentCoeff)) N - radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  refine derivCoeff_preserves_discrepancy hb (C := 1) zero_le_one 1 j ?_ ?_ x
  · intro X
    have h := pentCoeff_absMass_le X
    push_cast; linarith
  · refine tendsto_of_supportCount_le_const_sqrt 2 (fun N => ?_)
    exact_mod_cast pentagonal_supportCount_le N

/-- **All derivatives of Jacobi's cube series `E_b³` lie in `K_b` (Track D4.2).** -/
theorem deriv_eulerCube_discrepancy_tendsto_one {b : ℕ} (hb : 2 ≤ b) (j : ℕ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b (derivCoeff j jacobiCubeCoeff)) N)
      atTop (𝓝 1) := by
  refine derivCoeff_tendsto_one hb (C := 4) (by norm_num) 1 j ?_ ?_
  · intro X
    have h := jacobiCube_absMass_le X
    push_cast; linarith
  · refine tendsto_of_supportCount_le_const_sqrt 1 (fun N => ?_)
    have h : supportCount jacobiCubeCoeff N ≤ Nat.sqrt (2 * N) + 1 :=
      (jacobiCube_supportCount_le N).trans (Nat.le_succ _)
    simpa using (show (supportCount jacobiCubeCoeff N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) by
      exact_mod_cast h)

/-- Discrepancy preservation by `D^j (E_b³)` for every `j ≥ 0`, `b ≥ 2`, `x ∈ ℝ`. -/
theorem deriv_eulerCube_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) (j : ℕ) (x : ℝ) :
    Tendsto (fun N : ℕ =>
      radixDiscrepancy b (x + coeffSeries b (derivCoeff j jacobiCubeCoeff)) N -
        radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  refine derivCoeff_preserves_discrepancy hb (C := 4) (by norm_num) 1 j ?_ ?_ x
  · intro X
    have h := jacobiCube_absMass_le X
    push_cast; linarith
  · refine tendsto_of_supportCount_le_const_sqrt 1 (fun N => ?_)
    have h : supportCount jacobiCubeCoeff N ≤ Nat.sqrt (2 * N) + 1 :=
      (jacobiCube_supportCount_le N).trans (Nat.le_succ _)
    simpa using (show (supportCount jacobiCubeCoeff N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) by
      exact_mod_cast h)

/-- Coefficient sequence of `Θ_3(q) = 1 + 2 ∑_{k ≥ 1} q^(k^2)`. -/
noncomputable def thetaThreeCoeff (m : ℕ) : ℤ :=
  by classical
  exact if m = 0 then 1 else if ∃ k : ℕ, 1 ≤ k ∧ k * k = m then 2 else 0

theorem thetaThree_supportCount_le (M : ℕ) :
    supportCount thetaThreeCoeff M ≤ Nat.sqrt M := by
  classical
  unfold supportCount
  let K := Nat.sqrt M
  have hsub : (Icc 1 M).filter (fun m => thetaThreeCoeff m ≠ 0) ⊆
      (Icc 1 K).image (fun k => k * k) := by
    intro m hm
    obtain ⟨hmI, hne⟩ := mem_filter.mp hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hmI).1
    have hmM : m ≤ M := (mem_Icc.mp hmI).2
    have hm0 : m ≠ 0 := by omega
    have hex : ∃ k : ℕ, 1 ≤ k ∧ k * k = m := by
      by_contra hno
      apply hne
      unfold thetaThreeCoeff
      simp [hm0, hno]
    obtain ⟨k, hk1, rfl⟩ := hex
    exact mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk1, Nat.le_sqrt.mpr hmM⟩, rfl⟩
  calc ((Icc 1 M).filter (fun m => thetaThreeCoeff m ≠ 0)).card
      ≤ ((Icc 1 K).image (fun k => k * k)).card := card_le_card hsub
    _ ≤ (Icc 1 K).card := card_image_le
    _ = K := by rw [Nat.card_Icc]; omega

theorem thetaThree_absMass_le (M : ℕ) : absMass thetaThreeCoeff M ≤ 2 * (M : ℝ) := by
  classical
  have hbound : ∀ m ∈ Icc 1 M, |(thetaThreeCoeff m : ℝ)| ≤ 2 := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    unfold thetaThreeCoeff
    simp only [hm0, ↓reduceIte]
    split_ifs <;> norm_num
  calc absMass thetaThreeCoeff M
      ≤ ∑ _m ∈ Icc 1 M, (2 : ℝ) := Finset.sum_le_sum hbound
    _ = ((Icc 1 M).card : ℝ) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (M : ℝ) := by rw [Nat.card_Icc]; simp [mul_comm]

/-- **All derivatives of Jacobi's theta constant `Θ_3(1/b)` lie in `K_b` (Track D4.2).** -/
theorem deriv_thetaThree_discrepancy_tendsto_one {b : ℕ} (hb : 2 ≤ b) (j : ℕ) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b (derivCoeff j thetaThreeCoeff)) N)
      atTop (𝓝 1) := by
  refine derivCoeff_tendsto_one hb (C := 2) (by norm_num) 1 j ?_ ?_
  · intro X
    have h := thetaThree_absMass_le X
    push_cast; linarith
  · refine tendsto_of_supportCount_le_const_sqrt 1 (fun N => ?_)
    have h1 : supportCount thetaThreeCoeff N ≤ Nat.sqrt (2 * N) + 1 :=
      (thetaThree_supportCount_le N).trans
        ((Nat.sqrt_le_sqrt (by omega : N ≤ 2 * N)).trans (Nat.le_succ _))
    simpa using (show (supportCount thetaThreeCoeff N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) by
      exact_mod_cast h1)

/-- Discrepancy preservation by `D^j Θ_3(1/b)` for every `j ≥ 0`, `b ≥ 2`, `x ∈ ℝ`. -/
theorem deriv_thetaThree_preserves_discrepancy {b : ℕ} (hb : 2 ≤ b) (j : ℕ) (x : ℝ) :
    Tendsto (fun N : ℕ =>
      radixDiscrepancy b (x + coeffSeries b (derivCoeff j thetaThreeCoeff)) N -
        radixDiscrepancy b x N)
      atTop (𝓝 0) := by
  refine derivCoeff_preserves_discrepancy hb (C := 2) (by norm_num) 1 j ?_ ?_ x
  · intro X
    have h := thetaThree_absMass_le X
    push_cast; linarith
  · refine tendsto_of_supportCount_le_const_sqrt 1 (fun N => ?_)
    have h1 : supportCount thetaThreeCoeff N ≤ Nat.sqrt (2 * N) + 1 :=
      (thetaThree_supportCount_le N).trans
        ((Nat.sqrt_le_sqrt (by omega : N ≤ 2 * N)).trans (Nat.le_succ _))
    simpa using (show (supportCount thetaThreeCoeff N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) by
      exact_mod_cast h1)

/-! ### Part 3: The cancellation product `E_b² · DE_b = (1/3) D(E_b³) ∈ K_b` -/

/-- Exact divisibility `6 ∣ k * (k + 1) * (2 * k + 1)` for every `k : ℕ`. -/
theorem six_dvd_sum_sq_num (k : ℕ) : 6 ∣ k * (k + 1) * (2 * k + 1) := by
  have h2 : 2 ∣ k * (k + 1) * (2 * k + 1) := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (m + m + 1) * (2 * (m + m) + 1), by ring⟩
    · exact ⟨(2 * m + 1) * (m + 1) * (2 * (2 * m + 1) + 1), by ring⟩
  have h3 : 3 ∣ k * (k + 1) * (2 * k + 1) := by
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2'
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h0) _) _
    · have h3' : 3 ∣ 2 * k + 1 := by omega
      exact dvd_mul_of_dvd_right h3' _
    · have h3' : 3 ∣ k + 1 := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3' _) _
  have hcop : Nat.Coprime 2 3 := by decide
  exact hcop.mul_dvd_of_dvd_of_dvd h2 h3

/-- Coefficient sequence of `E_b² · DE_b = (1/3) D(E_b³)`:
`(-1)^k * k(k + 1)(2k + 1)/6` at `m = triNum k`, `0` elsewhere. -/
noncomputable def eulerSqDerivCoeff (m : ℕ) : ℤ :=
  by classical
  exact if h : ∃ k : ℕ, triNum k = m then
    (-1 : ℤ) ^ h.choose * ((h.choose * (h.choose + 1) * (2 * h.choose + 1) / 6 : ℕ) : ℤ)
  else 0

/-- Exact integer identity `3 * eulerSqDerivCoeff m = derivCoeff 1 jacobiCubeCoeff m`. -/
theorem three_mul_eulerSqDerivCoeff (m : ℕ) :
    3 * eulerSqDerivCoeff m = derivCoeff 1 jacobiCubeCoeff m := by
  classical
  unfold eulerSqDerivCoeff derivCoeff jacobiCubeCoeff
  by_cases h : ∃ k : ℕ, triNum k = m
  · simp only [h, ↓reduceDIte, pow_one]
    set k := h.choose
    have hm : triNum k = m := h.choose_spec
    have h2 : 2 * m = k * (k + 1) := hm ▸ two_mul_triNum k
    have h6 : 6 * (k * (k + 1) * (2 * k + 1) / 6) = k * (k + 1) * (2 * k + 1) :=
      Nat.mul_div_cancel' (six_dvd_sum_sq_num k)
    have h6z : (6 : ℤ) * ((k * (k + 1) * (2 * k + 1) / 6 : ℕ) : ℤ) =
        (k : ℤ) * ((k : ℤ) + 1) * (2 * (k : ℤ) + 1) := by exact_mod_cast h6
    have h2z : (2 : ℤ) * (m : ℤ) = (k : ℤ) * ((k : ℤ) + 1) := by exact_mod_cast h2
    have heq : (3 : ℤ) * ((k * (k + 1) * (2 * k + 1) / 6 : ℕ) : ℤ) =
        (m : ℤ) * (2 * (k : ℤ) + 1) := by nlinarith
    calc (3 : ℤ) * ((-1 : ℤ) ^ k * ((k * (k + 1) * (2 * k + 1) / 6 : ℕ) : ℤ))
        = (-1 : ℤ) ^ k * ((3 : ℤ) * ((k * (k + 1) * (2 * k + 1) / 6 : ℕ) : ℤ)) := by ring
      _ = (-1 : ℤ) ^ k * ((m : ℤ) * (2 * (k : ℤ) + 1)) := by rw [heq]
      _ = (m : ℤ) * ((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1)) := by ring
  · simp [h]

/-- **`E_b² · DE_b ∈ K_b` for every integer radix `b ≥ 2` (Track D4.2 / Corollary D4.3).** -/
theorem eulerSqDeriv_discrepancy_tendsto_one {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b eulerSqDerivCoeff) N)
      atTop (𝓝 1) := by
  have habs : ∀ m : ℕ, |(eulerSqDerivCoeff m : ℝ)| ≤ |(derivCoeff 1 jacobiCubeCoeff m : ℝ)| := by
    intro m
    have h3 : (3 : ℝ) * (eulerSqDerivCoeff m : ℝ) = (derivCoeff 1 jacobiCubeCoeff m : ℝ) := by
      exact_mod_cast three_mul_eulerSqDerivCoeff m
    have h3a : (3 : ℝ) * |(eulerSqDerivCoeff m : ℝ)| = |(derivCoeff 1 jacobiCubeCoeff m : ℝ)| := by
      rw [← h3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith [abs_nonneg (eulerSqDerivCoeff m : ℝ)]
  refine poly_mass_sparse_tendsto_one hb (C := 4) (by norm_num) 2 ?_ ?_
  · intro X
    have h1 : absMass eulerSqDerivCoeff X ≤ absMass (derivCoeff 1 jacobiCubeCoeff) X :=
      Finset.sum_le_sum (fun m _ => habs m)
    have h2 : absMass (derivCoeff 1 jacobiCubeCoeff) X ≤ 4 * ((X + 1 : ℕ) : ℝ) ^ (1 + 1) :=
      derivCoeff_poly_mass 1 1 (fun Y => by have := jacobiCube_absMass_le Y; push_cast; linarith) X
    exact h1.trans h2
  · refine tendsto_of_supportCount_le_const_sqrt 1 (fun N => ?_)
    have hsup1 : supportCount eulerSqDerivCoeff N ≤ supportCount (derivCoeff 1 jacobiCubeCoeff) N := by
      unfold supportCount
      refine Finset.card_le_card (fun m hm => ?_)
      rw [mem_filter] at hm ⊢
      refine ⟨hm.1, fun h0 => hm.2 ?_⟩
      have h3 := three_mul_eulerSqDerivCoeff m
      rw [h0] at h3; omega
    have hsup2 : supportCount (derivCoeff 1 jacobiCubeCoeff) N ≤ Nat.sqrt (2 * N) + 1 :=
      ((derivCoeff_supportCount_le 1 jacobiCubeCoeff N).trans
        (jacobiCube_supportCount_le N)).trans (Nat.le_succ _)
    simpa using (show (supportCount eulerSqDerivCoeff N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) by
      exact_mod_cast hsup1.trans hsup2)

/-! ### Part 4: Width–density wall Lemma W.1 (`b`-coprime factors survive in `radixUnit`) -/

/-- **Lemma W.1 (`b`-coprime parts survive in the displaced radix unit).**
For any integer radix `b ≥ 2`, nonzero integers `x, y`, and any natural divisor `d ∣ x.natAbs`
coprime to `b`, we have `d ≤ (radixUnit b (x * y)).natAbs`. -/
theorem coprimePart_le_natAbs_radixUnit_mul {b : ℕ} {x y : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) {d : ℕ} (hd : d ∣ x.natAbs) (hcop : Nat.Coprime d b) :
    d ≤ (radixUnit b (x * y)).natAbs := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hfac := radixVal_mul_radixUnit b (x * y)
  -- Take `natAbs`: `b^V * |U| = |x| * |y|`.
  have hnat : b ^ radixVal b (x * y) * (radixUnit b (x * y)).natAbs = x.natAbs * y.natAbs := by
    have h1 := congrArg Int.natAbs hfac
    simpa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using h1.symm
  have hd_dvd_prod : d ∣ b ^ radixVal b (x * y) * (radixUnit b (x * y)).natAbs := by
    rw [hnat]
    exact dvd_mul_of_dvd_left hd y.natAbs
  have hcop_pow : Nat.Coprime d (b ^ radixVal b (x * y)) := hcop.pow_right _
  have hd_dvd_U : d ∣ (radixUnit b (x * y)).natAbs := hcop_pow.dvd_of_dvd_mul_left hd_dvd_prod
  have hU_ne : (radixUnit b (x * y)).natAbs ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnat
    have hxy0 : (x * y).natAbs = 0 := by rw [Int.natAbs_mul]; exact hnat.symm
    exact hxy (Int.natAbs_eq_zero.mp hxy0)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hU_ne) hd_dvd_U

/-! ### Part 5: Carry-window shift register (Proposition D3.5(1)) -/

/-- Unreduced `L`-digit carry window `R̂_{n, L} = ∑_{j=1}^L a(n + j) b^{L - j}`. -/
def carryWindow (b : ℕ) (a : ℕ → ℤ) (n L : ℕ) : ℤ :=
  ∑ j ∈ Icc 1 L, a (n + j) * (b : ℤ) ^ (L - j)

/-- **Exact carry-window shift register (Proposition D3.5(1)).**
For every `a : ℕ → ℤ` and `b, n, L : ℕ`,
`R̂_{n+1, L} = b * R̂_{n, L} + a(n + L + 1) - a(n + 1) * b^L`,
hence `R̂_{n+1, L} ≡ b * R̂_{n, L} + a(n + L + 1) [ZMOD b^L]`. -/
theorem carryWindow_succ_eq (b : ℕ) (a : ℕ → ℤ) (n L : ℕ) :
    carryWindow b a (n + 1) L + a (n + 1) * (b : ℤ) ^ L =
      (b : ℤ) * carryWindow b a n L + a (n + L + 1) := by
  unfold carryWindow
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · -- Split `L` off the LHS sum (`Icc 1 L = insert L (Icc 1 (L - 1))`) and `1` off the RHS sum.
    have hL_split : Icc 1 L = insert L (Icc 1 (L - 1)) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    have h1_split : Icc 1 L = insert 1 (Icc 2 L) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    conv_lhs => rw [hL_split, Finset.sum_insert (by simp only [mem_Icc]; omega)]
    conv_rhs => rw [h1_split, Finset.sum_insert (by simp only [mem_Icc]; omega), mul_add, Finset.mul_sum]
    have hsub : ∑ j ∈ Icc 1 (L - 1), a (n + 1 + j) * (b : ℤ) ^ (L - j) =
        ∑ j ∈ Icc 2 L, (b : ℤ) * (a (n + j) * (b : ℤ) ^ (L - j)) := by
      refine Finset.sum_nbij (fun j => j + 1) ?_ ?_ ?_ ?_
      · intro j hj; simp only [mem_Icc] at hj ⊢; omega
      · intro j₁ _ j₂ _ h; dsimp only at h; omega
      · intro k hk
        simp only [mem_coe, mem_Icc] at hk
        exact ⟨k - 1, by simp only [mem_coe, mem_Icc]; omega, by dsimp only; omega⟩
      · intro j hj
        simp only [mem_Icc] at hj
        have hidx1 : n + 1 + j = n + (j + 1) := by omega
        have hidx2 : L - j = (L - (j + 1)) + 1 := by omega
        rw [hidx1, hidx2, pow_succ]
        ring
    rw [hsub]
    have hlast : n + 1 + L = n + L + 1 := by omega
    have hpow1 : (b : ℤ) * (a (n + 1) * (b : ℤ) ^ (L - 1)) = a (n + 1) * (b : ℤ) ^ L := by
      have hL1 : L - 1 + 1 = L := by omega
      calc (b : ℤ) * (a (n + 1) * (b : ℤ) ^ (L - 1))
          = a (n + 1) * ((b : ℤ) ^ (L - 1) * (b : ℤ)) := by ring
        _ = a (n + 1) * (b : ℤ) ^ (L - 1 + 1) := by rw [pow_succ]
        _ = a (n + 1) * (b : ℤ) ^ L := by rw [hL1]
    simp only [Nat.sub_self, pow_zero, mul_one, hlast, hpow1]
    ring

theorem carryWindow_succ_modEq (b : ℕ) (a : ℕ → ℤ) (n L : ℕ) :
    carryWindow b a (n + 1) L ≡ (b : ℤ) * carryWindow b a n L + a (n + L + 1) [ZMOD (b : ℤ) ^ L] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨a (n + 1), ?_⟩
  have h := carryWindow_succ_eq b a n L
  linarith

end NormalityChecker.DerivativeTransfer
