module

public import NormalityChecker.Correlations
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Toeplitz Orbit Gram Determinants and Positivity (Phase 26, Track H1)

Kernel-checked versions of the finite matrix theorems from Track A (`A1`, `A4`, `A6`, `A7`) of
`notes/phase26/toeplitz-determinants-and-uniformity.md`.

* **Gram / Toeplitz orbit matrix and PSD structure**: the orbit Toeplitz Gram matrix
  `orbitGram x b N r h` with entries `S_N((j - i) h)` factors as `Vᴴ * V` for the normalized
  orbit Vandermonde matrix `V`, hence is Hermitian, positive semidefinite, has unit diagonal
  for `N ≥ 1`, satisfies the finite Fourier quadratic form identity, and has real nonnegative
  determinant (`orbitGram_isHermitian`, `orbitGram_posSemidef`, `orbitGram_diag`,
  `orbitGram_det_nonneg`, `orbitGram_det_im_eq_zero`).
* **`A1` sharp Gram determinant inequality and Hadamard–Fischer**:
  - Gram–Schmidt determinant product formula `gramMatrix_det_eq_prod_gramSchmidt` for arbitrary
    (including singular) finite families in a complex inner product space;
  - general consecutive-overlap bound `gram_det_le_prod_consecutive` for vectors of norm `≤ 1`;
  - sharp orbit inequality `orbitGram_det_le_pow` (`det G_{N,r}(h) ≤ (1 - ‖S_N(h)‖^2)^(r - 1)`),
    equality characterization `orbitGram_det_eq_pow_iff`, and exact `2 × 2` identity
    `orbitGram_two_det`;
  - Hadamard's inequality `posSemidef_det_re_le_prod_diag`, the general Hadamard–Fischer PSD
    block inequality `posSemidef_det_fromBlocks_le` and `posSemidef_det_le_mul_submatrix`,
    the Toeplitz remainder-block bound `orbitGram_det_fischer` / `orbitGram_det_le_pow_div`,
    and monotone normalized roots `orbitGram_det_pow_antitone`.
* **`A4` exact compound-symmetric control determinant**: over any commutative ring `R` and
  every `r ≥ 1` and `α : R` (including negative `α`),
  `det ((1 - α) I_r + α J_r) = (1 - α)^(r - 1) * (1 + (r - 1) α)`
  (`oneSubAlphaI_add_alphaJ_det`), together with `r = 0`, `ℝ`/`ℂ` specializations, and the
  `α ∈ [0, 1]` determinant sandwich (`oneSubAlphaI_add_alphaJ_det_bounds`).
* **`A7` exact finite Cauchy–Binet expansion**: general rectangular Cauchy–Binet formula
  `det_mul_eq_sum_powersetCard` over any commutative ring, the exact Vandermonde squared-norm
  expansion `pointGram_det_eq_cauchy_binet` / `orbitGram_det_eq_cauchy_binet`, vanishing for
  `r > N` (`orbitGram_det_eq_zero_of_lt`), and strict positivity for every irrational `x` and
  `r ≤ N` (`orbitGram_det_pos_of_irrational`).
* **`A6` finite regularized matrix positivity**: for every PSD matrix `G` and `0 < t ≤ 1`,
  `(1 - t) • G + t • 1` is positive definite (`posSemidef_regularized_posDef`,
  `orbitGram_regularized_posDef`) with determinant at least `t ^ r`
  (`posSemidef_regularized_det_ge`, `orbitGram_regularized_det_ge`).
-/

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace ComplexOrder

namespace NormalityChecker.ToeplitzDeterminants

/-! ## 1. Unimodular point sets, orbit Weyl sums, and Toeplitz Gram matrices -/

/-- Normalized Weyl sum of a finite family of complex points at integer frequency `k`. -/
noncomputable def pointWeylSum {N : ℕ} (z : Fin N → ℂ) (k : ℤ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n : Fin N, z n ^ k

/-- Toeplitz Gram matrix `G i j = S((j - i))` associated to a finite family of points `z`. -/
noncomputable def pointGram {N : ℕ} (z : Fin N → ℂ) (r : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => pointWeylSum z ((j : ℤ) - (i : ℤ))

/-- Complex character `e(h b^n x)` along the base-`b` multiplicative orbit of `x`. -/
noncomputable def orbitPoint (x : ℝ) (b : ℕ) (h : ℤ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (((b : ℝ) ^ n * x : ℝ) : ℂ))

/-- Normalized Weyl sum `S_N(x, b, h) = (1 / N) ∑_{n < N} e(h b^n x)`. -/
noncomputable def orbitWeylSum (x : ℝ) (b N : ℕ) (h : ℤ) : ℂ :=
  (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, orbitPoint x b h n

/-- The `r × r` orbit Toeplitz Gram matrix with `(i, j)`-entry `S_N((j - i) h)`. -/
noncomputable def orbitGram (x : ℝ) (b N r : ℕ) (h : ℤ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j =>
    (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * ((((j : ℤ) - (i : ℤ)) * h : ℤ) : ℂ) *
        (((b : ℝ) ^ n * x : ℝ) : ℂ))

private lemma star_mul_self_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  have h := Complex.conj_mul' z
  rw [hz] at h
  simpa using h

private lemma ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

private lemma star_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : star z = z⁻¹ :=
  (inv_eq_of_mul_eq_one_left (star_mul_self_of_norm_eq_one hz)).symm

private lemma star_pow_mul_pow_eq_zpow {z : ℂ} (hz : ‖z‖ = 1) (i j : ℕ) :
    star (z ^ i) * z ^ j = z ^ ((j : ℤ) - (i : ℤ)) := by
  have hz0 : z ≠ 0 := ne_zero_of_norm_eq_one hz
  rw [star_pow, star_eq_inv_of_norm_eq_one hz, inv_pow, ← zpow_natCast z i,
    ← _root_.zpow_neg, ← zpow_natCast z j, ← zpow_add₀ hz0, neg_add_eq_sub]

theorem orbitPoint_eq_phase (x : ℝ) (b : ℕ) (h : ℤ) (n : ℕ) :
    orbitPoint x b h n = phase ((h : ℝ) * ((b : ℝ) ^ n * x)) := by
  simp only [orbitPoint, phase, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring_nf

theorem norm_orbitPoint (x : ℝ) (b : ℕ) (h : ℤ) (n : ℕ) : ‖orbitPoint x b h n‖ = 1 := by
  rw [orbitPoint_eq_phase]
  exact norm_phase _

theorem orbitPoint_zpow (x : ℝ) (b : ℕ) (h k : ℤ) (n : ℕ) :
    orbitPoint x b h n ^ k = orbitPoint x b (k * h) n := by
  unfold orbitPoint
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem orbitWeylSum_eq_pointWeylSum (x : ℝ) (b N : ℕ) (h k : ℤ) :
    orbitWeylSum x b N (k * h) = pointWeylSum (fun n : Fin N => orbitPoint x b h n.val) k := by
  simp only [orbitWeylSum, pointWeylSum, one_div, Fin.sum_univ_eq_sum_range, orbitPoint_zpow]

theorem orbitWeylSum_eq_pointWeylSum_one (x : ℝ) (b N : ℕ) (h : ℤ) :
    orbitWeylSum x b N h = pointWeylSum (fun n : Fin N => orbitPoint x b h n.val) 1 := by
  simpa using orbitWeylSum_eq_pointWeylSum x b N h 1

theorem orbitWeylSum_eq_mean (x : ℝ) (b N : ℕ) (h : ℤ) :
    orbitWeylSum x b N h = mean (fun n => phase ((h : ℝ) * ((b : ℝ) ^ n * x))) N := by
  simp only [orbitWeylSum, mean, one_div, orbitPoint_eq_phase]
  ring

theorem orbitWeylSum_eq_fourierMean (x : ℝ) (b N : ℕ) (h : ℤ) :
    orbitWeylSum x b N h = Weyl.fourierMean (fun n => (b : ℝ) ^ n * x) h N := by
  rw [orbitWeylSum_eq_mean, mean_phase]

theorem orbitGram_apply (x : ℝ) (b N r : ℕ) (h : ℤ) (i j : Fin r) :
    orbitGram x b N r h i j = orbitWeylSum x b N (((j : ℤ) - (i : ℤ)) * h) := rfl

theorem orbitGram_eq_pointGram (x : ℝ) (b N r : ℕ) (h : ℤ) :
    orbitGram x b N r h = pointGram (fun n : Fin N => orbitPoint x b h n.val) r := by
  ext i j
  rw [orbitGram_apply, pointGram, Matrix.of_apply, orbitWeylSum_eq_pointWeylSum]

/-- The `N × r` scaled Vandermonde factor `V n j = N^(-1/2) z_n^j`. -/
noncomputable def vandermondeFactor {N : ℕ} (z : Fin N → ℂ) (r : ℕ) : Matrix (Fin N) (Fin r) ℂ :=
  Matrix.of fun n j => ((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ * z n ^ (j : ℕ)

/-- The `N × r` unscaled Vandermonde matrix `W n j = z_n^j`. -/
def unscaledVandermonde {N : ℕ} (z : Fin N → ℂ) (r : ℕ) : Matrix (Fin N) (Fin r) ℂ :=
  Matrix.of fun n j => z n ^ (j : ℕ)

theorem natCast_smul_pointGram_eq_conjTranspose_mul_self {N r : ℕ} {z : Fin N → ℂ}
    (hz : ∀ n, ‖z n‖ = 1) :
    (N : ℂ) • pointGram z r = (unscaledVandermonde z r)ᴴ * unscaledVandermonde z r := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, pointGram, pointWeylSum, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, unscaledVandermonde]
  by_cases hN : N = 0
  · subst hN
    simp
  · have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [← mul_assoc, mul_inv_cancel₀ hNc, one_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact (star_pow_mul_pow_eq_zpow (hz n) i.val j.val).symm

/-- Factorization `pointGram z r = Vᴴ * V` for unimodular points `z`. -/
theorem pointGram_eq_conjTranspose_mul_self {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    pointGram z r = (vandermondeFactor z r)ᴴ * vandermondeFactor z r := by
  ext i j
  simp only [pointGram, pointWeylSum, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    vandermondeFactor]
  by_cases hN : N = 0
  · subst hN
    simp
  · have hsqrt : (((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹) * (((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹) =
        (N : ℂ)⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N),
        Complex.ofReal_natCast]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal]
    calc
      (N : ℂ)⁻¹ * z n ^ ((j : ℤ) - (i : ℤ))
          = ((((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹) * (((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹)) *
              (star (z n ^ i.val) * z n ^ j.val) := by
            rw [hsqrt, star_pow_mul_pow_eq_zpow (hz n) i.val j.val]
      _ = ((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (z n ^ i.val) *
            (((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ * z n ^ j.val) := by
            rw [Complex.star_def]
            ring

/-- Finite Fourier quadratic form identity for `pointGram`. -/
theorem pointGram_quadForm {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) (a : Fin r → ℂ) :
    star a ⬝ᵥ (pointGram z r *ᵥ a) =
      (N : ℂ)⁻¹ * ∑ n : Fin N, ((‖∑ j : Fin r, a j * z n ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ n : Fin N,
      ((‖∑ j : Fin r, a j * z n ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) =
        star (∑ i : Fin r, a i * z n ^ (i : ℕ)) * (∑ j : Fin r, a j * z n ^ (j : ℕ)) := by
    intro n
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  simp_rw [h1]
  simp only [dotProduct, mulVec, pointGram, pointWeylSum, Matrix.of_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← star_pow_mul_pow_eq_zpow (hz n) j.val i.val]
  ring

theorem pointGram_posSemidef {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).PosSemidef := by
  rw [pointGram_eq_conjTranspose_mul_self hz]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem pointGram_isHermitian {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).IsHermitian :=
  (pointGram_posSemidef hz).isHermitian

theorem pointGram_diag {N r : ℕ} (hN : 0 < N) (z : Fin N → ℂ) (i : Fin r) :
    pointGram z r i i = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp [pointGram, pointWeylSum, hNc]

theorem pointGram_det_nonneg_complex {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    0 ≤ (pointGram z r).det :=
  (pointGram_posSemidef hz).det_nonneg

theorem pointGram_det_nonneg {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    0 ≤ (pointGram z r).det.re :=
  (Complex.nonneg_iff.mp (pointGram_det_nonneg_complex hz)).1

theorem pointGram_det_im_eq_zero {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).det.im = 0 :=
  (Complex.nonneg_iff.mp (pointGram_det_nonneg_complex hz)).2.symm

/-- Finite Fourier quadratic form identity for `orbitGram`. -/
theorem orbitGram_quadForm (x : ℝ) (b N r : ℕ) (h : ℤ) (a : Fin r → ℂ) :
    star a ⬝ᵥ (orbitGram x b N r h *ᵥ a) =
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        ((‖∑ j : Fin r, a j * orbitPoint x b h n ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [orbitGram_eq_pointGram, pointGram_quadForm (fun n => norm_orbitPoint x b h n.val)]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun n =>
    ((‖∑ j : Fin r, a j * orbitPoint x b h n ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ)) N

/-- `orbitGram x b N r h` is positive semidefinite for all parameters. -/
theorem orbitGram_posSemidef (x : ℝ) (b N r : ℕ) (h : ℤ) :
    (orbitGram x b N r h).PosSemidef := by
  rw [orbitGram_eq_pointGram]
  exact pointGram_posSemidef fun n => norm_orbitPoint x b h n.val

/-- `orbitGram x b N r h` is Hermitian for all parameters. -/
theorem orbitGram_isHermitian (x : ℝ) (b N r : ℕ) (h : ℤ) :
    (orbitGram x b N r h).IsHermitian :=
  (orbitGram_posSemidef x b N r h).isHermitian

/-- Unit diagonal of `orbitGram x b N r h` for `N ≥ 1`. -/
theorem orbitGram_diag (x : ℝ) (b : ℕ) {N : ℕ} (hN : 0 < N) (r : ℕ) (h : ℤ) (i : Fin r) :
    orbitGram x b N r h i i = 1 := by
  rw [orbitGram_eq_pointGram]
  exact pointGram_diag hN _ i

/-- The determinant of `orbitGram x b N r h` has nonnegative real part. -/
theorem orbitGram_det_nonneg (x : ℝ) (b N r : ℕ) (h : ℤ) :
    0 ≤ (orbitGram x b N r h).det.re := by
  rw [orbitGram_eq_pointGram]
  exact pointGram_det_nonneg fun n => norm_orbitPoint x b h n.val

/-- The determinant of `orbitGram x b N r h` is real (vanishing imaginary part). -/
theorem orbitGram_det_im_eq_zero (x : ℝ) (b N r : ℕ) (h : ℤ) :
    (orbitGram x b N r h).det.im = 0 := by
  rw [orbitGram_eq_pointGram]
  exact pointGram_det_im_eq_zero fun n => norm_orbitPoint x b h n.val

/-! ## 2. Gram–Schmidt factorization, A1 inequality, and Hadamard–Fischer -/

/-- Gram matrix `G i j = ⟪v i, v j⟫_ℂ` of a finite family of vectors in a complex inner product
space. -/
noncomputable def gramMatrix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ}
    (v : Fin r → E) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ⟪v i, v j⟫_ℂ

section GramSchmidtDet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma sub_gramSchmidt_mem_span {r : ℕ} (v : Fin r → E) (j : Fin r) :
    v j - InnerProductSpace.gramSchmidt ℂ v j ∈ Submodule.span ℂ (v '' Set.Iio j) := by
  have hdef : v j - InnerProductSpace.gramSchmidt ℂ v j =
      ∑ i ∈ Finset.Iio j,
        (⟪InnerProductSpace.gramSchmidt ℂ v i, v j⟫_ℂ /
          ((‖InnerProductSpace.gramSchmidt ℂ v i‖ : ℂ) ^ 2)) •
        InnerProductSpace.gramSchmidt ℂ v i :=
    (eq_sub_of_add_eq' (InnerProductSpace.gramSchmidt_def'' ℂ v j).symm).symm
  rw [← InnerProductSpace.span_gramSchmidt_Iio ℂ v j, hdef]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩

/-- **Gram–Schmidt determinant product formula (Lemma 1.1).** For every finite family of vectors
`v : Fin r → E` (including linearly dependent families and `r = 0`), the Gram determinant equals
the product of the squared norms of the Gram–Schmidt residuals. -/
theorem gramMatrix_det_eq_prod_gramSchmidt {r : ℕ} (v : Fin r → E) :
    (gramMatrix v).det = ∏ i : Fin r, ((‖InnerProductSpace.gramSchmidt ℂ v i‖ ^ 2 : ℝ) : ℂ) := by
  let u : Fin r → E := InnerProductSpace.gramSchmidt ℂ v
  let T : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j =>
    if i < j then ⟪u i, v j⟫_ℂ / ((‖u i‖ : ℂ) ^ 2)
    else if i = j then 1 else 0
  let D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun i => ((‖u i‖ ^ 2 : ℝ) : ℂ)
  have hv_expand : ∀ j : Fin r, v j = ∑ i : Fin r, T i j • u i := by
    intro j
    have hgs := InnerProductSpace.gramSchmidt_def'' ℂ v j
    rw [hgs]
    have hsplit :
        ∑ i : Fin r, T i j • u i =
          T j j • u j + ∑ i ∈ Finset.univ.erase j, T i j • u i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    rw [hsplit]
    have hdiag : T j j • u j = u j := by
      simp [T]
    rw [hdiag]
    congr 1
    rw [← Finset.sum_subset (s₁ := Finset.Iio j) (s₂ := Finset.univ.erase j)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i < j := Finset.mem_Iio.mp hi
      simp [T, hij, u]
    · intro i hi
      exact Finset.mem_erase.mpr ⟨(Finset.mem_Iio.mp hi).ne, Finset.mem_univ i⟩
    · intro i hi hni
      have hne : i ≠ j := (Finset.mem_erase.mp hi).1
      have hnotlt : ¬ i < j := fun hlt => hni (Finset.mem_Iio.mpr hlt)
      simp [T, hnotlt, hne]
  have hfactor : gramMatrix v = Tᴴ * D * T := by
    ext i j
    rw [gramMatrix, Matrix.of_apply, hv_expand i, hv_expand j]
    rw [sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right]
    have hcollapse :
        ∀ a : Fin r,
          ∑ b : Fin r, (starRingEnd ℂ) (T a i) * (T b j * ⟪u a, u b⟫_ℂ) =
            star (T a i) * ((‖u a‖ ^ 2 : ℝ) : ℂ) * T a j := by
      intro a
      rw [Finset.sum_eq_single a]
      · rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.star_def,
          Complex.ofReal_pow]
        ring
      · intro b _ hba
        rw [InnerProductSpace.gramSchmidt_orthogonal ℂ v hba.symm, mul_zero, mul_zero]
      · intro ha
        exact (ha (Finset.mem_univ a)).elim
    simp_rw [hcollapse]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, D, Matrix.diagonal_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hT_upper : T.IsUpperTriangular := by
    intro i j hij
    have hnotlt : ¬ i < j := not_lt_of_gt hij
    have hne : i ≠ j := ne_of_gt hij
    simp [T, hnotlt, hne]
  have hT_det : T.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hT_upper]
    refine Finset.prod_eq_one fun i _ => ?_
    simp [T]
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hT_det, star_one,
    one_mul, mul_one, Matrix.det_diagonal]

theorem gramMatrix_det_re_eq_prod_gramSchmidt {r : ℕ} (v : Fin r → E) :
    (gramMatrix v).det.re = ∏ i : Fin r, ‖InnerProductSpace.gramSchmidt ℂ v i‖ ^ 2 := by
  rw [gramMatrix_det_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem gramMatrix_det_im_eq_zero {r : ℕ} (v : Fin r → E) :
    (gramMatrix v).det.im = 0 := by
  rw [gramMatrix_det_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_im]

theorem gramMatrix_det_nonneg {r : ℕ} (v : Fin r → E) :
    0 ≤ (gramMatrix v).det.re := by
  rw [gramMatrix_det_re_eq_prod_gramSchmidt]
  exact Finset.prod_nonneg fun _ _ => sq_nonneg _

/-- Orthogonality of the `j`-th Gram–Schmidt residual to the span of the preceding vectors. -/
theorem inner_gramSchmidt_eq_zero_of_mem_span {r : ℕ} (v : Fin r → E) (j : Fin r) {y : E}
    (hy : y ∈ Submodule.span ℂ (v '' Set.Iio j)) :
    ⟪InnerProductSpace.gramSchmidt ℂ v j, y⟫_ℂ = 0 := by
  rw [← InnerProductSpace.span_gramSchmidt_Iio ℂ v j] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    exact InnerProductSpace.gramSchmidt_orthogonal ℂ v (ne_of_gt hi)
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- Exact Pythagorean decomposition of `‖v j - w‖^2` for any `w` in the span of `v_0, …, v_{j-1}`. -/
theorem norm_sub_sq_eq_norm_gramSchmidt_sq_add {r : ℕ} (v : Fin r → E) (j : Fin r) {w : E}
    (hw : w ∈ Submodule.span ℂ (v '' Set.Iio j)) :
    ‖v j - w‖ ^ 2 =
      ‖InnerProductSpace.gramSchmidt ℂ v j‖ ^ 2 +
        ‖(v j - InnerProductSpace.gramSchmidt ℂ v j) - w‖ ^ 2 := by
  let u := InnerProductSpace.gramSchmidt ℂ v j
  let p := v j - u
  have hp_mem : p ∈ Submodule.span ℂ (v '' Set.Iio j) := sub_gramSchmidt_mem_span v j
  have horth : ⟪u, p - w⟫_ℂ = 0 :=
    inner_gramSchmidt_eq_zero_of_mem_span v j (Submodule.sub_mem _ hp_mem hw)
  have hsplit : v j - w = u + (p - w) := by
    dsimp only [p]
    abel
  rw [hsplit, norm_add_sq (𝕜 := ℂ), horth, map_zero]
  ring

/-- Minimality of the Gram–Schmidt residual norm over the span of preceding vectors. -/
theorem norm_gramSchmidt_sq_le_sub {r : ℕ} (v : Fin r → E) (j : Fin r) {w : E}
    (hw : w ∈ Submodule.span ℂ (v '' Set.Iio j)) :
    ‖InnerProductSpace.gramSchmidt ℂ v j‖ ^ 2 ≤ ‖v j - w‖ ^ 2 := by
  rw [norm_sub_sq_eq_norm_gramSchmidt_sq_add v j hw]
  linarith [sq_nonneg ‖(v j - InnerProductSpace.gramSchmidt ℂ v j) - w‖]

/-- **A1.1 (general Gram form).** For any finite family of vectors `v : Fin r → E` with
`‖v i‖ ≤ 1` (including singular Gram matrices and `r = 0, 1`), the Gram determinant satisfies
`det G ≤ ∏_{k < r - 1} (1 - |⟪v_k, v_{k+1}⟫|^2)`. -/
theorem gram_det_le_prod_consecutive {r : ℕ} (v : Fin r → E) (hv : ∀ i : Fin r, ‖v i‖ ≤ 1) :
    (gramMatrix v).det.re ≤
      ∏ k : Fin (r - 1),
        (1 - ‖⟪v ⟨k.val, by omega⟩, v ⟨k.val + 1, by omega⟩⟫_ℂ‖ ^ 2) := by
  rw [gramMatrix_det_re_eq_prod_gramSchmidt]
  cases r with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ]
    have h0_le : ‖InnerProductSpace.gramSchmidt ℂ v 0‖ ^ 2 ≤ 1 := by
      have h0eq : InnerProductSpace.gramSchmidt ℂ v 0 = v 0 :=
        InnerProductSpace.gramSchmidt_bot (𝕜 := ℂ) v
      rw [h0eq]
      have h1 := hv 0
      nlinarith [norm_nonneg (v 0)]
    have hstep : ∀ k : Fin m,
        ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 ≤
          1 - ‖⟪v ⟨k.val, by omega⟩, v ⟨k.val + 1, by omega⟩⟫_ℂ‖ ^ 2 := by
      intro k
      let i0 : Fin (m + 1) := ⟨k.val, by omega⟩
      let i1 : Fin (m + 1) := ⟨k.val + 1, by omega⟩
      have hi1 : i1 = k.succ := Fin.ext rfl
      have hmem : ⟪v i0, v i1⟫_ℂ • v i0 ∈ Submodule.span ℂ (v '' Set.Iio i1) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i0, show i0 < i1 from Nat.lt_succ_self _, rfl⟩)
      have hle := norm_gramSchmidt_sq_le_sub v i1 hmem
      have hexpand : ‖v i1 - ⟪v i0, v i1⟫_ℂ • v i0‖ ^ 2 =
          ‖v i1‖ ^ 2 - 2 * ‖⟪v i0, v i1⟫_ℂ‖ ^ 2 + ‖⟪v i0, v i1⟫_ℂ‖ ^ 2 * ‖v i0‖ ^ 2 := by
        rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow,
          ← inner_conj_symm (v i1) (v i0), RCLike.re_to_complex, Complex.mul_conj',
          ← Complex.ofReal_pow, Complex.ofReal_re]
      have hvi0 : ‖v i0‖ ^ 2 ≤ 1 := by nlinarith [hv i0, norm_nonneg (v i0)]
      have hvi1 : ‖v i1‖ ^ 2 ≤ 1 := by nlinarith [hv i1, norm_nonneg (v i1)]
      have hbound : ‖v i1 - ⟪v i0, v i1⟫_ℂ • v i0‖ ^ 2 ≤ 1 - ‖⟪v i0, v i1⟫_ℂ‖ ^ 2 := by
        rw [hexpand]
        nlinarith [sq_nonneg ‖⟪v i0, v i1⟫_ℂ‖]
      rw [← hi1]
      exact hle.trans hbound
    have hprod_le :
        ∏ k : Fin m, ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 ≤
          ∏ k : Fin m, (1 - ‖⟪v ⟨k.val, by omega⟩, v ⟨k.val + 1, by omega⟩⟫_ℂ‖ ^ 2) :=
      Finset.prod_le_prod₀ (fun k _ => sq_nonneg _) (fun k _ => hstep k)
    have hprod_nonneg :
        0 ≤ ∏ k : Fin m, ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 :=
      Finset.prod_nonneg fun _ _ => sq_nonneg _
    exact (mul_le_of_le_one_left hprod_nonneg h0_le).trans hprod_le

end GramSchmidtDet

/-- Normalized orbit vector `v_j(n) = N^(-1/2) z_n^j` in `EuclideanSpace ℂ (Fin N)`. -/
noncomputable def pointVec {N : ℕ} (z : Fin N → ℂ) (j : ℕ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun n : Fin N => ((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ * z n ^ j

theorem inner_pointVec {N : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) (i j : ℕ) :
    ⟪pointVec z i, pointVec z j⟫_ℂ = pointWeylSum z ((j : ℤ) - (i : ℤ)) := by
  have h := congrFun (congrFun (pointGram_eq_conjTranspose_mul_self (r := max i j + 1) hz)
    ⟨i, by omega⟩) ⟨j, by omega⟩
  simp only [pointGram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    vandermondeFactor] at h
  rw [pointVec, pointVec, PiLp.inner_apply]
  simp only [RCLike.inner_apply, ← Complex.star_def]
  rw [h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_comm]

theorem gramMatrix_pointVec {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    gramMatrix (fun j : Fin r => pointVec z j.val) = pointGram z r := by
  ext i j
  simp only [gramMatrix, pointGram, Matrix.of_apply]
  exact inner_pointVec hz i.val j.val

theorem norm_pointVec {N : ℕ} (hN : 0 < N) {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) (j : ℕ) :
    ‖pointVec z j‖ = 1 := by
  have hsq : ‖pointVec z j‖ ^ 2 = 1 := by
    have hinner := inner_pointVec hz j j
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, sub_self,
      ← Complex.ofReal_pow] at hinner
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp only [pointWeylSum, zpow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, inv_mul_cancel₀ hNc] at hinner
    exact_mod_cast hinner
  nlinarith [norm_nonneg (pointVec z j)]

/-- **A1.1 for unimodular point sets.** For every `N ≥ 1`, `r`, and unimodular `z : Fin N → ℂ`,
`det (pointGram z r) ≤ (1 - ‖S(1)‖^2)^(r - 1)`. -/
theorem pointGram_det_le_pow {N r : ℕ} (hN : 0 < N) {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).det.re ≤ (1 - ‖pointWeylSum z 1‖ ^ 2) ^ (r - 1) := by
  rw [← gramMatrix_pointVec hz]
  have hle := gram_det_le_prod_consecutive (fun j : Fin r => pointVec z j.val)
    (fun i => (norm_pointVec hN hz i.val).le)
  have hprod :
      ∏ k : Fin (r - 1),
        (1 - ‖⟪pointVec z k.val, pointVec z (k.val + 1)⟫_ℂ‖ ^ 2) =
        (1 - ‖pointWeylSum z 1‖ ^ 2) ^ (r - 1) := by
    have hterm : ∀ k : Fin (r - 1),
        ⟪pointVec z k.val, pointVec z (k.val + 1)⟫_ℂ = pointWeylSum z 1 := by
      intro k
      rw [inner_pointVec hz]
      congr 1
      push_cast
      ring
    simp [hterm]
  exact hle.trans_eq hprod

/-- **A1.1 (Theorem 1.2) for `orbitGram`.** For every `x : ℝ`, `b`, `N ≥ 1`, `r`, `h : ℤ`,
`det (orbitGram x b N r h) ≤ (1 - ‖orbitWeylSum x b N h‖^2)^(r - 1)` (singular case included). -/
theorem orbitGram_det_le_pow (x : ℝ) (b : ℕ) {N : ℕ} (hN : 0 < N) (r : ℕ) (h : ℤ) :
    (orbitGram x b N r h).det.re ≤ (1 - ‖orbitWeylSum x b N h‖ ^ 2) ^ (r - 1) := by
  rw [orbitGram_eq_pointGram, orbitWeylSum_eq_pointWeylSum_one]
  exact pointGram_det_le_pow hN fun n => norm_orbitPoint x b h n.val

/-- **Exact `2 × 2` determinant identity** for `pointGram`. -/
theorem pointGram_two_det {N : ℕ} (hN : 0 < N) {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z 2).det = 1 - ((‖pointWeylSum z 1‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, pointGram_diag hN z 0, pointGram_diag hN z 1, mul_one]
  simp only [pointGram, Matrix.of_apply, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    sub_zero, zero_sub]
  have hneg : pointWeylSum z (-1) = star (pointWeylSum z 1) := by
    simp only [pointWeylSum, Complex.star_def, map_mul, map_inv₀, map_sum, Complex.conj_natCast]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [_root_.zpow_neg_one, zpow_one, ← Complex.star_def, star_eq_inv_of_norm_eq_one (hz n)]
  rw [hneg, Complex.star_def, Complex.mul_conj']
  push_cast
  rfl

/-- **Exact `2 × 2` determinant identity (A6.2)** for `orbitGram`:
`det (orbitGram x b N 2 h) = 1 - ‖orbitWeylSum x b N h‖^2`. -/
theorem orbitGram_two_det (x : ℝ) (b : ℕ) {N : ℕ} (hN : 0 < N) (h : ℤ) :
    (orbitGram x b N 2 h).det = 1 - ((‖orbitWeylSum x b N h‖ ^ 2 : ℝ) : ℂ) := by
  rw [orbitGram_eq_pointGram, orbitWeylSum_eq_pointWeylSum_one]
  exact pointGram_two_det hN fun n => norm_orbitPoint x b h n.val

/-- Real-part form of the `2 × 2` determinant identity for `orbitGram`. -/
theorem orbitGram_two_det_re (x : ℝ) (b : ℕ) {N : ℕ} (hN : 0 < N) (h : ℤ) :
    (orbitGram x b N 2 h).det.re = 1 - ‖orbitWeylSum x b N h‖ ^ 2 := by
  rw [orbitGram_two_det x b hN h, Complex.sub_re, Complex.one_re, Complex.ofReal_re]

private lemma pointWeylSum_norm_le_one {N : ℕ} (hN : 0 < N) {z : Fin N → ℂ}
    (hz : ∀ n, ‖z n‖ = 1) (k : ℤ) : ‖pointWeylSum z k‖ ≤ 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [pointWeylSum, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hNr, mul_one]
  calc
    ‖∑ n : Fin N, z n ^ k‖ ≤ ∑ n : Fin N, ‖z n ^ k‖ := norm_sum_le _ _
    _ = ∑ _n : Fin N, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_zpow, hz n, _root_.one_zpow]
    _ = N := by simp

private lemma pointWeylSum_eq_const_of_norm_eq_one {N : ℕ} (hN : 0 < N) {z : Fin N → ℂ}
    (hz : ∀ n, ‖z n‖ = 1) (hS : ‖pointWeylSum z 1‖ = 1) :
    ∀ n : Fin N, z n = pointWeylSum z 1 := by
  set S := pointWeylSum z 1
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsum_z : ∑ n : Fin N, z n = (N : ℂ) * S := by
    simp only [S, pointWeylSum, zpow_one, ← mul_assoc, mul_inv_cancel₀ hNc, one_mul]
  have hvar : ∑ n : Fin N, ‖z n - S‖ ^ 2 = 0 := by
    have hterm : ∀ n : Fin N,
        ‖z n - S‖ ^ 2 = 1 - 2 * (z n * star S).re + 1 := by
      intro n
      have hc : ((‖z n - S‖ ^ 2 : ℝ) : ℂ) = star (z n - S) * (z n - S) := by
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        rfl
      have hre := congrArg Complex.re hc
      rw [Complex.ofReal_re, star_sub, sub_mul, mul_sub, mul_sub,
        star_mul_self_of_norm_eq_one (hz n), star_mul_self_of_norm_eq_one hS] at hre
      have hconj : (star (z n) * S).re = (z n * star S).re := by
        simp [mul_comm]
      simp only [Complex.sub_re, Complex.one_re, mul_comm (star S) (z n)] at hre
      linarith
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hre_sum : ∑ n : Fin N, (z n * star S).re = (N : ℝ) := by
      rw [← Complex.re_sum, ← Finset.sum_mul, hsum_z, mul_assoc,
        show S * star S = 1 by rw [mul_comm]; exact star_mul_self_of_norm_eq_one hS, mul_one,
        Complex.natCast_re]
    rw [hre_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  intro n
  have hzero : ‖z n - S‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun m _ => sq_nonneg _).mp hvar n (Finset.mem_univ n)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

/-- **A1.1 equality characterization** for `pointGram`: for `r ≥ 1`, `N ≥ 1`, equality holds in
`pointGram_det_le_pow` iff the moments are geometric (`S(k) = S(1)^k` for all `k < r`). -/
theorem pointGram_det_eq_pow_iff {N r : ℕ} (hN : 0 < N) (hr : 1 ≤ r) {z : Fin N → ℂ}
    (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).det.re = (1 - ‖pointWeylSum z 1‖ ^ 2) ^ (r - 1) ↔
      ∀ k : ℕ, k < r → pointWeylSum z k = pointWeylSum z 1 ^ k := by
  set S := pointWeylSum z 1
  have hSle : ‖S‖ ≤ 1 := pointWeylSum_norm_le_one hN hz 1
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rcases hSle.eq_or_lt with hSeq | hSlt
  · -- Degenerate case `‖S‖ = 1`: all points coincide, so both sides hold unconditionally.
    have hall : ∀ n : Fin N, z n = S := pointWeylSum_eq_const_of_norm_eq_one hN hz hSeq
    have hgeom : ∀ k : ℕ, k < r → pointWeylSum z k = S ^ k := by
      intro k _
      rw [pointWeylSum]
      simp_rw [zpow_natCast, hall]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
    have hdet : (pointGram z r).det.re = (1 - ‖S‖ ^ 2) ^ (r - 1) := by
      have hle : (pointGram z r).det.re ≤ (1 - ‖S‖ ^ 2) ^ (r - 1) :=
        pointGram_det_le_pow (r := r) hN hz
      have hge := pointGram_det_nonneg (r := r) hz
      cases r with
      | zero => omega
      | succ m =>
        cases m with
        | zero =>
          simp [pointGram_diag hN]
        | succ k =>
          have h0 : (1 - ‖S‖ ^ 2) ^ (k + 1 + 1 - 1) = 0 := by
            rw [hSeq]
            norm_num
          linarith
    exact ⟨fun _ => hgeom, fun _ => hdet⟩
  · -- Nondegenerate case `‖S‖ < 1`: `1 - ‖S‖^2 > 0`.
    have hbase_pos : 0 < 1 - ‖S‖ ^ 2 := by nlinarith [norm_nonneg S]
    cases r with
    | zero => omega
    | succ m =>
      simp only [Nat.add_sub_cancel]
      let v : Fin (m + 1) → EuclideanSpace ℂ (Fin N) := fun j => pointVec z j.val
      have hG : gramMatrix v = pointGram z (m + 1) := gramMatrix_pointVec hz
      rw [← hG, gramMatrix_det_re_eq_prod_gramSchmidt, Fin.prod_univ_succ]
      have h0eq : ‖InnerProductSpace.gramSchmidt ℂ v 0‖ ^ 2 = 1 := by
        have hbot : InnerProductSpace.gramSchmidt ℂ v 0 = v 0 :=
          InnerProductSpace.gramSchmidt_bot (𝕜 := ℂ) v
        rw [hbot]
        simp only [v, Fin.val_zero, norm_pointVec hN hz 0, one_pow]
      rw [h0eq, one_mul]
      have hstep_id : ∀ k : Fin m,
          ‖v k.succ - S • v k.castSucc‖ ^ 2 = 1 - ‖S‖ ^ 2 := by
        intro k
        have hinner : ⟪v k.castSucc, v k.succ⟫_ℂ = S := by
          change ⟪pointVec z k.val, pointVec z (k.val + 1)⟫_ℂ = pointWeylSum z 1
          rw [inner_pointVec hz]
          congr 1
          push_cast
          ring
        rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow,
          ← inner_conj_symm (v k.succ) (v k.castSucc), hinner, RCLike.re_to_complex,
          Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
        have hn1 : ‖v k.succ‖ = 1 := norm_pointVec hN hz k.succ.val
        have hn0 : ‖v k.castSucc‖ = 1 := norm_pointVec hN hz k.castSucc.val
        rw [hn1, hn0]
        ring
      have hmem_span : ∀ k : Fin m,
          S • v k.castSucc ∈ Submodule.span ℂ (v '' Set.Iio k.succ) := fun k =>
        Submodule.smul_mem _ _
          (Submodule.subset_span ⟨k.castSucc, Fin.castSucc_lt_succ (i := k), rfl⟩)
      have hstep_le : ∀ k : Fin m,
          ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 ≤ 1 - ‖S‖ ^ 2 := fun k =>
        (norm_gramSchmidt_sq_le_sub v k.succ (hmem_span k)).trans_eq (hstep_id k)
      have hstep_eq_iff : ∀ k : Fin m,
          ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 = 1 - ‖S‖ ^ 2 ↔
            ∀ i : Fin (m + 1), i < k.succ → ⟪v i, v k.succ - S • v k.castSucc⟫_ℂ = 0 := by
        intro k
        have hpyth := norm_sub_sq_eq_norm_gramSchmidt_sq_add v k.succ (hmem_span k)
        rw [hstep_id k] at hpyth
        constructor
        · intro heq i hi
          have hdiff0 : (v k.succ - InnerProductSpace.gramSchmidt ℂ v k.succ) - S • v k.castSucc = 0 := by
            apply norm_eq_zero.mp
            apply sq_eq_zero_iff.mp
            linarith
          have hres : v k.succ - S • v k.castSucc = InnerProductSpace.gramSchmidt ℂ v k.succ := by
            rw [sub_eq_zero] at hdiff0
            rw [← hdiff0]
            abel
          rw [hres, ← inner_conj_symm]
          have horth := inner_gramSchmidt_eq_zero_of_mem_span v k.succ
            (Submodule.subset_span ⟨i, hi, rfl⟩)
          rw [horth, map_zero]
        · intro horth
          let rvec := v k.succ - S • v k.castSucc
          let p := v k.succ - InnerProductSpace.gramSchmidt ℂ v k.succ
          have hp_mem : p ∈ Submodule.span ℂ (v '' Set.Iio k.succ) :=
            sub_gramSchmidt_mem_span v k.succ
          have hr_orth : ∀ y ∈ Submodule.span ℂ (v '' Set.Iio k.succ), ⟪y, rvec⟫_ℂ = 0 := by
            intro y hy
            induction hy using Submodule.span_induction with
            | mem x hx =>
              rcases hx with ⟨i, hi, rfl⟩
              exact horth i hi
            | zero => exact inner_zero_left _
            | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
            | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
          have hdiff_mem : p - S • v k.castSucc ∈ Submodule.span ℂ (v '' Set.Iio k.succ) :=
            Submodule.sub_mem _ hp_mem (hmem_span k)
          have hself0 : ⟪p - S • v k.castSucc, p - S • v k.castSucc⟫_ℂ = 0 := by
            have h1 := hr_orth _ hdiff_mem
            have h2 := inner_gramSchmidt_eq_zero_of_mem_span v k.succ hdiff_mem
            have h2' : ⟪p - S • v k.castSucc, InnerProductSpace.gramSchmidt ℂ v k.succ⟫_ℂ = 0 := by
              rw [← inner_conj_symm, h2, map_zero]
            have hsplit : p - S • v k.castSucc = rvec - InnerProductSpace.gramSchmidt ℂ v k.succ := by
              dsimp only [p, rvec]
              abel
            calc
              ⟪p - S • v k.castSucc, p - S • v k.castSucc⟫_ℂ
                  = ⟪p - S • v k.castSucc, rvec - InnerProductSpace.gramSchmidt ℂ v k.succ⟫_ℂ := by
                    rw [hsplit]
              _ = ⟪p - S • v k.castSucc, rvec⟫_ℂ -
                    ⟪p - S • v k.castSucc, InnerProductSpace.gramSchmidt ℂ v k.succ⟫_ℂ :=
                  inner_sub_right _ _ _
              _ = 0 := by rw [h1, h2', sub_zero]
          have hnorm0 : ‖p - S • v k.castSucc‖ = 0 := by
            rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
              ← Complex.ofReal_pow] at hself0
            have : ‖p - S • v k.castSucc‖ ^ 2 = 0 := by exact_mod_cast hself0
            exact sq_eq_zero_iff.mp this
          dsimp only [p] at hnorm0
          rw [hnorm0, zero_pow two_ne_zero, add_zero] at hpyth
          exact hpyth.symm
      constructor
      · intro hprod_eq
        have hall_eq : ∀ k : Fin m, ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 = 1 - ‖S‖ ^ 2 := by
          intro k
          by_contra hne
          have hlt : ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 < 1 - ‖S‖ ^ 2 :=
            lt_of_le_of_ne (hstep_le k) hne
          have hstrict :
              ∏ j : Fin m, ‖InnerProductSpace.gramSchmidt ℂ v j.succ‖ ^ 2 <
                ∏ _j : Fin m, (1 - ‖S‖ ^ 2) := by
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
              ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
            have hrest_le :
                ∏ j ∈ Finset.univ.erase k, ‖InnerProductSpace.gramSchmidt ℂ v j.succ‖ ^ 2 ≤
                  ∏ _j ∈ Finset.univ.erase k, (1 - ‖S‖ ^ 2) :=
              Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun j _ => hstep_le j)
            have hrest_pos : 0 < ∏ _j ∈ Finset.univ.erase k, (1 - ‖S‖ ^ 2) :=
              Finset.prod_pos fun _ _ => hbase_pos
            have hrest_nonneg :
                0 ≤ ∏ j ∈ Finset.univ.erase k, ‖InnerProductSpace.gramSchmidt ℂ v j.succ‖ ^ 2 :=
              Finset.prod_nonneg fun _ _ => sq_nonneg _
            nlinarith [sq_nonneg ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hstrict
          linarith
        intro k hk
        induction k with
        | zero =>
          simp [pointWeylSum, hNc]
        | succ k ih =>
          have hkm : k < m := by omega
          have horth := (hstep_eq_iff ⟨k, hkm⟩).mp (hall_eq ⟨k, hkm⟩) 0 (Fin.succ_pos ⟨k, hkm⟩)
          rw [inner_sub_right, inner_smul_right] at horth
          have h1 : ⟪v 0, v (⟨k, hkm⟩ : Fin m).succ⟫_ℂ = pointWeylSum z ((k + 1 : ℕ) : ℤ) := by
            change ⟪pointVec z 0, pointVec z (k + 1)⟫_ℂ = _
            rw [inner_pointVec hz]
            simp
          have h2 : ⟪v 0, v (⟨k, hkm⟩ : Fin m).castSucc⟫_ℂ = pointWeylSum z (k : ℤ) := by
            change ⟪pointVec z 0, pointVec z k⟫_ℂ = _
            rw [inner_pointVec hz]
            simp
          rw [h1, h2, sub_eq_zero] at horth
          rw [horth, ih (by omega), pow_succ']
      · intro hgeom
        have hall_eq : ∀ k : Fin m, ‖InnerProductSpace.gramSchmidt ℂ v k.succ‖ ^ 2 = 1 - ‖S‖ ^ 2 := by
          intro k
          rw [hstep_eq_iff k]
          intro i hi
          have hik : i.val ≤ k.val := Nat.lt_succ_iff.mp hi
          rw [inner_sub_right, inner_smul_right]
          have h1 : ⟪v i, v k.succ⟫_ℂ = pointWeylSum z ((k.val + 1 - i.val : ℕ) : ℤ) := by
            change ⟪pointVec z i.val, pointVec z (k.val + 1)⟫_ℂ = _
            rw [inner_pointVec hz]
            congr 1
            omega
          have h2 : ⟪v i, v k.castSucc⟫_ℂ = pointWeylSum z ((k.val - i.val : ℕ) : ℤ) := by
            change ⟪pointVec z i.val, pointVec z k.val⟫_ℂ = _
            rw [inner_pointVec hz]
            congr 1
            omega
          rw [h1, h2, hgeom (k.val + 1 - i.val) (by omega), hgeom (k.val - i.val) (by omega)]
          have heq : k.val + 1 - i.val = (k.val - i.val) + 1 := by omega
          rw [heq, pow_succ', sub_self]
        simp [hall_eq]

/-- **A1.1 equality characterization** for `orbitGram`. -/
theorem orbitGram_det_eq_pow_iff (x : ℝ) (b : ℕ) {N r : ℕ} (hN : 0 < N) (hr : 1 ≤ r) (h : ℤ) :
    (orbitGram x b N r h).det.re = (1 - ‖orbitWeylSum x b N h‖ ^ 2) ^ (r - 1) ↔
      ∀ k : ℕ, k < r → orbitWeylSum x b N ((k : ℤ) * h) = orbitWeylSum x b N h ^ k := by
  rw [orbitGram_eq_pointGram, orbitWeylSum_eq_pointWeylSum_one,
    pointGram_det_eq_pow_iff hN hr (fun n => norm_orbitPoint x b h n.val)]
  refine forall₂_congr fun k _ => ?_
  rw [orbitWeylSum_eq_pointWeylSum]

/-! ### Hadamard and Hadamard–Fischer PSD block inequalities -/

/-- Every complex positive semidefinite matrix is the Gram matrix of a finite family of vectors
in `EuclideanSpace ℂ ι`. -/
theorem posSemidef_exists_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    ∃ v : ι → EuclideanSpace ℂ ι, ∀ i j, ⟪v i, v j⟫_ℂ = M i j := by
  let U : Matrix ι ι ℂ := (hM.1.eigenvectorUnitary : Matrix ι ι ℂ)
  let D : Matrix ι ι ℂ := Matrix.diagonal fun k => ((Real.sqrt (hM.1.eigenvalues k) : ℝ) : ℂ)
  let V : Matrix ι ι ℂ := D * Uᴴ
  have hfactor : Vᴴ * V = M := by
    have hDstar : Dᴴ * D = Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) := by
      ext i j
      rw [Matrix.mul_apply]
      have hterm : ∀ k : ι, Dᴴ i k * D k j =
          if k = i ∧ k = j then ((hM.1.eigenvalues k : ℝ) : ℂ) else 0 := by
        intro k
        simp only [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
        by_cases hki : k = i <;> by_cases hkj : k = j
        · subst hki; subst hkj
          simp only [↓reduceIte, and_self, Complex.star_def, Complex.conj_ofReal,
            ← Complex.ofReal_mul, Real.mul_self_sqrt (hM.eigenvalues_nonneg k)]
        · subst hki; simp [hkj]
        · subst hkj; simp [hki]
        · simp [hki, hkj]
      simp_rw [hterm]
      by_cases hij : i = j
      · subst hij
        simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Matrix.diagonal_apply, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]
      · simp only [Matrix.diagonal_apply, hij, ↓reduceIte]
        refine Finset.sum_eq_zero fun k _ => ?_
        have hnot : ¬ (k = i ∧ k = j) := fun ⟨h1, h2⟩ => hij (h1.symm.trans h2)
        simp [hnot]
    have hspec := hM.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    calc
      Vᴴ * V = (D * Uᴴ)ᴴ * (D * Uᴴ) := rfl
      _ = (U * Dᴴ) * (D * Uᴴ) := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = U * (Dᴴ * D) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) * star U := by
        rw [hDstar]
        rfl
      _ = M := hspec.symm
  refine ⟨fun j => WithLp.toLp 2 fun k => V k j, fun i j => ?_⟩
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  have hEntry := congrFun (congrFun hfactor i) j
  rw [← hEntry, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm]

/-- **Hadamard's inequality for PSD matrices:** `det M ≤ ∏ i, (M i i).re`. -/
theorem posSemidef_det_re_le_prod_diag {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ}
    (hM : M.PosSemidef) :
    M.det.re ≤ ∏ i : Fin r, (M i i).re := by
  obtain ⟨v, hv⟩ := posSemidef_exists_gram hM
  have hG : gramMatrix v = M := by
    ext i j
    exact hv i j
  conv_lhs => rw [← hG]
  rw [gramMatrix_det_re_eq_prod_gramSchmidt]
  refine Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) fun i _ => ?_
  have hle : ‖InnerProductSpace.gramSchmidt ℂ v i‖ ^ 2 ≤ ‖v i‖ ^ 2 := by
    simpa only [sub_zero] using norm_gramSchmidt_sq_le_sub v i (Submodule.zero_mem _)
  have hdiag : ‖v i‖ ^ 2 = (M i i).re := by
    have h := hv i i
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow] at h
    have hre := congrArg Complex.re h
    rwa [Complex.ofReal_re] at hre
  exact hle.trans_eq hdiag

private lemma gramSchmidt_castAdd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a b : ℕ} (v : Fin (a + b) → E) (i : Fin a) :
    InnerProductSpace.gramSchmidt ℂ v (Fin.castAdd b i) =
      InnerProductSpace.gramSchmidt ℂ (v ∘ Fin.castAdd b) i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [InnerProductSpace.gramSchmidt_def, InnerProductSpace.gramSchmidt_def]
    congr 1
    refine (Finset.sum_bij (fun (k : Fin a) _ => Fin.castAdd b k)
      (fun k hk => Finset.mem_Iio.mpr (show (Fin.castAdd b k).val < (Fin.castAdd b i).val by
        simpa using Finset.mem_Iio.mp hk))
      (fun _ _ _ _ h => Fin.castAdd_injective a b h)
      (fun j hj => ?_)
      (fun k hk => ?_)).symm
    · have hjlt : j.val < i.val := Fin.lt_def.mp (Finset.mem_Iio.mp hj)
      refine ⟨⟨j.val, lt_trans hjlt i.isLt⟩, Finset.mem_Iio.mpr hjlt, Fin.ext rfl⟩
    · rw [ih k (Finset.mem_Iio.mp hk)]
      rfl

private lemma norm_gramSchmidt_sq_le_of_subset {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {r s : ℕ} (f : Fin r → E) (g : Fin s → E) (j : Fin r) (k : Fin s)
    (hjk : f j = g k) (hsub : g '' Set.Iio k ⊆ f '' Set.Iio j) :
    ‖InnerProductSpace.gramSchmidt ℂ f j‖ ^ 2 ≤ ‖InnerProductSpace.gramSchmidt ℂ g k‖ ^ 2 := by
  let w := g k - InnerProductSpace.gramSchmidt ℂ g k
  have hw_mem_g : w ∈ Submodule.span ℂ (g '' Set.Iio k) := sub_gramSchmidt_mem_span g k
  have hw_mem_f : w ∈ Submodule.span ℂ (f '' Set.Iio j) :=
    Submodule.span_mono hsub hw_mem_g
  have hle := norm_gramSchmidt_sq_le_sub f j hw_mem_f
  have hdiff : f j - w = InnerProductSpace.gramSchmidt ℂ g k := by
    dsimp only [w]
    rw [hjk, sub_sub_cancel]
  rwa [hdiff] at hle

/-- **Hadamard–Fischer PSD block inequality on `Fin (a + b)`.** For any complex positive
semidefinite `(a + b) × (a + b)` matrix `M` (singular blocks included),
`det M ≤ det M_{[0,a)} · det M_{[a,a+b)}`. -/
theorem posSemidef_det_fin_add_le {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.PosSemidef) :
    M.det.re ≤
      (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
        (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det.re := by
  obtain ⟨v, hv⟩ := posSemidef_exists_gram hM
  have hG : gramMatrix v = M := by ext i j; exact hv i j
  have hGA : gramMatrix (v ∘ Fin.castAdd b) = M.submatrix (Fin.castAdd b) (Fin.castAdd b) := by
    ext i j; exact hv _ _
  have hGD : gramMatrix (v ∘ Fin.natAdd a) = M.submatrix (Fin.natAdd a) (Fin.natAdd a) := by
    ext i j; exact hv _ _
  rw [← hGA, ← hGD, ← hG, gramMatrix_det_re_eq_prod_gramSchmidt,
    gramMatrix_det_re_eq_prod_gramSchmidt, gramMatrix_det_re_eq_prod_gramSchmidt,
    Fin.prod_univ_add]
  have hA :
      ∏ i : Fin a, ‖InnerProductSpace.gramSchmidt ℂ v (Fin.castAdd b i)‖ ^ 2 =
        ∏ i : Fin a, ‖InnerProductSpace.gramSchmidt ℂ (v ∘ Fin.castAdd b) i‖ ^ 2 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [gramSchmidt_castAdd]
  have hD :
      ∏ k : Fin b, ‖InnerProductSpace.gramSchmidt ℂ v (Fin.natAdd a k)‖ ^ 2 ≤
        ∏ k : Fin b, ‖InnerProductSpace.gramSchmidt ℂ (v ∘ Fin.natAdd a) k‖ ^ 2 := by
    refine Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) fun k _ => ?_
    refine norm_gramSchmidt_sq_le_of_subset v (v ∘ Fin.natAdd a) (Fin.natAdd a k) k rfl ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨Fin.natAdd a i, show (Fin.natAdd a i).val < (Fin.natAdd a k).val from
      Nat.add_lt_add_left hi a, rfl⟩
  rw [hA]
  exact mul_le_mul_of_nonneg_left hD (Finset.prod_nonneg fun _ _ => sq_nonneg _)

/-- **General Hadamard–Fischer PSD inequality on `m ⊕ n`.** For any finite types `m, n` and any
complex PSD matrix `M : Matrix (m ⊕ n) (m ⊕ n) ℂ`,
`det M ≤ det (M_{m,m}) · det (M_{n,n})`. -/
theorem posSemidef_det_le_mul_submatrix {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {M : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hM : M.PosSemidef) :
    M.det.re ≤
      (M.submatrix Sum.inl Sum.inl).det.re * (M.submatrix Sum.inr Sum.inr).det.re := by
  let em : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm
  let en : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  let e : Fin (Fintype.card m + Fintype.card n) ≃ m ⊕ n :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr em en)
  let M' : Matrix (Fin (Fintype.card m + Fintype.card n))
      (Fin (Fintype.card m + Fintype.card n)) ℂ := M.submatrix e e
  have hM' : M'.PosSemidef := hM.submatrix e
  have hdet : M'.det = M.det := Matrix.det_submatrix_equiv_self e M
  have hdetA : (M'.submatrix (Fin.castAdd (Fintype.card n)) (Fin.castAdd (Fintype.card n))).det =
      (M.submatrix Sum.inl Sum.inl).det := by
    have hsub : M'.submatrix (Fin.castAdd (Fintype.card n)) (Fin.castAdd (Fintype.card n)) =
        (M.submatrix Sum.inl Sum.inl).submatrix em em := by
      ext i j
      simp [M', e]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hdetD : (M'.submatrix (Fin.natAdd (Fintype.card m)) (Fin.natAdd (Fintype.card m))).det =
      (M.submatrix Sum.inr Sum.inr).det := by
    have hsub : M'.submatrix (Fin.natAdd (Fintype.card m)) (Fin.natAdd (Fintype.card m)) =
        (M.submatrix Sum.inr Sum.inr).submatrix en en := by
      ext i j
      simp [M', e]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hle := posSemidef_det_fin_add_le hM'
  rwa [hdet, hdetA, hdetD] at hle

/-- **Hadamard–Fischer inequality for block PSD matrices `fromBlocks A B Bᴴ D`.** -/
theorem posSemidef_det_fromBlocks_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℂ} {B : Matrix m n ℂ} {D : Matrix n n ℂ}
    (hM : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).det.re ≤ A.det.re * D.det.re := by
  have hle := posSemidef_det_le_mul_submatrix hM
  have hA : (Matrix.fromBlocks A B Bᴴ D).submatrix Sum.inl Sum.inl = A := by ext i j; rfl
  have hD : (Matrix.fromBlocks A B Bᴴ D).submatrix Sum.inr Sum.inr = D := by ext i j; rfl
  rwa [hA, hD] at hle

/-- Submultiplicativity of Toeplitz Gram determinants:
`det (pointGram z (a + c)) ≤ det (pointGram z a) · det (pointGram z c)`. -/
theorem pointGram_det_add_le {N a c : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z (a + c)).det.re ≤ (pointGram z a).det.re * (pointGram z c).det.re := by
  have hle := posSemidef_det_fin_add_le (a := a) (b := c) (M := pointGram z (a + c))
    (pointGram_posSemidef (r := a + c) hz)
  have hA : (pointGram z (a + c)).submatrix (Fin.castAdd c) (Fin.castAdd c) = pointGram z a := by
    ext i j
    simp [pointGram]
  have hC : (pointGram z (a + c)).submatrix (Fin.natAdd a) (Fin.natAdd a) = pointGram z c := by
    ext i j
    simp only [Matrix.submatrix_apply, pointGram, Matrix.of_apply, Fin.val_natAdd, Nat.cast_add]
    congr 1
    ring
  rwa [hA, hC] at hle

/-- **Hadamard–Fischer with remainder block (Corollary 1.5(3))** for `pointGram`:
`det G_{N,r} ≤ (det G_{N,m})^(r / m) · det G_{N, r % m}`. -/
theorem pointGram_det_fischer {N r m : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).det.re ≤
      (pointGram z m).det.re ^ (r / m) * (pointGram z (r % m)).det.re := by
  have hmul : ∀ q s : ℕ,
      (pointGram z (m * q + s)).det.re ≤
        (pointGram z m).det.re ^ q * (pointGram z s).det.re := by
    intro q
    induction q with
    | zero =>
      intro s
      have h0 : m * 0 + s = s := by omega
      rw [h0, pow_zero, one_mul]
    | succ q ih =>
      intro s
      have heq : m * (q + 1) + s = m + (m * q + s) := by ring
      rw [heq, pow_succ', mul_assoc]
      exact (pointGram_det_add_le hz).trans
        (mul_le_mul_of_nonneg_left (ih s) (pointGram_det_nonneg hz))
  have hdiv := hmul (r / m) (r % m)
  rwa [Nat.div_add_mod r m] at hdiv

/-- Unit-diagonal upper bound `det (pointGram z r) ≤ 1` for `N ≥ 1`. -/
theorem pointGram_det_le_one {N r : ℕ} (hN : 0 < N) {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).det.re ≤ 1 := by
  calc
    (pointGram z r).det.re ≤ ∏ i : Fin r, (pointGram z r i i).re :=
      posSemidef_det_re_le_prod_diag (pointGram_posSemidef (r := r) hz)
    _ = 1 := by simp [pointGram_diag hN]

/-- Submultiplicativity of `orbitGram` determinants. -/
theorem orbitGram_det_add_le (x : ℝ) (b N a c : ℕ) (h : ℤ) :
    (orbitGram x b N (a + c) h).det.re ≤
      (orbitGram x b N a h).det.re * (orbitGram x b N c h).det.re := by
  simp only [orbitGram_eq_pointGram]
  exact pointGram_det_add_le fun n => norm_orbitPoint x b h n.val

/-- **Hadamard–Fischer with remainder block (Corollary 1.5(3))** for `orbitGram`:
`det G_{N,r}(h) ≤ (det G_{N,m}(h))^(r / m) · det G_{N, r % m}(h)`. -/
theorem orbitGram_det_fischer (x : ℝ) (b N r m : ℕ) (h : ℤ) :
    (orbitGram x b N r h).det.re ≤
      (orbitGram x b N m h).det.re ^ (r / m) * (orbitGram x b N (r % m) h).det.re := by
  simp only [orbitGram_eq_pointGram]
  exact pointGram_det_fischer fun n => norm_orbitPoint x b h n.val

/-- **Hadamard–Fischer block bound for `orbitGram`** (unit-diagonal corollary):
`det G_{N,r}(h) ≤ (det G_{N,m}(h))^(r / m)` for `N ≥ 1`. -/
theorem orbitGram_det_le_pow_div (x : ℝ) (b : ℕ) {N : ℕ} (hN : 0 < N) (r m : ℕ) (h : ℤ) :
    (orbitGram x b N r h).det.re ≤ (orbitGram x b N m h).det.re ^ (r / m) := by
  have hf := orbitGram_det_fischer x b N r m h
  have hrem : (orbitGram x b N (r % m) h).det.re ≤ 1 := by
    rw [orbitGram_eq_pointGram]
    exact pointGram_det_le_one hN fun n => norm_orbitPoint x b h n.val
  have hpow_nonneg : 0 ≤ (orbitGram x b N m h).det.re ^ (r / m) :=
    pow_nonneg (orbitGram_det_nonneg x b N m h) _
  exact hf.trans (mul_le_of_le_one_right hpow_nonneg hrem)

/-! ### Monotone Gram–Schmidt residuals and monotone normalized roots (Corollary 1.5(1)-(2)) -/

/-- The unitary multiplication operator `(D u)_n = z_n u_n` on `EuclideanSpace ℂ (Fin N)`. -/
private noncomputable def shiftMap {N : ℕ} (z : Fin N → ℂ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) where
  toFun u := WithLp.toLp 2 fun n => z n * u n
  map_add' u w := by ext n; simp [mul_add]
  map_smul' c u := by ext n; simp [mul_left_comm]

private lemma norm_shiftMap {N : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1)
    (u : EuclideanSpace ℂ (Fin N)) : ‖shiftMap z u‖ = ‖u‖ := by
  have hsq : ‖shiftMap z u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, shiftMap, LinearMap.coe_mk, AddHom.coe_mk,
      norm_mul, hz, one_mul]
  nlinarith [norm_nonneg (shiftMap z u), norm_nonneg u]

private lemma shiftMap_pointVec {N : ℕ} (z : Fin N → ℂ) (k : ℕ) :
    shiftMap z (pointVec z k) = pointVec z (k + 1) := by
  ext n
  simp only [shiftMap, pointVec, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, pow_succ]
  ring

private lemma gramSchmidt_pointVec_antitone {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1)
    {i j : Fin r} (hij : i ≤ j) :
    ‖InnerProductSpace.gramSchmidt ℂ (fun k : Fin r => pointVec z k.val) j‖ ^ 2 ≤
      ‖InnerProductSpace.gramSchmidt ℂ (fun k : Fin r => pointVec z k.val) i‖ ^ 2 := by
  let v : Fin r → EuclideanSpace ℂ (Fin N) := fun k => pointVec z k.val
  suffices hstep : ∀ k : ℕ, (hk : k + 1 < r) →
      ‖InnerProductSpace.gramSchmidt ℂ v ⟨k + 1, hk⟩‖ ^ 2 ≤
        ‖InnerProductSpace.gramSchmidt ℂ v ⟨k, by omega⟩‖ ^ 2 by
    have hd : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < r),
        ‖InnerProductSpace.gramSchmidt ℂ v ⟨a + d, ha⟩‖ ^ 2 ≤
          ‖InnerProductSpace.gramSchmidt ℂ v ⟨a, by omega⟩‖ ^ 2 := by
      intro d
      induction d with
      | zero => intro a ha; exact le_rfl
      | succ d ih =>
        intro a ha
        exact (hstep (a + d) ha).trans (ih a (by omega))
    have hdiff : i.val + (j.val - i.val) = j.val := Nat.add_sub_cancel' hij
    have h := hd (j.val - i.val) i.val (by omega)
    have h1 : (⟨i.val + (j.val - i.val), by omega⟩ : Fin r) = j := Fin.ext hdiff
    have h2 : (⟨i.val, by omega⟩ : Fin r) = i := Fin.ext rfl
    rwa [h1, h2] at h
  intro k hk
  let jk : Fin r := ⟨k, by omega⟩
  let jk1 : Fin r := ⟨k + 1, hk⟩
  let p := v jk - InnerProductSpace.gramSchmidt ℂ v jk
  have hp_mem : p ∈ Submodule.span ℂ (v '' Set.Iio jk) := sub_gramSchmidt_mem_span v jk
  have hDp_mem : shiftMap z p ∈ Submodule.span ℂ (v '' Set.Iio jk1) := by
    have himg : shiftMap z p ∈ Submodule.map (shiftMap z) (Submodule.span ℂ (v '' Set.Iio jk)) :=
      Submodule.mem_map_of_mem hp_mem
    rw [Submodule.map_span] at himg
    refine Submodule.span_mono ?_ himg
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hilt : i.val + 1 < k + 1 := Nat.succ_lt_succ hi
    refine ⟨⟨i.val + 1, lt_trans hilt hk⟩, hilt, ?_⟩
    exact (shiftMap_pointVec z i.val).symm
  have hle := norm_gramSchmidt_sq_le_sub v jk1 hDp_mem
  have hdiff : v jk1 - shiftMap z p = shiftMap z (InnerProductSpace.gramSchmidt ℂ v jk) := by
    dsimp only [p, v, jk, jk1]
    rw [map_sub, shiftMap_pointVec z k, sub_sub_cancel]
  rw [hdiff, norm_shiftMap hz] at hle
  exact hle

/-- **Monotone normalized determinant root (Corollary 1.5(2))** for `pointGram`:
for `m ≤ r`, `(det G_{N,r})^m ≤ (det G_{N,m})^r`. -/
theorem pointGram_det_pow_antitone {N m r : ℕ} (hm : m ≤ r) {z : Fin N → ℂ}
    (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).det.re ^ m ≤ (pointGram z m).det.re ^ r := by
  let d : Fin r → ℝ := fun j =>
    ‖InnerProductSpace.gramSchmidt ℂ (fun k : Fin r => pointVec z k.val) j‖ ^ 2
  have hd_nonneg : ∀ j : Fin r, 0 ≤ d j := fun _ => sq_nonneg _
  have hd_anti : ∀ {i j : Fin r}, i ≤ j → d j ≤ d i := fun hij =>
    gramSchmidt_pointVec_antitone hz hij
  have hdet_r : (pointGram z r).det.re = ∏ j : Fin r, d j := by
    rw [← gramMatrix_pointVec hz, gramMatrix_det_re_eq_prod_gramSchmidt]
  have hdet_m : (pointGram z m).det.re =
      ∏ i : Fin m, d ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ := by
    rw [← gramMatrix_pointVec hz, gramMatrix_det_re_eq_prod_gramSchmidt]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hcast : ∀ (k : Fin m),
        InnerProductSpace.gramSchmidt ℂ (fun j : Fin r => pointVec z j.val)
          ⟨k.val, lt_of_lt_of_le k.isLt hm⟩ =
        InnerProductSpace.gramSchmidt ℂ (fun j : Fin m => pointVec z j.val) k := by
      intro k
      induction k using WellFoundedLT.induction with
      | ind k ih =>
        rw [InnerProductSpace.gramSchmidt_def, InnerProductSpace.gramSchmidt_def]
        congr 1
        refine (Finset.sum_bij (fun (a : Fin m) _ => (⟨a.val, lt_of_lt_of_le a.isLt hm⟩ : Fin r))
          (fun a ha => by
            have hlt : a < k := Finset.mem_Iio.mp ha
            exact Finset.mem_Iio.mpr (show (⟨a.val, lt_of_lt_of_le a.isLt hm⟩ : Fin r) <
              ⟨k.val, lt_of_lt_of_le k.isLt hm⟩ from hlt))
          (fun _ _ _ _ h => Fin.ext (congrArg (Fin.val : Fin r → ℕ) h))
          (fun j hj => ?_)
          (fun a ha => by rw [ih a (Finset.mem_Iio.mp ha)])).symm
        have hjlt : j.val < k.val := Fin.lt_def.mp (Finset.mem_Iio.mp hj)
        exact ⟨⟨j.val, lt_trans hjlt k.isLt⟩, Finset.mem_Iio.mpr hjlt, Fin.ext rfl⟩
    dsimp only [d]
    rw [hcast i]
  rw [hdet_r, hdet_m]
  have hsplit :
      ∏ j : Fin r, d j =
        (∏ i : Fin m, d ⟨i.val, lt_of_lt_of_le i.isLt hm⟩) *
          (∏ k : Fin (r - m), d ⟨m + k.val, by omega⟩) := by
    let e : Fin (m + (r - m)) ≃ Fin r := finCongr (Nat.add_sub_of_le hm)
    rw [← Fintype.prod_equiv e (fun j => d (e j)) d (fun _ => rfl), Fin.prod_univ_add]
    congr 1
  rw [hsplit, mul_pow]
  set P := ∏ i : Fin m, d ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
  have hP_nonneg : 0 ≤ P := Finset.prod_nonneg fun _ _ => hd_nonneg _
  have htail :
      (∏ k : Fin (r - m), d ⟨m + k.val, by omega⟩) ^ m ≤ P ^ (r - m) := by
    rw [← Finset.prod_pow]
    calc
      ∏ k : Fin (r - m), d ⟨m + k.val, by omega⟩ ^ m
          ≤ ∏ _k : Fin (r - m), P := by
            refine Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (hd_nonneg _) _) fun k _ => ?_
            have hconst : d ⟨m + k.val, by omega⟩ ^ m =
                ∏ _i : Fin m, d ⟨m + k.val, by omega⟩ := by simp
            rw [hconst]
            refine Finset.prod_le_prod₀ (fun _ _ => hd_nonneg _) fun i _ => ?_
            exact hd_anti (show (⟨i.val, lt_of_lt_of_le i.isLt hm⟩ : Fin r) ≤
              ⟨m + k.val, by omega⟩ from
              Nat.le_of_lt (lt_of_lt_of_le i.isLt (Nat.le_add_right m k.val)))
      _ = P ^ (r - m) := by simp
  calc
    P ^ m * (∏ k : Fin (r - m), d ⟨m + k.val, by omega⟩) ^ m
        ≤ P ^ m * P ^ (r - m) := mul_le_mul_of_nonneg_left htail (pow_nonneg hP_nonneg _)
    _ = P ^ r := by rw [← pow_add, Nat.add_sub_of_le hm]

/-- **Monotone normalized determinant root (Corollary 1.5(2))** for `orbitGram`:
for `m ≤ r`, `(det G_{N,r}(h))^m ≤ (det G_{N,m}(h))^r`. -/
theorem orbitGram_det_pow_antitone (x : ℝ) (b N : ℕ) {m r : ℕ} (hm : m ≤ r) (h : ℤ) :
    (orbitGram x b N r h).det.re ^ m ≤ (orbitGram x b N m h).det.re ^ r := by
  simp only [orbitGram_eq_pointGram]
  exact pointGram_det_pow_antitone hm fun n => norm_orbitPoint x b h n.val

/-! ## 3. Track A4: exact control matrix determinant `(1 - α) I + α J` -/

/-- **General compound-symmetric determinant** over any commutative ring `R`:
for `r ≥ 1` and all `β, α : R`,
`det (β • I_r + α • J_r) = β ^ (r - 1) * (β + r * α)`. -/
theorem betaI_add_alphaJ_det {R : Type*} [CommRing R] {r : ℕ} (hr : 1 ≤ r) (β α : R) :
    (β • (1 : Matrix (Fin r) (Fin r) R) + α • Matrix.of (fun _ _ => (1 : R))).det =
      β ^ (r - 1) * (β + (r : R) * α) := by
  cases r with
  | zero => omega
  | succ n =>
    simp only [Nat.add_sub_cancel]
    let M : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
      β • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) + α • Matrix.of (fun _ _ => (1 : R))
    -- `L` subtracts row `0` from every row `i ≠ 0`; `U` adds every column `j ≠ 0` to column `0`.
    let L : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun i k =>
      (if i = k then 1 else 0) - (if i ≠ 0 ∧ k = 0 then 1 else 0)
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun k j =>
      (if k = j then 1 else 0) + (if k ≠ 0 ∧ j = 0 then 1 else 0)
    have hL_lower : L.IsLowerTriangular := by
      intro i k hik
      have hne : i ≠ k := ne_of_lt hik
      have hk0 : k ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hik)
      simp [L, hne, hk0]
    have hU_lower : U.IsLowerTriangular := by
      intro k j hkj
      have hne : k ≠ j := ne_of_lt hkj
      have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le k) hkj)
      simp [U, hne, hj0]
    have hL_det : L.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular L hL_lower]
      refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = 0 <;> simp [L, hi]
    have hU_det : U.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular U hU_lower]
      refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = 0 <;> simp [U, hi]
    have hLM : ∀ i k : Fin (n + 1),
        (L * M) i k =
          if i = 0 then (if (0 : Fin (n + 1)) = k then β else 0) + α
          else (if i = k then β else 0) - (if (0 : Fin (n + 1)) = k then β else 0) := by
      intro i k
      simp only [Matrix.mul_apply, L, M, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_one]
      by_cases hi : i = 0
      · subst hi
        simp only [↓reduceIte, ne_eq, not_true_eq_false, false_and, sub_zero, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq, Finset.mem_univ, mul_ite, mul_one, mul_zero]
      · simp only [hi, ↓reduceIte, ne_eq, not_false_eq_true, true_and, sub_mul, ite_mul, one_mul,
          zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
          mul_ite, mul_one, mul_zero]
        ring
    have hLMU : ∀ i j : Fin (n + 1),
        (L * M * U) i j =
          if j = 0 then (if i = 0 then β + ((n + 1 : ℕ) : R) * α else 0)
          else if i = 0 then α
          else if i = j then β else 0 := by
      intro i j
      rw [Matrix.mul_apply]
      by_cases hj : j = 0
      · subst hj
        have hU0 : ∀ k : Fin (n + 1), U k 0 = 1 := by
          intro k
          by_cases hk : k = 0 <;> simp [U, hk]
        simp_rw [hU0, mul_one, hLM]
        by_cases hi : i = 0
        · subst hi
          simp only [↓reduceIte, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        · simp only [hi, ↓reduceIte, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
            sub_self]
      · have hUj : ∀ k : Fin (n + 1), U k j = if k = j then 1 else 0 := by
          intro k
          simp [U, hj]
        simp only [hUj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          hLM]
        by_cases hi : i = 0
        · subst hi
          have h0j : (0 : Fin (n + 1)) ≠ j := Ne.symm hj
          simp [hj, h0j]
        · have h0j : (0 : Fin (n + 1)) ≠ j := Ne.symm hj
          simp [hj, hi, h0j]
    have hW_upper : (L * M * U).IsUpperTriangular := by
      intro i j hij
      rw [hLMU]
      have hi0 : i ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le j) hij)
      have hij_ne : i ≠ j := ne_of_gt hij
      by_cases hj : j = 0 <;> simp [hj, hi0, hij_ne]
    have hW_det : (L * M * U).det = β ^ n * (β + ((n + 1 : ℕ) : R) * α) := by
      rw [Matrix.det_of_isUpperTriangular hW_upper, Fin.prod_univ_succ]
      have h0 : (L * M * U) 0 0 = β + ((n + 1 : ℕ) : R) * α := by simp [hLMU]
      have hsucc : ∀ k : Fin n, (L * M * U) k.succ k.succ = β := by
        intro k
        simp [hLMU, Fin.succ_ne_zero]
      rw [h0]
      simp [hsucc, mul_comm]
    change M.det = β ^ n * (β + ((n + 1 : ℕ) : R) * α)
    calc
      M.det = L.det * M.det * U.det := by rw [hL_det, hU_det, one_mul, mul_one]
      _ = (L * M * U).det := by rw [Matrix.det_mul, Matrix.det_mul]
      _ = β ^ n * (β + ((n + 1 : ℕ) : R) * α) := hW_det

/-- **A4 exact control matrix determinant (Proposition 4.1)** over any commutative ring `R`:
for every `r ≥ 1` and every `α : R` (including negative `α`),
`det ((1 - α) I_r + α J_r) = (1 - α)^(r - 1) * (1 + (r - 1) α)`. -/
theorem oneSubAlphaI_add_alphaJ_det {R : Type*} [CommRing R] {r : ℕ} (hr : 1 ≤ r) (α : R) :
    ((1 - α) • (1 : Matrix (Fin r) (Fin r) R) + α • Matrix.of (fun _ _ => (1 : R))).det =
      (1 - α) ^ (r - 1) * (1 + ((r : R) - 1) * α) := by
  rw [betaI_add_alphaJ_det hr (1 - α) α]
  ring

/-- `r = 0` case of the A4 control matrix determinant (`det = 1`). -/
theorem oneSubAlphaI_add_alphaJ_det_zero {R : Type*} [CommRing R] (α : R) :
    ((1 - α) • (1 : Matrix (Fin 0) (Fin 0) R) + α • Matrix.of (fun _ _ => (1 : R))).det = 1 :=
  Matrix.det_isEmpty

/-- Real specialization of `oneSubAlphaI_add_alphaJ_det`. -/
theorem oneSubAlphaI_add_alphaJ_det_real {r : ℕ} (hr : 1 ≤ r) (α : ℝ) :
    ((1 - α) • (1 : Matrix (Fin r) (Fin r) ℝ) + α • Matrix.of (fun _ _ => (1 : ℝ))).det =
      (1 - α) ^ (r - 1) * (1 + ((r : ℝ) - 1) * α) :=
  oneSubAlphaI_add_alphaJ_det hr α

/-- Complex specialization of `oneSubAlphaI_add_alphaJ_det`. -/
theorem oneSubAlphaI_add_alphaJ_det_complex {r : ℕ} (hr : 1 ≤ r) (α : ℂ) :
    ((1 - α) • (1 : Matrix (Fin r) (Fin r) ℂ) + α • Matrix.of (fun _ _ => (1 : ℂ))).det =
      (1 - α) ^ (r - 1) * (1 + ((r : ℂ) - 1) * α) :=
  oneSubAlphaI_add_alphaJ_det hr α

/-- **A4 determinant sandwich** for `α ∈ [0, 1]` and `r ≥ 1`:
`(1 - α)^r ≤ det ((1 - α) I_r + α J_r) ≤ r * (1 - α)^(r - 1)`. -/
theorem oneSubAlphaI_add_alphaJ_det_bounds {r : ℕ} (hr : 1 ≤ r) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (1 - α) ^ r ≤
        ((1 - α) • (1 : Matrix (Fin r) (Fin r) ℝ) + α • Matrix.of (fun _ _ => (1 : ℝ))).det ∧
      ((1 - α) • (1 : Matrix (Fin r) (Fin r) ℝ) + α • Matrix.of (fun _ _ => (1 : ℝ))).det ≤
        (r : ℝ) * (1 - α) ^ (r - 1) := by
  rw [oneSubAlphaI_add_alphaJ_det_real hr α]
  have hpow : 0 ≤ (1 - α) ^ (r - 1) := pow_nonneg (sub_nonneg.mpr h1) _
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  constructor
  · have hpow_eq : (1 - α) ^ r = (1 - α) ^ (r - 1) * (1 - α) := by
      conv_lhs => rw [← Nat.sub_add_cancel hr, pow_succ]
    rw [hpow_eq]
    refine mul_le_mul_of_nonneg_left ?_ hpow
    nlinarith
  · rw [mul_comm (r : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ hpow
    nlinarith

/-! ## 4. Track A7: exact finite Cauchy–Binet expansion and rank positivity -/

private lemma det_mul_rect_aux {R : Type*} [CommRing R] {r N : ℕ}
    (A : Matrix (Fin r) (Fin N) R) (B : Matrix (Fin N) (Fin r) R) {p : Fin r → Fin N}
    (H : ¬ Function.Injective p) :
    (∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin r, A (σ i) (p i) * B (p i) i) = 0 := by
  have hex : ∃ i j : Fin r, p i = p j ∧ i ≠ j := by
    unfold Function.Injective at H
    push Not at H
    exact H
  obtain ⟨i, j, hpij, hij⟩ := hex
  refine Finset.sum_involution (fun σ _ => σ * Equiv.swap i j) ?_ ?_ ?_ ?_
  · intro σ _
    have hprod : (∏ x : Fin r, A (σ x) (p x)) =
        ∏ x : Fin r, A ((σ * Equiv.swap i j) x) (p x) := by
      refine Fintype.prod_equiv (Equiv.swap i j) _ _ fun x => ?_
      simp [Equiv.apply_swap_eq_self hpij]
    simp only [Finset.prod_mul_distrib, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
      ← hprod, Units.val_neg, mul_neg_one, Int.cast_neg]
    ring
  · intro σ _ _ heq
    have h1 : Equiv.swap i j = 1 := mul_left_cancel (a := σ) (by simpa using heq)
    have h2 := Equiv.congr_fun h1 i
    simp at h2
    exact hij h2.symm
  · intro _ _
    exact Finset.mem_univ _
  · intro σ _
    simp [mul_assoc]

/-- **General rectangular Cauchy–Binet theorem** over any commutative ring `R`:
for `A : Matrix (Fin r) (Fin N) R` and `B : Matrix (Fin N) (Fin r) R`,
`det (A * B) = ∑_{|s| = r} det (A_{*, s}) · det (B_{s, *})`. -/
theorem det_mul_eq_sum_powersetCard {R : Type*} [CommRing R] {r N : ℕ}
    (A : Matrix (Fin r) (Fin N) R) (B : Matrix (Fin N) (Fin r) R) :
    (A * B).det =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        if hs : s.card = r then
          (A.submatrix id (s.orderEmbOfFin hs)).det * (B.submatrix (s.orderEmbOfFin hs) id).det
        else 0 := by
  -- Step 1: expand `det (A * B)` over all functions `p : Fin r → Fin N`.
  have hexpand : (A * B).det =
      ∑ p : Fin r → Fin N, ∑ σ : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin r, A (σ i) (p i) * B (p i) i := by
    simp only [Matrix.det_apply', Matrix.mul_apply, Fintype.prod_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
  -- Step 2: drop non-injective functions `p`.
  have hinj : (A * B).det =
      ∑ p ∈ (Finset.univ : Finset (Fin r → Fin N)).filter Function.Injective,
        ∑ σ : Equiv.Perm (Fin r),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin r, A (σ i) (p i) * B (p i) i := by
    rw [hexpand]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun p _ hp => ?_).symm
    have hnot : ¬ Function.Injective p := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp
    exact det_mul_rect_aux A B hnot
  -- Step 3: decompose injective `p : Fin r → Fin N` uniquely as `(s.orderEmbOfFin hs) ∘ τ`.
  rw [hinj]
  let P := ((Finset.univ : Finset (Fin N)).powersetCard r).attach
  have hsum_P :
      (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        if hs : s.card = r then
          (A.submatrix id (s.orderEmbOfFin hs)).det * (B.submatrix (s.orderEmbOfFin hs) id).det
        else 0) =
      ∑ s ∈ P,
        (A.submatrix id (s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2)).det *
          (B.submatrix (s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2) id).det := by
    rw [← Finset.sum_attach (s := (Finset.univ : Finset (Fin N)).powersetCard r)]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [(Finset.mem_powersetCard.mp s.2).2, ↓reduceDIte]
  rw [hsum_P]
  -- Rewrite RHS as a double sum over `(s, τ) ∈ P ×ˢ univ`.
  have hrhs :
      (∑ s ∈ P,
        (A.submatrix id (s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2)).det *
          (B.submatrix (s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2) id).det) =
      ∑ x ∈ P ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin r))),
        ∑ σ : Equiv.Perm (Fin r),
          ((Equiv.Perm.sign σ : ℤ) : R) *
            ∏ i : Fin r,
              A (σ i) (x.1.1.orderEmbOfFin (Finset.mem_powersetCard.mp x.1.2).2 (x.2 i)) *
              B (x.1.1.orderEmbOfFin (Finset.mem_powersetCard.mp x.1.2).2 (x.2 i)) i := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun s _ => ?_
    set f : Fin r ↪o Fin N := s.1.orderEmbOfFin (Finset.mem_powersetCard.mp s.2).2
    simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_
    have hprodA : (∏ i : Fin r, A (σ i) (f i)) = ∏ i : Fin r, A ((σ * τ) i) (f (τ i)) := by
      refine (Fintype.prod_equiv τ _ _ fun i => ?_).symm
      rfl
    change (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin r, A (σ i) (f i)) *
        (((Equiv.Perm.sign τ : ℤ) : R) * ∏ i : Fin r, B (f (τ i)) i) =
      ((Equiv.Perm.sign (σ * τ) : ℤ) : R) * ∏ i : Fin r, A ((σ * τ) i) (f (τ i)) * B (f (τ i)) i
    rw [Finset.prod_mul_distrib, ← hprodA, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
    ring
  rw [hrhs]
  -- Step 4: exhibit the bijection `(s, τ) ↦ f_s ∘ τ`.
  refine (Finset.sum_bij
    (fun (x : {s // s ∈ (Finset.univ : Finset (Fin N)).powersetCard r} × Equiv.Perm (Fin r)) _ =>
      fun i : Fin r => x.1.1.orderEmbOfFin (Finset.mem_powersetCard.mp x.1.2).2 (x.2 i))
    ?_ ?_ ?_ ?_).symm
  · intro x _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (x.1.1.orderEmbOfFin (Finset.mem_powersetCard.mp x.1.2).2).injective.comp x.2.injective
  · intro x₁ _ x₂ _ hfun
    set h₁ := (Finset.mem_powersetCard.mp x₁.1.2).2
    set h₂ := (Finset.mem_powersetCard.mp x₂.1.2).2
    have himg : x₁.1.1 = x₂.1.1 := by
      have h1 : Finset.image ((x₁.1.1.orderEmbOfFin h₁) ∘ x₁.2) Finset.univ = x₁.1.1 := by
        rw [← Finset.image_image, Finset.image_univ_of_surjective x₁.2.surjective,
          Finset.image_orderEmbOfFin_univ]
      have h2 : Finset.image ((x₂.1.1.orderEmbOfFin h₂) ∘ x₂.2) Finset.univ = x₂.1.1 := by
        rw [← Finset.image_image, Finset.image_univ_of_surjective x₂.2.surjective,
          Finset.image_orderEmbOfFin_univ]
      have hcomp : ((x₁.1.1.orderEmbOfFin h₁) ∘ x₁.2) = ((x₂.1.1.orderEmbOfFin h₂) ∘ x₂.2) := hfun
      rw [← h1, ← h2, hcomp]
    have hx1 : x₁.1 = x₂.1 := Subtype.ext himg
    have hx2 : x₁.2 = x₂.2 := by
      cases x₁ with
      | mk s₁ τ₁ =>
        cases x₂ with
        | mk s₂ τ₂ =>
          dsimp only at hx1 hfun
          subst hx1
          exact Equiv.ext fun i => (s₁.1.orderEmbOfFin _).injective (congrFun hfun i)
    exact Prod.ext hx1 hx2
  · intro p hp
    have hpinj : Function.Injective p := (Finset.mem_filter.mp hp).2
    let s : Finset (Fin N) := Finset.image p Finset.univ
    have hscard : s.card = r := by
      rw [Finset.card_image_of_injective _ hpinj, Finset.card_univ, Fintype.card_fin]
    have hsmem : s ∈ (Finset.univ : Finset (Fin N)).powersetCard r :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hscard⟩
    let f : Fin r ↪o Fin N := s.orderEmbOfFin hscard
    have hex : ∀ i : Fin r, ∃ j : Fin r, f j = p i := by
      intro i
      have hmem : p i ∈ (s : Set (Fin N)) :=
        Finset.mem_coe.mpr (Finset.mem_image_of_mem p (Finset.mem_univ i))
      rw [← Finset.range_orderEmbOfFin s hscard] at hmem
      exact hmem
    choose g hg using hex
    have hginj : Function.Injective g := by
      intro i₁ i₂ h
      apply hpinj
      rw [← hg i₁, ← hg i₂, h]
    let τ : Equiv.Perm (Fin r) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj)
    refine ⟨(⟨s, hsmem⟩, τ), Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩, ?_⟩
    funext i
    exact hg i
  · intro x _
    rfl

private lemma prod_Ioi_eq_prod_filter_lt {N r : ℕ} (s : Finset (Fin N)) (hs : s.card = r)
    (g : Fin N → Fin N → ℝ) (hcomm : ∀ a b, g a b = g b a) :
    (∏ i : Fin r, ∏ j ∈ Finset.Ioi i, g (s.orderEmbOfFin hs j) (s.orderEmbOfFin hs i)) =
      ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), g p.1 p.2 := by
  let f := s.orderEmbOfFin hs
  have h1 :
      (∏ i : Fin r, ∏ j ∈ Finset.Ioi i, g (f j) (f i)) =
        ∏ p ∈ ((Finset.univ : Finset (Fin r)) ×ˢ (Finset.univ : Finset (Fin r))).filter
          (fun p => p.1 < p.2), g (f p.1) (f p.2) := by
    rw [Finset.prod_filter, Finset.prod_product]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    have hIoi : Finset.univ.filter (fun j : Fin r => i < j) = Finset.Ioi i := by
      ext j; simp
    rw [hIoi]
    refine Finset.prod_congr rfl fun j _ => hcomm _ _
  rw [h1]
  refine Finset.prod_bij (fun p _ => (f p.1, f p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨Finset.orderEmbOfFin_mem s hs p.1, Finset.orderEmbOfFin_mem s hs p.2⟩,
      f.strictMono hp.2⟩
  · intro p₁ _ p₂ _ h
    exact Prod.ext (f.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h))
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    have hq1 : q.1 ∈ Set.range f := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hq.1.1
    have hq2 : q.2 ∈ Set.range f := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hq.1.2
    rcases hq1 with ⟨i, hi⟩
    rcases hq2 with ⟨j, hj⟩
    have hij : i < j := by
      rw [← hi, ← hj] at hq
      exact f.lt_iff_lt.mp hq.2
    refine ⟨(i, j), ?_, Prod.ext hi hj⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij⟩
  · intro _ _
    rfl

/-- **A7 exact finite Cauchy–Binet expansion (complex form)** for `pointGram`:
`N^r · det (pointGram z r) = ∑_{|s| = r} ∏_{a < b ∈ s} ‖z_a - z_b‖^2`. -/
theorem pointGram_det_eq_cauchy_binet_complex {N r : ℕ} {z : Fin N → ℂ} (hz : ∀ n, ‖z n‖ = 1) :
    (N : ℂ) ^ r * (pointGram z r).det =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ((‖z p.1 - z p.2‖ ^ 2 : ℝ) : ℂ) := by
  have hsmul : (N : ℂ) ^ r * (pointGram z r).det =
      ((unscaledVandermonde z r)ᴴ * unscaledVandermonde z r).det := by
    rw [← natCast_smul_pointGram_eq_conjTranspose_mul_self hz, Matrix.det_smul, Fintype.card_fin]
  rw [hsmul, det_mul_eq_sum_powersetCard]
  refine Finset.sum_congr rfl fun s hs_mem => ?_
  have hs : s.card = r := (Finset.mem_powersetCard.mp hs_mem).2
  simp only [hs, ↓reduceDIte]
  let f := s.orderEmbOfFin hs
  have hsubB : (unscaledVandermonde z r).submatrix f id = Matrix.vandermonde (z ∘ f) := by
    ext i j
    simp [unscaledVandermonde, Matrix.vandermonde]
  have hsubA : (unscaledVandermonde z r)ᴴ.submatrix id f = (Matrix.vandermonde (z ∘ f))ᴴ := by
    ext i j
    simp [unscaledVandermonde, Matrix.vandermonde]
  rw [hsubA, hsubB, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, Matrix.det_vandermonde]
  rw [norm_prod, ← Finset.prod_pow]
  simp_rw [norm_prod, ← Finset.prod_pow]
  simp only [Function.comp_apply]
  have hprod_re :
      (∏ i : Fin r, ∏ j ∈ Finset.Ioi i, ‖z (f j) - z (f i)‖ ^ 2) =
        ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ‖z p.1 - z p.2‖ ^ 2 :=
    prod_Ioi_eq_prod_filter_lt s hs (fun a b => ‖z a - z b‖ ^ 2)
      (fun a b => by rw [norm_sub_rev])
  rw [hprod_re, Complex.ofReal_prod]

/-- **A7 exact finite Cauchy–Binet expansion (real form)** for `pointGram`. -/
theorem pointGram_det_eq_cauchy_binet {N r : ℕ} (hN : 0 < N) {z : Fin N → ℂ}
    (hz : ∀ n, ‖z n‖ = 1) :
    (pointGram z r).det.re =
      (N : ℝ)⁻¹ ^ r * ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ‖z p.1 - z p.2‖ ^ 2 := by
  have hre := congrArg Complex.re (pointGram_det_eq_cauchy_binet_complex (r := r) hz)
  have hlhs : ((N : ℂ) ^ r * (pointGram z r).det).re = (N : ℝ) ^ r * (pointGram z r).det.re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hrhs :
      (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ((‖z p.1 - z p.2‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), ‖z p.1 - z p.2‖ ^ 2 := by
    simp_rw [← Complex.ofReal_prod, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hlhs, hrhs] at hre
  have hNr : (N : ℝ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hN.ne')
  rw [inv_pow, eq_inv_mul_iff_mul_eq₀ hNr]
  exact hre

private lemma powersetCard_fin_sum_eq_range {R : Type*} [CommRing R] {N r : ℕ}
    (g : ℕ → ℕ → R) :
    (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
      ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), g p.1.val p.2.val) =
    ∑ s ∈ (Finset.range N).powersetCard r,
      ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), g p.1 p.2 := by
  let emb : Fin N ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  refine Finset.sum_bij (fun s _ => s.map emb) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powersetCard] at hs ⊢
    refine ⟨?_, by rw [Finset.card_map, hs.2]⟩
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
    exact Finset.mem_range.mpr a.isLt
  · intro s₁ _ s₂ _ h
    exact Finset.map_injective emb h
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    let s : Finset (Fin N) := Finset.univ.filter fun a : Fin N => a.val ∈ t
    have hmap : s.map emb = t := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, s, emb,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx; exact ⟨⟨x, Finset.mem_range.mp (ht.1 hx)⟩, hx, rfl⟩
    refine ⟨s, ?_, hmap⟩
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [← Finset.card_map emb, hmap, ht.2]
  · intro s _
    refine Finset.prod_bij (fun p _ => (p.1.val, p.2.val)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨Finset.mem_map_of_mem emb hp.1.1, Finset.mem_map_of_mem emb hp.1.2⟩, hp.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      rcases Finset.mem_map.mp hq.1.1 with ⟨a, ha, hqa⟩
      rcases Finset.mem_map.mp hq.1.2 with ⟨b, hb, hqb⟩
      have hqa' : a.val = q.1 := hqa
      have hqb' : b.val = q.2 := hqb
      refine ⟨(a, b), ?_, Prod.ext hqa' hqb'⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha, hb⟩, show a.val < b.val by rw [hqa', hqb']; exact hq.2⟩
    · intro _ _
      rfl

/-- **A7 exact finite Cauchy–Binet expansion for `orbitGram` (complex form):**
`N^r · det (orbitGram x b N r h) = ∑_{s ⊆ {0,…,N-1}, |s|=r} ∏_{j < k ∈ s} ‖z_j - z_k‖^2`. -/
theorem orbitGram_det_eq_cauchy_binet_complex (x : ℝ) (b N r : ℕ) (h : ℤ) :
    (N : ℂ) ^ r * (orbitGram x b N r h).det =
      ∑ s ∈ (Finset.range N).powersetCard r,
        ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2),
          ((‖orbitPoint x b h p.1 - orbitPoint x b h p.2‖ ^ 2 : ℝ) : ℂ) := by
  rw [orbitGram_eq_pointGram, pointGram_det_eq_cauchy_binet_complex
    (fun n => norm_orbitPoint x b h n.val)]
  exact powersetCard_fin_sum_eq_range
    (fun j k => ((‖orbitPoint x b h j - orbitPoint x b h k‖ ^ 2 : ℝ) : ℂ))

/-- **A7 exact finite Cauchy–Binet expansion for `orbitGram` (real form):**
`(orbitGram x b N r h).det.re = N^(-r) · ∑_{s ⊆ {0,…,N-1}, |s|=r} ∏_{j < k ∈ s} ‖z_j - z_k‖^2`. -/
theorem orbitGram_det_eq_cauchy_binet (x : ℝ) (b : ℕ) {N : ℕ} (hN : 0 < N) (r : ℕ) (h : ℤ) :
    (orbitGram x b N r h).det.re =
      (N : ℝ)⁻¹ ^ r * ∑ s ∈ (Finset.range N).powersetCard r,
        ∏ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2),
          ‖orbitPoint x b h p.1 - orbitPoint x b h p.2‖ ^ 2 := by
  rw [orbitGram_eq_pointGram, pointGram_det_eq_cauchy_binet hN
    (fun n => norm_orbitPoint x b h n.val)]
  rw [powersetCard_fin_sum_eq_range (fun j k => ‖orbitPoint x b h j - orbitPoint x b h k‖ ^ 2)]

/-- Vanishing of `orbitGram` determinant whenever `r > N`. -/
theorem orbitGram_det_eq_zero_of_lt (x : ℝ) (b N r : ℕ) (h : ℤ) (hNr : N < r) :
    (orbitGram x b N r h).det = 0 := by
  by_cases hN0 : N = 0
  · subst hN0
    have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hNr
    have hzero : orbitGram x b 0 r h = 0 := by
      ext i j
      simp [orbitGram]
    rw [hzero, Matrix.det_zero]
  · have hmul := orbitGram_det_eq_cauchy_binet_complex x b N r h
    have hempty : (Finset.range N).powersetCard r = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using hNr)
    rw [hempty, Finset.sum_empty] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero r (Nat.cast_ne_zero.mpr hN0))

/-- **Rank-only positivity for irrational orbits (Proposition 1.6 / Theorem 7.4):**
for every irrational `x`, base `b ≥ 2`, nonzero frequency `h`, and `r ≤ N` with `0 < N`,
every Cauchy–Binet term is strictly positive and `0 < (orbitGram x b N r h).det.re`. -/
theorem orbitGram_det_pos_of_irrational {x : ℝ} (hx : Irrational x) {b : ℕ} (hb : 2 ≤ b)
    {h : ℤ} (hh : h ≠ 0) {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N) :
    0 < (orbitGram x b N r h).det.re := by
  rw [orbitGram_det_eq_cauchy_binet x b hN r h]
  have hpre : 0 < (N : ℝ)⁻¹ ^ r := pow_pos (inv_pos.mpr (Nat.cast_pos.mpr hN)) r
  refine mul_pos hpre ?_
  have hne : ((Finset.range N).powersetCard r).Nonempty := by
    refine ⟨Finset.range r, Finset.mem_powersetCard.mpr ⟨Finset.range_mono hrN, Finset.card_range r⟩⟩
  refine Finset.sum_pos (fun s _ => ?_) hne
  refine Finset.prod_pos fun p hp => ?_
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hdistinct : orbitPoint x b h p.1 ≠ orbitPoint x b h p.2 := by
    intro heq
    simp only [orbitPoint, Complex.exp_eq_exp_iff_exists_int] at heq
    rcases heq with ⟨k, hk⟩
    have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hreal_c :
        ((h : ℂ) * (((b : ℝ) ^ p.1 * x : ℝ) : ℂ)) =
          (h : ℂ) * (((b : ℝ) ^ p.2 * x : ℝ) : ℂ) + (k : ℂ) := by
      apply mul_left_cancel₀ h2piI
      linear_combination hk
    have hreal := congrArg Complex.re hreal_c
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hreal
    have hb_lt : (b : ℤ) ^ p.1 < (b : ℤ) ^ p.2 :=
      pow_lt_pow_right₀ (by exact_mod_cast (show 1 < b by omega)) hlt
    have hden_ne : (h * ((b : ℤ) ^ p.1 - (b : ℤ) ^ p.2) : ℤ) ≠ 0 :=
      mul_ne_zero hh (sub_ne_zero.mpr (ne_of_lt hb_lt))
    have hx_rat : x = (k : ℝ) / ((h * ((b : ℤ) ^ p.1 - (b : ℤ) ^ p.2) : ℤ) : ℝ) := by
      have hden_r : (((h * ((b : ℤ) ^ p.1 - (b : ℤ) ^ p.2) : ℤ) : ℝ)) ≠ 0 :=
        Int.cast_ne_zero.mpr hden_ne
      rw [eq_div_iff hden_r]
      push_cast
      linarith
    exact hx.ne_rational k (h * ((b : ℤ) ^ p.1 - (b : ℤ) ^ p.2)) hx_rat
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hdistinct)) 2

/-! ## 5. Track A6: finite regularized matrix positivity -/

/-- **A6 finite regularization (complex-scalar form):** for any complex PSD matrix `G` and
`0 < t ≤ 1`, the regularized matrix `(1 - t) G + t I` is positive definite. -/
theorem posSemidef_regularized_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℂ} (hG : G.PosSemidef) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (((1 - t : ℝ) : ℂ) • G + (t : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
  have heq :
      (((1 - t : ℝ) : ℂ) • G + (t : ℂ) • (1 : Matrix n n ℂ)) =
        (1 - t) • G + t • (1 : Matrix n n ℂ) := by
    ext i j
    simp [Complex.real_smul]
  rw [heq]
  exact Matrix.PosDef.posSemidef_add (hG.smul (sub_nonneg.mpr ht1)) (Matrix.PosDef.one.smul ht0)

/-- **A6 finite regularization (real-scalar form):** for any complex PSD matrix `G` and
`0 < t ≤ 1`, `(1 - t) • G + t • 1` is positive definite. -/
theorem posSemidef_regularized_posDef_realSmul {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℂ} (hG : G.PosSemidef) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((1 - t) • G + t • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add (hG.smul (sub_nonneg.mpr ht1)) (Matrix.PosDef.one.smul ht0)

/-- **A6 finite regularized determinant lower bound:** for any `r × r` complex PSD matrix `G` and
`0 < t ≤ 1`, `det ((1 - t) G + t I) ≥ t ^ r`. -/
theorem posSemidef_regularized_det_ge {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosSemidef)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ r ≤ (((1 - t : ℝ) : ℂ) • G + (t : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).det.re := by
  let R : Matrix (Fin r) (Fin r) ℂ :=
    ((1 - t : ℝ) : ℂ) • G + (t : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)
  have hRpd : R.PosDef := posSemidef_regularized_posDef hG ht0 ht1
  have hRh : R.IsHermitian := hRpd.isHermitian
  have hdet : R.det.re = ∏ i : Fin r, hRh.eigenvalues i := by
    rw [hRh.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_re]
  rw [hdet]
  have heig : ∀ i : Fin r, t ≤ hRh.eigenvalues i := by
    intro i
    rw [hRh.eigenvalues_eq i]
    let u : Fin r → ℂ := ⇑(hRh.eigenvectorBasis i)
    have hnorm : star u ⬝ᵥ u = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        RCLike.ofReal_eq_complex_ofReal, hRh.eigenvectorBasis.orthonormal.1 i,
        Complex.ofReal_one, one_pow]
    have hquad :
        star u ⬝ᵥ (R *ᵥ u) =
          ((1 - t : ℝ) : ℂ) * (star u ⬝ᵥ (G *ᵥ u)) + (t : ℂ) := by
      simp only [R, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_add, dotProduct_smul, smul_eq_mul, hnorm, mul_one]
    rw [hquad, RCLike.re_to_complex, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    have hGnonneg : 0 ≤ (star u ⬝ᵥ (G *ᵥ u)).re := by
      simpa using hG.re_dotProduct_nonneg u
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hGnonneg]
  calc
    t ^ r = ∏ _i : Fin r, t := by simp
    _ ≤ ∏ i : Fin r, hRh.eigenvalues i :=
      Finset.prod_le_prod₀ (fun _ _ => ht0.le) fun i _ => heig i

/-- **A6 regularized orbit Gram matrix** is positive definite for `0 < t ≤ 1`. -/
theorem orbitGram_regularized_posDef (x : ℝ) (b N r : ℕ) (h : ℤ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (((1 - t : ℝ) : ℂ) • orbitGram x b N r h + (t : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosDef :=
  posSemidef_regularized_posDef (orbitGram_posSemidef x b N r h) ht0 ht1

/-- **A6 regularized orbit Gram determinant floor** `det ((1 - t) G_{N,r}(h) + t I) ≥ t ^ r`. -/
theorem orbitGram_regularized_det_ge (x : ℝ) (b N r : ℕ) (h : ℤ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ r ≤
      (((1 - t : ℝ) : ℂ) • orbitGram x b N r h +
        (t : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).det.re :=
  posSemidef_regularized_det_ge (orbitGram_posSemidef x b N r h) ht0 ht1

end NormalityChecker.ToeplitzDeterminants
