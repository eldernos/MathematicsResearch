module

public import NormalityChecker.LogTwo
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Arithmetic Hankel determinants for `ln 2` (Phase 26, Track H1)

Kernel-checked versions of the Track B results `B1`, `B3` and `B4` of
`notes/phase26/arithmetic-hankel-determinants.md`.

* `B1` (prime-centred Hankel pole): for every prime `p`, every `1 ≤ r ≤ p` and every matrix of
  `p`-integral shifts `m`, the matrix `H i j = s_{p-r+1+i+j} - m i j` built from the BBP states
  `s_n = logPrefix n` satisfies `p • H ≡` anti-triangular `(mod p)`, `det H ≠ 0` and
  `v_p (det H) = -r` (`bbpHankel_det_ne_zero`, `bbpHankel_det_padicValRat`).
* `B3` (rank-sensitive local denominators): an integer matrix whose reduction modulo a prime `q`
  has rank `≤ s` has determinant divisible by `q ^ (r - s)` (`int_pow_dvd_det_of_rank_le`); a
  rational matrix `H` with `q • H` `q`-integral of reduced rank `≤ s` has `v_q (det H) ≥ -s`
  (`ratMatrix_det_padicValRat_ge_neg_rank`).  For BBP windows and primes `q` not dividing any
  integer of `(M, M + 2r - 2]` the reduced rank is at most one
  (`bbpHankel_nonEntering_rank_le_one`), so `v_q (det H) ≥ -1`, and in general
  `v_q (det H) ≥ -e` when `q ^ e • s_M` is `q`-integral.
* `B4` (positive moments): `2 ^ n * log 2 = s_n + ∫₀¹ tⁿ / (2 - t) dt`, the clean-window
  decomposition `H_c = ε • v vᵀ - K`, positive definiteness of `K`, the Loewner sandwich
  `C / 2 ≤ K ≤ C` against the Hilbert/Cauchy matrix `C i j = 1 / (M + i + j + 1)`, the resulting
  determinant comparison `2 ^ (-r) det C ≤ det K ≤ det C`, and the matrix determinant lemma for
  `H_c`.
-/

@[expose] public section

open Matrix Finset

namespace NormalityChecker.HankelLogTwo

/-! ## 0. `p`-integral rationals and reduction modulo `p` -/

/-- The subring `ℚ ∩ ℤ_(p)` of rationals whose reduced denominator is prime to `p`. -/
def pIntegral (p : ℕ) [hp : Fact p.Prime] : Subring ℚ where
  carrier := {x | ¬ p ∣ x.den}
  mul_mem' {x y} hx hy h :=
    ((Nat.Prime.dvd_mul hp.out).mp (h.trans (Rat.mul_den_dvd x y))).elim hx hy
  one_mem' := by simpa using hp.out.ne_one
  add_mem' {x y} hx hy h :=
    ((Nat.Prime.dvd_mul hp.out).mp (h.trans (Rat.add_den_dvd x y))).elim hx hy
  zero_mem' := by simpa using hp.out.ne_one
  neg_mem' {x} hx := by simpa [Rat.neg_den] using hx

section pIntegral

variable {p : ℕ} [hp : Fact p.Prime]

theorem mem_pIntegral {x : ℚ} : x ∈ pIntegral p ↔ ¬ p ∣ x.den := Iff.rfl

theorem den_cast_ne_zero {x : ℚ} (hx : x ∈ pIntegral p) : ((x.den : ℕ) : ZMod p) ≠ 0 :=
  fun h => hx ((ZMod.natCast_eq_zero_iff _ _).mp h)

/-- Reduction modulo `p` of `p`-integral rationals, as a ring homomorphism. -/
def pReduce (p : ℕ) [Fact p.Prime] : pIntegral p →+* ZMod p where
  toFun x := ((x : ℚ) : ZMod p)
  map_one' := by simp
  map_mul' x y := Rat.cast_mul_of_ne_zero (den_cast_ne_zero x.2) (den_cast_ne_zero y.2)
  map_zero' := by simp
  map_add' x y := Rat.cast_add_of_ne_zero (den_cast_ne_zero x.2) (den_cast_ne_zero y.2)

theorem pReduce_apply (x : pIntegral p) : pReduce p x = ((x : ℚ) : ZMod p) := rfl

theorem cast_add_mem {x y : ℚ} (hx : x ∈ pIntegral p) (hy : y ∈ pIntegral p) :
    ((x + y : ℚ) : ZMod p) = (x : ZMod p) + (y : ZMod p) :=
  Rat.cast_add_of_ne_zero (den_cast_ne_zero hx) (den_cast_ne_zero hy)

theorem cast_mul_mem {x y : ℚ} (hx : x ∈ pIntegral p) (hy : y ∈ pIntegral p) :
    ((x * y : ℚ) : ZMod p) = (x : ZMod p) * (y : ZMod p) :=
  Rat.cast_mul_of_ne_zero (den_cast_ne_zero hx) (den_cast_ne_zero hy)

theorem cast_sub_mem {x y : ℚ} (hx : x ∈ pIntegral p) (hy : y ∈ pIntegral p) :
    ((x - y : ℚ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  rw [sub_eq_add_neg, cast_add_mem hx (neg_mem hy), Rat.cast_neg, ← sub_eq_add_neg]

theorem cast_pow_mem {x : ℚ} (hx : x ∈ pIntegral p) (k : ℕ) :
    ((x ^ k : ℚ) : ZMod p) = (x : ZMod p) ^ k :=
  map_pow (pReduce p) ⟨x, hx⟩ k

theorem natCast_mem (k : ℕ) : (k : ℚ) ∈ pIntegral p := _root_.natCast_mem (pIntegral p) k

theorem intCast_mem (z : ℤ) : (z : ℚ) ∈ pIntegral p := _root_.intCast_mem (pIntegral p) z

theorem two_mem : (2 : ℚ) ∈ pIntegral p := ofNat_mem (pIntegral p) 2

theorem two_pow_mem (k : ℕ) : (2 : ℚ) ^ k ∈ pIntegral p := pow_mem two_mem k

theorem inv_natCast_mem {k : ℕ} (hk : ¬ p ∣ k) : ((k : ℚ)⁻¹) ∈ pIntegral p := by
  rw [mem_pIntegral, Rat.inv_natCast_den]
  split_ifs with h
  · simpa using hp.out.ne_one
  · exact hk

theorem cast_prime_mul {x : ℚ} (hx : x ∈ pIntegral p) : (((p : ℚ) * x : ℚ) : ZMod p) = 0 := by
  rw [cast_mul_mem (natCast_mem p) hx, Rat.cast_natCast, ZMod.natCast_self, zero_mul]

/-- A `p`-integral rational with nonzero reduction is a nonzero `p`-adic unit. -/
theorem padicValRat_eq_zero_of_cast_ne_zero {x : ℚ} (hx : x ∈ pIntegral p)
    (h : (x : ZMod p) ≠ 0) : x ≠ 0 ∧ padicValRat p x = 0 := by
  have hnum : ¬ (p : ℤ) ∣ x.num := by
    intro hd
    apply h
    rw [Rat.cast_def, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd, zero_div]
  refine ⟨fun h0 => hnum (by simp [h0]), ?_⟩
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum, multiplicity_eq_zero_of_not_dvd hx]
  simp

/-- `p`-integral rationals have nonnegative `p`-adic valuation. -/
theorem padicValRat_nonneg_of_mem {x : ℚ} (hx : x ∈ pIntegral p) : 0 ≤ padicValRat p x := by
  rw [padicValRat_def, multiplicity_eq_zero_of_not_dvd hx]
  simp

/-- A `p`-integral rational with zero reduction is `p` times a `p`-integral rational. -/
theorem exists_eq_prime_mul_of_cast_eq_zero {x : ℚ} (hx : x ∈ pIntegral p)
    (h : (x : ZMod p) = 0) : ∃ y ∈ pIntegral p, x = p * y := by
  have hnum : (p : ℤ) ∣ x.num := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Rat.cast_def] at h
    exact (div_eq_zero_iff.mp h).resolve_right (den_cast_ne_zero hx)
  obtain ⟨a, ha⟩ := hnum
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hy : x / p = Rat.divInt a x.den := by
    rw [Rat.divInt_eq_div]
    conv_lhs => rw [← Rat.num_div_den x, ha]
    push_cast
    field_simp
  refine ⟨x / p, ?_, by field_simp⟩
  rw [mem_pIntegral, hy]
  intro hd
  apply hx
  have h1 : ((Rat.divInt a x.den).den : ℤ) ∣ (x.den : ℤ) := Rat.den_dvd a x.den
  exact hd.trans (Int.natCast_dvd_natCast.mp h1)

/-- Determinants of `p`-integral matrices are `p`-integral and commute with reduction. -/
theorem det_mem_and_cast {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℚ)
    (hA : ∀ i j, A i j ∈ pIntegral p) :
    A.det ∈ pIntegral p ∧ ((A.det : ℚ) : ZMod p) = (A.map fun x : ℚ => (x : ZMod p)).det := by
  let B : Matrix n n (pIntegral p) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hdet : ((B.det : pIntegral p) : ℚ) = A.det := by
    change (pIntegral p).subtype B.det = _
    rw [RingHom.map_det]
    rfl
  refine ⟨hdet ▸ B.det.2, ?_⟩
  rw [← hdet]
  change pReduce p B.det = _
  rw [RingHom.map_det]
  rfl

end pIntegral

/-! ## 1. `B1`: the prime-centred BBP Hankel determinant -/

/-- The BBP recurrence `s_{n+1} = 2 s_n + 1/(n+1)` in inverse form. -/
theorem logPrefix_succ (n : ℕ) : logPrefix (n + 1) = 2 * logPrefix n + ((n + 1 : ℕ) : ℚ)⁻¹ := by
  simp only [logPrefix, one_div]
  push_cast
  ring

section B1

variable {p : ℕ} [hp : Fact p.Prime]

/-- `s_n` is `p`-integral for `n < p`. -/
theorem logPrefix_mem_of_lt {n : ℕ} (hn : n < p) : logPrefix n ∈ pIntegral p := by
  induction n with
  | zero => simp [logPrefix]
  | succ n ih =>
    rw [logPrefix_succ]
    exact add_mem (mul_mem two_mem (ih (by omega)))
      (inv_natCast_mem (Nat.not_dvd_of_pos_of_lt (by omega) hn))

/-- In the band `p ≤ n < 2p`, `p s_n` is `p`-integral and `p s_n ≡ 2 ^ (n - p) (mod p)`. -/
theorem logPrefix_prime_band {n : ℕ} (hlo : p ≤ n) (hhi : n < 2 * p) :
    (p : ℚ) * logPrefix n ∈ pIntegral p ∧
      (((p : ℚ) * logPrefix n : ℚ) : ZMod p) = 2 ^ (n - p) := by
  induction n, hlo using Nat.le_induction with
  | base =>
    have key : ∀ k : ℕ, ((k + 1 : ℕ) : ℚ) * logPrefix (k + 1) =
        2 * ((k + 1 : ℕ) : ℚ) * logPrefix k + 1 := by
      intro k
      rw [logPrefix_succ]
      have : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
    have e := key (p - 1)
    rw [Nat.sub_add_cancel hp.out.one_le] at e
    have hk : logPrefix (p - 1) ∈ pIntegral p := logPrefix_mem_of_lt (by have := hp.out.pos; omega)
    have h2p : 2 * (p : ℚ) ∈ pIntegral p := mul_mem two_mem (natCast_mem p)
    rw [e]
    refine ⟨add_mem (mul_mem h2p hk) (one_mem _), ?_⟩
    rw [cast_add_mem (mul_mem h2p hk) (one_mem _), cast_mul_mem h2p hk,
      cast_mul_mem two_mem (natCast_mem p), Rat.cast_natCast, ZMod.natCast_self]
    simp
  | succ n hn ih =>
    have e : (p : ℚ) * logPrefix (n + 1) =
        2 * ((p : ℚ) * logPrefix n) + (p : ℚ) * ((n + 1 : ℕ) : ℚ)⁻¹ := by
      rw [logPrefix_succ]
      ring
    have hinv : ((n + 1 : ℕ) : ℚ)⁻¹ ∈ pIntegral p := by
      refine inv_natCast_mem fun hd => ?_
      obtain ⟨c, hc⟩ := hd
      have hc2 : c < 2 := by
        by_contra h
        have h' : 2 ≤ c := by omega
        nlinarith
      interval_cases c <;> omega
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hA : 2 * ((p : ℚ) * logPrefix n) ∈ pIntegral p := mul_mem two_mem h1
    have hB : (p : ℚ) * ((n + 1 : ℕ) : ℚ)⁻¹ ∈ pIntegral p := mul_mem (natCast_mem p) hinv
    rw [e]
    refine ⟨add_mem hA hB, ?_⟩
    rw [cast_add_mem hA hB, cast_mul_mem two_mem h1, h2, cast_prime_mul hinv, add_zero,
      show n + 1 - p = (n - p) + 1 by omega, pow_succ]
    simp [mul_comm]

end B1

/-- The prime-centred `r × r` BBP Hankel matrix of `ln 2` with arbitrary rational shifts:
`H i j = s_{p-r+1+i+j} - m i j`, where `s_n = logPrefix n`. -/
def bbpHankel (p r : ℕ) (m : Fin r → Fin r → ℚ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j => logPrefix (p - r + 1 + i.val + j.val) - m i j

theorem bbpHankel_apply (p r : ℕ) (m : Fin r → Fin r → ℚ) (i j : Fin r) :
    bbpHankel p r m i j = logPrefix (p - r + 1 + i.val + j.val) - m i j := rfl

/-- The anti-triangular reduction pattern: `0` above the anti-diagonal, `2 ^ (i + j - (r - 1))`
on and below it. -/
def antiTriangular (R : Type*) [Semiring R] (r : ℕ) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => if i.val + j.val < r - 1 then 0 else 2 ^ (i.val + j.val - (r - 1))

/-- Reversing the columns of the anti-triangular pattern gives a unipotent lower-triangular
matrix, so its determinant is the sign of the reversal permutation. -/
theorem antiTriangular_det (R : Type*) [CommRing R] (r : ℕ) :
    (antiTriangular R r).det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r)) : ℤ) : R) := by
  have h := det_permute' (Fin.revPerm : Equiv.Perm (Fin r)) (antiTriangular R r)
  have htri : ((antiTriangular R r).submatrix id Fin.revPerm).det = 1 := by
    rw [det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have hi := i.isLt
      simp only [submatrix_apply, id_eq, Fin.revPerm_apply, antiTriangular, of_apply, Fin.val_rev]
      split_ifs with h
      · omega
      · rw [show i.val + (r - (i.val + 1)) - (r - 1) = 0 by omega, pow_zero]
    · intro i j hij
      have hj := j.isLt
      have hij' : i.val < j.val := Fin.lt_def.mp hij
      simp only [submatrix_apply, id_eq, Fin.revPerm_apply, antiTriangular, of_apply, Fin.val_rev]
      split_ifs with h
      · rfl
      · omega
  rw [htri] at h
  set s : R := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r)) : ℤ) : R)
  have hs : s * s = 1 := by
    simp only [s]
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  calc (antiTriangular R r).det = (s * s) * (antiTriangular R r).det := by rw [hs, one_mul]
    _ = s * (s * (antiTriangular R r).det) := by ring
    _ = s := by rw [← h, mul_one]

theorem sign_cast_ne_zero (R : Type*) [CommRing R] [Nontrivial R] {r : ℕ} :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r)) : ℤ) : R) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r))) with h | h <;>
    simp [h]

section B1Matrix

variable {p : ℕ} [hp : Fact p.Prime]

/-- **`B1`, entrywise structure.** For `1 ≤ r ≤ p` and `p`-integral shifts, every entry of
`p • H` is `p`-integral, and modulo `p` it is `0` strictly above the anti-diagonal
(`i + j < r - 1`) and `2 ^ (i + j - (r - 1))` on or below it (in particular `1` on it). -/
theorem bbpHankel_prime_mul_reduction {r : ℕ} (hrp : r ≤ p) (m : Fin r → Fin r → ℚ)
    (hm : ∀ i j, ¬ p ∣ (m i j).den) (i j : Fin r) :
    (p : ℚ) * bbpHankel p r m i j ∈ pIntegral p ∧
      (((p : ℚ) * bbpHankel p r m i j : ℚ) : ZMod p) = antiTriangular (ZMod p) r i j := by
  have hmi : m i j ∈ pIntegral p := hm i j
  have hi := i.isLt
  have hj := j.isLt
  rw [bbpHankel_apply]
  simp only [antiTriangular, of_apply]
  split_ifs with h
  · have hs := logPrefix_mem_of_lt (p := p) (n := p - r + 1 + i.val + j.val) (by omega)
    have hH : logPrefix (p - r + 1 + i.val + j.val) - m i j ∈ pIntegral p := sub_mem hs hmi
    exact ⟨mul_mem (natCast_mem p) hH, cast_prime_mul hH⟩
  · obtain ⟨h1, h2⟩ :=
      logPrefix_prime_band (p := p) (n := p - r + 1 + i.val + j.val) (by omega) (by omega)
    have hpm : (p : ℚ) * m i j ∈ pIntegral p := mul_mem (natCast_mem p) hmi
    rw [mul_sub]
    refine ⟨sub_mem h1 hpm, ?_⟩
    rw [cast_sub_mem h1 hpm, h2, cast_prime_mul hmi, sub_zero]
    congr 1
    omega

/-- **`B1`, anti-diagonal.** On the anti-diagonal `i + j = r - 1`, `p H i j ≡ 1 (mod p)`. -/
theorem bbpHankel_antidiag_reduction {r : ℕ} (hrp : r ≤ p) (m : Fin r → Fin r → ℚ)
    (hm : ∀ i j, ¬ p ∣ (m i j).den) (i j : Fin r) (hij : i.val + j.val = r - 1) :
    (((p : ℚ) * bbpHankel p r m i j : ℚ) : ZMod p) = 1 := by
  rw [(bbpHankel_prime_mul_reduction hrp m hm i j).2]
  simp [antiTriangular, hij]

/-- **`B1`, determinant congruence.** `p ^ r det H` is `p`-integral and congruent modulo `p` to
the sign of the column reversal, i.e. to `±1`. -/
theorem bbpHankel_det_reduction {r : ℕ} (hrp : r ≤ p) (m : Fin r → Fin r → ℚ)
    (hm : ∀ i j, ¬ p ∣ (m i j).den) :
    (p : ℚ) ^ r * (bbpHankel p r m).det ∈ pIntegral p ∧
      (((p : ℚ) ^ r * (bbpHankel p r m).det : ℚ) : ZMod p) =
        ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r)) : ℤ) : ZMod p) := by
  have hA : ∀ i j, ((p : ℚ) • bbpHankel p r m) i j ∈ pIntegral p := fun i j => by
    simpa [Matrix.smul_apply] using (bbpHankel_prime_mul_reduction hrp m hm i j).1
  obtain ⟨hmem, hcast⟩ := det_mem_and_cast _ hA
  have hdet : ((p : ℚ) • bbpHankel p r m).det = (p : ℚ) ^ r * (bbpHankel p r m).det := by
    rw [det_smul, Fintype.card_fin]
  rw [hdet] at hmem hcast
  refine ⟨hmem, ?_⟩
  rw [hcast, ← antiTriangular_det]
  congr 1
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact (bbpHankel_prime_mul_reduction hrp m hm i j).2

end B1Matrix

/-- **`B1` (Theorem 1.1).** For every prime `p` (including `p = 2`), every `1 ≤ r ≤ p` and every
matrix of `p`-integral rational shifts, the prime-centred BBP Hankel determinant is nonzero and
has exact `p`-adic valuation `-r`. -/
theorem bbpHankel_det_ne_zero_and_padicValRat {p r : ℕ} (hp : p.Prime) (hrp : r ≤ p)
    (m : Fin r → Fin r → ℚ) (hm : ∀ i j, ¬ p ∣ (m i j).den) :
    (bbpHankel p r m).det ≠ 0 ∧ padicValRat p (bbpHankel p r m).det = -(r : ℤ) := by
  have := Fact.mk hp
  obtain ⟨hmem, hcast⟩ := bbpHankel_det_reduction hrp m hm
  have hne : (((p : ℚ) ^ r * (bbpHankel p r m).det : ℚ) : ZMod p) ≠ 0 := by
    rw [hcast]
    exact sign_cast_ne_zero _
  obtain ⟨h0, hv⟩ := padicValRat_eq_zero_of_cast_ne_zero hmem hne
  have hdet0 : (bbpHankel p r m).det ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨hdet0, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [padicValRat.mul (pow_ne_zero _ hp0) hdet0, padicValRat.pow,
    padicValRat.self hp.one_lt] at hv
  linarith

/-- **`B1`, nonvanishing** for `p`-integral rational shifts. -/
theorem bbpHankel_det_ne_zero_of_pIntegral {p r : ℕ} (hp : p.Prime) (hrp : r ≤ p)
    (m : Fin r → Fin r → ℚ) (hm : ∀ i j, ¬ p ∣ (m i j).den) : (bbpHankel p r m).det ≠ 0 :=
  (bbpHankel_det_ne_zero_and_padicValRat hp hrp m hm).1

/-- **`B1`, exact pole** for `p`-integral rational shifts: `v_p (det H) = -r`. -/
theorem bbpHankel_det_padicValRat_of_pIntegral {p r : ℕ} (hp : p.Prime) (hrp : r ≤ p)
    (m : Fin r → Fin r → ℚ) (hm : ∀ i j, ¬ p ∣ (m i j).den) :
    padicValRat p (bbpHankel p r m).det = -(r : ℤ) :=
  (bbpHankel_det_ne_zero_and_padicValRat hp hrp m hm).2

theorem intCast_den_not_dvd {p : ℕ} (hp : p.Prime) (z : ℤ) : ¬ p ∣ (z : ℚ).den := by
  simpa using hp.ne_one

/-- **`B1`, unconditional nonvanishing** for arbitrary integer shifts `m i j ∈ ℤ`. -/
theorem bbpHankel_det_ne_zero {p r : ℕ} (hp : p.Prime) (hrp : r ≤ p) (m : Fin r → Fin r → ℤ) :
    (bbpHankel p r fun i j => (m i j : ℚ)).det ≠ 0 :=
  bbpHankel_det_ne_zero_of_pIntegral hp hrp _ fun i j => intCast_den_not_dvd hp (m i j)

/-- **`B1`, exact pole** for arbitrary integer shifts: `v_p (det H) = -r`. -/
theorem bbpHankel_det_padicValRat {p r : ℕ} (hp : p.Prime) (hrp : r ≤ p)
    (m : Fin r → Fin r → ℤ) :
    padicValRat p (bbpHankel p r fun i j => (m i j : ℚ)).det = -(r : ℤ) :=
  bbpHankel_det_padicValRat_of_pIntegral hp hrp _ fun i j => intCast_den_not_dvd hp (m i j)

/-- **`B1` for genuine Hankel shifts** `H i j = s_{M+i+j} - m_{M+i+j}` with `m : ℕ → ℤ`. -/
theorem bbpHankel_hankelShift_det {p r : ℕ} (hp : p.Prime) (hrp : r ≤ p) (m : ℕ → ℤ) :
    (bbpHankel p r fun i j => (m (p - r + 1 + i.val + j.val) : ℚ)).det ≠ 0 ∧
      padicValRat p (bbpHankel p r fun i j => (m (p - r + 1 + i.val + j.val) : ℚ)).det =
        -(r : ℤ) :=
  ⟨bbpHankel_det_ne_zero hp hrp fun i j => m (p - r + 1 + i.val + j.val),
    bbpHankel_det_padicValRat hp hrp fun i j => m (p - r + 1 + i.val + j.val)⟩

/-! ## 2. `B3`: rank-sensitive prime-local denominators -/

section RankLemma

variable {S F : Type*} [CommRing S] [Field F] {n : Type*} [Fintype n] [DecidableEq n]

theorem updateCol_mulVec_of_apply_eq_zero {R : Type*} [CommRing R] (M : Matrix n n R) (j : n)
    (c x : n → R) (hx : x j = 0) : (M.updateCol j c) *ᵥ x = M *ᵥ x := by
  ext i
  simp only [mulVec, dotProduct, updateCol_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · subst h
    simp [hx]
  · rfl

/-- **Generic rank-sensitive divisibility.** Let `φ : S →+* F` be a surjection onto a field whose
kernel is generated by `q`.  If the kernel of the reduction `A.map φ` has dimension at least `k`,
then `q ^ k ∣ det A`.  (Column operations lifted from `F`, one kernel vector at a time.) -/
theorem pow_dvd_det_of_le_finrank_ker (φ : S →+* F) (q : S) (hsurj : Function.Surjective φ)
    (hker : ∀ x, φ x = 0 → ∃ y, x = q * y) :
    ∀ (k : ℕ) (A : Matrix n n S),
      k ≤ Module.finrank F (LinearMap.ker (A.map φ).mulVecLin) → q ^ k ∣ A.det := by
  intro k
  induction k with
  | zero => intro A _; simp
  | succ k ih =>
    intro A hk
    set V := LinearMap.ker (A.map φ).mulVecLin with hV
    have hVpos : 0 < Module.finrank F V := by omega
    have hVne : V ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hVpos
      exact lt_irrefl _ hVpos
    obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv0
    set v' : n → F := (v j)⁻¹ • v with hv'
    have hv'V : v' ∈ V := V.smul_mem _ hvV
    have hv'j : v' j = 1 := by simp [v', hj]
    choose lift hlift using hsurj
    let w : n → S := fun l => if l = j then 1 else lift (v' l)
    have hw : ∀ l, φ (w l) = v' l := by
      intro l
      by_cases h : l = j
      · subst h
        simp [w, hv'j]
      · simp [w, h, hlift]
    have hwj : w j = 1 := by simp [w]
    have hAw : ∀ i, φ ((A *ᵥ w) i) = 0 := by
      intro i
      rw [RingHom.map_mulVec]
      have hcomp : (φ ∘ w) = v' := funext hw
      rw [hcomp]
      have h0 : (A.map φ).mulVecLin v' = 0 := hv'V
      rw [mulVecLin_apply] at h0
      exact congrFun h0 i
    choose u hu using fun i => hker _ (hAw i)
    have hcol : A.updateCol j (A *ᵥ w) = A.updateCol j (q • u) := by
      congr 1
      funext i
      simp [hu i]
    have hdet1 : (A.updateCol j (A *ᵥ w)).det = A.det := by
      have h := congrFun (cramer_eq_adjugate_mulVec A (A *ᵥ w)) j
      rw [cramer_apply] at h
      rw [h, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, Pi.smul_apply, hwj,
        smul_eq_mul, mul_one]
    have hdet2 : (A.updateCol j (q • u)).det = q * (A.updateCol j u).det :=
      det_updateCol_smul _ _ _ _
    -- the kernel of the new reduction still has dimension `≥ k`
    set T : Submodule F (n → F) := LinearMap.ker (LinearMap.proj j : (n → F) →ₗ[F] F)
    have hsub : V ⊓ T ≤ LinearMap.ker ((A.updateCol j u).map φ).mulVecLin := by
      intro x hx
      obtain ⟨hxV, hxT⟩ := Submodule.mem_inf.mp hx
      have hxj : x j = 0 := hxT
      have hxV' : (A.map φ) *ᵥ x = 0 := hxV
      change ((A.updateCol j u).map φ) *ᵥ x = 0
      rw [map_updateCol, updateCol_mulVec_of_apply_eq_zero _ _ _ _ hxj, hxV']
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq V T
    have hle : Module.finrank F ↥(V ⊔ T) ≤ Fintype.card n := by
      have := Submodule.finrank_le (V ⊔ T)
      rwa [Module.finrank_fintype_fun_eq_card] at this
    have hT : Fintype.card n ≤ Module.finrank F T + 1 := by
      have h1 : Module.finrank F (LinearMap.range (LinearMap.proj j : (n → F) →ₗ[F] F)) +
          Module.finrank F T = Module.finrank F (n → F) :=
        LinearMap.finrank_range_add_finrank_ker _
      have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.proj j : (n → F) →ₗ[F] F))
      rw [Module.finrank_fintype_fun_eq_card] at h1
      rw [Module.finrank_self] at h2
      omega
    have hmono := Submodule.finrank_mono hsub
    obtain ⟨c, hc⟩ := ih (A.updateCol j u) (by omega)
    exact ⟨c, by rw [← hdet1, hcol, hdet2, hc]; ring⟩

/-- **Rank form.** If `A.map φ` has rank `≤ s`, then `q ^ (card n - s) ∣ det A`. -/
theorem pow_dvd_det_of_rank_le (φ : S →+* F) (q : S) (hsurj : Function.Surjective φ)
    (hker : ∀ x, φ x = 0 → ∃ y, x = q * y) (A : Matrix n n S) (s : ℕ)
    (hs : (A.map φ).rank ≤ s) : q ^ (Fintype.card n - s) ∣ A.det := by
  apply pow_dvd_det_of_le_finrank_ker φ q hsurj hker
  have h := LinearMap.finrank_range_add_finrank_ker (A.map φ).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  unfold Matrix.rank at hs
  omega

end RankLemma

/-- **`B3` (Theorem 3.1(1), integer form).** If an integer matrix has rank `≤ s` modulo a prime
`q`, then `q ^ (card n - s)` divides its determinant. -/
theorem int_pow_dvd_det_of_rank_le {n : Type*} [Fintype n] [DecidableEq n] {q : ℕ}
    [Fact q.Prime] (A : Matrix n n ℤ) (s : ℕ)
    (hs : (A.map (Int.castRingHom (ZMod q))).rank ≤ s) :
    (q : ℤ) ^ (Fintype.card n - s) ∣ A.det :=
  pow_dvd_det_of_rank_le (Int.castRingHom (ZMod q)) (q : ℤ) ZMod.intCast_surjective
    (fun x hx => (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx) A s hs

/-- **`B3` for `r × r` integer matrices**: rank `≤ s` modulo `q` forces `q ^ (r - s) ∣ det A`. -/
theorem int_fin_pow_dvd_det_of_rank_le {r q : ℕ} [Fact q.Prime] (A : Matrix (Fin r) (Fin r) ℤ)
    (s : ℕ) (hs : (A.map (Int.castRingHom (ZMod q))).rank ≤ s) :
    (q : ℤ) ^ (r - s) ∣ A.det := by
  simpa using int_pow_dvd_det_of_rank_le A s hs

section RatRank

variable {q : ℕ} [hq : Fact q.Prime]

theorem pReduce_surjective : Function.Surjective (pReduce q) := fun z =>
  ⟨⟨(z.val : ℚ), natCast_mem _⟩, by
    change (((z.val : ℚ)) : ZMod q) = z
    rw [Rat.cast_natCast, ZMod.natCast_zmod_val]⟩

theorem pReduce_ker (x : pIntegral q) (hx : pReduce q x = 0) :
    ∃ y, x = (q : pIntegral q) * y := by
  obtain ⟨y, hy, hxy⟩ := exists_eq_prime_mul_of_cast_eq_zero x.2 hx
  exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hxy)⟩

/-- **`B3` (Theorem 3.1(1), rational form).** Let `H` be a rational matrix such that `q • H` is
`q`-integral and its reduction modulo `q` has rank `≤ s`.  If `det H ≠ 0`, then
`v_q (det H) ≥ -s`. -/
theorem ratMatrix_det_padicValRat_ge_neg_rank {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℚ) (hint : ∀ i j, ¬ q ∣ ((q : ℚ) * H i j).den) (s : ℕ)
    (hs : (Matrix.of fun i j => (((q : ℚ) * H i j : ℚ) : ZMod q)).rank ≤ s)
    (hdet : H.det ≠ 0) : -(s : ℤ) ≤ padicValRat q H.det := by
  let B : Matrix n n (pIntegral q) := Matrix.of fun i j => ⟨(q : ℚ) * H i j, hint i j⟩
  have hBmap : B.map (pReduce q) = Matrix.of fun i j => (((q : ℚ) * H i j : ℚ) : ZMod q) := by
    ext i j
    rfl
  obtain ⟨c, hc⟩ := pow_dvd_det_of_rank_le (pReduce q) (q : pIntegral q) pReduce_surjective
    pReduce_ker B s (by rw [hBmap]; exact hs)
  have hBdet : ((B.det : pIntegral q) : ℚ) = (q : ℚ) ^ Fintype.card n * H.det := by
    change (pIntegral q).subtype B.det = _
    rw [RingHom.map_det, ← det_smul]
    rfl
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have key : (q : ℚ) ^ Fintype.card n * H.det = (q : ℚ) ^ (Fintype.card n - s) * (c : ℚ) := by
    rw [← hBdet, hc]
    simp
  have hc0 : (c : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at key
    exact mul_ne_zero (pow_ne_zero _ hq0) hdet key
  have hv := congrArg (padicValRat q) key
  rw [padicValRat.mul (pow_ne_zero _ hq0) hdet, padicValRat.mul (pow_ne_zero _ hq0) hc0,
    padicValRat.pow, padicValRat.pow, padicValRat.self hq.out.one_lt] at hv
  have hcv := padicValRat_nonneg_of_mem c.2
  have : ((Fintype.card n - s : ℕ) : ℤ) ≥ (Fintype.card n : ℤ) - s := by omega
  linarith

/-- **`B3`, integer-entry form.** If `q • H = B` with `B` an integer matrix whose reduction
modulo `q` has rank `≤ s`, and `det H ≠ 0`, then `v_q (det H) ≥ -s`. -/
theorem ratMatrix_det_padicValRat_ge_neg_rank_of_int {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℚ) (B : Matrix n n ℤ) (hB : ∀ i j, (q : ℚ) * H i j = B i j) (s : ℕ)
    (hs : (B.map (Int.castRingHom (ZMod q))).rank ≤ s) (hdet : H.det ≠ 0) :
    -(s : ℤ) ≤ padicValRat q H.det := by
  refine ratMatrix_det_padicValRat_ge_neg_rank H (fun i j => by
    rw [hB]; simpa using hq.out.ne_one) s ?_ hdet
  convert hs using 2
  ext i j
  simp [hB]

/-- `q`-integral rank-one perturbations with a pole of depth `e`: if `A₀`, `u`, `w` are
`q`-integral and `q ^ e • s` is `q`-integral, then `v_q (det (A₀ + s • u wᵀ)) ≥ -e`.
(Bordered-matrix / Schur-complement argument; this is Theorem 3.1(3) for one rank-one term.) -/
theorem padicValRat_det_add_smul_vecMulVec_ge {n : Type*} [Fintype n] [DecidableEq n]
    (A₀ : Matrix n n ℚ) (hA₀ : ∀ i j, A₀ i j ∈ pIntegral q) (u w : n → ℚ)
    (hu : ∀ i, u i ∈ pIntegral q) (hw : ∀ j, w j ∈ pIntegral q) (s : ℚ) (e : ℕ)
    (hs : (q : ℚ) ^ e * s ∈ pIntegral q) (hdet : (A₀ + s • vecMulVec u w).det ≠ 0) :
    -(e : ℤ) ≤ padicValRat q (A₀ + s • vecMulVec u w).det := by
  let B : Matrix Unit n ℚ := Matrix.of fun _ j => w j
  let C : Matrix n Unit ℚ := Matrix.of fun i _ => -(s * u i)
  have hschur : (fromBlocks 1 B C A₀).det = (A₀ + s • vecMulVec u w).det := by
    rw [det_fromBlocks_one₁₁]
    congr 1
    ext i j
    simp [B, C, Matrix.mul_apply, vecMulVec_apply, sub_eq_add_neg, mul_assoc]
  let c : Unit ⊕ n → ℚ := Sum.elim (fun _ => (q : ℚ) ^ e) (fun _ => 1)
  let N : Matrix (Unit ⊕ n) (Unit ⊕ n) ℚ := Matrix.of fun a b => c b * fromBlocks 1 B C A₀ a b
  have hN : N.det = (q : ℚ) ^ e * (fromBlocks 1 B C A₀).det := by
    change (Matrix.of fun a b => c b * fromBlocks 1 B C A₀ a b).det = _
    rw [det_mul_row]
    simp [c, Fintype.prod_sum_type]
  have hNmem : ∀ a b, N a b ∈ pIntegral q := by
    intro a b
    rcases a with a | i <;> rcases b with b | j
    · simpa [N, c] using pow_mem (natCast_mem (p := q) q) e
    · simpa [N, c, B] using hw j
    · have : (q : ℚ) ^ e * -(s * u i) = -(((q : ℚ) ^ e * s) * u i) := by ring
      simpa [N, c, C, this] using neg_mem (mul_mem hs (hu i))
    · simpa [N, c] using hA₀ i j
  have hmem := (det_mem_and_cast N hNmem).1
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rw [hN, hschur] at hmem
  have hv := padicValRat_nonneg_of_mem hmem
  rw [padicValRat.mul (pow_ne_zero _ hq0) hdet, padicValRat.pow,
    padicValRat.self hq.out.one_lt] at hv
  linarith

end RatRank

/-! ### `B3` for BBP windows: non-entering primes -/

section NonEntering

variable {q : ℕ} [hq : Fact q.Prime]

/-- If `q ∤ M + t` for `1 ≤ t ≤ k`, then `s_{M+k} - 2^k s_M` is `q`-integral. -/
theorem logPrefix_sub_pow_mem {M k : ℕ} (h : ∀ t, 1 ≤ t → t ≤ k → ¬ q ∣ M + t) :
    logPrefix (M + k) - 2 ^ k * logPrefix M ∈ pIntegral q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : logPrefix (M + (k + 1)) - 2 ^ (k + 1) * logPrefix M =
        2 * (logPrefix (M + k) - 2 ^ k * logPrefix M) + ((M + k + 1 : ℕ) : ℚ)⁻¹ := by
      rw [show M + (k + 1) = (M + k) + 1 by omega, logPrefix_succ]
      ring
    rw [e]
    refine add_mem (mul_mem two_mem (ih fun t h1 h2 => h t h1 (by omega))) (inv_natCast_mem ?_)
    simpa [add_assoc] using h (k + 1) (by omega) le_rfl

/-- The dyadic vector `v = (1, 2, 4, …, 2^(r-1))`. -/
def dyadicVec (R : Type*) [Semiring R] (r : ℕ) : Fin r → R := fun i => 2 ^ i.val

/-- **Rank-one decomposition at a non-entering prime.** If `q` divides no integer of
`(M, M + 2r - 2]` (`M = p - r + 1`) and the shifts are `q`-integral, then
`H = A₀ + s_M • v vᵀ` with `A₀` `q`-integral. -/
theorem bbpHankel_nonEntering_decomp {p r : ℕ} (m : Fin r → Fin r → ℚ)
    (hm : ∀ i j, m i j ∈ pIntegral q)
    (hqM : ∀ t, 1 ≤ t → t ≤ 2 * r - 2 → ¬ q ∣ p - r + 1 + t) :
    ∃ A₀ : Matrix (Fin r) (Fin r) ℚ, (∀ i j, A₀ i j ∈ pIntegral q) ∧
      bbpHankel p r m = A₀ + logPrefix (p - r + 1) • vecMulVec (dyadicVec ℚ r) (dyadicVec ℚ r) := by
  refine ⟨Matrix.of fun i j => (logPrefix (p - r + 1 + (i.val + j.val)) -
      2 ^ (i.val + j.val) * logPrefix (p - r + 1)) - m i j, fun i j => ?_, ?_⟩
  · have hi := i.isLt
    have hj := j.isLt
    exact sub_mem (logPrefix_sub_pow_mem fun t h1 h2 => hqM t h1 (by omega)) (hm i j)
  · ext i j
    rw [bbpHankel_apply, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, vecMulVec_apply,
      show p - r + 1 + i.val + j.val = p - r + 1 + (i.val + j.val) by omega]
    simp only [dyadicVec, smul_eq_mul, pow_add]
    ring

/-- **`B3`, rank `≤ 1` at a non-entering prime of depth `≤ 1`.**  If `q` divides no integer of
`(M, M + 2r - 2]`, the shifts are `q`-integral and `q s_M` is `q`-integral, then `q • H` is
`q`-integral and its reduction modulo `q` has rank at most one. -/
theorem bbpHankel_nonEntering_rank_le_one {p r : ℕ} (m : Fin r → Fin r → ℚ)
    (hm : ∀ i j, ¬ q ∣ (m i j).den)
    (hqM : ∀ t, 1 ≤ t → t ≤ 2 * r - 2 → ¬ q ∣ p - r + 1 + t)
    (hs : ¬ q ∣ ((q : ℚ) * logPrefix (p - r + 1)).den) :
    (∀ i j, ¬ q ∣ ((q : ℚ) * bbpHankel p r m i j).den) ∧
      (Matrix.of fun i j => (((q : ℚ) * bbpHankel p r m i j : ℚ) : ZMod q)).rank ≤ 1 := by
  obtain ⟨A₀, hA₀, hH⟩ := bbpHankel_nonEntering_decomp m hm hqM
  have hs' : (q : ℚ) * logPrefix (p - r + 1) ∈ pIntegral q := hs
  have hent : ∀ i j, (q : ℚ) * bbpHankel p r m i j =
      (q : ℚ) * A₀ i j + ((q : ℚ) * logPrefix (p - r + 1)) * (2 ^ i.val * 2 ^ j.val) := by
    intro i j
    rw [hH]
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, dyadicVec, smul_eq_mul]
    ring
  have hX : ∀ i j, (q : ℚ) * A₀ i j ∈ pIntegral q := fun i j => mul_mem (natCast_mem q) (hA₀ i j)
  have hY : ∀ i j : Fin r, ((q : ℚ) * logPrefix (p - r + 1)) * (2 ^ i.val * 2 ^ j.val) ∈
      pIntegral q := fun i j => mul_mem hs' (mul_mem (two_pow_mem _) (two_pow_mem _))
  refine ⟨fun i j => by rw [hent]; exact add_mem (hX i j) (hY i j), ?_⟩
  set α : ZMod q := (((q : ℚ) * logPrefix (p - r + 1) : ℚ) : ZMod q)
  have hmat : (Matrix.of fun i j => (((q : ℚ) * bbpHankel p r m i j : ℚ) : ZMod q)) =
      vecMulVec (fun i : Fin r => α * 2 ^ i.val) (dyadicVec (ZMod q) r) := by
    ext i j
    rw [of_apply, hent, cast_add_mem (hX i j) (hY i j), cast_prime_mul (hA₀ i j), zero_add,
      cast_mul_mem hs' (mul_mem (two_pow_mem _) (two_pow_mem _)),
      cast_mul_mem (two_pow_mem _) (two_pow_mem _), cast_pow_mem two_mem, cast_pow_mem two_mem]
    simp [vecMulVec_apply, dyadicVec, α, mul_assoc]
  rw [hmat]
  exact rank_vecMulVec_le _ _

/-- **`B3`, non-entering prime of depth `e`.** If `q` divides no integer of `(M, M + 2r - 2]`,
the shifts are `q`-integral, `q ^ e s_M` is `q`-integral and `det H ≠ 0`, then
`v_q (det H) ≥ -e`. -/
theorem bbpHankel_nonEntering_padicValRat_ge {p r : ℕ} (m : Fin r → Fin r → ℚ)
    (hm : ∀ i j, ¬ q ∣ (m i j).den)
    (hqM : ∀ t, 1 ≤ t → t ≤ 2 * r - 2 → ¬ q ∣ p - r + 1 + t) (e : ℕ)
    (hs : ¬ q ∣ ((q : ℚ) ^ e * logPrefix (p - r + 1)).den) (hdet : (bbpHankel p r m).det ≠ 0) :
    -(e : ℤ) ≤ padicValRat q (bbpHankel p r m).det := by
  obtain ⟨A₀, hA₀, hH⟩ := bbpHankel_nonEntering_decomp m hm hqM
  rw [hH] at hdet ⊢
  exact padicValRat_det_add_smul_vecMulVec_ge A₀ hA₀ _ _ (fun i => two_pow_mem _)
    (fun j => two_pow_mem _) _ e hs hdet

end NonEntering

/-- **`B3`, non-entering prime corollary for integer shifts (depth `1`).** Let `p` be prime,
`1 ≤ r ≤ p`, `M = p - r + 1`, and let `q` be a prime dividing no integer of `(M, M + 2r - 2]`
with `q s_M` `q`-integral.  Then the reduction of `q • H` has rank `≤ 1` and
`v_q (det H) ≥ -1`, for every integer shift matrix. -/
theorem bbpHankel_nonEntering_padicValRat_ge_neg_one {p r q : ℕ} (hp : p.Prime) (hrp : r ≤ p)
    (hq : q.Prime) (m : Fin r → Fin r → ℤ)
    (hqM : ∀ t, 1 ≤ t → t ≤ 2 * r - 2 → ¬ q ∣ p - r + 1 + t)
    (hs : ¬ q ∣ ((q : ℚ) * logPrefix (p - r + 1)).den) :
    -1 ≤ padicValRat q (bbpHankel p r fun i j => (m i j : ℚ)).det := by
  have := Fact.mk hq
  obtain ⟨hint, hrank⟩ := bbpHankel_nonEntering_rank_le_one (fun i j => (m i j : ℚ))
    (fun i j => intCast_den_not_dvd hq (m i j)) hqM hs
  have := ratMatrix_det_padicValRat_ge_neg_rank _ hint 1 hrank (bbpHankel_det_ne_zero hp hrp m)
  simpa using this

/-- **`B3`, non-entering prime corollary for integer shifts (general depth `e`).** -/
theorem bbpHankel_nonEntering_padicValRat_ge_neg_depth {p r q : ℕ} (hp : p.Prime)
    (hrp : r ≤ p) (hq : q.Prime) (m : Fin r → Fin r → ℤ)
    (hqM : ∀ t, 1 ≤ t → t ≤ 2 * r - 2 → ¬ q ∣ p - r + 1 + t) (e : ℕ)
    (hs : ¬ q ∣ ((q : ℚ) ^ e * logPrefix (p - r + 1)).den) :
    -(e : ℤ) ≤ padicValRat q (bbpHankel p r fun i j => (m i j : ℚ)).det := by
  have := Fact.mk hq
  exact bbpHankel_nonEntering_padicValRat_ge _ (fun i j => intCast_den_not_dvd hq (m i j)) hqM e
    hs (bbpHankel_det_ne_zero hp hrp m)

/-! ## 3. `B4`: positive moments, Loewner comparison and the clean-window decomposition -/

section B4

open MeasureTheory

/-- The BBP tail `T_n = ∫₀¹ tⁿ / (2 - t) dt`. -/
noncomputable def bbpTail (n : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ n / (2 - t)

theorem two_sub_pos_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < 2 - t := by
  linarith [ht.2]

theorem continuousOn_bbpWeight : ContinuousOn (fun t : ℝ => 1 / (2 - t)) (Set.Icc 0 1) :=
  continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun _ ht =>
    (two_sub_pos_of_mem ht).ne'

theorem bbpTail_integrable (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ n / (2 - t)) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    ((continuous_pow n).continuousOn.div (continuousOn_const.sub continuousOn_id) fun _ ht =>
      (two_sub_pos_of_mem ht).ne')

theorem bbpTail_zero : bbpTail 0 = Real.log 2 := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) (a := 0) (b := 1) 2
  unfold bbpTail
  simp only [pow_zero, one_div]
  rw [h, integral_inv_of_pos (by norm_num) (by norm_num)]
  norm_num

theorem bbpTail_succ (n : ℕ) : bbpTail (n + 1) = 2 * bbpTail n - 1 / ((n : ℝ) + 1) := by
  have heq : Set.EqOn (fun t : ℝ => t ^ (n + 1) / (2 - t))
      (fun t => 2 * (t ^ n / (2 - t)) - t ^ n) (Set.uIcc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h2 : (2 : ℝ) - t ≠ 0 := (two_sub_pos_of_mem ht).ne'
    simp only
    field_simp
    ring
  unfold bbpTail
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_sub ((bbpTail_integrable n).const_mul 2)
      ((continuous_pow n).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num

/-- **`B4`, integral form of the BBP tail.** `2ⁿ log 2 = s_n + ∫₀¹ tⁿ / (2 - t) dt`. -/
theorem two_pow_mul_log_two_eq_logPrefix_add_bbpTail (n : ℕ) :
    (2 : ℝ) ^ n * Real.log 2 = (logPrefix n : ℝ) + bbpTail n := by
  induction n with
  | zero => simp [logPrefix, bbpTail_zero]
  | succ n ih =>
    rw [logPrefix_succ, bbpTail_succ, pow_succ]
    push_cast
    linear_combination 2 * ih

/-- The integral tail agrees with the tail of `LogTwo.lean`, so `0 ≤ T_n ≤ 1/(n+1)`. -/
theorem bbpTail_bounds (n : ℕ) : 0 ≤ bbpTail n ∧ bbpTail n ≤ 1 / (n + 1 : ℝ) := by
  have h := two_pow_mul_log_two_eq_logPrefix_add_bbpTail n
  obtain ⟨h1, h2⟩ := logTwo_tail_bounds n
  constructor <;> linarith

/-- The weighted Hankel moment matrix `∫₀¹ t^(M+i+j) w(t) dt`. -/
noncomputable def momentMatrix (w : ℝ → ℝ) (M r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => ∫ t in (0 : ℝ)..1, t ^ (M + i.val + j.val) * w t

/-- The BBP tail moment matrix `K(M, r) i j = T_{M+i+j}`. -/
noncomputable def tailMatrix (M r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => bbpTail (M + i.val + j.val)

/-- The Hilbert/Cauchy matrix `C(M, r) i j = 1 / (M + i + j + 1)`. -/
noncomputable def cauchyMatrix (M r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => 1 / (((M + i.val + j.val : ℕ) : ℝ) + 1)

theorem tailMatrix_eq_moment (M r : ℕ) :
    tailMatrix M r = momentMatrix (fun t => 1 / (2 - t)) M r := by
  ext i j
  simp only [tailMatrix, momentMatrix, of_apply, bbpTail, mul_one_div]

theorem cauchyMatrix_eq_moment (M r : ℕ) :
    cauchyMatrix M r = momentMatrix (fun _ => (1 : ℝ)) M r := by
  ext i j
  simp only [cauchyMatrix, momentMatrix, of_apply, mul_one, integral_pow]
  norm_num

/-- The quadratic form of a moment matrix is the integral of a squared polynomial. -/
theorem momentMatrix_quadForm (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Icc 0 1)) (M r : ℕ)
    (x : Fin r → ℝ) :
    x ⬝ᵥ (momentMatrix w M r *ᵥ x) =
      ∫ t in (0 : ℝ)..1, (∑ i, x i * t ^ i.val) ^ 2 * t ^ M * w t := by
  have hint : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => t ^ k * w t) volume 0 1 := fun k =>
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one ((continuous_pow k).continuousOn.mul hw)
  have hpt : ∀ t : ℝ, (∑ i, x i * t ^ i.val) ^ 2 * t ^ M * w t =
      ∑ i, x i * ∑ j, x j * (t ^ (M + i.val + j.val) * w t) := by
    intro t
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrow : ∀ i : Fin r, IntervalIntegrable
      (fun t : ℝ => x i * ∑ j, x j * (t ^ (M + i.val + j.val) * w t)) volume 0 1 := by
    intro i
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun j _ =>
      continuousOn_const.mul ((continuous_pow _).continuousOn.mul hw))
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ => hrow i]
  simp only [dotProduct, mulVec, momentMatrix, of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun j _ => (hint _).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, mul_comm]

/-- Pointwise comparison of weights gives Loewner comparison of moment matrices. -/
theorem momentMatrix_quadForm_mono {w₁ w₂ : ℝ → ℝ} (h₁ : ContinuousOn w₁ (Set.Icc 0 1))
    (h₂ : ContinuousOn w₂ (Set.Icc 0 1)) (hle : ∀ t ∈ Set.Icc (0 : ℝ) 1, w₁ t ≤ w₂ t)
    (M r : ℕ) (x : Fin r → ℝ) :
    x ⬝ᵥ (momentMatrix w₁ M r *ᵥ x) ≤ x ⬝ᵥ (momentMatrix w₂ M r *ᵥ x) := by
  rw [momentMatrix_quadForm w₁ h₁, momentMatrix_quadForm w₂ h₂]
  have hP : ContinuousOn (fun t : ℝ => (∑ i, x i * t ^ i.val) ^ 2 * t ^ M) (Set.Icc 0 1) :=
    ((continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.mul (continuous_pow _).continuousOn).pow 2).mul
      (continuous_pow _).continuousOn
  refine intervalIntegral.integral_mono_on zero_le_one
    (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (hP.mul h₁))
    (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (hP.mul h₂)) fun t ht => ?_
  exact mul_le_mul_of_nonneg_left (hle t ht) (mul_nonneg (sq_nonneg _) (pow_nonneg ht.1 _))

theorem bbpWeight_bounds {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    1 / 2 ≤ 1 / (2 - t) ∧ 1 / (2 - t) ≤ 1 := by
  have h := two_sub_pos_of_mem ht
  refine ⟨one_div_le_one_div_of_le h (by linarith [ht.1]), ?_⟩
  simpa using one_div_le_one_div_of_le one_pos (by linarith [ht.2] : (1 : ℝ) ≤ 2 - t)

/-- **`B4`, Loewner sandwich** `C / 2 ≤ K ≤ C` (as quadratic forms). -/
theorem tail_cauchy_sandwich (M r : ℕ) (x : Fin r → ℝ) :
    (1 / 2) * (x ⬝ᵥ (cauchyMatrix M r *ᵥ x)) ≤ x ⬝ᵥ (tailMatrix M r *ᵥ x) ∧
      x ⬝ᵥ (tailMatrix M r *ᵥ x) ≤ x ⬝ᵥ (cauchyMatrix M r *ᵥ x) := by
  constructor
  · have h := momentMatrix_quadForm_mono (w₁ := fun _ => (1 / 2 : ℝ))
      (w₂ := fun t => 1 / (2 - t)) continuousOn_const continuousOn_bbpWeight
      (fun t ht => (bbpWeight_bounds ht).1) M r x
    have hs : momentMatrix (fun _ => (1 / 2 : ℝ)) M r = (1 / 2 : ℝ) • cauchyMatrix M r := by
      rw [cauchyMatrix_eq_moment]
      ext i j
      simp only [momentMatrix, of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
      rw [intervalIntegral.integral_mul_const]
      ring
    rwa [hs, smul_mulVec, dotProduct_smul, smul_eq_mul, ← tailMatrix_eq_moment] at h
  · have h := momentMatrix_quadForm_mono (w₁ := fun t => 1 / (2 - t))
      (w₂ := fun _ => (1 : ℝ)) continuousOn_bbpWeight continuousOn_const
      (fun t ht => (bbpWeight_bounds ht).2) M r x
    rwa [← tailMatrix_eq_moment, ← cauchyMatrix_eq_moment] at h

/-- A nonzero coefficient vector gives a strictly positive squared-polynomial moment. -/
theorem quadForm_pos_of_ne_zero (M r : ℕ) (x : Fin r → ℝ) (hx : x ≠ 0) :
    0 < ∫ t in (0 : ℝ)..1, (∑ i, x i * t ^ i.val) ^ 2 * t ^ M * (fun _ => (1 : ℝ)) t := by
  obtain ⟨c, hc, hPc⟩ : ∃ c ∈ Set.Ioo (0 : ℝ) 1, (∑ i, x i * c ^ i.val) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    let P : Polynomial ℝ := ∑ i : Fin r, Polynomial.C (x i) * Polynomial.X ^ i.val
    have hroot : Set.Ioo (0 : ℝ) 1 ⊆ {t | P.IsRoot t} := by
      intro t ht
      show P.IsRoot t
      simp only [Polynomial.IsRoot.def, P, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact hcon t ht
    have hP0 : P = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot P ((Set.Ioo_infinite zero_lt_one).mono hroot)
    apply hx
    funext i
    have hcoeff : P.coeff i.val = x i := by
      rw [Polynomial.finsetSum_coeff]
      simp [Fin.val_inj]
    rw [← hcoeff, hP0, Polynomial.coeff_zero, Pi.zero_apply]
  have hP : ContinuousOn
      (fun t : ℝ => (∑ i, x i * t ^ i.val) ^ 2 * t ^ M * (fun _ => (1 : ℝ)) t) (Set.Icc 0 1) :=
    (((continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.mul (continuous_pow _).continuousOn).pow 2).mul
      (continuous_pow _).continuousOn).mul continuousOn_const
  refine intervalIntegral.integral_pos zero_lt_one hP (fun t ht => ?_)
    ⟨c, Set.Ioo_subset_Icc_self hc, ?_⟩
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg ht.1.le _)) zero_le_one
  · have hsq : 0 < (∑ i, x i * c ^ i.val) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hPc))
    simpa using mul_pos hsq (pow_pos hc.1 M)

theorem cauchyMatrix_isHermitian (M r : ℕ) : (cauchyMatrix M r).IsHermitian :=
  IsHermitian.ext fun i j => by
    simp only [cauchyMatrix, of_apply, star_trivial]
    rw [Nat.add_right_comm M j.val i.val]

theorem tailMatrix_isHermitian (M r : ℕ) : (tailMatrix M r).IsHermitian :=
  IsHermitian.ext fun i j => by
    simp only [tailMatrix, of_apply, star_trivial]
    rw [Nat.add_right_comm M j.val i.val]

/-- **`B4`.** The Hilbert/Cauchy matrix `C(M, r)` is positive definite. -/
theorem cauchyMatrix_posDef (M r : ℕ) : (cauchyMatrix M r).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (cauchyMatrix_isHermitian M r) fun x hx => ?_
  rw [star_trivial, cauchyMatrix_eq_moment, momentMatrix_quadForm _ continuousOn_const]
  exact quadForm_pos_of_ne_zero M r x hx

/-- **`B4`.** The BBP tail moment matrix `K(M, r)` is positive definite. -/
theorem tailMatrix_posDef (M r : ℕ) : (tailMatrix M r).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (tailMatrix_isHermitian M r) fun x hx => ?_
  rw [star_trivial]
  have h1 := (tail_cauchy_sandwich M r x).1
  have h2 := (cauchyMatrix_posDef M r).dotProduct_mulVec_pos hx
  rw [star_trivial] at h2
  linarith

/-- A real symmetric matrix dominating the identity has determinant at least `1`. -/
theorem one_le_det_of_quadForm {n : Type*} [Fintype n] [DecidableEq n] {N : Matrix n n ℝ}
    (hN : N.IsHermitian) (h : ∀ y, y ⬝ᵥ y ≤ y ⬝ᵥ (N *ᵥ y)) : 1 ≤ N.det := by
  rw [hN.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hev : ∀ i, 1 ≤ hN.eigenvalues i := by
    intro i
    have hu : (⇑(hN.eigenvectorBasis i) : n → ℝ) ⬝ᵥ ⇑(hN.eigenvectorBasis i) = 1 := by
      have h1 : inner ℝ (hN.eigenvectorBasis i) (hN.eigenvectorBasis i) = 1 := by
        rw [real_inner_self_eq_norm_sq, hN.eigenvectorBasis.orthonormal.1 i]
        norm_num
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h1
      exact h1
    have h1 := h ⇑(hN.eigenvectorBasis i)
    rw [hN.mulVec_eigenvectorBasis i, dotProduct_smul, smul_eq_mul, hu] at h1
    simpa using h1
  exact Finset.one_le_prod₀ fun i _ => hev i

/-- **Loewner monotonicity of the determinant.** If `A` is positive definite, `B` is symmetric
and `xᵀ A x ≤ xᵀ B x` for all `x`, then `det A ≤ det B`. -/
theorem det_le_det_of_quadForm_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.IsHermitian)
    (hAB : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) : A.det ≤ B.det := by
  have hAH := hA.isHermitian
  set U : Matrix n n ℝ := (hAH.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  set ev := hAH.eigenvalues with hevdef
  have hev : ∀ i, 0 < ev i := hA.eigenvalues_pos
  have hspec : A = U * diagonal ev * Uᵀ := by
    have h := hAH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [U, ev, RCLike.ofReal_real_eq_id, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using h
  have hUU : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hAH.eigenvectorUnitary
    simpa [U, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
  set D' : Matrix n n ℝ := diagonal fun i => (Real.sqrt (ev i))⁻¹ with hD'
  set S : Matrix n n ℝ := D' * Uᵀ with hS
  have hSA : S * A * Sᵀ = 1 := by
    rw [hspec]
    simp only [S, transpose_mul, D', diagonal_transpose, transpose_transpose]
    calc D' * Uᵀ * (U * diagonal ev * Uᵀ) * (U * D') =
        D' * (Uᵀ * U) * diagonal ev * (Uᵀ * U) * D' := by simp only [Matrix.mul_assoc]
      _ = D' * diagonal ev * D' := by rw [hUU, Matrix.mul_one, Matrix.mul_one]
      _ = 1 := by
        simp only [D', diagonal_mul_diagonal]
        rw [← diagonal_one]
        congr 1
        funext i
        have h0 := hev i
        rw [show (Real.sqrt (ev i))⁻¹ * ev i * (Real.sqrt (ev i))⁻¹ =
            ev i / (Real.sqrt (ev i) * Real.sqrt (ev i)) by ring,
          Real.mul_self_sqrt h0.le, div_self h0.ne']
  have key : ∀ (X : Matrix n n ℝ) (y : n → ℝ),
      y ⬝ᵥ ((S * X * Sᵀ) *ᵥ y) = (Sᵀ *ᵥ y) ⬝ᵥ (X *ᵥ (Sᵀ *ᵥ y)) := by
    intro X y
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  have hNH : (S * B * Sᵀ).IsHermitian := by
    have h := isHermitian_mul_mul_conjTranspose S hB
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have hNq : ∀ y, y ⬝ᵥ y ≤ y ⬝ᵥ ((S * B * Sᵀ) *ᵥ y) := by
    intro y
    have h1 := hAB (Sᵀ *ᵥ y)
    rw [← key A, ← key B, hSA, one_mulVec] at h1
    exact h1
  have hdetN := one_le_det_of_quadForm hNH hNq
  have hd1 : S.det * A.det * S.det = 1 := by
    have h := congrArg det hSA
    rwa [det_mul, det_mul, det_transpose, det_one] at h
  have hd2 : (S * B * Sᵀ).det = S.det * B.det * S.det := by
    rw [det_mul, det_mul, det_transpose]
  have hApos : 0 < A.det := hA.det_pos
  have hBeq : B.det = (S * B * Sᵀ).det * A.det := by
    rw [hd2]
    linear_combination (-B.det) * hd1
  rw [hBeq]
  calc A.det = 1 * A.det := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hdetN hApos.le

/-- **`B4`, determinant comparison.** `0 < det C`, `0 < det K` and
`2 ^ (-r) det C ≤ det K ≤ det C`. -/
theorem tailMatrix_det_bounds (M r : ℕ) :
    0 < (cauchyMatrix M r).det ∧ 0 < (tailMatrix M r).det ∧
      (1 / 2 : ℝ) ^ r * (cauchyMatrix M r).det ≤ (tailMatrix M r).det ∧
      (tailMatrix M r).det ≤ (cauchyMatrix M r).det := by
  refine ⟨(cauchyMatrix_posDef M r).det_pos, (tailMatrix_posDef M r).det_pos, ?_, ?_⟩
  · have hpd : ((1 / 2 : ℝ) • cauchyMatrix M r).PosDef := by
      refine PosDef.of_dotProduct_mulVec_pos (IsHermitian.ext fun i j => ?_) fun x hx => ?_
      · have h := (cauchyMatrix_isHermitian M r).apply i j
        rw [star_trivial] at h
        simp only [Matrix.smul_apply, smul_eq_mul, star_trivial, h]
      · have h := (cauchyMatrix_posDef M r).dotProduct_mulVec_pos hx
        rw [star_trivial] at h ⊢
        rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
        positivity
    have h := det_le_det_of_quadForm_le hpd (tailMatrix_isHermitian M r) fun x => by
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
      exact (tail_cauchy_sandwich M r x).1
    rwa [det_smul, Fintype.card_fin] at h
  · exact det_le_det_of_quadForm_le (tailMatrix_posDef M r) (cauchyMatrix_isHermitian M r)
      fun x => (tail_cauchy_sandwich M r x).2

/-- **`B4`, clean-window decomposition** (Proposition 4.1(3)). For any integer `m_M`, the window
`H_c i j = s_{M+i+j} - 2^(i+j) m_M` equals `ε • v vᵀ - K(M, r)` with `ε = 2^M log 2 - m_M` and
`v = (2^i)`. -/
theorem cleanWindow_decomposition (M r : ℕ) (m : ℤ) :
    (Matrix.of fun i j : Fin r =>
        ((logPrefix (M + i.val + j.val) : ℚ) : ℝ) - 2 ^ (i.val + j.val) * (m : ℝ)) =
      ((2 : ℝ) ^ M * Real.log 2 - m) • vecMulVec (dyadicVec ℝ r) (dyadicVec ℝ r) -
        tailMatrix M r := by
  ext i j
  simp only [of_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, dyadicVec,
    tailMatrix, smul_eq_mul]
  have h := two_pow_mul_log_two_eq_logPrefix_add_bbpTail (M + i.val + j.val)
  linear_combination (-1 : ℝ) * h

/-- **`B4`, clean prime-centred BBP window.** With integer shifts `m i j = 2^(i+j) m_M`,
the real image of `bbpHankel p r` is `ε • v vᵀ - K(p - r + 1, r)`. -/
theorem bbpHankel_clean_decomposition (p r : ℕ) (m : ℤ) :
    (bbpHankel p r fun i j => (2 : ℚ) ^ (i.val + j.val) * m).map (fun x : ℚ => (x : ℝ)) =
      ((2 : ℝ) ^ (p - r + 1) * Real.log 2 - m) • vecMulVec (dyadicVec ℝ r) (dyadicVec ℝ r) -
        tailMatrix (p - r + 1) r := by
  rw [← cleanWindow_decomposition]
  ext i j
  simp [bbpHankel_apply]

/-- **Matrix determinant lemma for `K`.** `det (K - ε • v vᵀ) = det K * (1 - ε vᵀ K⁻¹ v)`. -/
theorem tailMatrix_sub_det (M r : ℕ) (ε : ℝ) (v : Fin r → ℝ) :
    (tailMatrix M r - ε • vecMulVec v v).det =
      (tailMatrix M r).det * (1 - ε * (v ⬝ᵥ ((tailMatrix M r)⁻¹ *ᵥ v))) := by
  have hunit : IsUnit (tailMatrix M r).det := (tailMatrix_posDef M r).det_pos.ne'.isUnit
  have e : tailMatrix M r - ε • vecMulVec v v =
      tailMatrix M r + replicateCol Unit (-ε • v) * replicateRow Unit v := by
    rw [← vecMulVec_eq Unit]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, det_add_replicateCol_mul_replicateRow hunit, Matrix.mul_assoc,
    ← replicateCol_mulVec]
  congr 1
  rw [det_unique, Matrix.add_apply, one_apply_eq, replicateRow_mul_replicateCol_apply,
    mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- **`B4`, determinant of the clean window** (Proposition 4.1(3)):
`det (ε • v vᵀ - K) = (-1)^r det K (1 - ε vᵀ K⁻¹ v)`. -/
theorem cleanWindow_det (M r : ℕ) (ε : ℝ) :
    (ε • vecMulVec (dyadicVec ℝ r) (dyadicVec ℝ r) - tailMatrix M r).det =
      (-1) ^ r * ((tailMatrix M r).det *
        (1 - ε * (dyadicVec ℝ r ⬝ᵥ ((tailMatrix M r)⁻¹ *ᵥ dyadicVec ℝ r)))) := by
  rw [← tailMatrix_sub_det, ← neg_sub, det_neg, Fintype.card_fin]

end B4

end NormalityChecker.HankelLogTwo
