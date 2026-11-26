module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic

/-! # Band identity, character-sum vanishing, and automaton periodicity (Track D1–D2)

Kernel-checked finite algebraic and harmonic core supporting
`notes/phase21/euler-scalings-and-reciprocals.md`:

1. **Exact band identity (`band_identity`, Lemma D2.1):**
   If `2 ≤ b`, `R : ℚ` has denominator coprime to `b`, and `orderOf (b : ZMod R.den) ∣ m`, then
   for every band index `i : ℕ` and offset `r : ℕ`,
   `b^(i * m + r) * (R * b^m / (b^m - 1)) - ((i + 1) * b^r * R + b^r * R / (b^m - 1))`
   is an integer.

2. **Exact alternating-sign band identity (`signed_band_identity`, Proposition D2.5):**
   Under the same hypotheses with the opposite sign `1 / (1 + b^(-m)) = b^m / (b^m + 1)`,
   `b^(i * m + r) * (R * b^m / (b^m + 1)) - ((if Even i then 1 else 0) * b^r * R + (-1)^(i + 1) * b^r * R / (b^m + 1))`
   is an integer. In particular, the leading multiplier vanishes on every odd band.

3. **Complete residue character-sum vanishing (`sum_residues_cexp_eq_zero`, Lemma D2.2):**
   For `D ≥ 1`, `Nat.Coprime u D`, and `¬ D ∣ k`,
   `∑ c : ZMod D, Complex.exp (2 * π * I * (c.val * k * u : ℂ) / D) = 0`.

4. **Pure periodicity of the Euler rational-scaling automaton (`eulerAutomatonStep_bijective`,
   `eulerAutomaton_purely_periodic`, Theorem D1.1):**
   For `d ≥ 1` with `Nat.Coprime b d`, the step `(k mod L, u) ↦ (k + 1 mod L, b^(3(k+1)-1) u + (-1)^(k+1)(b^(k+1)+1))`
   is a bijection on `ZMod L × ZMod d` (with `L = Nat.lcm 2 (orderOf (b : ZMod d))`), hence
   every orbit is purely periodic.
-/

@[expose] public section

open Finset

namespace NormalityChecker.NormalReciprocalCore

/-! ### Part 1: Exact rational band identities (Lemma D2.1 & Proposition D2.5) -/

/-- If `orderOf (b : ZMod R.den) ∣ m`, then `(b^m - 1) * R` is an integer. -/
theorem exists_int_pow_sub_one_mul_rat {b m : ℕ} {R : ℚ}
    (hT : orderOf (b : ZMod R.den) ∣ m) :
    ∃ z : ℤ, ((b : ℚ) ^ m - 1) * R = (z : ℚ) := by
  have hpow : ((b : ZMod R.den)) ^ m = 1 := by
    obtain ⟨q, rfl⟩ := hT
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hdvd_nat : (R.den : ℤ) ∣ ((b : ℤ) ^ m - 1) := by
    have hsub : ((b : ZMod R.den) ^ m - 1) = 0 := sub_eq_zero.mpr hpow
    have hcast : ((((b : ℤ) ^ m - 1 : ℤ) : ZMod R.den)) = 0 := by
      simpa using hsub
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨c, hc⟩ := hdvd_nat
  refine ⟨c * R.num, ?_⟩
  have hden_ne : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_nz
  have hcz : ((b : ℚ) ^ m - 1) = (R.den : ℚ) * (c : ℚ) := by exact_mod_cast hc
  calc ((b : ℚ) ^ m - 1) * R
      = ((R.den : ℚ) * (c : ℚ)) * ((R.num : ℚ) / (R.den : ℚ)) := by rw [hcz, Rat.num_div_den]
    _ = ((c * R.num : ℤ) : ℚ) := by push_cast; field_simp [hden_ne]

/-- Helper: for any `j : ℕ`, `(b^(j * m) - 1) * R` is an integer when `orderOf (b : ZMod R.den) ∣ m`. -/
private lemma exists_int_pow_mul_sub_one_mul_rat {b m j : ℕ} {R : ℚ}
    (hT : orderOf (b : ZMod R.den) ∣ m) :
    ∃ z : ℤ, ((b : ℚ) ^ (j * m) - 1) * R = (z : ℚ) := by
  have hTj : orderOf (b : ZMod R.den) ∣ j * m := dvd_mul_of_dvd_right hT j
  exact exists_int_pow_sub_one_mul_rat hTj

/-- **Lemma D2.1 (exact rational band identity).**
If `2 ≤ b`, `1 ≤ m`, and `orderOf (b : ZMod R.den) ∣ m`, then for every `i, r : ℕ`,
`b^(i * m + r) * (R * b^m / (b^m - 1)) = (i + 1) * b^r * R + b^r * R / (b^m - 1) + z`
for some integer `z : ℤ`. -/
theorem band_identity {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) {R : ℚ}
    (hT : orderOf (b : ZMod R.den) ∣ m) (i r : ℕ) :
    ∃ z : ℤ,
      (b : ℚ) ^ (i * m + r) * (R * (b : ℚ) ^ m / ((b : ℚ) ^ m - 1)) =
        ((i + 1 : ℕ) : ℚ) * (b : ℚ) ^ r * R +
          (b : ℚ) ^ r * R / ((b : ℚ) ^ m - 1) + (z : ℚ) := by
  have hbm_gt : (1 : ℚ) < (b : ℚ) ^ m := by
    have hb1 : (1 : ℚ) < (b : ℚ) := by exact_mod_cast (show 1 < b by omega)
    exact one_lt_pow₀ hb1 (by omega)
  have hden_ne : (b : ℚ) ^ m - 1 ≠ 0 := by linarith
  -- Algebraic identity: b^(i*m + m) / (b^m - 1) = ∑_{j=0}^i b^(j*m) + 1 / (b^m - 1).
  have hgeom : ((b : ℚ) ^ m - 1) * ∑ j ∈ range (i + 1), (b : ℚ) ^ (j * m) =
      (b : ℚ) ^ ((i + 1) * m) - 1 := by
    have hsum := geom_sum_mul ((b : ℚ) ^ m) (i + 1)
    calc ((b : ℚ) ^ m - 1) * ∑ j ∈ range (i + 1), (b : ℚ) ^ (j * m)
        = (∑ j ∈ range (i + 1), ((b : ℚ) ^ m) ^ j) * ((b : ℚ) ^ m - 1) := by
          rw [mul_comm]
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← pow_mul, mul_comm m j]
      _ = ((b : ℚ) ^ m) ^ (i + 1) - 1 := hsum
      _ = (b : ℚ) ^ ((i + 1) * m) - 1 := by rw [← pow_mul, mul_comm m (i + 1)]
  have hfrac : (b : ℚ) ^ (i * m + r) * (R * (b : ℚ) ^ m / ((b : ℚ) ^ m - 1)) =
      (b : ℚ) ^ r * R * (∑ j ∈ range (i + 1), (b : ℚ) ^ (j * m)) +
        (b : ℚ) ^ r * R / ((b : ℚ) ^ m - 1) := by
    have hpow : (b : ℚ) ^ (i * m + r) * (b : ℚ) ^ m = (b : ℚ) ^ r * (b : ℚ) ^ ((i + 1) * m) := by
      rw [← pow_add, ← pow_add]
      congr 1; ring
    field_simp [hden_ne]
    calc (b : ℚ) ^ (i * m + r) * R * (b : ℚ) ^ m
        = R * ((b : ℚ) ^ (i * m + r) * (b : ℚ) ^ m) := by ring
      _ = R * ((b : ℚ) ^ r * (b : ℚ) ^ ((i + 1) * m)) := by rw [hpow]
      _ = R * (b : ℚ) ^ r * (((b : ℚ) ^ ((i + 1) * m) - 1) + 1) := by ring
      _ = R * (b : ℚ) ^ r * (((b : ℚ) ^ m - 1) * ∑ j ∈ range (i + 1), (b : ℚ) ^ (j * m) + 1) := by
          rw [hgeom]
  -- Each `(b^(j*m) - 1) * R` is an integer, so `∑_{j=0}^i (b^(j*m) - 1) * b^r * R` is an integer.
  have hterm : ∀ j : ℕ, ∃ z : ℤ, ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R) = (z : ℚ) := by
    intro j
    obtain ⟨z, hz⟩ := exists_int_pow_mul_sub_one_mul_rat (j := j) hT
    refine ⟨(b : ℤ) ^ r * z, ?_⟩
    push_cast
    calc ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R)
        = (b : ℚ) ^ r * (((b : ℚ) ^ (j * m) - 1) * R) := by ring
      _ = (b : ℚ) ^ r * (z : ℚ) := by rw [hz]
  choose zf hzf using hterm
  refine ⟨∑ j ∈ range (i + 1), zf j, ?_⟩
  rw [hfrac]
  have hdiff : (b : ℚ) ^ r * R * (∑ j ∈ range (i + 1), (b : ℚ) ^ (j * m)) -
      ((i + 1 : ℕ) : ℚ) * (b : ℚ) ^ r * R =
      ∑ j ∈ range (i + 1), ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R) := by
    rw [Finset.mul_sum]
    have hcard : ((i + 1 : ℕ) : ℚ) * (b : ℚ) ^ r * R =
        ∑ _j ∈ range (i + 1), (b : ℚ) ^ r * R := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [hcard, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have hsum_z : ((∑ j ∈ range (i + 1), zf j : ℤ) : ℚ) =
      ∑ j ∈ range (i + 1), ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl (fun j _ => (hzf j).symm)
  linarith

/-- **Proposition D2.5 (exact alternating-sign band identity).**
With `+` in place of `-`, on every band `i` the leading multiplier is `1` for even `i` and `0`
for odd `i`, so odd bands concentrate near `0 mod 1`. -/
theorem signed_band_identity {b m : ℕ} (hb : 2 ≤ b) {R : ℚ}
    (hT : orderOf (b : ZMod R.den) ∣ m) (i r : ℕ) :
    ∃ z : ℤ,
      (b : ℚ) ^ (i * m + r) * (R * (b : ℚ) ^ m / ((b : ℚ) ^ m + 1)) =
        (if Even i then (1 : ℚ) else 0) * (b : ℚ) ^ r * R +
          (-1 : ℚ) ^ (i + 1) * (b : ℚ) ^ r * R / ((b : ℚ) ^ m + 1) + (z : ℚ) := by
  have hbm_pos : (0 : ℚ) < (b : ℚ) ^ m + 1 := by
    have : (0 : ℚ) < (b : ℚ) := by exact_mod_cast (show 0 < b by omega)
    positivity
  have hden_ne : (b : ℚ) ^ m + 1 ≠ 0 := hbm_pos.ne'
  -- Alternating geometric sum: `((-b^m) - 1) * ∑_{j=0}^i (-b^m)^j = (-b^m)^(i+1) - 1`.
  have hgeom : ((b : ℚ) ^ m + 1) * ∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) * (b : ℚ) ^ (j * m) =
      (b : ℚ) ^ ((i + 1) * m) - (-1 : ℚ) ^ (i + 1) := by
    have hsum := geom_sum_mul (-(b : ℚ) ^ m) (i + 1)
    -- `∑_{j=0}^i (-b^m)^j * (-b^m - 1) = (-b^m)^(i+1) - 1`.
    -- Multiply by `(-1)^(i+1)`: `(-1)^i * (-1)^j = (-1)^(i - j)` for `j ≤ i`.
    have hmul := congrArg (fun t => (-1 : ℚ) ^ (i + 1) * t) hsum
    have hLHS : (-1 : ℚ) ^ (i + 1) *
        ((∑ j ∈ range (i + 1), (-(b : ℚ) ^ m) ^ j) * (-(b : ℚ) ^ m - 1)) =
        ((b : ℚ) ^ m + 1) * ∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) * (b : ℚ) ^ (j * m) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hneg : (-(b : ℚ) ^ m) ^ j = (-1 : ℚ) ^ j * (b : ℚ) ^ (j * m) := by
        rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul, mul_comm m j]
      have hsign : (-1 : ℚ) ^ (i + 1) * (-1 : ℚ) ^ j * (-1 : ℚ) = (-1 : ℚ) ^ (i - j) := by
        have h1 : (-1 : ℚ) ^ (i + 1) * (-1 : ℚ) ^ j * (-1 : ℚ) = (-1 : ℚ) ^ (i + j + 2) := by
          rw [← pow_add, ← pow_succ]; congr 1; omega
        have h2 : i + j + 2 = (i - j) + 2 * (j + 1) := by omega
        rw [h1, h2, pow_add, pow_mul]
        norm_num
      rw [hneg]
      have hneg2 : -(b : ℚ) ^ m - 1 = (-1 : ℚ) * ((b : ℚ) ^ m + 1) := by ring
      rw [hneg2]
      calc (-1 : ℚ) ^ (i + 1) * ((-1 : ℚ) ^ j * (b : ℚ) ^ (j * m) * ((-1 : ℚ) * ((b : ℚ) ^ m + 1)))
          = ((-1 : ℚ) ^ (i + 1) * (-1 : ℚ) ^ j * (-1 : ℚ)) * ((b : ℚ) ^ m + 1) * (b : ℚ) ^ (j * m) := by ring
        _ = (-1 : ℚ) ^ (i - j) * ((b : ℚ) ^ m + 1) * (b : ℚ) ^ (j * m) := by rw [hsign]
        _ = ((b : ℚ) ^ m + 1) * ((-1 : ℚ) ^ (i - j) * (b : ℚ) ^ (j * m)) := by ring
    have hRHS : (-1 : ℚ) ^ (i + 1) * ((-(b : ℚ) ^ m) ^ (i + 1) - 1) =
        (b : ℚ) ^ ((i + 1) * m) - (-1 : ℚ) ^ (i + 1) := by
      have hneg : (-(b : ℚ) ^ m) ^ (i + 1) = (-1 : ℚ) ^ (i + 1) * (b : ℚ) ^ ((i + 1) * m) := by
        rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul, mul_comm m (i + 1)]
      have hsq : (-1 : ℚ) ^ (i + 1) * (-1 : ℚ) ^ (i + 1) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [hneg]
      calc (-1 : ℚ) ^ (i + 1) * ((-1 : ℚ) ^ (i + 1) * (b : ℚ) ^ ((i + 1) * m) - 1)
          = ((-1 : ℚ) ^ (i + 1) * (-1 : ℚ) ^ (i + 1)) * (b : ℚ) ^ ((i + 1) * m) - (-1 : ℚ) ^ (i + 1) := by ring
        _ = (b : ℚ) ^ ((i + 1) * m) - (-1 : ℚ) ^ (i + 1) := by rw [hsq, one_mul]
    rw [← hLHS, ← hRHS]
    exact hmul
  have hfrac : (b : ℚ) ^ (i * m + r) * (R * (b : ℚ) ^ m / ((b : ℚ) ^ m + 1)) =
      (b : ℚ) ^ r * R * (∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) * (b : ℚ) ^ (j * m)) +
        (-1 : ℚ) ^ (i + 1) * (b : ℚ) ^ r * R / ((b : ℚ) ^ m + 1) := by
    have hpow : (b : ℚ) ^ (i * m + r) * (b : ℚ) ^ m = (b : ℚ) ^ r * (b : ℚ) ^ ((i + 1) * m) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    field_simp [hden_ne]
    calc (b : ℚ) ^ (i * m + r) * R * (b : ℚ) ^ m
        = R * ((b : ℚ) ^ (i * m + r) * (b : ℚ) ^ m) := by ring
      _ = R * ((b : ℚ) ^ r * (b : ℚ) ^ ((i + 1) * m)) := by rw [hpow]
      _ = R * (b : ℚ) ^ r * (((b : ℚ) ^ ((i + 1) * m) - (-1 : ℚ) ^ (i + 1)) + (-1 : ℚ) ^ (i + 1)) := by ring
      _ = R * (b : ℚ) ^ r *
            (((b : ℚ) ^ m + 1) * (∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) * (b : ℚ) ^ (j * m)) +
              (-1 : ℚ) ^ (i + 1)) := by rw [hgeom]
  -- Alternating sum of signs `∑_{j=0}^i (-1)^(i - j) = if Even i then 1 else 0`.
  have halt : ∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) = if Even i then 1 else 0 := by
    clear hgeom hfrac hbm_pos hden_ne hT hb R b m r
    induction i with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero]
      have hshift : ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (k + 1 - j) =
          -(∑ j ∈ range (k + 1), (-1 : ℚ) ^ (k - j)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have hsub : k + 1 - j = (k - j) + 1 := by omega
        rw [hsub, pow_succ]; ring
      rw [hshift, ih]
      by_cases hk : Even k
      · have hnot : ¬ Even (k + 1) := by
          obtain ⟨t, rfl⟩ := hk
          intro ⟨s, hs⟩; omega
        simp [hk, hnot]
      · have hev : Even (k + 1) := by
          rw [Nat.not_even_iff_odd] at hk
          obtain ⟨t, rfl⟩ := hk
          exact ⟨t + 1, by omega⟩
        simp [hk, hev]
  have hterm : ∀ j : ℕ, ∃ z : ℤ,
      (-1 : ℚ) ^ (i - j) * ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R) = (z : ℚ) := by
    intro j
    obtain ⟨z, hz⟩ := exists_int_pow_mul_sub_one_mul_rat (j := j) hT
    refine ⟨(-1 : ℤ) ^ (i - j) * (b : ℤ) ^ r * z, ?_⟩
    push_cast
    calc (-1 : ℚ) ^ (i - j) * ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R)
        = (-1 : ℚ) ^ (i - j) * (b : ℚ) ^ r * (((b : ℚ) ^ (j * m) - 1) * R) := by ring
      _ = (-1 : ℚ) ^ (i - j) * (b : ℚ) ^ r * (z : ℚ) := by rw [hz]
  choose zf hzf using hterm
  refine ⟨∑ j ∈ range (i + 1), zf j, ?_⟩
  rw [hfrac]
  have hdiff : (b : ℚ) ^ r * R * (∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) * (b : ℚ) ^ (j * m)) -
      (if Even i then (1 : ℚ) else 0) * (b : ℚ) ^ r * R =
      ∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) * ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R) := by
    rw [← halt, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have hsum_z : ((∑ j ∈ range (i + 1), zf j : ℤ) : ℚ) =
      ∑ j ∈ range (i + 1), (-1 : ℚ) ^ (i - j) * ((b : ℚ) ^ (j * m) - 1) * ((b : ℚ) ^ r * R) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl (fun j _ => (hzf j).symm)
  linarith

/-! ### Part 2: Complete residue character-sum vanishing (Lemma D2.2) -/

/-- **Lemma D2.2 (complete exponential sum over `ZMod D` vanishes off `D ∣ k`).**
For `D ≥ 1`, `Nat.Coprime u D`, and `¬ D ∣ k`,
`∑ c : ZMod D, Complex.exp (2 * π * I * (c.val * k * u : ℂ) / D) = 0`. -/
theorem sum_residues_cexp_eq_zero {D : ℕ} [NeZero D] (k u : ℕ)
    (hu : Nat.Coprime u D) (hk : ¬ D ∣ k) :
    ∑ c : ZMod D,
      Complex.exp (2 * Real.pi * Complex.I * ((c.val * k * u : ℕ) : ℂ) / (D : ℂ)) = 0 := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((k * u : ℕ) : ℂ) / (D : ℂ))
  have hω_pow : ω ^ D = 1 := by
    rw [← Complex.exp_nat_mul]
    have hD_ne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hmul : (D : ℂ) * (2 * Real.pi * Complex.I * ((k * u : ℕ) : ℂ) / (D : ℂ)) =
        ((k * u : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp [hD_ne]
    rw [hmul]
    exact Complex.exp_nat_mul_two_pi_mul_I (k * u)
  have hω_ne : ω ≠ 1 := by
    intro h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    have hD_ne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hrat : ((k * u : ℕ) : ℂ) / (D : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      calc 2 * Real.pi * Complex.I * (((k * u : ℕ) : ℂ) / (D : ℂ))
          = 2 * Real.pi * Complex.I * ((k * u : ℕ) : ℂ) / (D : ℂ) := by ring
        _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
        _ = 2 * Real.pi * Complex.I * (n : ℂ) := by ring
    have heq_c : ((k * u : ℕ) : ℂ) = (n : ℂ) * (D : ℂ) := (div_eq_iff hD_ne).mp hrat
    have heq_z : ((k * u : ℕ) : ℤ) = n * (D : ℤ) := by exact_mod_cast heq_c
    have hdvd_z : (D : ℤ) ∣ ((k * u : ℕ) : ℤ) := ⟨n, by linarith⟩
    have hdvd_n : D ∣ k * u := Int.natCast_dvd_natCast.mp hdvd_z
    exact hk (hu.symm.dvd_of_dvd_mul_right hdvd_n)
  -- Rewrite the sum over `ZMod D` as `∑ j ∈ range D, ω^j`.
  have hsum_eq : ∑ c : ZMod D,
      Complex.exp (2 * Real.pi * Complex.I * ((c.val * k * u : ℕ) : ℂ) / (D : ℂ)) =
      ∑ j ∈ range D, ω ^ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => ω ^ j)]
    refine Fintype.sum_equiv (ZMod.finEquiv D).symm.toEquiv _ _ (fun c => ?_)
    have hval : ((ZMod.finEquiv D).symm.toEquiv c).val = c.val := by
      cases D with
      | zero => exact absurd rfl (NeZero.ne 0)
      | succ n => rfl
    rw [hval, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hsum_eq]
  have hgeom := geom_sum_mul ω D
  rw [hω_pow, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hω_ne)

/-! ### Part 3: Pure periodicity of the Euler rational-scaling automaton (Theorem D1.1) -/

/-- One step of the finite automaton `(k mod L, u ∈ ZMod d)` governing `(a/d) E_b` (Theorem D1.1). -/
def eulerAutomatonStep (b d L : ℕ) (state : ZMod L × ZMod d) : ZMod L × ZMod d :=
  let k := state.1.val + 1
  (state.1 + 1, (b : ZMod d) ^ (3 * k - 1) * state.2 + (-1 : ZMod d) ^ k * ((b : ZMod d) ^ k + 1))

/-- When `Nat.Coprime b d`, `eulerAutomatonStep b d L` is a bijection on `ZMod L × ZMod d`. -/
theorem eulerAutomatonStep_bijective {b d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (hcop : Nat.Coprime b d) :
    Function.Bijective (eulerAutomatonStep b d L) := by
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero L := ⟨hL.ne'⟩
  refine (Finite.injective_iff_bijective).mp ?_
  intro s₁ s₂ heq
  have h1 : s₁.1 + 1 = s₂.1 + 1 := congrArg Prod.fst heq
  have hfst : s₁.1 = s₂.1 := add_right_cancel h1
  have h2 := congrArg Prod.snd heq
  simp only [eulerAutomatonStep, hfst] at h2
  have hmul : (b : ZMod d) ^ (3 * (s₂.1.val + 1) - 1) * s₁.2 =
      (b : ZMod d) ^ (3 * (s₂.1.val + 1) - 1) * s₂.2 := add_right_cancel h2
  have hunit : IsUnit ((b : ZMod d) ^ (3 * (s₂.1.val + 1) - 1)) :=
    ((ZMod.isUnit_iff_coprime b d).mpr hcop).pow _
  have hsnd : s₁.2 = s₂.2 := hunit.mul_left_cancel hmul
  exact Prod.ext hfst hsnd

/-- **Theorem D1.1 (pure periodicity of the Euler automaton).**
Any bijection on a nonempty finite type has a uniform positive period; in particular, for
`Nat.Coprime b d` and `L > 0`, `eulerAutomatonStep b d L` is purely periodic on `ZMod L × ZMod d`. -/
theorem eulerAutomaton_purely_periodic {b d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (hcop : Nat.Coprime b d) :
    ∃ P : ℕ, 0 < P ∧ ∀ s : ZMod L × ZMod d,
      (eulerAutomatonStep b d L)^[P] s = s := by
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero L := ⟨hL.ne'⟩
  let e : Equiv.Perm (ZMod L × ZMod d) := Equiv.ofBijective _ (eulerAutomatonStep_bijective hd hL hcop)
  refine ⟨orderOf e, orderOf_pos e, fun s => ?_⟩
  have hiter : ∀ n : ℕ, (eulerAutomatonStep b d L)^[n] s = (e ^ n) s := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl
  rw [hiter, pow_orderOf_eq_one]
  rfl

end NormalityChecker.NormalReciprocalCore
