module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

/-! # Finite arithmetic and combinatorial core for higher-degree power schedules (Track C1)

Kernel-checked finite lemmas underlying the arbitrary-degree power-schedule normality theorem
(`GF-11`, `notes/phase20/cubic-power-schedule.md`, `notes/phase21/nonlinear-boundary.md`):

1. **Divisor bound for `d`-th power differences (`card_pow_diff_eq_le_divisors`):**
   For every `d ≥ 2` and `M > 0`, the number of pairs `(a, c) ∈ ℕ × ℕ` with `c < a` and
   `a^d - c^d = M` is at most `(Nat.divisors M).card`, because `e = a - c` divides `M` and
   `c ↦ (c + e)^d - c^d` is strictly increasing for `e > 0`.

2. **Exact polynomial recurrence and nonvanishing of `Φ_q(X, B)` (`phiPoly_natDegree`,
   `phiPoly_leadingCoeff`, `phiPoly_ne_zero`):**
   Representing `Φ_q(X, B)` in `(ℤ[B])[X]` via
   `Φ_2 = 1` and `Φ_{q+1} = ((d - q)(X + B) + (1 - q d) X) Φ_q + d X (X + B) ∂_X Φ_q`,
   for every `d ≥ 1` and `q ≥ 2`, `Φ_q` has `X`-degree `q - 2` and leading `X`-coefficient
   `(-1)^q ∏_{j=1}^{q-2} (d + j) ≠ 0`.

3. **Dominant-loss `p`-adic peeling lemma (`dominant_loss_unique_top_coord`):**
   If a rational `p`-adic sum `∑ y_i^d` has a unique top-loss coordinate of loss `h_top`
   (so its reduced denominator is divisible by `p^(d * h_top)` and not by `p^(d * h_top + 1)`),
   and `∑ y_i^d = ∑ w_i^d` where the coordinates `w_i` have total `p`-adic loss `< 2 * h_top`,
   then `w` has a unique coordinate of loss `h_top` and every other coordinate of `w` has loss
   strictly less than `h_top`.
-/

@[expose] public section

open Finset Polynomial

namespace NormalityChecker.PowerSumPeeling

/-! ### Part 1: Divisor bound for `d`-th power differences (`d ≥ 2`) -/

/-- For `d ≥ 2` and `e ≥ 1`, the map `c ↦ (c + e)^d - c^d` is strictly increasing on `ℕ`. -/
theorem strictMono_add_pow_sub_pow {d e : ℕ} (hd : 2 ≤ d) (he : 1 ≤ e) :
    StrictMono (fun c : ℕ => (c + e) ^ d - c ^ d) := by
  refine strictMono_nat_of_lt_succ (fun c => ?_)
  have hlt1 : c ^ d ≤ (c + e) ^ d := Nat.pow_le_pow_left (by omega) d
  have hlt2 : (c + 1) ^ d ≤ (c + 1 + e) ^ d := Nat.pow_le_pow_left (by omega) d
  suffices h : (c + e) ^ d + (c + 1) ^ d < (c + 1 + e) ^ d + c ^ d by omega
  clear hlt1 hlt2
  induction d, hd using Nat.le_induction with
  | base =>
    nlinarith
  | succ k hk ih =>
    have hpow_le : c ^ k ≤ (c + e) ^ k := Nat.pow_le_pow_left (by omega) k
    have hpow_lt : (c + 1) ^ k < (c + 1 + e) ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
    have hpow_c_lt : c ^ k < (c + 1) ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
    have hpow_ce_lt : (c + e) ^ k < (c + 1 + e) ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
    have h1 : (c + e) ^ (k + 1) = (c + e) * (c + e) ^ k := by rw [pow_succ']
    have h2 : (c + 1) ^ (k + 1) = (c + 1) * (c + 1) ^ k := by rw [pow_succ']
    have h3 : (c + 1 + e) ^ (k + 1) = (c + 1 + e) * (c + 1 + e) ^ k := by rw [pow_succ']
    have h4 : c ^ (k + 1) = c * c ^ k := by rw [pow_succ']
    rw [h1, h2, h3, h4]
    zify at ih hpow_le hpow_lt hpow_c_lt hpow_ce_lt ⊢
    nlinarith

/-- For `c ≤ a`, `a - c` divides `a^d - c^d`. -/
theorem nat_sub_dvd_pow_sub_pow {a c : ℕ} (hca : c ≤ a) (d : ℕ) :
    (a - c) ∣ (a ^ d - c ^ d) := by
  have hpow : c ^ d ≤ a ^ d := Nat.pow_le_pow_left hca d
  rw [← Int.natCast_dvd_natCast, Int.ofNat_sub hca, Int.ofNat_sub hpow]
  push_cast
  exact _root_.sub_dvd_pow_sub_pow (a : ℤ) (c : ℤ) d

/-- **Divisor bound for `d`-th power differences (`d ≥ 2`).**
Any finite set `S` of pairs `(a, c) ∈ ℕ × ℕ` satisfying `c < a` and `a^d - c^d = M` (for `M > 0`)
has cardinality at most `(Nat.divisors M).card`. -/
theorem card_pow_diff_eq_le_divisors {d M : ℕ} (hd : 2 ≤ d) (hM : 0 < M)
    (S : Finset (ℕ × ℕ)) (hS : ∀ p ∈ S, p.2 < p.1 ∧ p.1 ^ d - p.2 ^ d = M) :
    S.card ≤ M.divisors.card := by
  refine Finset.card_le_card_of_injOn (fun p => p.1 - p.2) ?_ ?_
  · intro p hp
    obtain ⟨hlt, heq⟩ := hS p hp
    simp only [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, hM.ne'⟩
    rw [← heq]
    exact nat_sub_dvd_pow_sub_pow hlt.le d
  · intro p₁ hp₁ p₂ hp₂ hdiff
    simp only at hdiff
    obtain ⟨hlt₁, heq₁⟩ := hS p₁ hp₁
    obtain ⟨hlt₂, heq₂⟩ := hS p₂ hp₂
    set e := p₁.1 - p₁.2
    have he : 1 ≤ e := by omega
    have ha₁ : p₁.1 = p₁.2 + e := by omega
    have ha₂ : p₂.1 = p₂.2 + e := by omega
    have hval : (p₁.2 + e) ^ d - p₁.2 ^ d = (p₂.2 + e) ^ d - p₂.2 ^ d := by
      rw [← ha₁, ← ha₂, heq₁, heq₂]
    have hc : p₁.2 = p₂.2 := (strictMono_add_pow_sub_pow hd he).injective hval
    ext
    · omega
    · exact hc

/-! ### Part 2: Exact polynomial recurrence and nonvanishing of `Φ_q(X, B)` -/

/-- The polynomial `Φ_q(X, B)` in `(ℤ[B])[X]` appearing in the `q`-th derivative of
`f_B(x) = (x^d + B)^(1/d)`:
`Φ_2 = 1`, `Φ_{q+1} = ((d - q)(X + B) + (1 - q d) X) Φ_q + d X (X + B) ∂_X Φ_q`.
Indexed by `n = q - 2 : ℕ`, so `phiPoly d n` represents `Φ_{n+2}(X, B)`. -/
noncomputable def phiPoly (d : ℕ) : ℕ → Polynomial (Polynomial ℤ)
  | 0 => 1
  | n + 1 =>
    let q : ℤ := (n + 2 : ℤ)
    let di : ℤ := (d : ℤ)
    let Xb : Polynomial (Polynomial ℤ) := Polynomial.X
    let Bb : Polynomial (Polynomial ℤ) := Polynomial.C Polynomial.X
    let P := phiPoly d n
    (Polynomial.C (Polynomial.C (di - q)) * (Xb + Bb) +
      Polynomial.C (Polynomial.C (1 - q * di)) * Xb) * P +
      Polynomial.C (Polynomial.C di) * Xb * (Xb + Bb) * Polynomial.derivative P

/-- Explicit leading `X`-coefficient of `Φ_{n+2}(X, B)`: `(-1)^n ∏_{j < n} (d + 1 + j)`. -/
def phiLead (d : ℕ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => -((d : ℤ) + (n : ℤ) + 1) * phiLead d n

theorem phiLead_ne_zero {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : phiLead d n ≠ 0 := by
  induction n with
  | zero => simp [phiLead]
  | succ n ih =>
    unfold phiLead
    refine mul_ne_zero ?_ ih
    omega

/-- Helper: rewriting the `Φ` recurrence cleanly in powers of `X`. -/
private lemma phiPoly_step_eq (d n : ℕ) :
    let q : ℤ := (n + 2 : ℤ)
    let di : ℤ := (d : ℤ)
    phiPoly d (n + 1) =
      (Polynomial.C (Polynomial.C (di - q + 1 - q * di)) * Polynomial.X +
        Polynomial.C (Polynomial.C (di - q) * Polynomial.X)) * phiPoly d n +
      (Polynomial.C (Polynomial.C di) * Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.C di * Polynomial.X) * Polynomial.X) *
          Polynomial.derivative (phiPoly d n) := by
  simp only [phiPoly, map_mul, map_add, map_sub, map_one]
  ring

private lemma coeff_X_mul_add_C_mul (R : Type*) [CommRing R] (a b : R) (P : Polynomial R) (k : ℕ) :
    ((Polynomial.C a * Polynomial.X + Polynomial.C b) * P).coeff (k + 1) =
      a * P.coeff k + b * P.coeff (k + 1) := by
  rw [add_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]

private lemma coeff_X_sq_mul_add_CX_mul (R : Type*) [CommRing R] (a b : R) (P : Polynomial R)
    (k : ℕ) :
    ((Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X) * P).coeff (k + 1) =
      (if k = 0 then 0 else a * P.coeff (k - 1)) + b * P.coeff k := by
  rw [add_mul, Polynomial.coeff_add, mul_assoc, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
  congr 1
  rcases k with _ | k
  · simp [pow_two, mul_assoc]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [pow_two, mul_assoc, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]

/-- Joint induction on `n = q - 2`: `phiPoly d n` has `X`-degree at most `n` and exact coefficient
`C (phiLead d n)` at degree `n`. -/
theorem phiPoly_spec (d n : ℕ) :
    (∀ k > n, (phiPoly d n).coeff k = 0) ∧
    (phiPoly d n).coeff n = Polynomial.C (phiLead d n) := by
  induction n with
  | zero =>
    constructor
    · intro k hk
      simp [phiPoly, Polynomial.coeff_one, hk.ne']
    · simp [phiPoly, phiLead]
  | succ n ih =>
    obtain ⟨hdeg, hlead⟩ := ih
    have hstep := phiPoly_step_eq d n
    set P := phiPoly d n
    set q : ℤ := (n + 2 : ℤ)
    set di : ℤ := (d : ℤ)
    have hderiv_zero : ∀ k ≥ n, (Polynomial.derivative P).coeff k = 0 := by
      intro k hk
      rw [Polynomial.coeff_derivative, hdeg (k + 1) (by omega), zero_mul]
    constructor
    · intro k hk
      rcases k with _ | k
      · omega
      · rw [hstep, Polynomial.coeff_add, coeff_X_mul_add_C_mul, coeff_X_sq_mul_add_CX_mul]
        have hk1 : k > n := by omega
        have hP1 : P.coeff k = 0 := hdeg k hk1
        have hP2 : P.coeff (k + 1) = 0 := hdeg (k + 1) (by omega)
        have hd2 : (Polynomial.derivative P).coeff k = 0 := hderiv_zero k (by omega)
        have hd1 : (if k = 0 then (0 : Polynomial ℤ) else
            Polynomial.C di * (Polynomial.derivative P).coeff (k - 1)) = 0 := by
          split_ifs with hk0
          · rfl
          · rw [hderiv_zero (k - 1) (by omega), mul_zero]
        rw [hP1, hP2, hd1, hd2]
        simp
    · rw [hstep, Polynomial.coeff_add, coeff_X_mul_add_C_mul, coeff_X_sq_mul_add_CX_mul]
      have hP_succ : P.coeff (n + 1) = 0 := hdeg (n + 1) (by omega)
      have hd_n : (Polynomial.derivative P).coeff n = 0 := hderiv_zero n le_rfl
      rw [hP_succ, hd_n, mul_zero, mul_zero, add_zero, add_zero, hlead]
      rcases n with _ | m
      · simp only [↓reduceIte, add_zero, phiLead, q, di]
        rw [← Polynomial.C_mul]
        congr 1
        ring
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
          Polynomial.coeff_derivative, hlead]
        have hcast : ((m : Polynomial ℤ) + 1) = Polynomial.C ((m : ℤ) + 1) := by
          simp
        rw [hcast, ← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_add]
        congr 1
        simp only [phiLead, q, di]
        push_cast
        ring

/-- For every `d ≥ 1` and `n = q - 2 ≥ 0`, `phiPoly d n` is nonzero. -/
theorem phiPoly_ne_zero {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : phiPoly d n ≠ 0 := by
  intro h0
  have hlead := (phiPoly_spec d n).2
  rw [h0, Polynomial.coeff_zero] at hlead
  have hne : Polynomial.C (phiLead d n) ≠ (0 : Polynomial ℤ) := by
    rw [ne_eq, Polynomial.C_eq_zero]
    exact phiLead_ne_zero hd n
  exact hne hlead.symm

/-- For every `d ≥ 1` and `n = q - 2 ≥ 0`, `phiPoly d n` has exact `X`-degree `n`. -/
theorem phiPoly_natDegree {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : (phiPoly d n).natDegree = n := by
  obtain ⟨hdeg, hlead⟩ := phiPoly_spec d n
  apply le_antisymm
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => hdeg k hk)
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [hlead, ne_eq, Polynomial.C_eq_zero]
    exact phiLead_ne_zero hd n

/-- For every `d ≥ 1` and `n = q - 2 ≥ 0`, `phiPoly d n` has exact leading `X`-coefficient
`C (phiLead d n)` (which is a nonzero constant in `ℤ[B]`). -/
theorem phiPoly_leadingCoeff {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    (phiPoly d n).leadingCoeff = Polynomial.C (phiLead d n) := by
  rw [Polynomial.leadingCoeff, phiPoly_natDegree hd n, (phiPoly_spec d n).2]

/-! ### Part 3: Dominant-loss `p`-adic coincidence peeling lemma -/

private lemma rat_isCoprime_num_den (q : ℚ) : IsCoprime q.num (q.den : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
  exact q.reduced

private lemma sum_div_pow_eq {p d : ℕ} {ι : Type*} (u : ι → ℤ) (e : ι → ℕ) (S : Finset ι) :
    ∑ i ∈ S, ((u i : ℚ) / (p : ℚ) ^ (e i)) ^ d =
      ∑ i ∈ S, (((u i ^ d : ℤ) : ℚ) / (p : ℚ) ^ (d * e i)) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [div_pow, ← pow_mul, mul_comm (e i) d]
  push_cast; rfl

/-- Helper: `p`-adic denominator exactness of a rational sum with a single strictly deepest term
`a / p^M` (`p ∤ a`, `M > 0`) plus terms whose denominators divide `p^(M - 1)`. -/
private lemma pow_dvd_den_and_not_succ_of_unique_max {p : ℕ} (hp : p.Prime)
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (e : ι → ℕ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (he₀ : 1 ≤ e i₀) (ha₀ : ¬ (p : ℤ) ∣ a i₀)
    (hstrict : ∀ i ∈ s, i ≠ i₀ → e i < e i₀) :
    let val : ℚ := ∑ i ∈ s, (a i : ℚ) / (p : ℚ) ^ (e i)
    p ^ (e i₀) ∣ val.den ∧ ¬ p ^ (e i₀ + 1) ∣ val.den := by
  classical
  intro val
  set M := e i₀
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpM_ne : ((p ^ M : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (pow_pos hp.pos M).ne'
  let N_tot : ℤ := ∑ i ∈ s, a i * (p : ℤ) ^ (M - e i)
  have hval_eq : val = (N_tot : ℚ) / ((p ^ M : ℕ) : ℚ) := by
    rw [eq_div_iff hpM_ne]
    simp only [val, N_tot, Finset.sum_mul, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hle : e i ≤ M := by
      by_cases h : i = i₀
      · subst h; exact le_rfl
      · exact (hstrict i hi h).le
    have hp_ne : (p : ℚ) ≠ 0 := hp_pos.ne'
    have hsplit : (p : ℚ) ^ M = (p : ℚ) ^ (e i) * (p : ℚ) ^ (M - e i) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    push_cast
    rw [hsplit]
    field_simp [hp_ne]
  have hnot_dvd : ¬ (p : ℤ) ∣ N_tot := by
    have hsplit : N_tot = a i₀ + ∑ i ∈ s.erase i₀, a i * (p : ℤ) ^ (M - e i) := by
      simp only [N_tot]
      rw [← Finset.add_sum_erase s _ hi₀]
      simp [M]
    rw [hsplit]
    intro hdvd
    have hrest : (p : ℤ) ∣ ∑ i ∈ s.erase i₀, a i * (p : ℤ) ^ (M - e i) := by
      refine Finset.dvd_sum (fun i hi => ?_)
      have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      have hmem : i ∈ s := (Finset.mem_erase.mp hi).2
      have hlt : e i < M := hstrict i hmem hne
      have hpos : 1 ≤ M - e i := by omega
      exact dvd_mul_of_dvd_right (dvd_pow_self (p : ℤ) (by omega)) _
    have hsub : (p : ℤ) ∣ a i₀ := by
      have := dvd_sub hdvd hrest
      simpa using this
    exact ha₀ hsub
  have hcross : val.num * (p ^ M : ℤ) = N_tot * (val.den : ℤ) := by
    have hrat : (val.num : ℚ) / (val.den : ℚ) = (N_tot : ℚ) / ((p ^ M : ℕ) : ℚ) := by
      rw [Rat.num_div_den, hval_eq]
    have hden_ne : (val.den : ℚ) ≠ 0 := by exact_mod_cast val.den_nz
    have hq : (val.num : ℚ) * ((p ^ M : ℕ) : ℚ) = (N_tot : ℚ) * (val.den : ℚ) := by
      field_simp [hden_ne, hpM_ne] at hrat
      linarith
    exact_mod_cast hq
  have hden_dvd : val.den ∣ p ^ M := by
    have hcop : IsCoprime val.num (val.den : ℤ) := rat_isCoprime_num_den val
    have hdvd_z : (val.den : ℤ) ∣ val.num * (p ^ M : ℤ) := ⟨N_tot, by linarith⟩
    have hdvd_z' : (val.den : ℤ) ∣ (p ^ M : ℤ) := hcop.symm.dvd_of_dvd_mul_left hdvd_z
    exact_mod_cast hdvd_z'
  have hpM_dvd : p ^ M ∣ val.den := by
    have hcop_p : IsCoprime (p : ℤ) N_tot :=
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).coprime_iff_not_dvd.mpr hnot_dvd
    have hcop_pow : IsCoprime ((p : ℤ) ^ M) N_tot := hcop_p.pow_left
    have hdvd_z : ((p : ℤ) ^ M) ∣ N_tot * (val.den : ℤ) := ⟨val.num, by linarith⟩
    have hdvd_z' : ((p : ℤ) ^ M) ∣ (val.den : ℤ) := hcop_pow.dvd_of_dvd_mul_left hdvd_z
    exact_mod_cast hdvd_z'
  have hden_eq : val.den = p ^ M := Nat.dvd_antisymm hden_dvd hpM_dvd
  constructor
  · rw [hden_eq]
  · rw [hden_eq]
    intro hle
    have hlt : p ^ M < p ^ (M + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self M)
    have hle' : p ^ (M + 1) ≤ p ^ M := Nat.le_of_dvd (pow_pos hp.pos M) hle
    omega

/-- Upper denominator bound when every term in a sum has denominator dividing `p^B`. -/
private lemma den_dvd_pow_of_all_le {p : ℕ} (hp : p.Prime)
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (e : ι → ℕ) {B : ℕ}
    (hle : ∀ i ∈ s, e i ≤ B) :
    (∑ i ∈ s, (a i : ℚ) / (p : ℚ) ^ (e i)).den ∣ p ^ B := by
  set val : ℚ := ∑ i ∈ s, (a i : ℚ) / (p : ℚ) ^ (e i)
  let N_tot : ℤ := ∑ i ∈ s, a i * (p : ℤ) ^ (B - e i)
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpB_ne : ((p ^ B : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (pow_pos hp.pos B).ne'
  have hval_eq : val = (N_tot : ℚ) / ((p ^ B : ℕ) : ℚ) := by
    rw [eq_div_iff hpB_ne]
    simp only [val, N_tot, Finset.sum_mul, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hp_ne : (p : ℚ) ≠ 0 := hp_pos.ne'
    have hsplit : (p : ℚ) ^ B = (p : ℚ) ^ (e i) * (p : ℚ) ^ (B - e i) := by
      rw [← pow_add, Nat.add_sub_of_le (hle i hi)]
    push_cast
    rw [hsplit]
    field_simp [hp_ne]
  have hcross : val.num * (p ^ B : ℤ) = N_tot * (val.den : ℤ) := by
    have hrat : (val.num : ℚ) / (val.den : ℚ) = (N_tot : ℚ) / ((p ^ B : ℕ) : ℚ) := by
      rw [Rat.num_div_den, hval_eq]
    have hden_ne : (val.den : ℚ) ≠ 0 := by exact_mod_cast val.den_nz
    have hq : (val.num : ℚ) * ((p ^ B : ℕ) : ℚ) = (N_tot : ℚ) * (val.den : ℚ) := by
      field_simp [hden_ne, hpB_ne] at hrat
      linarith
    exact_mod_cast hq
  have hcop : IsCoprime val.num (val.den : ℤ) := rat_isCoprime_num_den val
  have hdvd_z : (val.den : ℤ) ∣ val.num * (p ^ B : ℤ) := ⟨N_tot, by linarith⟩
  have hdvd_z' : (val.den : ℤ) ∣ (p ^ B : ℤ) := hcop.symm.dvd_of_dvd_mul_left hdvd_z
  exact_mod_cast hdvd_z'

/-- **Dominant-loss `p`-adic coincidence peeling lemma (Track C1 / C3-M1).**
Let `p` be prime and `d ≥ 1`. Suppose `y_i = a_i / p^(h_i)` (`i ∈ s`) has a unique top loss
`h_top = h j₀ ≥ 1` with `p ∤ a j₀`, and `w_i = c_i / p^(g_i)` (`i ∈ t`) has `p ∤ c i` for all
`i ∈ t` and total loss `∑ i ∈ t, g i < 2 * h_top`. If
`∑ i ∈ s, (a i / p^(h i))^d = ∑ i ∈ t, (c i / p^(g i))^d`,
then there is a **unique** `i₀ ∈ t` with `g i₀ = h_top`, and every other `i ∈ t` has `g i < h_top`. -/
theorem dominant_loss_unique_top_coord {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    {ι₁ ι₂ : Type*} (s : Finset ι₁) (t : Finset ι₂)
    (a : ι₁ → ℤ) (h : ι₁ → ℕ) (c : ι₂ → ℤ) (g : ι₂ → ℕ)
    {j₀ : ι₁} (hj₀ : j₀ ∈ s) (hh₀ : 1 ≤ h j₀) (ha₀ : ¬ (p : ℤ) ∣ a j₀)
    (hstrict : ∀ j ∈ s, j ≠ j₀ → h j < h j₀)
    (hc : ∀ i ∈ t, ¬ (p : ℤ) ∣ c i)
    (hsum_g : ∑ i ∈ t, g i < 2 * h j₀)
    (heq : ∑ j ∈ s, ((a j : ℚ) / (p : ℚ) ^ (h j)) ^ d =
           ∑ i ∈ t, ((c i : ℚ) / (p : ℚ) ^ (g i)) ^ d) :
    ∃! i₀ ∈ t, g i₀ = h j₀ ∧ ∀ i ∈ t, i ≠ i₀ → g i < h j₀ := by
  classical
  rw [sum_div_pow_eq a h s, sum_div_pow_eq c g t] at heq
  have ha₀_d : ¬ (p : ℤ) ∣ (a j₀) ^ d := fun hdvd =>
    ha₀ ((Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_of_dvd_pow hdvd)
  have hLHS := pow_dvd_den_and_not_succ_of_unique_max hp s (fun j => a j ^ d) (fun j => d * h j)
    hj₀ (by nlinarith) ha₀_d (fun j hj hne => Nat.mul_lt_mul_of_pos_left (hstrict j hj hne) hd)
  have hatmost1 : ∀ i₁ ∈ t, ∀ i₂ ∈ t, h j₀ ≤ g i₁ → h j₀ ≤ g i₂ → i₁ = i₂ := by
    intro i₁ hi₁ i₂ hi₂ hg₁ hg₂
    by_contra hne
    have hpair : g i₁ + g i₂ ≤ ∑ i ∈ t, g i := by
      have hsub : ({i₁, i₂} : Finset ι₂) ⊆ t := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      calc g i₁ + g i₂ = ∑ i ∈ ({i₁, i₂} : Finset ι₂), g i := by
            rw [Finset.sum_pair hne]
        _ ≤ ∑ i ∈ t, g i := Finset.sum_le_sum_of_subset hsub
    omega
  by_cases hex : ∃ i ∈ t, h j₀ ≤ g i
  · obtain ⟨i₀, hi₀, hgi₀⟩ := hex
    have hother : ∀ i ∈ t, i ≠ i₀ → g i < h j₀ := by
      intro i hi hne
      by_contra hge
      exact hne (hatmost1 i hi i₀ hi₀ (by omega) hgi₀)
    have hgi₀_eq : g i₀ = h j₀ := by
      by_contra hne
      have hgt : h j₀ < g i₀ := by omega
      have hc₀_d : ¬ (p : ℤ) ∣ (c i₀) ^ d := fun hdvd =>
        hc i₀ hi₀ ((Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_of_dvd_pow hdvd)
      have hRHS := pow_dvd_den_and_not_succ_of_unique_max hp t (fun i => c i ^ d)
        (fun i => d * g i) hi₀ (by nlinarith) hc₀_d
        (fun i hi hneq => Nat.mul_lt_mul_of_pos_left ((hother i hi hneq).trans hgt) hd)
      rw [← heq] at hRHS
      have hle_exp : d * h j₀ + 1 ≤ d * g i₀ := by nlinarith
      have hdvd_succ : p ^ (d * h j₀ + 1) ∣ (∑ j ∈ s, (((a j ^ d : ℤ) : ℚ) / (p : ℚ) ^ (d * h j))).den :=
        (Nat.pow_dvd_pow p hle_exp).trans hRHS.1
      exact hLHS.2 hdvd_succ
    refine ⟨i₀, ⟨hi₀, hgi₀_eq, hother⟩, ?_⟩
    rintro i' ⟨hi', hgi', _⟩
    exact hatmost1 i' hi' i₀ hi₀ (by omega) hgi₀
  · push Not at hex
    have hall : ∀ i ∈ t, d * g i ≤ d * (h j₀ - 1) := by
      intro i hi
      have hlt := hex i hi
      exact Nat.mul_le_mul_left d (by omega)
    have hdvd_small := den_dvd_pow_of_all_le hp t (fun i => c i ^ d) (fun i => d * g i) hall
    rw [← heq] at hdvd_small
    have hdvd_trans : p ^ (d * h j₀) ∣ p ^ (d * (h j₀ - 1)) := hLHS.1.trans hdvd_small
    have hlt_pow : p ^ (d * (h j₀ - 1)) < p ^ (d * h j₀) := by
      apply Nat.pow_lt_pow_right hp.one_lt
      have : h j₀ - 1 < h j₀ := by omega
      exact Nat.mul_lt_mul_of_pos_left this hd
    have hle_pow : p ^ (d * h j₀) ≤ p ^ (d * (h j₀ - 1)) :=
      Nat.le_of_dvd (pow_pos hp.pos _) hdvd_trans
    omega

/-! ### Part 4: Truncated `r`-fold mass and exact jump at an isolated centre (Track C1.3) -/

/-- Truncated `r`-fold `p`-adic mass up to unweighted loss `Λ` and power-sum cutoff `u`. -/
def truncMass (r p s d Λ : ℕ) (coords : Finset ℚ) (loss : ℚ → ℕ) (u : ℚ) : ℤ :=
  ∑ z ∈ (Fintype.piFinset fun _ : Fin r => coords).filter
      (fun z => ∑ i, loss (z i) ≤ Λ ∧ ∑ i, z i ^ d ≤ u),
    (p : ℤ) ^ (s * ∑ i, loss (z i))

/-- Exact difference of the truncated `r`-fold mass across `(u, u']`. -/
theorem truncMass_sub {r p s d Λ : ℕ} {coords : Finset ℚ} {loss : ℚ → ℕ} {u u' : ℚ}
    (h : u ≤ u') :
    truncMass r p s d Λ coords loss u' - truncMass r p s d Λ coords loss u =
      ∑ z ∈ (Fintype.piFinset fun _ : Fin r => coords).filter
          (fun z => ∑ i, loss (z i) ≤ Λ ∧ u < ∑ i, z i ^ d ∧ ∑ i, z i ^ d ≤ u'),
        (p : ℤ) ^ (s * ∑ i, loss (z i)) := by
  classical
  unfold truncMass
  set U := (Fintype.piFinset fun _ : Fin r => coords).filter
      (fun z => ∑ i, loss (z i) ≤ Λ ∧ ∑ i, z i ^ d ≤ u')
  set S₁ := (Fintype.piFinset fun _ : Fin r => coords).filter
      (fun z => ∑ i, loss (z i) ≤ Λ ∧ ∑ i, z i ^ d ≤ u)
  set S₂ := (Fintype.piFinset fun _ : Fin r => coords).filter
      (fun z => ∑ i, loss (z i) ≤ Λ ∧ u < ∑ i, z i ^ d ∧ ∑ i, z i ^ d ≤ u')
  have hpart : U = S₁ ∪ S₂ := by
    ext z
    simp only [U, S₁, S₂, mem_union, mem_filter]
    constructor
    · rintro ⟨hz, hΛ, hle'⟩
      rcases le_or_gt (∑ i, z i ^ d) u with hle | hgt
      · left; exact ⟨hz, hΛ, hle⟩
      · right; exact ⟨hz, hΛ, hgt, hle'⟩
    · rintro (⟨hz, hΛ, hle⟩ | ⟨hz, hΛ, _, hle'⟩)
      · exact ⟨hz, hΛ, hle.trans h⟩
      · exact ⟨hz, hΛ, hle'⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    simp only [S₁, S₂, mem_filter] at hz₁ hz₂
    linarith
  rw [hpart, Finset.sum_union hdisj]
  ring

/-- **Exact jump of `truncMass` at an isolated centre with distinct coordinates (Track C1.3).**
If `c : Fin r → ℚ` has pairwise distinct coordinates in `coords`, total loss `H ≤ Λ`, and every
competitor `z` of loss `≤ Λ` with `|∑ z_i^d - ∑ c_i^d| < δ` is a permutation of `c`, then
`truncMass (∑ c_i^d + δ/2) - truncMass (∑ c_i^d - δ/2) = r! * p^(s * H)`. -/
theorem truncMass_jump_of_isolated {r p s d Λ H : ℕ} {coords : Finset ℚ} {loss : ℚ → ℕ}
    {c : Fin r → ℚ} (hc : ∀ i, c i ∈ coords) (hinj : Function.Injective c)
    (hlev : ∑ i, loss (c i) = H) (hHΛ : H ≤ Λ) {δ : ℚ} (hδ : 0 < δ)
    (hiso : ∀ z : Fin r → ℚ, (∀ i, z i ∈ coords) → ∑ i, loss (z i) ≤ Λ →
      |∑ i, z i ^ d - ∑ i, c i ^ d| < δ → ∃ σ : Equiv.Perm (Fin r), z = c ∘ σ) :
    truncMass r p s d Λ coords loss (∑ i, c i ^ d + δ / 2)
        - truncMass r p s d Λ coords loss (∑ i, c i ^ d - δ / 2)
      = (r.factorial : ℤ) * (p : ℤ) ^ (s * H) := by
  classical
  rw [truncMass_sub (by linarith)]
  set F := (Fintype.piFinset fun _ : Fin r => coords).filter
      (fun z => ∑ i, loss (z i) ≤ Λ ∧
        ∑ i, c i ^ d - δ / 2 < ∑ i, z i ^ d ∧ ∑ i, z i ^ d ≤ ∑ i, c i ^ d + δ / 2)
  have hbij : F = (Finset.univ : Finset (Equiv.Perm (Fin r))).image
      (fun σ : Equiv.Perm (Fin r) => c ∘ σ) := by
    ext z
    simp only [F, mem_filter, Fintype.mem_piFinset, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hz, hΛ, hlo, hhi⟩
      have habs : |∑ i, z i ^ d - ∑ i, c i ^ d| < δ := by
        rw [abs_lt]; constructor <;> linarith
      obtain ⟨σ, rfl⟩ := hiso z hz hΛ habs
      exact ⟨σ, rfl⟩
    · rintro ⟨σ, rfl⟩
      have hsum_loss : ∑ i : Fin r, loss ((c ∘ σ) i) = H := by
        simpa [Function.comp] using (Equiv.sum_comp σ (fun i => loss (c i))).trans hlev
      have hsum_pow : ∑ i : Fin r, ((c ∘ σ) i) ^ d = ∑ i : Fin r, c i ^ d := by
        simpa [Function.comp] using Equiv.sum_comp σ (fun i => c i ^ d)
      refine ⟨fun i => hc (σ i), ?_, ?_, ?_⟩
      · rw [hsum_loss]; exact hHΛ
      · rw [hsum_pow]; linarith
      · rw [hsum_pow]; linarith
  have hinj_perm : Set.InjOn (fun σ : Equiv.Perm (Fin r) => c ∘ σ)
      (Finset.univ : Finset (Equiv.Perm (Fin r))) := by
    intro σ₁ _ σ₂ _ heq
    exact Equiv.ext fun i => hinj (congrFun heq i)
  rw [hbij, Finset.sum_image hinj_perm]
  have hconst : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin r))),
      (p : ℤ) ^ (s * ∑ i : Fin r, loss ((c ∘ σ) i)) = (p : ℤ) ^ (s * H) := by
    intro σ _
    have hsum_loss : ∑ i : Fin r, loss ((c ∘ σ) i) = H := by
      simpa [Function.comp] using (Equiv.sum_comp σ (fun i => loss (c i))).trans hlev
    rw [hsum_loss]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

end NormalityChecker.PowerSumPeeling
