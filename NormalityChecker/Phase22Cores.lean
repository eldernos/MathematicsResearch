module

public import NormalityChecker.ClassicalBarriers
public import NormalityChecker.DiscrepancyGeometry
public import NormalityChecker.NormalReciprocalCore

/-! # Phase 22 finite algebraic, automaton, and discrepancy cores (Tracks A3–A4, C1, E1)

Kernel-checked algebraic, combinatorial, and discrepancy cores supporting Phase 22
(`notes/phase22/flagship-digit-laws.md`, `notes/phase22/nonlinear-equality-boundary.md`,
and `notes/phase22/classical-targets-and-recon.md`):

1. **Track A3 — Real-character nonnegativity, `χ₁₂` sign rule, and pentagonal gap balance:**
   - `digits_eq_zero_of_fract_lt`, `digits_eq_top_of_fract_gt` (Lemma 0.1): oriented tail digits
     `0^L` and `(b - 1)^L` from small fractional parts.
   - `dirichletOneConv_mul_of_coprime`, `dirichletOneConv_prime_pow_of_completelyMul`,
     `dirichletOneConv_prime_pow_nonneg_of_realMul`, `dirichletOneConv_nonneg_of_realMul`
     (Proposition 1.1): if `χ : ℕ → ℤ` is completely multiplicative with values in `{-1, 0, 1}`,
     then `0 ≤ (1 * χ)(n)` for every `n : ℕ`.
   - `chi12`, `chi12_sq_sub_sq`, `chi12_int_sq_sub_sq` (Proposition 4.1): for `u` odd, `v` even,
     and exactly one divisible by `3`, `χ₁₂(u² - v²) = 1` if `3 ∣ v` and `-1` otherwise.
   - `sum_alt_pent_gaps`, `abs_sum_alt_pent_gaps_le` (Theorem 2): exact alternating pentagonal
     gap-sum cancellation bound `|∑_{k=1}^K (-1)^k (3k - 1)| ≤ (3K + 2) / 2`.

2. **Track A4 — Strict interiority of nonzero atoms and odd-order complement symmetry:**
   - `atom_ne_grid` (Lemma 5.1): for `Nat.Coprime d b` and `0 < c < d`, `c * b^L ≠ k * d`.
   - `pentHeadSum_add_order` (Theorem 5.3, Euler part): when `t = orderOf (b : ZMod d)` is odd,
     `pentHeadSum b d (k + t) = - pentHeadSum b d k`.
   - `eulerAutomaton_iterate_eq`, `eulerAutomaton_snd_add_order`: exact closed form and odd-order
     antisymmetry `u_{k + t} = - u_k` for `NormalReciprocalCore.eulerAutomatonStep`.
   - `cubeHeadSum_add_period` (Theorem 5.3, Jacobi cube part): when `orderOf (b : ZMod d)` and
     `d` are both odd, `cubeHeadSum b d (k + lcm t d) = - cubeHeadSum b d k`.

3. **Track C1 — Multiplier discrepancy inequality and total-depth retirement split:**
   - `one_sub_radixDiscrepancy_natMul_le`, `one_sub_radixDiscrepancy_intMul_le`,
     `fixed_depth_transfer_deficit_le` (Lemma W & Corollary R3): `1 - D_N(m x; b) ≤ m (1 - D_N(x; b))`.
   - `total_depth_split_sum`, `total_depth_split_sum_zpow` (Theorem R1): exact finite algebraic
     splitting of `p^(s H) * (∑_{i ∈ S} p^(-s v(i)) f(i))^r` into the integral low-depth part
     (`tupleDepth v t ≤ H`) plus the remaining high-depth part (`H < tupleDepth v t`).

4. **Track E1 — Exact arithmetic coefficient identity for `E_+(b) = ∑ 1/(b^n + 1)`:**
   - `erdosBorweinPlusCoeff`: `a_+(n) = τ(n) - 2 [2 ∣ n] τ(n / 2)`.
   - `erdosBorweinPlusCoeff_eq`: for `n ≥ 1`, `a_+(n) = (1 - v₂(n)) * τ_odd(n)`.
   - `erdosBorweinPlusCoeff_eq_altDivisorSum`: for `n ≥ 1`, `a_+(n) = ∑_{d ∣ n} (-1)^(d - 1)`.
   - `erdosBorweinPlusCoeff_pos_iff`, `erdosBorweinPlusCoeff_eq_zero_iff`,
     `erdosBorweinPlusCoeff_neg_iff`: exact sign classification (`Odd n`, `n % 4 = 2`, `4 ∣ n`).
   - `erdosBorweinPlusCoeff_odd_iff`: for `n ≥ 1`, `Odd (a_+(n)) ↔ IsSquare n`.
   - `erdosBorweinPlus_eq_sub`: exact series identity `E_+(b) = E(b) - 2 E(b^2)` for `b ≥ 2`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.Phase22Cores

open AntisymmetricLambert ClassicalBarriers DiscrepancyGeometry NormalReciprocalCore SharpTranslation

/-! ### Part 1: Track A3 — Oriented tails, real-character nonnegativity, `χ₁₂`, and pentagonal balance -/

/-- **Lemma 0.1 (positive side):** a nonnegative fractional part below `b^(-L)` forces `L` zero digits. -/
theorem digits_eq_zero_of_fract_lt {b L : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (h : Int.fract x < ((b : ℝ) ^ L)⁻¹) :
    ⌊(b : ℝ) ^ L * Int.fract x⌋ = 0 := by
  have hb_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by exact_mod_cast (show 0 < b by omega)) L
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · simp only [Int.cast_zero]
    exact mul_nonneg hb_pos.le (Int.fract_nonneg x)
  · simp only [Int.cast_zero, zero_add]
    calc (b : ℝ) ^ L * Int.fract x
        < (b : ℝ) ^ L * ((b : ℝ) ^ L)⁻¹ := mul_lt_mul_of_pos_left h hb_pos
      _ = 1 := mul_inv_cancel₀ hb_pos.ne'

/-- **Lemma 0.1 (negative side):** a fractional part above `1 - b^(-L)` forces `L` digits `b - 1`. -/
theorem digits_eq_top_of_fract_gt {b L : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (h : 1 - ((b : ℝ) ^ L)⁻¹ < Int.fract x) :
    ⌊(b : ℝ) ^ L * Int.fract x⌋ = (b : ℤ) ^ L - 1 := by
  have hb_pos : (0 : ℝ) < (b : ℝ) ^ L := pow_pos (by exact_mod_cast (show 0 < b by omega)) L
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · push_cast
    have hmul : (b : ℝ) ^ L * (1 - ((b : ℝ) ^ L)⁻¹) < (b : ℝ) ^ L * Int.fract x :=
      mul_lt_mul_of_pos_left h hb_pos
    rw [mul_sub, mul_one, mul_inv_cancel₀ hb_pos.ne'] at hmul
    exact hmul.le
  · push_cast
    have hlt : (b : ℝ) ^ L * Int.fract x < (b : ℝ) ^ L * 1 :=
      mul_lt_mul_of_pos_left (Int.fract_lt_one x) hb_pos
    linarith

/-- Multiplicativity of `dirichletOneConv χ` on coprime arguments. -/
theorem dirichletOneConv_mul_of_coprime {χ : ℕ → ℤ}
    (hmul : ∀ a b, Nat.Coprime a b → χ (a * b) = χ a * χ b)
    {a b : ℕ} (hcop : Nat.Coprime a b) :
    dirichletOneConv χ (a * b) = dirichletOneConv χ a * dirichletOneConv χ b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [dirichletOneConv]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [dirichletOneConv]
  unfold dirichletOneConv
  have hab : a * b ≠ 0 := Nat.mul_ne_zero ha.ne' hb.ne'
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij (fun p : ℕ × ℕ => p.1 * p.2) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpa, hpb⟩ := mem_product.mp hp
    obtain ⟨h1, _⟩ := Nat.mem_divisors.mp hpa
    obtain ⟨h2, _⟩ := Nat.mem_divisors.mp hpb
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul h1 h2, hab⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    dsimp only at heq
    obtain ⟨h1a, h1b⟩ := mem_product.mp hp₁
    obtain ⟨h2a, h2b⟩ := mem_product.mp hp₂
    obtain ⟨d1a, _⟩ := Nat.mem_divisors.mp h1a
    obtain ⟨d1b, _⟩ := Nat.mem_divisors.mp h1b
    obtain ⟨d2a, _⟩ := Nat.mem_divisors.mp h2a
    obtain ⟨d2b, _⟩ := Nat.mem_divisors.mp h2b
    have hcop12 : Nat.Coprime p₁.1 p₂.2 := hcop.coprime_dvd_left d1a |>.coprime_dvd_right d2b
    have hcop21 : Nat.Coprime p₂.1 p₁.2 := hcop.coprime_dvd_left d2a |>.coprime_dvd_right d1b
    have h1_dvd_2 : p₁.1 ∣ p₂.1 := hcop12.dvd_of_dvd_mul_right ⟨p₁.2, by rw [← heq]⟩
    have h2_dvd_1 : p₂.1 ∣ p₁.1 := hcop21.dvd_of_dvd_mul_right ⟨p₂.2, by rw [heq]⟩
    have hf : p₁.1 = p₂.1 := Nat.dvd_antisymm h1_dvd_2 h2_dvd_1
    have hp1_pos : 0 < p₁.1 := Nat.pos_of_dvd_of_pos d1a ha
    have hs : p₁.2 = p₂.2 := by
      rw [hf] at heq
      exact Nat.eq_of_mul_eq_mul_left (by omega) heq
    exact Prod.ext hf hs
  · intro d hd
    obtain ⟨hdab, _⟩ := Nat.mem_divisors.mp (mem_coe.mp hd)
    refine ⟨(Nat.gcd d a, Nat.gcd d b),
      mem_coe.mpr (mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d a, ha.ne'⟩,
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d b, hb.ne'⟩⟩), ?_⟩
    dsimp only
    set x : ℕ := Nat.gcd d a
    set y : ℕ := Nat.gcd d b
    have hx_pos : 0 < x := Nat.gcd_pos_of_pos_right d ha
    have hxd : x ∣ d := Nat.gcd_dvd_left d a
    have hxa : x ∣ a := Nat.gcd_dvd_right d a
    have hyd : y ∣ d := Nat.gcd_dvd_left d b
    have hyb : y ∣ b := Nat.gcd_dvd_right d b
    have hxy_cop : Nat.Coprime x y := (hcop.coprime_dvd_left hxa).coprime_dvd_right hyb
    have hdvd1 : x * y ∣ d := hxy_cop.mul_dvd_of_dvd_of_dvd hxd hyd
    have hdvd2 : d ∣ x * y := by
      have hcop_ua : Nat.Coprime (d / x) (a / x) := Nat.coprime_div_gcd_div_gcd hx_pos
      have hxu : x * (d / x) = d := Nat.mul_div_cancel' hxd
      have hxa' : x * (a / x) = a := Nat.mul_div_cancel' hxa
      have hu_dvd_ab : d / x ∣ (a / x) * b := by
        apply (Nat.mul_dvd_mul_iff_left hx_pos).mp
        rw [hxu, ← mul_assoc, hxa']
        exact hdab
      have hu_dvd_b : d / x ∣ b := hcop_ua.dvd_of_dvd_mul_left hu_dvd_ab
      have hu_dvd_y : d / x ∣ y := Nat.dvd_gcd (Nat.div_dvd_of_dvd hxd) hu_dvd_b
      rw [← hxu]
      exact mul_dvd_mul_left x hu_dvd_y
    exact Nat.dvd_antisymm hdvd1 hdvd2
  · intro p hp
    obtain ⟨hpa, hpb⟩ := mem_product.mp hp
    obtain ⟨d1, _⟩ := Nat.mem_divisors.mp hpa
    obtain ⟨d2, _⟩ := Nat.mem_divisors.mp hpb
    exact (hmul p.1 p.2 (hcop.coprime_dvd_left d1 |>.coprime_dvd_right d2)).symm

/-- Prime-power evaluation of `1 * χ` for any completely multiplicative `χ : ℕ → ℤ`. -/
theorem dirichletOneConv_prime_pow_of_completelyMul {χ : ℕ → ℤ}
    (h1 : χ 1 = 1) (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dirichletOneConv χ (p ^ e) = ∑ i ∈ range (e + 1), (χ p) ^ i := by
  have hpow : ∀ i : ℕ, χ (p ^ i) = (χ p) ^ i := by
    intro i
    induction i with
    | zero => simpa using h1
    | succ i ih => rw [pow_succ, hmul, ih, pow_succ]
  unfold dirichletOneConv
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact hpow i

/-- Alternating sum of `(-1)^i` over `0 ≤ i ≤ e`. -/
private lemma sum_neg_one_pow_range (e : ℕ) :
    ∑ i ∈ range (e + 1), (-1 : ℤ) ^ i = if Even e then 1 else 0 := by
  induction e with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hk : Even k
    · have hnot : ¬ Even (k + 1) := by
        rcases hk with ⟨m, rfl⟩
        intro ⟨n, hn⟩; omega
      have hpow : (-1 : ℤ) ^ (k + 1) = -1 := by
        rcases hk with ⟨m, rfl⟩
        rw [← two_mul, pow_succ, pow_mul]
        norm_num
      simp [hk, hnot, hpow]
    · have hev : Even (k + 1) := by
        rw [Nat.not_even_iff_odd] at hk
        rcases hk with ⟨m, rfl⟩
        exact ⟨m + 1, by omega⟩
      have hpow : (-1 : ℤ) ^ (k + 1) = 1 := by
        rcases hev with ⟨m, hm⟩
        rw [hm, ← two_mul, pow_mul]
        norm_num
      simp [hk, hev, hpow]

/-- Explicit local prime-power nonnegativity of `1 * χ` for real completely multiplicative
functions taking values in `{-1, 0, 1}` (Proposition 1.1 local factor). -/
theorem dirichletOneConv_prime_pow_nonneg_of_realMul {χ : ℕ → ℤ}
    (h1 : χ 1 = 1) (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hval : ∀ n, χ n = -1 ∨ χ n = 0 ∨ χ n = 1)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    0 ≤ dirichletOneConv χ (p ^ e) := by
  rw [dirichletOneConv_prime_pow_of_completelyMul h1 hmul hp e]
  rcases hval p with hneg | hzero | hone
  · rw [hneg, sum_neg_one_pow_range]
    split_ifs <;> norm_num
  · rw [hzero]
    have hsplit : ∑ i ∈ range (e + 1), (0 : ℤ) ^ i = 1 := by
      rw [Finset.sum_range_succ']
      simp
    linarith
  · rw [hone]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    omega

/-- **Proposition 1.1 (Track A3): nonnegativity of `1 * χ` for completely multiplicative real characters.**
If `χ : ℕ → ℤ` is completely multiplicative (`χ 1 = 1`, `χ (a * b) = χ a * χ b`) and takes values
in `{-1, 0, 1}`, then `0 ≤ dirichletOneConv χ n` for every `n : ℕ`. -/
theorem dirichletOneConv_nonneg_of_realMul {χ : ℕ → ℤ}
    (h1 : χ 1 = 1) (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hval : ∀ n, χ n = -1 ∨ χ n = 0 ∨ χ n = 1) (n : ℕ) :
    0 ≤ dirichletOneConv χ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases le_or_gt n 1 with hn | hn
    · interval_cases n
      · simp [dirichletOneConv]
      · simp [dirichletOneConv, h1]
    · set p : ℕ := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpn : p ∣ n := Nat.minFac_dvd n
      set e : ℕ := n.factorization p
      set m : ℕ := n / p ^ e
      have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
      have hn_eq : p ^ e * m = n := Nat.mul_div_cancel' hpe_dvd
      have hn0 : n ≠ 0 := by omega
      have he_pos : 1 ≤ e :=
        (hp.pow_dvd_iff_le_factorization hn0 (k := 1)).mp (by simpa using hpn)
      have hpm : ¬ p ∣ m := by
        intro hdvd
        have h1' : p ^ (e + 1) ∣ n := by
          rw [← hn_eq, pow_succ]
          exact mul_dvd_mul_left (p ^ e) hdvd
        have hle := (hp.pow_dvd_iff_le_factorization hn0).mp h1'
        omega
      have hcop : Nat.Coprime (p ^ e) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left e
      have hpe_gt : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
      have hm_lt : m < n := by
        have hm_pos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · rw [h0, mul_zero] at hn_eq; omega
          · exact hpos
        calc m = 1 * m := (one_mul m).symm
          _ < p ^ e * m := Nat.mul_lt_mul_of_pos_right hpe_gt hm_pos
          _ = n := hn_eq
      rw [← hn_eq, dirichletOneConv_mul_of_coprime (fun a b _ => hmul a b) hcop]
      exact mul_nonneg (dirichletOneConv_prime_pow_nonneg_of_realMul h1 hmul hval hp e)
        (ih m hm_lt)

/-- The primitive real character modulo 12: `χ₁₂(m) = (12 / m)` on `ZMod 12`, taking value `+1`
on `{1, 11}`, `-1` on `{5, 7}`, and `0` elsewhere. -/
def chi12 (x : ZMod 12) : ℤ :=
  match x.val with
  | 1 | 11 => 1
  | 5 | 7 => -1
  | _ => 0

theorem chi12_one : chi12 1 = 1 := by decide

theorem chi12_neg (x : ZMod 12) : chi12 (-x) = chi12 x := by
  revert x; decide

theorem chi12_mul (x y : ZMod 12) : chi12 (x * y) = chi12 x * chi12 y := by
  revert x y; decide

/-- **Proposition 4.1 finite core (Track A3):**
For `u, v : ZMod 12` with `u` odd, `v` even, and exactly one of `u, v` divisible by `3`,
`χ₁₂(u² - v²) = 1` if `3 ∣ v` and `-1` otherwise. -/
theorem chi12_sq_sub_sq (u v : ZMod 12) (hu : u.val % 2 = 1) (hv : v.val % 2 = 0)
    (h3 : (u.val % 3 = 0 ∧ v.val % 3 ≠ 0) ∨ (v.val % 3 = 0 ∧ u.val % 3 ≠ 0)) :
    chi12 (u ^ 2 - v ^ 2) = if v.val % 3 = 0 then 1 else -1 := by
  revert u v hu hv h3
  decide

/-- Integer form of Proposition 4.1's sign rule: if `u, v : ℤ` have `u` odd, `v` even, and
`u² + v² ≡ 1 [ZMOD 12]`, then exactly one of `u, v` is divisible by `3` and
`χ₁₂((u² - v² : ZMod 12)) = 1` iff `3 ∣ v`. -/
theorem chi12_int_sq_sub_sq {u v : ℤ} (hu : Odd u) (hv : Even v)
    (hmod : u ^ 2 + v ^ 2 ≡ 1 [ZMOD 12]) :
    (((3 : ℤ) ∣ u ∧ ¬ (3 : ℤ) ∣ v) ∨ ((3 : ℤ) ∣ v ∧ ¬ (3 : ℤ) ∣ u)) ∧
      chi12 (((u ^ 2 - v ^ 2 : ℤ) : ZMod 12)) = if (3 : ℤ) ∣ v then 1 else -1 := by
  have hzmod : ((u : ZMod 12) ^ 2 + (v : ZMod 12) ^ 2) = 1 := by
    have hcast : (((u ^ 2 + v ^ 2 : ℤ) : ZMod 12)) = ((1 : ℤ) : ZMod 12) :=
      (ZMod.intCast_eq_intCast_iff _ _ 12).mpr hmod
    simpa using hcast
  have hval_mod : ∀ z : ℤ, ∀ m : ℕ, m ∣ 12 → ((z : ZMod 12).val : ℤ) ≡ z [ZMOD (m : ℤ)] := by
    intro z m hm
    have h12 : (((z : ZMod 12).val : ℤ)) ≡ z [ZMOD ((12 : ℕ) : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      simp
    exact h12.of_dvd (Int.natCast_dvd_natCast.mpr hm)
  have hu2 : (u : ZMod 12).val % 2 = 1 := by
    have h := hval_mod u 2 (by decide)
    rcases hu with ⟨k, hk⟩
    have hm : ((u : ZMod 12).val : ℤ) % 2 = u % 2 := h
    omega
  have hv2 : (v : ZMod 12).val % 2 = 0 := by
    have h := hval_mod v 2 (by decide)
    rcases hv with ⟨k, hk⟩
    have hm : ((v : ZMod 12).val : ℤ) % 2 = v % 2 := h
    omega
  have h3_iff : ∀ z : ℤ, ((3 : ℤ) ∣ z) ↔ (z : ZMod 12).val % 3 = 0 := by
    intro z
    have h := hval_mod z 3 (by decide)
    have hm : ((z : ZMod 12).val : ℤ) % 3 = z % 3 := h
    constructor
    · intro hd; omega
    · intro h0; omega
  have hxor_zmod : ((u : ZMod 12).val % 3 = 0 ∧ (v : ZMod 12).val % 3 ≠ 0) ∨
      ((v : ZMod 12).val % 3 = 0 ∧ (u : ZMod 12).val % 3 ≠ 0) := by
    have hdec : ∀ a b : ZMod 12, a ^ 2 + b ^ 2 = 1 →
        (a.val % 3 = 0 ∧ b.val % 3 ≠ 0) ∨ (b.val % 3 = 0 ∧ a.val % 3 ≠ 0) := by
      decide
    exact hdec (u : ZMod 12) (v : ZMod 12) hzmod
  refine ⟨?_, ?_⟩
  · rcases hxor_zmod with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨(h3_iff u).mpr h1, fun hv3 => h2 ((h3_iff v).mp hv3)⟩
    · right; exact ⟨(h3_iff v).mpr h1, fun hu3 => h2 ((h3_iff u).mp hu3)⟩
  · have hcast : (((u ^ 2 - v ^ 2 : ℤ) : ZMod 12)) = (u : ZMod 12) ^ 2 - (v : ZMod 12) ^ 2 := by
      push_cast; rfl
    rw [hcast, chi12_sq_sub_sq (u : ZMod 12) (v : ZMod 12) hu2 hv2 hxor_zmod]
    by_cases hv3 : (3 : ℤ) ∣ v
    · simp [hv3, (h3_iff v).mp hv3]
    · simp [hv3, mt (h3_iff v).mpr hv3]

/-- Exact closed form of the alternating pentagonal gap sum `∑_{k=1}^K (-1)^k (3k - 1)`. -/
theorem sum_alt_pent_gaps (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (-1 : ℤ) ^ k * (3 * (k : ℤ) - 1) =
      if Even K then 3 * ((K / 2 : ℕ) : ℤ) else -(3 * ((K / 2 : ℕ) : ℤ) + 2) := by
  induction K with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp), ih]
    by_cases hn : Even n
    · rcases hn with ⟨m, rfl⟩
      have hnot : ¬ Even (m + m + 1) := by intro ⟨r, hr⟩; omega
      have hpow : (-1 : ℤ) ^ (m + m + 1) = -1 := by
        rw [← two_mul, pow_succ, pow_mul]; norm_num
      have hd1 : (m + m) / 2 = m := by omega
      have hd2 : (m + m + 1) / 2 = m := by omega
      simp only [show Even (m + m) from ⟨m, rfl⟩, hnot, ↓reduceIte, hpow, hd1, hd2]
      push_cast
      ring
    · rw [Nat.not_even_iff_odd] at hn
      rcases hn with ⟨m, rfl⟩
      have hnot : ¬ Even (2 * m + 1) := by intro ⟨r, hr⟩; omega
      have hev : Even (2 * m + 1 + 1) := ⟨m + 1, by omega⟩
      have hpow : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul]; norm_num
      have hd1 : (2 * m + 1) / 2 = m := by omega
      have hd2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      simp only [hnot, hev, ↓reduceIte, hpow, hd1, hd2]
      push_cast
      ring

/-- **Theorem 2 sign balance core (Track A3):**
For every `K : ℕ`, `|∑_{k=1}^K (-1)^k (3k - 1)| ≤ (3K + 2) / 2`. -/
theorem abs_sum_alt_pent_gaps_le (K : ℕ) :
    |∑ k ∈ Finset.Icc 1 K, (-1 : ℤ) ^ k * (3 * (k : ℤ) - 1)| ≤ (3 * (K : ℤ) + 2) / 2 := by
  rw [sum_alt_pent_gaps]
  split_ifs with hK
  · rcases hK with ⟨m, rfl⟩
    have hd : (m + m) / 2 = m := by omega
    rw [hd, abs_of_nonneg (by positivity)]
    omega
  · rw [Nat.not_even_iff_odd] at hK
    rcases hK with ⟨m, rfl⟩
    have hd : (2 * m + 1) / 2 = m := by omega
    rw [hd, abs_neg, abs_of_nonneg (by positivity)]
    omega

/-! ### Part 2: Track A4 — Nonzero atom interiority and odd-order complement symmetry -/

/-- **Lemma 5.1 (Track A4):** nonzero atoms `c / d` (`0 < c < d`, `Nat.Coprime d b`) never land
on a `b`-adic grid point `k / b^L`. -/
theorem atom_ne_grid {b d c L : ℕ} (hcop : Nat.Coprime d b) (hc0 : 0 < c) (hcd : c < d)
    (k : ℤ) : (c : ℤ) * (b : ℤ) ^ L ≠ k * (d : ℤ) := by
  intro h
  have hdvd_z : (d : ℤ) ∣ (c : ℤ) * (b : ℤ) ^ L := ⟨k, by linarith⟩
  have hdvd_n : d ∣ c * b ^ L := by
    have : ((d : ℕ) : ℤ) ∣ ((c * b ^ L : ℕ) : ℤ) := by simpa using hdvd_z
    exact Int.natCast_dvd_natCast.mp this
  have hcop_pow : Nat.Coprime d (b ^ L) := hcop.pow_right L
  have hd_c : d ∣ c := hcop_pow.dvd_of_dvd_mul_right hdvd_n
  have hle : d ≤ c := Nat.le_of_dvd hc0 hd_c
  omega

/-- Generalized pentagonal exponent `P(j) = j(3j - 1) / 2 ≥ 0` for `j : ℤ`. -/
def genPent (j : ℤ) : ℕ :=
  (j * (3 * j - 1) / 2).toNat

theorem two_mul_genPent (j : ℤ) : 2 * (genPent j : ℤ) = j * (3 * j - 1) := by
  have hnn : 0 ≤ j * (3 * j - 1) := by
    rcases le_or_gt 1 j with h1 | h1
    · nlinarith
    · rcases le_or_gt j 0 with h0 | h0
      · nlinarith
      · omega
  have hdvd : (2 : ℤ) ∣ j * (3 * j - 1) := by
    rcases Int.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (3 * (m + m) - 1), by ring⟩
    · exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
  have hdiv_nn : 0 ≤ j * (3 * j - 1) / 2 := Int.ediv_nonneg hnn (by norm_num)
  unfold genPent
  rw [Int.toNat_of_nonneg hdiv_nn]
  exact Int.mul_ediv_cancel' hdvd

private lemma genPent_zero : genPent 0 = 0 := by
  have h := two_mul_genPent 0
  omega

private lemma genPent_neg_nat_eq_add (k : ℕ) :
    genPent (-(k : ℤ)) = genPent (k : ℤ) + k := by
  have h1 := two_mul_genPent (-(k : ℤ))
  have h2 := two_mul_genPent (k : ℤ)
  have heq : (genPent (-(k : ℤ)) : ℤ) = (genPent (k : ℤ) : ℤ) + (k : ℤ) := by linarith
  exact_mod_cast heq

private lemma genPent_neg_succ (k : ℕ) :
    genPent (-((k + 1 : ℕ) : ℤ)) = genPent (-(k : ℤ)) + (3 * (k + 1) - 1) := by
  have h1 := two_mul_genPent (-((k + 1 : ℕ) : ℤ))
  have h2 := two_mul_genPent (-(k : ℤ))
  have h3 : ((3 * (k + 1) - 1 : ℕ) : ℤ) = 3 * (k : ℤ) + 2 := by omega
  have heq : (genPent (-((k + 1 : ℕ) : ℤ)) : ℤ) =
      (genPent (-(k : ℤ)) : ℤ) + ((3 * (k + 1) - 1 : ℕ) : ℤ) := by
    rw [h3]
    push_cast at h1 ⊢
    linarith
  exact_mod_cast heq

private lemma dvd_genPent_add_sub_of_odd {t : ℕ} (hodd : Odd t) (j : ℤ) :
    (t : ℤ) ∣ (genPent (j + t) : ℤ) - (genPent j : ℤ) := by
  rcases hodd with ⟨m, rfl⟩
  have h1 := two_mul_genPent (j + ((2 * m + 1 : ℕ) : ℤ))
  have h2 := two_mul_genPent j
  refine ⟨3 * j + 3 * (m : ℤ) + 1, ?_⟩
  push_cast at h1 ⊢
  linarith

/-- Helper: if `x ^ t = 1` in a monoid and `(t : ℤ) ∣ (a : ℤ) - (b : ℤ)`, then `x ^ a = x ^ b`. -/
private lemma pow_eq_of_pow_eq_one_of_int_dvd {M : Type*} [Monoid M] {x : M} {t a b : ℕ}
    (hxt : x ^ t = 1) (hdvd : (t : ℤ) ∣ (a : ℤ) - (b : ℤ)) :
    x ^ a = x ^ b := by
  rcases le_total a b with hab | hba
  · have hdvd' : (t : ℤ) ∣ ((b - a : ℕ) : ℤ) := by
      rw [Nat.cast_sub hab]
      simpa [neg_sub] using hdvd.neg_right
    obtain ⟨q, hq⟩ := Int.natCast_dvd_natCast.mp hdvd'
    have hbe : b = a + t * q := by omega
    rw [hbe, pow_add, pow_mul, hxt, one_pow, mul_one]
  · have hdvd' : (t : ℤ) ∣ ((a - b : ℕ) : ℤ) := by
      rw [Nat.cast_sub hba]; exact hdvd
    obtain ⟨q, hq⟩ := Int.natCast_dvd_natCast.mp hdvd'
    have hae : a = b + t * q := by omega
    rw [hae, pow_add, pow_mul, hxt, one_pow, mul_one]

/-- Helper: `(-1)^(|j + t|) = - (-1)^(|j|)` in any ring when `t : ℕ` is odd. -/
private lemma neg_one_pow_natAbs_add_odd {R : Type*} [Ring R] {t : ℕ} (hodd : Odd t) (j : ℤ) :
    (-1 : R) ^ (j + (t : ℤ)).natAbs = -((-1 : R) ^ j.natAbs) := by
  have hev_natAbs : ∀ z : ℤ, Even z.natAbs ↔ Even z := by
    intro z
    rw [Nat.even_iff, Int.even_iff]
    omega
  have hpar : ∀ z : ℤ, (-1 : R) ^ z.natAbs = if Even z then 1 else -1 := by
    intro z
    by_cases hz : Even z
    · have hna : Even z.natAbs := (hev_natAbs z).mpr hz
      rcases hna with ⟨r, hr⟩
      simp only [hz, ↓reduceIte]
      rw [hr, ← two_mul, pow_mul]
      norm_num
    · have hna : Odd z.natAbs := by
        rw [← Nat.not_even_iff_odd]
        intro he
        exact hz ((hev_natAbs z).mp he)
      rcases hna with ⟨r, hr⟩
      simp only [hz, ↓reduceIte]
      rw [hr, pow_succ, pow_mul]
      norm_num
  rw [hpar, hpar]
  have ht_not : ¬ Even (t : ℤ) := by
    rcases hodd with ⟨m, rfl⟩
    intro ⟨r, hr⟩; omega
  by_cases hj : Even j
  · have hnot : ¬ Even (j + (t : ℤ)) := by
      intro hjt
      exact ht_not (by
        rcases hj with ⟨r, rfl⟩
        rcases hjt with ⟨s, hs⟩
        exact ⟨s - r, by linarith⟩)
    simp [hj, hnot]
  · have hev : Even (j + (t : ℤ)) := by
      rw [Int.not_even_iff_odd] at hj
      rcases hj with ⟨r, rfl⟩
      rcases hodd with ⟨m, rfl⟩
      refine ⟨r + (m : ℤ) + 1, ?_⟩
      push_cast; ring
    simp [hj, hev]

/-- Pentagonal head term `(-1)^j * b^(-P(j))` in `ZMod d`. -/
def pentTerm (b d : ℕ) (j : ℤ) : ZMod d :=
  (-1 : ZMod d) ^ j.natAbs * ((b : ZMod d)⁻¹) ^ (genPent j)

/-- Generalized pentagonal head sum `∑_{-k ≤ j ≤ k} (-1)^j b^(-P(j))` in `ZMod d`. -/
def pentHeadSum (b d k : ℕ) : ZMod d :=
  ∑ j ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), pentTerm b d j

/-- Under odd multiplicative order `t = orderOf (b : ZMod d)`, shifting `j` by `t` negates
`pentTerm b d j`. -/
theorem pentTerm_add_order {b d : ℕ} [NeZero d] (hcop : Nat.Coprime b d)
    (hodd : Odd (orderOf (b : ZMod d))) (j : ℤ) :
    pentTerm b d (j + (orderOf (b : ZMod d) : ℤ)) = - pentTerm b d j := by
  set t : ℕ := orderOf (b : ZMod d)
  have hunit : IsUnit (b : ZMod d) := (ZMod.isUnit_iff_coprime b d).mpr hcop
  have hmul_inv : (b : ZMod d) * (b : ZMod d)⁻¹ = 1 := ZMod.mul_inv_of_unit (b : ZMod d) hunit
  have hb_pow : (b : ZMod d) ^ t = 1 := pow_orderOf_eq_one (b : ZMod d)
  have hinv_pow : ((b : ZMod d)⁻¹) ^ t = 1 := by
    calc ((b : ZMod d)⁻¹) ^ t
        = 1 * ((b : ZMod d)⁻¹) ^ t := (one_mul _).symm
      _ = (b : ZMod d) ^ t * ((b : ZMod d)⁻¹) ^ t := by rw [hb_pow]
      _ = ((b : ZMod d) * (b : ZMod d)⁻¹) ^ t := (mul_pow _ _ _).symm
      _ = 1 := by rw [hmul_inv, one_pow]
  have hpow_eq : ((b : ZMod d)⁻¹) ^ (genPent (j + t)) = ((b : ZMod d)⁻¹) ^ (genPent j) :=
    pow_eq_of_pow_eq_one_of_int_dvd hinv_pow (dvd_genPent_add_sub_of_odd hodd j)
  unfold pentTerm
  rw [hpow_eq, neg_one_pow_natAbs_add_odd hodd j, neg_mul]

/-- Any block of `2 * orderOf (b : ZMod d)` consecutive pentagonal terms sums to `0` when the
multiplicative order is odd. -/
theorem sum_pentTerm_two_orders_eq_zero {b d : ℕ} [NeZero d] (hcop : Nat.Coprime b d)
    (hodd : Odd (orderOf (b : ZMod d))) (a : ℤ) :
    ∑ j ∈ Finset.Icc (a + 1) (a + 2 * (orderOf (b : ZMod d) : ℤ)), pentTerm b d j = 0 := by
  set t : ℕ := orderOf (b : ZMod d)
  have ht_pos : (0 : ℤ) < (t : ℤ) := by
    rcases hodd with ⟨m, hm⟩; omega
  have hunion : Finset.Icc (a + 1) (a + 2 * (t : ℤ)) =
      Finset.Icc (a + 1) (a + (t : ℤ)) ∪ Finset.Icc (a + (t : ℤ) + 1) (a + 2 * (t : ℤ)) := by
    ext x; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Finset.Icc (a + 1) (a + (t : ℤ)))
      (Finset.Icc (a + (t : ℤ) + 1) (a + 2 * (t : ℤ))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [mem_Icc] at hx1 hx2
    omega
  rw [hunion, Finset.sum_union hdisj]
  have hshift : ∑ j ∈ Finset.Icc (a + (t : ℤ) + 1) (a + 2 * (t : ℤ)), pentTerm b d j =
      ∑ j ∈ Finset.Icc (a + 1) (a + (t : ℤ)), (- pentTerm b d j) := by
    symm
    refine Finset.sum_nbij (fun j : ℤ => j + (t : ℤ)) ?_ ?_ ?_ ?_
    · intro j hj
      rw [mem_Icc] at hj ⊢; omega
    · intro j₁ _ j₂ _ h
      dsimp only at h
      omega
    · intro y hy
      rw [mem_coe, mem_Icc] at hy
      refine ⟨y - (t : ℤ), mem_coe.mpr (mem_Icc.mpr (by omega)), by ring⟩
    · intro j _
      exact (pentTerm_add_order hcop hodd j).symm
  rw [hshift, Finset.sum_neg_distrib, add_neg_cancel]

/-- **Theorem 5.3, Euler part (Track A4):**
When `t = orderOf (b : ZMod d)` is odd and `Nat.Coprime b d`, the generalized pentagonal head sum
is antiperiodic of period `t`: `pentHeadSum b d (k + t) = - pentHeadSum b d k`. -/
theorem pentHeadSum_add_order {b d : ℕ} [NeZero d] (hcop : Nat.Coprime b d)
    (hodd : Odd (orderOf (b : ZMod d))) (k : ℕ) :
    pentHeadSum b d (k + orderOf (b : ZMod d)) = - pentHeadSum b d k := by
  set t : ℕ := orderOf (b : ZMod d)
  have ht_pos : (0 : ℤ) < (t : ℤ) := by
    rcases hodd with ⟨m, hm⟩; omega
  unfold pentHeadSum
  have hunion : Finset.Icc (-((k + t : ℕ) : ℤ)) ((k + t : ℕ) : ℤ) =
      Finset.Icc (-(k : ℤ) - (t : ℤ)) ((k : ℤ) - (t : ℤ)) ∪
        Finset.Icc (((k : ℤ) - (t : ℤ)) + 1) (((k : ℤ) - (t : ℤ)) + 2 * (t : ℤ)) := by
    ext x
    simp only [mem_Icc, mem_union, Nat.cast_add]
    omega
  have hdisj : Disjoint (Finset.Icc (-(k : ℤ) - (t : ℤ)) ((k : ℤ) - (t : ℤ)))
      (Finset.Icc (((k : ℤ) - (t : ℤ)) + 1) (((k : ℤ) - (t : ℤ)) + 2 * (t : ℤ))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [mem_Icc] at hx1 hx2
    omega
  rw [hunion, Finset.sum_union hdisj, sum_pentTerm_two_orders_eq_zero hcop hodd ((k : ℤ) - (t : ℤ)),
    add_zero]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij (fun j : ℤ => j + (t : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    rw [mem_Icc] at hj ⊢; omega
  · intro j₁ _ j₂ _ h
    dsimp only at h
    omega
  · intro y hy
    rw [mem_coe, mem_Icc] at hy
    refine ⟨y - (t : ℤ), mem_coe.mpr (mem_Icc.mpr (by omega)), by ring⟩
  · intro j _
    have h := pentTerm_add_order hcop hodd j
    rw [h, neg_neg]

/-- Exact closed form of the `k`-th iterate of `NormalReciprocalCore.eulerAutomatonStep` from `(0, 1)`
in terms of `pentHeadSum`. -/
theorem eulerAutomaton_iterate_eq {b d L : ℕ} [NeZero d] (hL : 0 < L)
    (h2L : 2 ∣ L) (htL : orderOf (b : ZMod d) ∣ L) (hcop : Nat.Coprime b d) (k : ℕ) :
    (eulerAutomatonStep b d L)^[k] (0, 1) =
      ((k : ZMod L), (b : ZMod d) ^ (genPent (-(k : ℤ))) * pentHeadSum b d k) := by
  have : NeZero L := ⟨hL.ne'⟩
  have hunit : IsUnit (b : ZMod d) := (ZMod.isUnit_iff_coprime b d).mpr hcop
  have hmul_inv : (b : ZMod d) * (b : ZMod d)⁻¹ = 1 := ZMod.mul_inv_of_unit (b : ZMod d) hunit
  have hbL : (b : ZMod d) ^ L = 1 := by
    obtain ⟨q, hq⟩ := htL
    rw [hq, pow_mul, pow_orderOf_eq_one, one_pow]
  induction k with
  | zero =>
    simp [pentHeadSum, pentTerm, genPent_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold eulerAutomatonStep
    dsimp only
    apply Prod.ext
    · push_cast; rfl
    · dsimp only
      set m : ℕ := (k : ZMod L).val + 1
      have hm_val : (k : ZMod L).val = k % L := ZMod.val_natCast L k
      have hk1 : k + 1 = L * (k / L) + m := by
        have hdm := Nat.div_add_mod k L
        omega
      have h3k1 : 3 * (k + 1) - 1 = L * (3 * (k / L)) + (3 * m - 1) := by
        have hm1 : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
        have hmul3 : 3 * (L * (k / L)) = L * (3 * (k / L)) := by ring
        omega
      have hbm : (b : ZMod d) ^ m = (b : ZMod d) ^ (k + 1) := by
        symm
        rw [hk1, pow_add, pow_mul, hbL, one_pow, one_mul]
      have hb3m : (b : ZMod d) ^ (3 * m - 1) = (b : ZMod d) ^ (3 * (k + 1) - 1) := by
        symm
        rw [h3k1, pow_add, pow_mul, hbL, one_pow, one_mul]
      have hsign : (-1 : ZMod d) ^ m = (-1 : ZMod d) ^ (k + 1) := by
        obtain ⟨q, hq⟩ := h2L
        symm
        rw [hk1, hq, mul_assoc, pow_add, pow_mul]
        norm_num
      rw [hbm, hb3m, hsign]
      have hIcc : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
          insert (-((k + 1 : ℕ) : ℤ))
            (insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ))) := by
        ext x; simp only [mem_Icc, mem_insert, Nat.cast_add, Nat.cast_one]; omega
      have hnot1 : (-((k + 1 : ℕ) : ℤ)) ∉
          insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
        simp only [mem_insert, mem_Icc, Nat.cast_add, Nat.cast_one]; omega
      have hnot2 : ((k + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
        simp only [mem_Icc, Nat.cast_add, Nat.cast_one]; omega
      have hsum_succ : pentHeadSum b d (k + 1) =
          pentTerm b d (-((k + 1 : ℕ) : ℤ)) + pentTerm b d ((k + 1 : ℕ) : ℤ) +
            pentHeadSum b d k := by
        unfold pentHeadSum
        rw [hIcc, Finset.sum_insert hnot1, Finset.sum_insert hnot2]
        ring
      have hcancel : ∀ e : ℕ, (b : ZMod d) ^ e * ((b : ZMod d)⁻¹) ^ e = 1 := fun e => by
        rw [← mul_pow, hmul_inv, one_pow]
      have hterm_neg : (b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) *
          pentTerm b d (-((k + 1 : ℕ) : ℤ)) = (-1 : ZMod d) ^ (k + 1) := by
        unfold pentTerm
        have hna : (-((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := Int.natAbs_neg _
        rw [hna]
        calc (b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) *
              ((-1 : ZMod d) ^ (k + 1) * ((b : ZMod d)⁻¹) ^ (genPent (-((k + 1 : ℕ) : ℤ))))
            = (-1 : ZMod d) ^ (k + 1) *
                ((b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) *
                  ((b : ZMod d)⁻¹) ^ (genPent (-((k + 1 : ℕ) : ℤ)))) := by ring
          _ = (-1 : ZMod d) ^ (k + 1) := by rw [hcancel, mul_one]
      have hterm_pos : (b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) *
          pentTerm b d ((k + 1 : ℕ) : ℤ) = (-1 : ZMod d) ^ (k + 1) * (b : ZMod d) ^ (k + 1) := by
        unfold pentTerm
        have hna : ((k + 1 : ℕ) : ℤ).natAbs = k + 1 := Int.natAbs_natCast _
        rw [hna, genPent_neg_nat_eq_add (k + 1), pow_add]
        calc (b : ZMod d) ^ (genPent ((k + 1 : ℕ) : ℤ)) * (b : ZMod d) ^ (k + 1) *
              ((-1 : ZMod d) ^ (k + 1) * ((b : ZMod d)⁻¹) ^ (genPent ((k + 1 : ℕ) : ℤ)))
            = (-1 : ZMod d) ^ (k + 1) * (b : ZMod d) ^ (k + 1) *
                ((b : ZMod d) ^ (genPent ((k + 1 : ℕ) : ℤ)) *
                  ((b : ZMod d)⁻¹) ^ (genPent ((k + 1 : ℕ) : ℤ))) := by ring
          _ = (-1 : ZMod d) ^ (k + 1) * (b : ZMod d) ^ (k + 1) := by rw [hcancel, mul_one]
      rw [hsum_succ]
      calc (b : ZMod d) ^ (3 * (k + 1) - 1) * ((b : ZMod d) ^ (genPent (-(k : ℤ))) * pentHeadSum b d k) +
            (-1 : ZMod d) ^ (k + 1) * ((b : ZMod d) ^ (k + 1) + 1)
          = (b : ZMod d) ^ (genPent (-(k : ℤ)) + (3 * (k + 1) - 1)) * pentHeadSum b d k +
              (-1 : ZMod d) ^ (k + 1) * (b : ZMod d) ^ (k + 1) + (-1 : ZMod d) ^ (k + 1) := by
            rw [pow_add]; ring
        _ = (b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) * pentHeadSum b d k +
              (b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) * pentTerm b d ((k + 1 : ℕ) : ℤ) +
              (b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) * pentTerm b d (-((k + 1 : ℕ) : ℤ)) := by
            rw [hterm_pos, hterm_neg, genPent_neg_succ k]
        _ = (b : ZMod d) ^ (genPent (-((k + 1 : ℕ) : ℤ))) *
              (pentTerm b d (-((k + 1 : ℕ) : ℤ)) + pentTerm b d ((k + 1 : ℕ) : ℤ) + pentHeadSum b d k) := by
            ring

/-- **Track A4 — Odd-order complement symmetry of `NormalReciprocalCore.eulerAutomatonStep`:**
When `t = orderOf (b : ZMod d)` is odd, `Nat.Coprime b d`, `2 ∣ L`, and `t ∣ L`, the residue state
of the Euler rational-scaling automaton negates after `t` steps: `u_{k + t} = - u_k`. -/
theorem eulerAutomaton_snd_add_order {b d L : ℕ} [NeZero d] (hL : 0 < L)
    (h2L : 2 ∣ L) (htL : orderOf (b : ZMod d) ∣ L)
    (hcop : Nat.Coprime b d) (hodd : Odd (orderOf (b : ZMod d))) (k : ℕ) :
    ((eulerAutomatonStep b d L)^[k + orderOf (b : ZMod d)] (0, 1)).2 =
      - ((eulerAutomatonStep b d L)^[k] (0, 1)).2 := by
  set t : ℕ := orderOf (b : ZMod d)
  rw [eulerAutomaton_iterate_eq hL h2L htL hcop (k + t),
    eulerAutomaton_iterate_eq hL h2L htL hcop k]
  dsimp only
  have hpow : (b : ZMod d) ^ (genPent (-((k + t : ℕ) : ℤ))) =
      (b : ZMod d) ^ (genPent (-(k : ℤ))) := by
    have hdvd := dvd_genPent_add_sub_of_odd hodd (-((k + t : ℕ) : ℤ))
    have hshift : -((k + t : ℕ) : ℤ) + (t : ℤ) = -(k : ℤ) := by push_cast; ring
    rw [hshift] at hdvd
    exact (pow_eq_of_pow_eq_one_of_int_dvd (pow_orderOf_eq_one (b : ZMod d)) hdvd).symm
  rw [hpow, pentHeadSum_add_order hcop hodd k, mul_neg]

/-- Triangular number `T_i = i (i + 1) / 2`. -/
def triNum (i : ℕ) : ℕ := i * (i + 1) / 2

private lemma two_mul_triNum (i : ℕ) : 2 * triNum i = i * (i + 1) := by
  unfold triNum
  apply Nat.mul_div_cancel'
  rcases Nat.even_or_odd i with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨m * (m + m + 1), by ring⟩
  · exact ⟨(2 * m + 1) * (m + 1), by ring⟩

/-- Jacobi-cube head term `(-1)^i * (2i + 1) * b^(-T_i)` in `ZMod d`. -/
def cubeTerm (b d i : ℕ) : ZMod d :=
  (-1 : ZMod d) ^ i * ((2 * i + 1 : ℕ) : ZMod d) * ((b : ZMod d)⁻¹) ^ (triNum i)

/-- Jacobi-cube head sum `∑_{0 ≤ i ≤ k} (-1)^i (2i + 1) b^(-T_i)` in `ZMod d`. -/
def cubeHeadSum (b d k : ℕ) : ZMod d :=
  ∑ i ∈ Finset.range (k + 1), cubeTerm b d i

/-- **Theorem 5.3, Jacobi cube part (Track A4):**
When `t = orderOf (b : ZMod d)` and `d` are both odd and `Nat.Coprime b d`, the Jacobi-cube head
sum is antiperiodic of period `T = Nat.lcm t d`: `cubeHeadSum b d (k + T) = - cubeHeadSum b d k`. -/
theorem cubeHeadSum_add_period {b d : ℕ} [NeZero d] (hcop : Nat.Coprime b d)
    (hodd_t : Odd (orderOf (b : ZMod d))) (hodd_d : Odd d) (k : ℕ) :
    cubeHeadSum b d (k + Nat.lcm (orderOf (b : ZMod d)) d) = - cubeHeadSum b d k := by
  set t : ℕ := orderOf (b : ZMod d)
  set T : ℕ := Nat.lcm t d
  have htT : t ∣ T := Nat.dvd_lcm_left t d
  have hdT : d ∣ T := Nat.dvd_lcm_right t d
  have hodd_T : Odd T := by
    rw [← Nat.not_even_iff_odd]
    intro ⟨r, hr⟩
    have h2T : 2 ∣ T := ⟨r, by omega⟩
    have h2or : 2 ∣ t ∨ 2 ∣ d := Nat.prime_two.dvd_mul.mp (h2T.trans (Nat.lcm_dvd_mul t d))
    rcases h2or with ⟨q, hq⟩ | ⟨q, hq⟩
    · rcases hodd_t with ⟨m, hm⟩; omega
    · rcases hodd_d with ⟨m, hm⟩; omega
  have hunit : IsUnit (b : ZMod d) := (ZMod.isUnit_iff_coprime b d).mpr hcop
  have hmul_inv : (b : ZMod d) * (b : ZMod d)⁻¹ = 1 := ZMod.mul_inv_of_unit (b : ZMod d) hunit
  have hb_pow : (b : ZMod d) ^ t = 1 := pow_orderOf_eq_one (b : ZMod d)
  have hinv_pow : ((b : ZMod d)⁻¹) ^ t = 1 := by
    calc ((b : ZMod d)⁻¹) ^ t
        = (b : ZMod d) ^ t * ((b : ZMod d)⁻¹) ^ t := by rw [hb_pow, one_mul]
      _ = ((b : ZMod d) * (b : ZMod d)⁻¹) ^ t := (mul_pow _ _ _).symm
      _ = 1 := by rw [hmul_inv, one_pow]
  have hT_zmod : (T : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff T d).mpr hdT
  -- Step 1: shifting `i` by `T` negates `cubeTerm b d i`.
  have hshift : ∀ i : ℕ, cubeTerm b d (i + T) = - cubeTerm b d i := by
    intro i
    have hpow_tri : ((b : ZMod d)⁻¹) ^ (triNum (i + T)) = ((b : ZMod d)⁻¹) ^ (triNum i) := by
      apply pow_eq_of_pow_eq_one_of_int_dvd hinv_pow
      have h1 := two_mul_triNum (i + T)
      have h2 := two_mul_triNum i
      rcases hodd_T with ⟨m, hm⟩
      have hdvdT : (T : ℤ) ∣ (triNum (i + T) : ℤ) - (triNum i : ℤ) := by
        refine ⟨(i : ℤ) + (m : ℤ) + 1, ?_⟩
        have h1z : (2 : ℤ) * (triNum (i + T) : ℤ) = ((i + T : ℕ) : ℤ) * ((i + T + 1 : ℕ) : ℤ) := by
          exact_mod_cast h1
        have h2z : (2 : ℤ) * (triNum i : ℤ) = (i : ℤ) * ((i + 1 : ℕ) : ℤ) := by
          exact_mod_cast h2
        have hTz : (T : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
        push_cast at h1z h2z
        nlinarith
      exact (Int.natCast_dvd_natCast.mpr htT).trans hdvdT
    have hneg_pow : (-1 : ZMod d) ^ (i + T) = - ((-1 : ZMod d) ^ i) := by
      rcases hodd_T with ⟨m, hm⟩
      rw [pow_add, hm, pow_succ, pow_mul]
      norm_num
    have hlin : ((2 * (i + T) + 1 : ℕ) : ZMod d) = ((2 * i + 1 : ℕ) : ZMod d) := by
      push_cast
      rw [hT_zmod]
      ring
    unfold cubeTerm
    rw [hpow_tri, hneg_pow, hlin]
    ring
  -- Step 2: reversal `i ↦ T - 1 - i` on `[0, T)` negates `cubeTerm b d i`.
  have hrev : ∀ i < T, cubeTerm b d (T - 1 - i) = - cubeTerm b d i := by
    intro i hi
    have hpow_tri : ((b : ZMod d)⁻¹) ^ (triNum (T - 1 - i)) = ((b : ZMod d)⁻¹) ^ (triNum i) := by
      apply pow_eq_of_pow_eq_one_of_int_dvd hinv_pow
      have h1 := two_mul_triNum (T - 1 - i)
      have h2 := two_mul_triNum i
      rcases hodd_T with ⟨m, hm⟩
      have hdvdT : (T : ℤ) ∣ (triNum (T - 1 - i) : ℤ) - (triNum i : ℤ) := by
        refine ⟨(m : ℤ) - (i : ℤ), ?_⟩
        have h1z : (2 : ℤ) * (triNum (T - 1 - i) : ℤ) =
            ((T - 1 - i : ℕ) : ℤ) * ((T - 1 - i + 1 : ℕ) : ℤ) := by
          exact_mod_cast h1
        have h2z : (2 : ℤ) * (triNum i : ℤ) = (i : ℤ) * ((i + 1 : ℕ) : ℤ) := by
          exact_mod_cast h2
        have hsub1 : ((T - 1 - i : ℕ) : ℤ) = (T : ℤ) - 1 - (i : ℤ) := by omega
        have hsub2 : ((T - 1 - i + 1 : ℕ) : ℤ) = (T : ℤ) - (i : ℤ) := by omega
        have hTz : (T : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
        rw [hsub1, hsub2] at h1z
        push_cast at h2z
        nlinarith
      exact (Int.natCast_dvd_natCast.mpr htT).trans hdvdT
    have hsign : (-1 : ZMod d) ^ (T - 1 - i) = (-1 : ZMod d) ^ i := by
      rcases hodd_T with ⟨m, hm⟩
      have hpar : ∀ a b : ℕ, a % 2 = b % 2 → (-1 : ZMod d) ^ a = (-1 : ZMod d) ^ b := by
        intro a b hab
        rw [← Nat.div_add_mod a 2, ← Nat.div_add_mod b 2, hab, pow_add, pow_add, pow_mul, pow_mul]
        norm_num
      exact hpar (T - 1 - i) i (by omega)
    have hlin : ((2 * (T - 1 - i) + 1 : ℕ) : ZMod d) = - ((2 * i + 1 : ℕ) : ZMod d) := by
      have hadd : (2 * (T - 1 - i) + 1) + (2 * i + 1) = 2 * T := by omega
      have hcast : (((2 * (T - 1 - i) + 1) + (2 * i + 1) : ℕ) : ZMod d) = ((2 * T : ℕ) : ZMod d) :=
        congrArg Nat.cast hadd
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hT_zmod, mul_zero] at hcast
      exact eq_neg_of_add_eq_zero_left hcast
    unfold cubeTerm
    rw [hpow_tri, hsign, hlin]
    ring
  -- Step 3: full block `∑_{i < T} cubeTerm b d i = 0` since `d` is odd.
  have hblock : ∑ i ∈ Finset.range T, cubeTerm b d i = 0 := by
    have hsym : ∑ i ∈ Finset.range T, cubeTerm b d (T - 1 - i) =
        ∑ i ∈ Finset.range T, cubeTerm b d i := by
      refine Finset.sum_nbij (fun i => T - 1 - i) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro i hi; rw [mem_range] at hi ⊢; omega
      · intro i₁ hi₁ i₂ hi₂ heq
        dsimp only at heq
        rw [mem_coe, mem_range] at hi₁ hi₂
        omega
      · intro j hj
        rw [mem_coe, mem_range] at hj
        exact ⟨T - 1 - j, mem_coe.mpr (mem_range.mpr (by omega)), by dsimp only; omega⟩
    have hneg : ∑ i ∈ Finset.range T, cubeTerm b d (T - 1 - i) =
        - ∑ i ∈ Finset.range T, cubeTerm b d i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i hi => hrev i (mem_range.mp hi))
    have htwice : (2 : ZMod d) * (∑ i ∈ Finset.range T, cubeTerm b d i) = 0 := by
      rw [two_mul]
      conv_lhs => arg 2; rw [← hsym]
      rw [hneg, add_neg_cancel]
    have hcop2 : Nat.Coprime 2 d := by
      refine Nat.prime_two.coprime_iff_not_dvd.mpr ?_
      intro ⟨q, hq⟩
      rcases hodd_d with ⟨m, hm⟩; omega
    have hunit2 : IsUnit (2 : ZMod d) := (ZMod.isUnit_iff_coprime 2 d).mpr hcop2
    exact hunit2.mul_right_eq_zero.mp htwice
  -- Step 4: split `[0, k + T + 1)` into `[0, T)` and `[T, T + k + 1)`.
  unfold cubeHeadSum
  rw [show k + T + 1 = T + (k + 1) by omega, Finset.sum_range_add, hblock, zero_add]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [add_comm T i, hshift i]

/-! ### Part 3: Track C1 — Multiplier discrepancy inequality & total-depth retirement split -/

/-- **Lemma W (second inequality, Track C1):**
For every radix `b`, cutoff `N > 0`, multiplier `m : ℕ`, and `x : ℝ`,
`1 - D_N(m x; b) ≤ m * (1 - D_N(x; b))`. -/
theorem one_sub_radixDiscrepancy_natMul_le (b : ℕ) {N : ℕ} (hN : 0 < N) (m : ℕ) (x : ℝ) :
    1 - radixDiscrepancy b ((m : ℝ) * x) N ≤ (m : ℝ) * (1 - radixDiscrepancy b x N) := by
  simpa [discDist] using discDist_natMul_le b hN m x 0

/-- Integer-multiplier version of Lemma W (Track C1):
`1 - D_N(m x; b) ≤ |m| * (1 - D_N(x; b))` for every `m : ℤ`. -/
theorem one_sub_radixDiscrepancy_intMul_le (b : ℕ) {N : ℕ} (hN : 0 < N) (m : ℤ) (x : ℝ) :
    1 - radixDiscrepancy b ((m : ℝ) * x) N ≤ |(m : ℝ)| * (1 - radixDiscrepancy b x N) := by
  simpa [discDist] using discDist_intMul_le b hN m x 0

/-- **Corollary R3(2) finite transfer bound (Track C1):**
Whenever `m * x = F + z`, the discrepancy deficit of `x` is controlled from below by that of `z`
minus the perturbation deficit `1 - D_N(F; b)`:
`1 - D_N(z; b) - (1 - D_N(F; b)) ≤ m * (1 - D_N(x; b))`. -/
theorem fixed_depth_transfer_deficit_le (b : ℕ) {N : ℕ} (hN : 0 < N) (m : ℕ) {x F z : ℝ}
    (hsplit : (m : ℝ) * x = F + z) :
    1 - radixDiscrepancy b z N - (1 - radixDiscrepancy b F N) ≤
      (m : ℝ) * (1 - radixDiscrepancy b x N) := by
  have h1 := one_sub_radixDiscrepancy_natMul_le b hN m x
  have h2 := (abs_le.mp (sharp_translation b z F hN)).2
  rw [add_comm z F, ← hsplit] at h2
  linarith

/-- Total depth `∑_{j : Fin r} v (t j)` of an ordered `r`-tuple `t : Fin r → ι`. -/
def tupleDepth {ι : Type*} {r : ℕ} (v : ι → ℕ) (t : Fin r → ι) : ℕ :=
  ∑ j : Fin r, v (t j)

/-- **Theorem R1 finite core (Track C1): total-depth retirement split.**
For any finite index set `S`, valuation function `v : ι → ℕ`, summand `f : ι → K`, nonzero `p : K`,
and integers `s, H, r : ℕ`, multiplying `(∑_{i ∈ S} p^(-s v(i)) f(i))^r` by `p^(s H)` splits
exactly into the integral low-depth part (`tupleDepth v t ≤ H`, with nonnegative powers
`p^(s (H - tupleDepth v t))`) plus the remaining high-depth part (`H < tupleDepth v t`). -/
theorem total_depth_split_sum {ι K : Type*} [Field K]
    (S : Finset ι) (v : ι → ℕ) (f : ι → K) {p : K} (hp : p ≠ 0) (s H r : ℕ) :
    p ^ (s * H) * (∑ i ∈ S, (p ^ (s * v i))⁻¹ * f i) ^ r =
      (∑ t ∈ (Fintype.piFinset fun _ : Fin r => S).filter (fun t => tupleDepth v t ≤ H),
          p ^ (s * (H - tupleDepth v t)) * ∏ j : Fin r, f (t j)) +
      (∑ t ∈ (Fintype.piFinset fun _ : Fin r => S).filter (fun t => H < tupleDepth v t),
          (p ^ (s * (tupleDepth v t - H)))⁻¹ * ∏ j : Fin r, f (t j)) := by
  set T : Finset (Fin r → ι) := Fintype.piFinset fun _ : Fin r => S
  have hexpand : (∑ i ∈ S, (p ^ (s * v i))⁻¹ * f i) ^ r =
      ∑ t ∈ T, ∏ j : Fin r, ((p ^ (s * v (t j)))⁻¹ * f (t j)) :=
    Finset.sum_pow' S (fun i => (p ^ (s * v i))⁻¹ * f i) r
  rw [hexpand, Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => tupleDepth v t ≤ H)]
  have hprod_eval : ∀ t : Fin r → ι,
      ∏ j : Fin r, ((p ^ (s * v (t j)))⁻¹ * f (t j)) =
        (p ^ (s * tupleDepth v t))⁻¹ * ∏ j : Fin r, f (t j) := by
    intro t
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    unfold tupleDepth
    rw [Finset.mul_sum]
  have hlow : ∑ t ∈ T.filter (fun t => tupleDepth v t ≤ H),
      p ^ (s * H) * ∏ j : Fin r, ((p ^ (s * v (t j)))⁻¹ * f (t j)) =
      ∑ t ∈ T.filter (fun t => tupleDepth v t ≤ H),
        p ^ (s * (H - tupleDepth v t)) * ∏ j : Fin r, f (t j) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hle : tupleDepth v t ≤ H := (mem_filter.mp ht).2
    rw [hprod_eval t, ← mul_assoc]
    congr 1
    have hadd : s * H = s * (H - tupleDepth v t) + s * tupleDepth v t := by
      rw [← mul_add, Nat.sub_add_cancel hle]
    rw [hadd, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp), mul_one]
  have hhigh_filt : T.filter (fun t => ¬ tupleDepth v t ≤ H) =
      T.filter (fun t => H < tupleDepth v t) := by
    refine Finset.filter_congr (fun _ _ => not_le)
  have hhigh : ∑ t ∈ T.filter (fun t => ¬ tupleDepth v t ≤ H),
      p ^ (s * H) * ∏ j : Fin r, ((p ^ (s * v (t j)))⁻¹ * f (t j)) =
      ∑ t ∈ T.filter (fun t => H < tupleDepth v t),
        (p ^ (s * (tupleDepth v t - H)))⁻¹ * ∏ j : Fin r, f (t j) := by
    rw [hhigh_filt]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hlt : H < tupleDepth v t := (mem_filter.mp ht).2
    rw [hprod_eval t, ← mul_assoc]
    congr 1
    have hadd : s * tupleDepth v t = s * H + s * (tupleDepth v t - H) := by
      rw [← mul_add, Nat.add_sub_of_le hlt.le]
    rw [hadd, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp), one_mul]
  rw [hlow, hhigh]

/-- `zpow`-form corollary of `total_depth_split_sum` matching `p^(-s * v i)` notation directly. -/
theorem total_depth_split_sum_zpow {ι K : Type*} [Field K]
    (S : Finset ι) (v : ι → ℕ) (f : ι → K) {p : K} (hp : p ≠ 0) (s H r : ℕ) :
    p ^ (s * H) * (∑ i ∈ S, p ^ (-((s * v i : ℕ) : ℤ)) * f i) ^ r =
      (∑ t ∈ (Fintype.piFinset fun _ : Fin r => S).filter (fun t => tupleDepth v t ≤ H),
          p ^ (s * (H - tupleDepth v t)) * ∏ j : Fin r, f (t j)) +
      (∑ t ∈ (Fintype.piFinset fun _ : Fin r => S).filter (fun t => H < tupleDepth v t),
          p ^ (-((s * (tupleDepth v t - H) : ℕ) : ℤ)) * ∏ j : Fin r, f (t j)) := by
  have hz : ∀ n : ℕ, p ^ (-(n : ℤ)) = (p ^ n)⁻¹ := fun n => by
    rw [zpow_neg, zpow_natCast]
  simpa only [hz] using total_depth_split_sum S v f hp s H r

/-! ### Part 4: Track E1 — Exact arithmetic coefficient identity for `E_+(b)` -/

/-- Dirichlet coefficient of `E_+(b) = ∑_{n ≥ 1} 1 / (b^n + 1) = E(b) - 2 E(b^2)`. -/
def erdosBorweinPlusCoeff (n : ℕ) : ℤ :=
  (n.divisors.card : ℤ) - if 2 ∣ n then 2 * ((n / 2).divisors.card : ℤ) else 0

/-- For `n > 0` with `n = 2^e * m` (`m` odd), the odd divisors of `n` are precisely the divisors
of `m`. -/
private lemma divisors_filter_odd_eq_oddPart {n : ℕ} (hn : 0 < n) :
    n.divisors.filter Odd = (n / 2 ^ (n.factorization 2)).divisors := by
  set e : ℕ := n.factorization 2
  set m : ℕ := n / 2 ^ e
  have h2e_dvd : 2 ^ e ∣ n := Nat.ordProj_dvd n 2
  have hn_eq : 2 ^ e * m = n := Nat.mul_div_cancel' h2e_dvd
  have hm_ne : m ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hn_eq; omega
  have h2m : ¬ 2 ∣ m := by
    intro hdvd
    have h1 : 2 ^ (e + 1) ∣ n := by
      rw [← hn_eq, pow_succ]
      exact mul_dvd_mul_left (2 ^ e) hdvd
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp h1
    omega
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdn, _⟩, hd_odd⟩
    refine ⟨?_, hm_ne⟩
    have hd_ndvd : ¬ 2 ∣ d := by
      intro ⟨q, hq⟩
      rcases hd_odd with ⟨r, hr⟩; omega
    have hcop : Nat.Coprime d (2 ^ e) := (Nat.prime_two.coprime_iff_not_dvd.mpr hd_ndvd).symm.pow_right e
    rw [← hn_eq] at hdn
    exact hcop.dvd_of_dvd_mul_left hdn
  · rintro ⟨hdm, _⟩
    refine ⟨⟨?_, hn.ne'⟩, ?_⟩
    · rw [← hn_eq]; exact dvd_mul_of_dvd_right hdm (2 ^ e)
    · rw [← Nat.not_even_iff_odd]
      intro ⟨q, hq⟩
      exact h2m (dvd_trans ⟨q, by omega⟩ hdm)

/-- Exact factorization `τ(n) = (v₂(n) + 1) * τ_odd(n)` for `n > 0`. -/
theorem card_divisors_eq_succ_fac_two_mul_tauOdd {n : ℕ} (hn : 0 < n) :
    (n.divisors.card : ℤ) = ((n.factorization 2 : ℤ) + 1) * tauOdd n := by
  set e : ℕ := n.factorization 2
  set m : ℕ := n / 2 ^ e
  have h2e_dvd : 2 ^ e ∣ n := Nat.ordProj_dvd n 2
  have hn_eq : 2 ^ e * m = n := Nat.mul_div_cancel' h2e_dvd
  have h2m : ¬ 2 ∣ m := by
    intro hdvd
    have h1 : 2 ^ (e + 1) ∣ n := by
      rw [← hn_eq, pow_succ]
      exact mul_dvd_mul_left (2 ^ e) hdvd
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp h1
    omega
  have hcop : Nat.Coprime (2 ^ e) m := (Nat.prime_two.coprime_iff_not_dvd.mpr h2m).pow_left e
  have hconv : dirichletOneConv (fun _ => (1 : ℤ)) (2 ^ e * m) =
      dirichletOneConv (fun _ => (1 : ℤ)) (2 ^ e) * dirichletOneConv (fun _ => (1 : ℤ)) m :=
    dirichletOneConv_mul_of_coprime (fun _ _ _ => by simp) hcop
  have hcard_conv : ∀ x : ℕ, dirichletOneConv (fun _ => (1 : ℤ)) x = (x.divisors.card : ℤ) := by
    intro x; simp [dirichletOneConv]
  have hpow_card : ((2 ^ e).divisors.card : ℤ) = (e : ℤ) + 1 := by
    rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
    push_cast; rfl
  have htau : tauOdd n = (m.divisors.card : ℤ) := by
    unfold tauOdd
    rw [divisors_filter_odd_eq_oddPart hn]
  rw [htau, ← hn_eq, ← hcard_conv, hconv, hcard_conv, hcard_conv, hpow_card]

/-- **Proposition 1.1 (Track E1): exact coefficient formula for `E_+(b)`.**
For every `n ≥ 1`, `erdosBorweinPlusCoeff n = (1 - v₂(n)) * tauOdd n`. -/
theorem erdosBorweinPlusCoeff_eq {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n = (1 - (n.factorization 2 : ℤ)) * tauOdd n := by
  unfold erdosBorweinPlusCoeff
  rw [card_divisors_eq_succ_fac_two_mul_tauOdd hn]
  by_cases h2 : 2 ∣ n
  · simp only [h2, ↓reduceIte]
    have he1 : 1 ≤ n.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne' (k := 1)).mp (by simpa using h2)
    have hn2_pos : 0 < n / 2 := Nat.div_pos (Nat.le_of_dvd hn h2) (by norm_num)
    have hfac2 : (n / 2).factorization 2 = n.factorization 2 - 1 := by
      have hmul : 2 * (n / 2) = n := Nat.mul_div_cancel' h2
      have := congrArg (fun x : ℕ => x.factorization 2) hmul
      rw [Nat.factorization_mul (by norm_num) hn2_pos.ne', Finsupp.add_apply,
        Nat.prime_two.factorization_self] at this
      omega
    have htau2 : tauOdd (n / 2) = tauOdd n := by
      unfold tauOdd
      rw [divisors_filter_odd_eq_oddPart hn2_pos, divisors_filter_odd_eq_oddPart hn, hfac2]
      congr 2
      have hpow : 2 ^ (n.factorization 2) = 2 * 2 ^ (n.factorization 2 - 1) := by
        conv_lhs => rw [show n.factorization 2 = (n.factorization 2 - 1) + 1 by omega, pow_succ, mul_comm]
      rw [hpow, ← Nat.div_div_eq_div_mul]
    rw [card_divisors_eq_succ_fac_two_mul_tauOdd hn2_pos, hfac2, htau2]
    have hcast : ((n.factorization 2 - 1 : ℕ) : ℤ) = (n.factorization 2 : ℤ) - 1 := by omega
    rw [hcast]
    ring
  · simp only [h2, ↓reduceIte, sub_zero, Nat.factorization_eq_zero_of_not_dvd h2]
    simp

/-- Alternating divisor-sum representation: for `n ≥ 1`,
`erdosBorweinPlusCoeff n = ∑_{d ∣ n} (-1)^(d - 1)`. -/
theorem erdosBorweinPlusCoeff_eq_altDivisorSum {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n = dirichletOneConv (fun d => (-1 : ℤ) ^ (d - 1)) n := by
  unfold dirichletOneConv
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors Odd]
  have hodd_sum : ∑ d ∈ n.divisors.filter Odd, (-1 : ℤ) ^ (d - 1) = tauOdd n := by
    have hconst : ∀ d ∈ n.divisors.filter Odd, (-1 : ℤ) ^ (d - 1) = 1 := by
      intro d hd
      rcases (mem_filter.mp hd).2 with ⟨m, rfl⟩
      rw [show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]; norm_num
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  have heven_card : ((n.divisors.filter (fun d => ¬ Odd d)).card : ℤ) =
      if 2 ∣ n then ((n / 2).divisors.card : ℤ) else 0 := by
    by_cases h2 : 2 ∣ n
    · simp only [h2, ↓reduceIte]
      have hn2_ne : n / 2 ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn h2) (by norm_num)).ne'
      have hcard : (n.divisors.filter (fun d => ¬ Odd d)).card = (n / 2).divisors.card := by
        refine Finset.card_bij (fun d _ => d / 2) ?_ ?_ ?_
        · intro d hd
          obtain ⟨hdn, hnot⟩ := mem_filter.mp hd
          obtain ⟨hd_dvd, _⟩ := Nat.mem_divisors.mp hdn
          rw [Nat.not_odd_iff_even] at hnot
          have h2d : 2 ∣ d := even_iff_two_dvd.mp hnot
          refine Nat.mem_divisors.mpr ⟨?_, hn2_ne⟩
          exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
            (by rw [Nat.mul_div_cancel' h2d, Nat.mul_div_cancel' h2]; exact hd_dvd)
        · intro d₁ hd₁ d₂ hd₂ heq
          have h2₁ : 2 ∣ d₁ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (mem_filter.mp hd₁).2)
          have h2₂ : 2 ∣ d₂ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (mem_filter.mp hd₂).2)
          omega
        · intro k hk
          obtain ⟨hk_dvd, _⟩ := Nat.mem_divisors.mp hk
          refine ⟨2 * k, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn.ne'⟩, ?_⟩, by omega⟩
          · have := mul_dvd_mul_left 2 hk_dvd
            rwa [Nat.mul_div_cancel' h2] at this
          · rw [Nat.not_odd_iff_even]; exact ⟨k, by omega⟩
      exact_mod_cast hcard
    · simp only [h2, ↓reduceIte]
      have hempty : n.divisors.filter (fun d => ¬ Odd d) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d hd hnot
        have h2d : 2 ∣ d := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
        exact h2 (h2d.trans (Nat.mem_divisors.mp hd).1)
      rw [hempty, Finset.card_empty, Nat.cast_zero]
  have heven_sum : ∑ d ∈ n.divisors.filter (fun d => ¬ Odd d), (-1 : ℤ) ^ (d - 1) =
      -(if 2 ∣ n then ((n / 2).divisors.card : ℤ) else 0) := by
    have hconst : ∀ d ∈ n.divisors.filter (fun d => ¬ Odd d), (-1 : ℤ) ^ (d - 1) = -1 := by
      intro d hd
      obtain ⟨hdn, hnot⟩ := mem_filter.mp hd
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdn).1 hn
      rw [Nat.not_odd_iff_even] at hnot
      rcases hnot with ⟨m, rfl⟩
      have hm1 : 1 ≤ m := by omega
      rw [show m + m - 1 = 2 * (m - 1) + 1 by omega, pow_succ, pow_mul]; norm_num
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_neg_one, heven_card]
  rw [hodd_sum, heven_sum]
  have htotal : (n.divisors.card : ℤ) =
      tauOdd n + if 2 ∣ n then ((n / 2).divisors.card : ℤ) else 0 := by
    have hcard_split : n.divisors.card =
        (n.divisors.filter Odd).card + (n.divisors.filter (fun d => ¬ Odd d)).card :=
      (Finset.card_filter_add_card_filter_not Odd).symm
    unfold tauOdd
    omega
  unfold erdosBorweinPlusCoeff
  split_ifs at htotal ⊢ <;> linarith

private lemma tauOdd_pos {n : ℕ} (hn : 0 < n) : 0 < tauOdd n := by
  unfold tauOdd
  have h1 : 1 ∈ n.divisors.filter Odd :=
    mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩, odd_one⟩
  exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩

/-- Exact positivity criterion for `a_+(n)`: for `n ≥ 1`, `0 < a_+(n) ↔ Odd n`. -/
theorem erdosBorweinPlusCoeff_pos_iff {n : ℕ} (hn : 0 < n) :
    0 < erdosBorweinPlusCoeff n ↔ Odd n := by
  rw [erdosBorweinPlusCoeff_eq hn]
  have htau : 0 < tauOdd n := tauOdd_pos hn
  constructor
  · intro hpos
    have h1 : 0 < 1 - (n.factorization 2 : ℤ) := pos_of_mul_pos_left hpos htau.le
    have he0 : n.factorization 2 = 0 := by omega
    rw [← Nat.not_even_iff_odd]
    intro hev
    have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne' (k := 1)).mp (by simpa using h2)
    omega
  · intro hodd
    have h2 : ¬ 2 ∣ n := by
      intro ⟨q, hq⟩; rcases hodd with ⟨m, hm⟩; omega
    rw [Nat.factorization_eq_zero_of_not_dvd h2]
    simpa using htau

/-- **Proposition 1.1 vanishing criterion (Track E1):**
For every `n ≥ 1`, `erdosBorweinPlusCoeff n = 0 ↔ n % 4 = 2`. -/
theorem erdosBorweinPlusCoeff_eq_zero_iff {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n = 0 ↔ n % 4 = 2 := by
  rw [erdosBorweinPlusCoeff_eq hn]
  have htau : tauOdd n ≠ 0 := (tauOdd_pos hn).ne'
  rw [mul_eq_zero, or_iff_left htau, sub_eq_zero]
  have hfac1 : (1 : ℤ) = (n.factorization 2 : ℤ) ↔ n.factorization 2 = 1 := by omega
  rw [hfac1]
  have h2_iff : 2 ∣ n ↔ 1 ≤ n.factorization 2 := by
    simpa using (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne' (k := 1))
  have h4_iff : 4 ∣ n ↔ 2 ≤ n.factorization 2 := by
    simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using
      (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne' (k := 2))
  constructor
  · intro h1
    have h2 : 2 ∣ n := h2_iff.mpr (by omega)
    have h4 : ¬ 4 ∣ n := fun h => by have := h4_iff.mp h; omega
    omega
  · intro hmod
    have h2 : 2 ∣ n := by omega
    have h4 : ¬ 4 ∣ n := by omega
    have hge := h2_iff.mp h2
    have hlt : ¬ 2 ≤ n.factorization 2 := fun h => h4 (h4_iff.mpr h)
    omega

/-- Exact negativity criterion for `a_+(n)`: for `n ≥ 1`, `a_+(n) < 0 ↔ 4 ∣ n`. -/
theorem erdosBorweinPlusCoeff_neg_iff {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n < 0 ↔ 4 ∣ n := by
  rw [erdosBorweinPlusCoeff_eq hn]
  have htau : 0 < tauOdd n := tauOdd_pos hn
  have h4_iff : 4 ∣ n ↔ 2 ≤ n.factorization 2 := by
    simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using
      (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne' (k := 2))
  rw [h4_iff]
  constructor
  · intro hneg
    have h1 : 1 - (n.factorization 2 : ℤ) < 0 := neg_of_mul_neg_left hneg htau.le
    omega
  · intro h2
    have h1 : 1 - (n.factorization 2 : ℤ) < 0 := by omega
    exact mul_neg_of_neg_of_pos h1 htau

/-- Classical parity of the divisor count: for `n > 0`, `Odd n.divisors.card ↔ IsSquare n`. -/
private theorem odd_card_divisors_iff_isSquare {n : ℕ} (hn : 0 < n) :
    Odd n.divisors.card ↔ IsSquare n := by
  have hsplit : n.divisors.card =
      (n.divisors.filter fun d => d * d = n).card +
        (n.divisors.filter fun d => d * d ≠ n).card :=
    (Finset.card_filter_add_card_filter_not (fun d => d * d = n)).symm
  -- Off-diagonal divisors pair via `d ↦ n / d`, so their count is even.
  have hoff_even : Even (n.divisors.filter fun d => d * d ≠ n).card := by
    let S_lt := n.divisors.filter fun d => d < n / d
    let S_gt := n.divisors.filter fun d => n / d < d
    have hunion : (n.divisors.filter fun d => d * d ≠ n) = S_lt ∪ S_gt := by
      ext d
      simp only [S_lt, S_gt, mem_filter, mem_union, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdn, hn0⟩, hne⟩
        have hdm : d * (n / d) = n := Nat.mul_div_cancel' hdn
        rcases lt_trichotomy d (n / d) with hlt | heq | hgt
        · left; exact ⟨⟨hdn, hn0⟩, hlt⟩
        · exfalso; apply hne; rw [← heq] at hdm; exact hdm
        · right; exact ⟨⟨hdn, hn0⟩, hgt⟩
      · rintro (⟨⟨hdn, hn0⟩, hlt⟩ | ⟨⟨hdn, hn0⟩, hgt⟩)
        · refine ⟨⟨hdn, hn0⟩, fun hsq => ?_⟩
          have hdm : d * (n / d) = n := Nat.mul_div_cancel' hdn
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
          have : d = n / d := Nat.eq_of_mul_eq_mul_left hd_pos (by linarith)
          omega
        · refine ⟨⟨hdn, hn0⟩, fun hsq => ?_⟩
          have hdm : d * (n / d) = n := Nat.mul_div_cancel' hdn
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
          have : d = n / d := Nat.eq_of_mul_eq_mul_left hd_pos (by linarith)
          omega
    have hdisj : Disjoint S_lt S_gt := by
      rw [Finset.disjoint_left]
      intro d h1 h2
      have := (mem_filter.mp h1).2
      have := (mem_filter.mp h2).2
      omega
    have hcard_eq : S_lt.card = S_gt.card := by
      refine Finset.card_bij (fun d _ => n / d) ?_ ?_ ?_
      · intro d hd
        obtain ⟨hdn, hlt⟩ := mem_filter.mp hd
        obtain ⟨hd_dvd, _⟩ := Nat.mem_divisors.mp hdn
        have hdiv_dvd : n / d ∣ n := Nat.div_dvd_of_dvd hd_dvd
        have hdiv_div : n / (n / d) = d := Nat.div_div_self hd_dvd hn.ne'
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv_dvd, hn.ne'⟩, by rw [hdiv_div]; exact hlt⟩
      · intro d₁ hd₁ d₂ hd₂ heq
        have hd₁_dvd := (Nat.mem_divisors.mp (mem_filter.mp hd₁).1).1
        have hd₂_dvd := (Nat.mem_divisors.mp (mem_filter.mp hd₂).1).1
        have h1 := Nat.div_div_self hd₁_dvd hn.ne'
        have h2 := Nat.div_div_self hd₂_dvd hn.ne'
        rw [← h1, ← h2, heq]
      · intro q hq
        obtain ⟨hqn, hgt⟩ := mem_filter.mp hq
        obtain ⟨hq_dvd, _⟩ := Nat.mem_divisors.mp hqn
        have hdiv_dvd : n / q ∣ n := Nat.div_dvd_of_dvd hq_dvd
        have hdiv_div : n / (n / q) = q := Nat.div_div_self hq_dvd hn.ne'
        refine ⟨n / q, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv_dvd, hn.ne'⟩, ?_⟩, hdiv_div⟩
        rw [hdiv_div]; exact hgt
    rw [hunion, Finset.card_union_of_disjoint hdisj, hcard_eq]
    exact ⟨S_gt.card, rfl⟩
  -- The diagonal filter has size `1` if `IsSquare n` and `0` otherwise.
  have hdiag : (n.divisors.filter fun d => d * d = n).card = if IsSquare n then 1 else 0 := by
    by_cases hsq : IsSquare n
    · simp only [hsq, ↓reduceIte]
      rcases hsq with ⟨r, hr⟩
      have hset : (n.divisors.filter fun d => d * d = n) = {r} := by
        ext d
        simp only [mem_filter, Nat.mem_divisors, mem_singleton]
        constructor
        · rintro ⟨_, hdd⟩
          nlinarith
        · rintro rfl
          exact ⟨⟨⟨d, hr⟩, hn.ne'⟩, hr.symm⟩
      rw [hset, Finset.card_singleton]
    · simp only [hsq, ↓reduceIte]
      have hempty : (n.divisors.filter fun d => d * d = n) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d _ hdd
        exact hsq ⟨d, hdd.symm⟩
      rw [hempty, Finset.card_empty]
  rw [hsplit, hdiag]
  rcases hoff_even with ⟨k, hk⟩
  rw [hk]
  by_cases hsq : IsSquare n
  · simp only [hsq, ↓reduceIte, iff_true]
    exact ⟨k, by omega⟩
  · simp only [hsq, ↓reduceIte, zero_add, iff_false]
    intro ⟨m, hm⟩; omega

/-- **Proposition 1.1 parity criterion (Track E1):**
For every `n ≥ 1`, `Odd (erdosBorweinPlusCoeff n) ↔ IsSquare n`. -/
theorem erdosBorweinPlusCoeff_odd_iff {n : ℕ} (hn : 0 < n) :
    Odd (erdosBorweinPlusCoeff n) ↔ IsSquare n := by
  rw [← odd_card_divisors_iff_isSquare hn]
  unfold erdosBorweinPlusCoeff
  constructor
  · rintro ⟨k, hk⟩
    by_cases h2 : 2 ∣ n
    · simp only [h2, ↓reduceIte] at hk
      have hcard : (n.divisors.card : ℤ) = 2 * (k + ((n / 2).divisors.card : ℤ)) + 1 := by linarith
      refine ⟨(k + ((n / 2).divisors.card : ℤ)).toNat, ?_⟩
      omega
    · simp only [h2, ↓reduceIte, sub_zero] at hk
      refine ⟨k.toNat, ?_⟩
      omega
  · rintro ⟨k, hk⟩
    by_cases h2 : 2 ∣ n
    · simp only [h2, ↓reduceIte]
      refine ⟨(k : ℤ) - ((n / 2).divisors.card : ℤ), ?_⟩
      have hcz : (n.divisors.card : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
      linarith
    · simp only [h2, ↓reduceIte, sub_zero]
      refine ⟨(k : ℤ), ?_⟩
      exact_mod_cast hk

/-- Exact termwise algebraic identity `1 / (x + 1) = 1 / (x - 1) - 2 / (x^2 - 1)` for `1 < x`. -/
theorem erdosBorweinPlus_term_identity {x : ℝ} (hx : 1 < x) :
    (1 : ℝ) / (x + 1) = 1 / (x - 1) - 2 / (x ^ 2 - 1) := by
  have h1 : x + 1 ≠ 0 := by linarith
  have h2 : x - 1 ≠ 0 := by linarith
  have h3 : x ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp [h1, h2, h3]
  ring

/-- **Proposition 1.1 series identity (Track E1):**
For every integer base `b ≥ 2`, `E_+(b) = E(b) - 2 E(b^2)`. -/
theorem erdosBorweinPlus_eq_sub {b : ℕ} (hb : 2 ≤ b) :
    (∑' n : ℕ, (1 : ℝ) / ((b : ℝ) ^ (n + 1) + 1)) =
      (∑' n : ℕ, (1 : ℝ) / ((b : ℝ) ^ (n + 1) - 1)) -
        2 * (∑' n : ℕ, (1 : ℝ) / (((b ^ 2 : ℕ) : ℝ) ^ (n + 1) - 1)) := by
  have hsum_lambert : ∀ {c : ℕ}, 2 ≤ c →
      Summable (fun n : ℕ => (1 : ℝ) / ((c : ℝ) ^ (n + 1) - 1)) := by
    intro c hc
    have hc1 : (1 : ℝ) < (c : ℝ) := by exact_mod_cast (show 1 < c by omega)
    have hgeom : Summable (fun n : ℕ => 2 * ((c : ℝ)⁻¹) ^ (n + 1)) :=
      ((summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hc1)).comp_injective
        Nat.succ_injective).mul_left 2
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
    · have hpow : (1 : ℝ) < (c : ℝ) ^ (n + 1) := one_lt_pow₀ hc1 (Nat.succ_ne_zero n)
      positivity
    · have hpow2 : (2 : ℝ) ≤ (c : ℝ) ^ (n + 1) := by
        have hc2 : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
          _ ≤ (c : ℝ) ^ 1 := pow_le_pow_left₀ (by norm_num) hc2 1
          _ ≤ (c : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (Nat.succ_le_succ (Nat.zero_le n))
      have hden_pos : (0 : ℝ) < (c : ℝ) ^ (n + 1) - 1 := by linarith
      have hc_pow_pos : (0 : ℝ) < (c : ℝ) ^ (n + 1) := by linarith
      rw [inv_pow, div_le_iff₀ hden_pos]
      have hmul : (2 : ℝ) * ((c : ℝ) ^ (n + 1))⁻¹ * ((c : ℝ) ^ (n + 1) - 1) =
          2 - 2 / (c : ℝ) ^ (n + 1) := by
        field_simp [hc_pow_pos.ne']
      have hinv_le : (2 : ℝ) / (c : ℝ) ^ (n + 1) ≤ 1 := by
        rw [div_le_one hc_pow_pos]; exact hpow2
      linarith
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((b : ℝ) ^ (n + 1) - 1)) := hsum_lambert hb
  have h2 : Summable (fun n : ℕ => 2 * ((1 : ℝ) / (((b ^ 2 : ℕ) : ℝ) ^ (n + 1) - 1))) :=
    (hsum_lambert (show 2 ≤ b ^ 2 by nlinarith)).mul_left 2
  rw [← tsum_mul_left, ← h1.tsum_sub h2]
  refine tsum_congr (fun n => ?_)
  have hpow_gt : (1 : ℝ) < (b : ℝ) ^ (n + 1) :=
    one_lt_pow₀ (by exact_mod_cast (show 1 < b by omega)) (Nat.succ_ne_zero n)
  have hsq : (((b ^ 2 : ℕ) : ℝ) ^ (n + 1)) = ((b : ℝ) ^ (n + 1)) ^ 2 := by
    push_cast
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hsq, erdosBorweinPlus_term_identity hpow_gt]
  ring

end NormalityChecker.Phase22Cores
