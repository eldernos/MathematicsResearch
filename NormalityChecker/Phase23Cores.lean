module

public import NormalityChecker.Phase22Cores
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! # Phase 23 finite algebraic, combinatorial, and arithmetic cores (Tracks A3, B1, B3+D3, C4, E)

Kernel-checked self-contained algebraic and finite core theorems supporting Phase 23
(`notes/phase23/nonlinear-multivariate-and-denser-mu.md`,
`notes/phase23/dense-characters-and-nonfundamental-forms.md`,
`notes/phase23/binary-partition-and-carry-complexity.md`,
`notes/phase23/classical-correlations-and-log2.md`,
and `notes/phase23/rational-scalings-and-signed-special.md`):

1. **Track C4 — Rational determinant folding core (`B(u)` & Lemma 5):**
   - `ratBadness`: `B(u) = inf_{l ≥ 1, h/l ≠ u} l² |u - h/l|`.
   - `ratDet_lower_of_approx`: integer determinant form `B ≤ |l| · |L| / q` for `q ∣ a l - L`.
   - `inv_le_ratBadness`, `ratBadness_pos`, `ratBadness_le_one`: `1 / q ≤ B(a/q) ≤ 1`.
   - `rat_det_folding_step`, `ratBadness_folding_step` (Lemma 5): for `v = a/q + (c/d)/q²`
     with `gcd(a, q) = 1` and `c ≠ 0`, `min (|c|/d) (B / (2 c²)) ≤ l² |v - h/l|` and
     `min (|c|/d) (B(a/q) / (2 c²)) ≤ B(v)`.

2. **Track B1 — Cubic digit-cylinder identity & split-prime local-factor bound:**
   - `sum_digit_cylinder_min_even_nat`, `sum_digit_cylinder_min_even`: for even `b = 2m`,
     `4 ∑_{d < 2m} min(d, 2m - 1 - d) = (2m)(2m - 2)` and
     `∑_{d < 2m} min(d, 2m - 1 - d) / (2m)² = 1/4 - 1/(2 · 2m)`.
   - `split_prime_local_factor_eq`, `split_prime_local_factor_le`: for `p ≥ 2` and `x = 1/p`,
     `(1 - x)(1 + x) + x²(3 - 2x)/(1 - x) = 1 + (2p - 1)/(p²(p - 1)) ≤ 1 + 3/p²`.

3. **Track D3 — Mahler binary partitions & signed Thue–Morse product identity:**
   - `binPart`: binary partition sequence `β(0) = 1`, `β(2n) = β(2n - 1) + β(n)`,
     `β(2n + 1) = β(2n)`.
   - `binPart_two_mul`, `binPart_even`: `β(2n) = ∑_{j ≤ n} β(j)` and `Even (β(n))` for `n ≥ 2`.
   - `binPart_mahler_finite`: exact finite Mahler functional equation
     `(b - 1) ∑_{n ≤ M} β(n) b^(M - n) = b ∑_{k ≤ M/2} β(k) b^(M - 2k) - β(M)`.
   - `thueMorseSign`, `prod_one_sub_pow_two_pow` (Theorem 3.1, `m = 2`):
     `∏_{j < r} (1 - q^(2^j)) = ∑_{n < 2^r} thueMorseSign(n) q^n` in every commutative ring.

4. **Track B3 — Carry-cancellation gauge identity & kernel characterization:**
   - `radix_coboundary_sum_int`, `carry_gauge_telescoping`, `carry_gauge_telescoping_shift`
     (Lemma 5.1 & Theorem 5.2): finite telescoping gauge identities in integer and real forms.
   - `carry_kernel_iff`, `carry_kernel_eq_zero_of_tendsto`, `carry_kernel_shift_iff`,
     `carry_kernel_shift_eq_zero_of_tendsto`: exact carry-kernel characterization and vanishing
     under `δ_m / b^m → 0`.
   - `carry_zero_transition` (Theorem 5.5(b)): exact three-state cost-free carry transitions.

5. **Track E — Arithmetic correlations and 2-adic peeling of `E_+` (`erdosBorweinPlusCoeff`):**
   - `erdosBorweinPlusCoeff_mul_add_odd_nonpos` (Theorem 2.2(1)): `a_+(n) a_+(n + h) ≤ 0` for
     every `n ≥ 1` and odd `h`.
   - `erdosBorweinPlusCoeff_four_consec_eq_zero` (§2.3):
     `a_+(n) a_+(n + 1) a_+(n + 2) a_+(n + 3) = 0` for every `n ≥ 1`.
   - `erdosBorweinPlusCoeff_emod_two`, `erdosBorweinPlusCoeff_peel_one`,
     `floor_half_tau_sub_floor_half_plus` (Theorem 1.5, `j = 1` peeling):
     `a_+(n) = [IsSquare n] + 2 (a_+(n) / 2)`.

6. **Track A3 & E2 — Derivative divisibility (`3 ∣ D^j E^3`) & `ln 2` Glaisher–Wieferich law:**
   - `three_dvd_triNum_pow_mul_odd` (Track A3 §6): `3 ∣ (k(k + 1)/2)^j (2k + 1)` for `j ≥ 1`.
   - `ln2Prefix`, `glaisher_wieferich_zmod`, `glaisher_wieferich_alt_zmod`,
     `glaisher_wieferich_zero_iff`, `ln2Prefix_num_dvd_iff_wieferich` (Track E2 Prop. 5.4):
     for odd prime `p`, `∑_{k=1}^{p-1} 2^(p-1-k) k⁻¹ = ((2^(p-1) - 1) / p)` in `ZMod p`, and
     `p ∣ A_{p-1} ↔ p² ∣ 2^(p-1) - 1`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.Phase23Cores

open Phase22Cores

/-! ### Section 1: Track C4 — Rational Determinant Folding Core (`B(u)` & Lemma 5) -/

/-- The Diophantine badness quantity `B(u) = inf_{l ≥ 1, h/l ≠ u} l² |u - h/l|`. -/
noncomputable def ratBadness (u : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ (l : ℕ) (h : ℤ), 1 ≤ l ∧ (h : ℝ) / l ≠ u ∧
    x = (l : ℝ) ^ 2 * |u - (h : ℝ) / l|}

/-- Integer determinant form of a lower bound `B` on `l² |a/q - h/l|`:
for any nonzero integers `l, L` with `q ∣ a * l - L`, we have `B ≤ |l| * |L| / q`. -/
theorem ratDet_lower_of_approx {a : ℤ} {q : ℕ} (hq : 1 ≤ q) {B : ℝ}
    (hB : ∀ l : ℕ, 1 ≤ l → ∀ h : ℤ, (h : ℝ) / l ≠ (a : ℝ) / q →
      B ≤ (l : ℝ) ^ 2 * |(a : ℝ) / q - (h : ℝ) / l|)
    {l L : ℤ} (hl : l ≠ 0) (hL : L ≠ 0) (hdiv : (q : ℤ) ∣ a * l - L) :
    B ≤ |(l : ℝ)| * |(L : ℝ)| / (q : ℝ) := by
  rcases hdiv with ⟨h, hh⟩
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  let s : ℤ := if 0 < l then 1 else -1
  have hs_abs : |(s : ℝ)| = 1 := by
    dsimp only [s]; split_ifs <;> norm_num
  set n : ℕ := l.natAbs with hn_def
  have hl_nat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hl)
  have hl_eq : (n : ℤ) = s * l := by
    dsimp only [s, n]
    split_ifs with hpos
    · simp [Int.natAbs_of_nonneg hpos.le]
    · have hneg : l ≤ 0 := by omega
      have h1 : ((l.natAbs : ℕ) : ℤ) = -l := by
        simpa using Int.ofNat_natAbs_of_nonpos hneg
      omega
  have hl'_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let h' : ℤ := s * h
  have hdet : a * (n : ℤ) - (q : ℤ) * h' = s * L := by
    dsimp only [h']
    rw [hl_eq]
    have hmul : a * (s * l) - (q : ℤ) * (s * h) = s * (a * l - (q : ℤ) * h) := by ring
    rw [hmul]
    have hL' : a * l - (q : ℤ) * h = L := by linarith
    rw [hL']
  have hdet_ne : a * (n : ℤ) - (q : ℤ) * h' ≠ 0 := by
    rw [hdet]
    refine mul_ne_zero ?_ hL
    dsimp only [s]; split_ifs <;> omega
  have hne : (h' : ℝ) / (n : ℝ) ≠ (a : ℝ) / (q : ℝ) := by
    intro heq
    apply hdet_ne
    have hR : ((a * (n : ℤ) - (q : ℤ) * h' : ℤ) : ℝ) = 0 := by
      push_cast
      have h1 : (h' : ℝ) * (q : ℝ) = (a : ℝ) * (n : ℝ) := by
        have := (div_eq_div_iff hl'_pos.ne' hq_pos.ne').mp heq
        linarith
      linarith
    exact_mod_cast hR
  have hbound := hB n hl_nat h' hne
  have hrewrite : (n : ℝ) ^ 2 * |(a : ℝ) / q - (h' : ℝ) / (n : ℝ)| =
      |(l : ℝ)| * |(L : ℝ)| / (q : ℝ) := by
    have hsub : (a : ℝ) / q - (h' : ℝ) / (n : ℝ) =
        ((a * (n : ℤ) - (q : ℤ) * h' : ℤ) : ℝ) / ((q : ℝ) * (n : ℝ)) := by
      push_cast
      field_simp [hq_pos.ne', hl'_pos.ne']
    rw [hsub, hdet, abs_div, abs_mul, abs_of_pos hq_pos, abs_of_pos hl'_pos]
    have hcast : ((s * L : ℤ) : ℝ) = (s : ℝ) * (L : ℝ) := by push_cast; rfl
    rw [hcast, abs_mul, hs_abs, one_mul]
    have hl_abs : (n : ℝ) = |(l : ℝ)| := by
      have h1 : (n : ℝ) = (s : ℝ) * (l : ℝ) := by exact_mod_cast hl_eq
      calc (n : ℝ) = |(n : ℝ)| := (abs_of_pos hl'_pos).symm
        _ = |(s : ℝ) * (l : ℝ)| := by rw [h1]
        _ = |(s : ℝ)| * |(l : ℝ)| := abs_mul _ _
        _ = |(l : ℝ)| := by rw [hs_abs, one_mul]
    rw [hl_abs]
    have hlab_ne : |(l : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hl)
    field_simp [hq_pos.ne', hlab_ne]
  rwa [hrewrite] at hbound

/-- For every rational `a / q` (`q ≥ 1`), `1 / q ≤ ratBadness (a / q)`. -/
theorem inv_le_ratBadness {a : ℤ} {q : ℕ} (hq : 1 ≤ q) :
    (1 : ℝ) / q ≤ ratBadness ((a : ℝ) / q) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hne_set : {x : ℝ | ∃ (l : ℕ) (h : ℤ), 1 ≤ l ∧ (h : ℝ) / l ≠ (a : ℝ) / q ∧
      x = (l : ℝ) ^ 2 * |(a : ℝ) / q - (h : ℝ) / l|}.Nonempty := by
    by_cases h0 : ((0 : ℤ) : ℝ) / (1 : ℕ) = (a : ℝ) / q
    · refine ⟨(1 : ℕ) ^ 2 * |(a : ℝ) / q - ((1 : ℤ) : ℝ) / (1 : ℕ)|, 1, 1, le_rfl, ?_, rfl⟩
      rw [← h0]; norm_num
    · exact ⟨(1 : ℕ) ^ 2 * |(a : ℝ) / q - ((0 : ℤ) : ℝ) / (1 : ℕ)|, 1, 0, le_rfl, h0, rfl⟩
  refine le_csInf hne_set ?_
  rintro x ⟨l, h, hl, hne, rfl⟩
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hl_ge1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hdet_ne : a * (l : ℤ) - (q : ℤ) * h ≠ 0 := by
    intro h0
    apply hne
    have hR : (a : ℝ) * (l : ℝ) = (q : ℝ) * (h : ℝ) := by
      have : ((a * (l : ℤ) - (q : ℤ) * h : ℤ) : ℝ) = 0 := by exact_mod_cast h0
      push_cast at this; linarith
    rw [div_eq_div_iff hl_pos.ne' hq_pos.ne']
    linarith
  have hdet_abs : (1 : ℝ) ≤ |((a * (l : ℤ) - (q : ℤ) * h : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |a * (l : ℤ) - (q : ℤ) * h| := Int.one_le_abs hdet_ne
    exact_mod_cast this
  have hsub : (a : ℝ) / q - (h : ℝ) / l =
      ((a * (l : ℤ) - (q : ℤ) * h : ℤ) : ℝ) / ((q : ℝ) * (l : ℝ)) := by
    push_cast; field_simp [hq_pos.ne', hl_pos.ne']
  rw [hsub, abs_div, abs_mul, abs_of_pos hq_pos, abs_of_pos hl_pos]
  have heq : (l : ℝ) ^ 2 * (|((a * (l : ℤ) - (q : ℤ) * h : ℤ) : ℝ)| / ((q : ℝ) * (l : ℝ))) =
      ((l : ℝ) * |((a * (l : ℤ) - (q : ℤ) * h : ℤ) : ℝ)|) / (q : ℝ) := by
    field_simp [hq_pos.ne', hl_pos.ne']
  rw [heq]
  exact div_le_div_of_nonneg_right (by nlinarith) hq_pos.le

/-- Positivity of `ratBadness (a / q)` for `q ≥ 1`. -/
theorem ratBadness_pos {a : ℤ} {q : ℕ} (hq : 1 ≤ q) :
    0 < ratBadness ((a : ℝ) / q) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  exact lt_of_lt_of_le (by positivity) (inv_le_ratBadness hq)

/-- Universal upper bound `ratBadness u ≤ 1` for every real `u`. -/
theorem ratBadness_le_one (u : ℝ) :
    ratBadness u ≤ 1 := by
  let h : ℤ := ⌊u⌋ + 1
  have hle : ((⌊u⌋ : ℤ) : ℝ) ≤ u := Int.floor_le u
  have hlt : u < (h : ℝ) := by
    dsimp only [h]; push_cast; exact Int.lt_floor_add_one u
  have hge : (h : ℝ) - 1 ≤ u := by
    dsimp only [h]; push_cast; linarith
  have hne : (h : ℝ) / (1 : ℕ) ≠ u := by
    rw [Nat.cast_one, div_one]; linarith
  have hbdd : BddBelow {x : ℝ | ∃ (l : ℕ) (h : ℤ), 1 ≤ l ∧ (h : ℝ) / l ≠ u ∧
      x = (l : ℝ) ^ 2 * |u - (h : ℝ) / l|} :=
    ⟨0, by rintro x ⟨l, h, _, _, rfl⟩; positivity⟩
  have hmem : (1 : ℕ) ^ 2 * |u - (h : ℝ) / (1 : ℕ)| ∈
      {x : ℝ | ∃ (l : ℕ) (h : ℤ), 1 ≤ l ∧ (h : ℝ) / l ≠ u ∧
        x = (l : ℝ) ^ 2 * |u - (h : ℝ) / l|} :=
    ⟨1, h, le_rfl, hne, rfl⟩
  calc ratBadness u
      ≤ (1 : ℕ) ^ 2 * |u - (h : ℝ) / (1 : ℕ)| := csInf_le hbdd hmem
    _ = |u - (h : ℝ)| := by simp
    _ ≤ 1 := by rw [abs_le]; constructor <;> linarith

/-- **Track C4, Lemma 5 (rational determinant folding inequality):**
For reduced `u = a / q` (`q ≥ 1`, `gcd(a, q) = 1`), nonzero `z = c / d` (`d ≥ 1`, `c ≠ 0`),
and any `B > 0` satisfying `B ≤ l² |u - h/l|` for all `l ≥ 1` and `h/l ≠ u`, the perturbed
rational `v = a/q + (c/d)/q²` satisfies `min (|c|/d) (B / (2 c²)) ≤ l² |v - h/l|` for every
`l ≥ 1` and `h : ℤ` with `h/l ≠ v`. -/
theorem rat_det_folding_step {a : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    {c : ℤ} {d : ℕ} (hc : c ≠ 0) (hd : 1 ≤ d) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ l : ℕ, 1 ≤ l → ∀ h : ℤ, (h : ℝ) / l ≠ (a : ℝ) / q →
      B ≤ (l : ℝ) ^ 2 * |(a : ℝ) / q - (h : ℝ) / l|)
    {l : ℕ} (hl : 1 ≤ l) {h : ℤ}
    (hne : (h : ℝ) / l ≠ (a : ℝ) / q + ((c : ℝ) / d) / (q : ℝ) ^ 2) :
    min (|(c : ℝ)| / d) (B / (2 * (c : ℝ) ^ 2)) ≤
      (l : ℝ) ^ 2 * |((a : ℝ) / q + ((c : ℝ) / d) / (q : ℝ) ^ 2) - (h : ℝ) / l| := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hc_ne : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  set z : ℝ := (c : ℝ) / d
  have hz_ne : z ≠ 0 := div_ne_zero hc_ne hd_pos.ne'
  have hz_abs : |z| = |(c : ℝ)| / d := by
    dsimp only [z]; rw [abs_div, abs_of_pos hd_pos]
  set w : ℝ := (l : ℝ) / q
  have hw_pos : 0 < w := div_pos hl_pos hq_pos
  set L : ℤ := a * (l : ℤ) - (q : ℤ) * h
  have hLHS : (l : ℝ) ^ 2 * |((a : ℝ) / q + z / (q : ℝ) ^ 2) - (h : ℝ) / l| =
      w * |(L : ℝ) + z * w| := by
    have h1 : ((a : ℝ) / q + z / (q : ℝ) ^ 2) - (h : ℝ) / l =
        ((L : ℝ) + z * w) / ((q : ℝ) * (l : ℝ)) := by
      dsimp only [L, w]; push_cast
      field_simp [hq_pos.ne', hl_pos.ne']
      ring
    rw [h1, abs_div, abs_mul, abs_of_pos hq_pos, abs_of_pos hl_pos]
    dsimp only [w]
    field_simp [hq_pos.ne', hl_pos.ne']
  rw [hLHS]
  -- Case 1: L = 0 (so q ∣ l and w ≥ 1).
  by_cases hL0 : L = 0
  · have hq_dvd_int : (q : ℤ) ∣ a * (l : ℤ) := ⟨h, by dsimp only [L] at hL0; linarith⟩
    have hq_dvd_nat : q ∣ a.natAbs * l := by
      have h1 := Int.natAbs_dvd_natAbs.mpr hq_dvd_int
      simpa [Int.natAbs_mul] using h1
    have hcop_qa : Nat.Coprime q a.natAbs := (Nat.coprime_comm.mp hcop)
    have hq_dvd_l : q ∣ l := hcop_qa.dvd_of_dvd_mul_left hq_dvd_nat
    have hq_le_l : q ≤ l := Nat.le_of_dvd (by omega) hq_dvd_l
    have hw_ge1 : 1 ≤ w := (one_le_div hq_pos).mpr (by exact_mod_cast hq_le_l)
    have hw2_ge1 : 1 ≤ w * w := by nlinarith
    calc min (|(c : ℝ)| / d) (B / (2 * (c : ℝ) ^ 2))
        ≤ |(c : ℝ)| / d := min_le_left _ _
      _ = |z| := hz_abs.symm
      _ = |z| * 1 := (mul_one _).symm
      _ ≤ |z| * (w * w) := mul_le_mul_of_nonneg_left hw2_ge1 (abs_nonneg z)
      _ = w * |(L : ℝ) + z * w| := by
          rw [hL0, Int.cast_zero, zero_add, abs_mul, abs_of_pos hw_pos]; ring
  -- Case 2: L ≠ 0 and |L| ≥ 2 |z| w.
  by_cases hbig : 2 * |z| * w ≤ |(L : ℝ)|
  · have htri : |(L : ℝ)| / 2 ≤ |(L : ℝ) + z * w| := by
      have hrev := abs_sub_abs_le_abs_sub (L : ℝ) (-(z * w))
      rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos hw_pos] at hrev
      linarith
    have hdet := ratDet_lower_of_approx hq hB (by omega : (l : ℤ) ≠ 0) hL0 ⟨h, by dsimp only [L]; ring⟩
    have hdet' : B ≤ w * |(L : ℝ)| := by
      have hl_abs : |((l : ℤ) : ℝ)| = (l : ℝ) := by
        rw [Int.cast_natCast, abs_of_pos hl_pos]
      rw [hl_abs] at hdet
      dsimp only [w]
      have : (l : ℝ) * |(L : ℝ)| / (q : ℝ) = (l : ℝ) / (q : ℝ) * |(L : ℝ)| := by ring
      linarith
    have hc_sq_ge1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
      have h1 : (1 : ℤ) ≤ c ^ 2 := by
        have := Int.one_le_abs hc
        nlinarith [sq_abs c]
      exact_mod_cast h1
    calc min (|(c : ℝ)| / d) (B / (2 * (c : ℝ) ^ 2))
        ≤ B / (2 * (c : ℝ) ^ 2) := min_le_right _ _
      _ ≤ B / 2 := by
          exact div_le_div_of_nonneg_left hB0.le (by norm_num) (by linarith)
      _ ≤ (w * |(L : ℝ)|) / 2 := by linarith
      _ = w * (|(L : ℝ)| / 2) := by ring
      _ ≤ w * |(L : ℝ) + z * w| := mul_le_mul_of_nonneg_left htri hw_pos.le
  -- Case 3: 0 < |L| < 2 |z| w (determinant folding).
  · push Not at hbig
    have hsum_ne : (L : ℝ) + z * w ≠ 0 := by
      intro h0
      apply hne
      have h1 : ((a : ℝ) / q + z / (q : ℝ) ^ 2) - (h : ℝ) / l = 0 := by
        have hsub : ((a : ℝ) / q + z / (q : ℝ) ^ 2) - (h : ℝ) / l =
            ((L : ℝ) + z * w) / ((q : ℝ) * (l : ℝ)) := by
          dsimp only [L, w]; push_cast
          field_simp [hq_pos.ne', hl_pos.ne']
          ring
        rw [hsub, h0, zero_div]
      linarith
    let N_int : ℤ := c * (l : ℤ) + (q : ℤ) * (d : ℤ) * L
    let M_int : ℤ := c * L
    have hN_cast : (N_int : ℝ) = (q : ℝ) * (c : ℝ) * (w + (L : ℝ) / z) := by
      dsimp only [N_int, w, z]; push_cast
      field_simp [hq_pos.ne', hc_ne, hd_pos.ne']
    have hwLz_ne : w + (L : ℝ) / z ≠ 0 := by
      intro h0
      apply hsum_ne
      have : (L : ℝ) + z * w = z * (w + (L : ℝ) / z) := by field_simp [hz_ne]; ring
      rw [this, h0, mul_zero]
    have hN_ne : N_int ≠ 0 := by
      intro h0
      have hR : (N_int : ℝ) = 0 := by exact_mod_cast h0
      rw [hN_cast] at hR
      exact mul_ne_zero (mul_ne_zero hq_pos.ne' hc_ne) hwLz_ne hR
    have hM_ne : M_int ≠ 0 := mul_ne_zero hc hL0
    have hdiv : (q : ℤ) ∣ a * N_int - M_int := by
      refine ⟨c * h + a * (d : ℤ) * L, ?_⟩
      dsimp only [N_int, M_int]
      have hL_def : a * (l : ℤ) - L = (q : ℤ) * h := by dsimp only [L]; ring
      linear_combination c * hL_def
    have hfold := ratDet_lower_of_approx hq hB hN_ne hM_ne hdiv
    have hfold_simp : |(N_int : ℝ)| * |(M_int : ℝ)| / (q : ℝ) =
        (c : ℝ) ^ 2 * |(L : ℝ)| * |w + (L : ℝ) / z| := by
      rw [hN_cast]
      have hM_cast : (M_int : ℝ) = (c : ℝ) * (L : ℝ) := by dsimp only [M_int]; push_cast; rfl
      rw [hM_cast, abs_mul, abs_mul, abs_mul, abs_of_pos hq_pos]
      have hcsq : |(c : ℝ)| * |(c : ℝ)| = (c : ℝ) ^ 2 := by
        rw [← sq, sq_abs]
      calc (q : ℝ) * |(c : ℝ)| * |w + (L : ℝ) / z| * (|(c : ℝ)| * |(L : ℝ)|) / (q : ℝ)
          = (q : ℝ) * ((|(c : ℝ)| * |(c : ℝ)|) * |(L : ℝ)| * |w + (L : ℝ) / z|) / (q : ℝ) := by
              ring
        _ = (|(c : ℝ)| * |(c : ℝ)|) * |(L : ℝ)| * |w + (L : ℝ) / z| :=
              mul_div_cancel_left₀ _ hq_pos.ne'
        _ = (c : ℝ) ^ 2 * |(L : ℝ)| * |w + (L : ℝ) / z| := by rw [hcsq]
    rw [hfold_simp] at hfold
    have h2c_pos : 0 < 2 * (c : ℝ) ^ 2 := by positivity
    have hstep : B ≤ 2 * (c : ℝ) ^ 2 * (w * |(L : ℝ) + z * w|) := by
      have hzw : |z| * |w + (L : ℝ) / z| = |(L : ℝ) + z * w| := by
        rw [← abs_mul]
        congr 1
        field_simp [hz_ne]
        ring
      calc B ≤ (c : ℝ) ^ 2 * |(L : ℝ)| * |w + (L : ℝ) / z| := hfold
        _ ≤ (c : ℝ) ^ 2 * (2 * |z| * w) * |w + (L : ℝ) / z| := by
            have hnn : 0 ≤ (c : ℝ) ^ 2 * |w + (L : ℝ) / z| := by positivity
            nlinarith
        _ = 2 * (c : ℝ) ^ 2 * (w * (|z| * |w + (L : ℝ) / z|)) := by ring
        _ = 2 * (c : ℝ) ^ 2 * (w * |(L : ℝ) + z * w|) := by rw [hzw]
    calc min (|(c : ℝ)| / d) (B / (2 * (c : ℝ) ^ 2))
        ≤ B / (2 * (c : ℝ) ^ 2) := min_le_right _ _
      _ ≤ w * |(L : ℝ) + z * w| := (div_le_iff₀ h2c_pos).mpr (by linarith)

/-- **Track C4, Lemma 5 (`ratBadness` form):**
`min (|c|/d) (B(a/q) / (2 c²)) ≤ B(a/q + (c/d)/q²)`. -/
theorem ratBadness_folding_step {a : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    {c : ℤ} {d : ℕ} (hc : c ≠ 0) (hd : 1 ≤ d) :
    min (|(c : ℝ)| / d) (ratBadness ((a : ℝ) / q) / (2 * (c : ℝ) ^ 2)) ≤
      ratBadness ((a : ℝ) / q + ((c : ℝ) / d) / (q : ℝ) ^ 2) := by
  set v : ℝ := (a : ℝ) / q + ((c : ℝ) / d) / (q : ℝ) ^ 2
  have hne_v : {x : ℝ | ∃ (l : ℕ) (h : ℤ), 1 ≤ l ∧ (h : ℝ) / l ≠ v ∧
      x = (l : ℝ) ^ 2 * |v - (h : ℝ) / l|}.Nonempty := by
    by_cases h0 : ((0 : ℤ) : ℝ) / (1 : ℕ) = v
    · refine ⟨(1 : ℕ) ^ 2 * |v - ((1 : ℤ) : ℝ) / (1 : ℕ)|, 1, 1, le_rfl, ?_, rfl⟩
      rw [← h0]; norm_num
    · exact ⟨(1 : ℕ) ^ 2 * |v - ((0 : ℤ) : ℝ) / (1 : ℕ)|, 1, 0, le_rfl, h0, rfl⟩
  have hbdd_u : BddBelow {x : ℝ | ∃ (l : ℕ) (h : ℤ), 1 ≤ l ∧ (h : ℝ) / l ≠ (a : ℝ) / q ∧
      x = (l : ℝ) ^ 2 * |(a : ℝ) / q - (h : ℝ) / l|} :=
    ⟨0, by rintro x ⟨l, h, _, _, rfl⟩; positivity⟩
  have hB : ∀ l : ℕ, 1 ≤ l → ∀ h : ℤ, (h : ℝ) / l ≠ (a : ℝ) / q →
      ratBadness ((a : ℝ) / q) ≤ (l : ℝ) ^ 2 * |(a : ℝ) / q - (h : ℝ) / l| :=
    fun l hl h hne => csInf_le hbdd_u ⟨l, h, hl, hne, rfl⟩
  refine le_csInf hne_v ?_
  rintro x ⟨l, h, hl, hne, rfl⟩
  exact rat_det_folding_step hq hcop hc hd (ratBadness_pos hq) hB hl hne

/-! ### Section 2: Track B1 — Cubic Digit-Cylinder Identity & Local Factor Upper Bound -/

/-- Exact integer digit-cylinder minimum sum for even radix `b = 2 m`:
`4 ∑_{d < 2m} min(d, 2m - 1 - d) = (2m)(2m - 2)`. -/
theorem sum_digit_cylinder_min_even_nat (m : ℕ) :
    4 * ∑ d ∈ Finset.range (2 * m), min d (2 * m - 1 - d) = (2 * m) * (2 * m - 2) := by
  have hhalf : ∑ d ∈ Finset.range (2 * m), min d (2 * m - 1 - d) =
      2 * ∑ d ∈ Finset.range m, d := by
    rw [show 2 * m = m + m by omega, Finset.sum_range_add]
    have h1 : ∑ d ∈ Finset.range m, min d (m + m - 1 - d) = ∑ d ∈ Finset.range m, d := by
      refine Finset.sum_congr rfl (fun d hd => ?_)
      have hdm : d < m := Finset.mem_range.mp hd
      exact min_eq_left (by omega)
    have h2 : ∑ d ∈ Finset.range m, min (m + d) (m + m - 1 - (m + d)) =
        ∑ d ∈ Finset.range m, d := by
      have h2' : ∑ d ∈ Finset.range m, min (m + d) (m + m - 1 - (m + d)) =
          ∑ d ∈ Finset.range m, (m - 1 - d) := by
        refine Finset.sum_congr rfl (fun d hd => ?_)
        have hdm : d < m := Finset.mem_range.mp hd
        rw [min_eq_right (by omega)]
        omega
      rw [h2', Finset.sum_range_reflect (fun d => d) m]
    rw [h1, h2, two_mul]
  rw [hhalf]
  have hsum' : 2 * ∑ d ∈ Finset.range m, d = m * (m - 1) := by
    simpa [mul_comm] using Finset.sum_range_id_mul_two m
  rw [hsum']
  rcases m with _ | k
  · simp
  · rw [show k + 1 - 1 = k by omega, show 2 * (k + 1) - 2 = 2 * k by omega]
    ring

/-- **Track B1, Theorem 4A (digit-cylinder minimum sum):**
For even radix `b = 2 m` (`m ≥ 1`),
`∑_{d < 2m} min(d, 2m - 1 - d) / (2m)² = 1/4 - 1/(2 · 2m)`. -/
theorem sum_digit_cylinder_min_even (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ Finset.range (2 * m), (min d (2 * m - 1 - d) : ℝ) / ((2 * m : ℝ) ^ 2) =
      1 / 4 - 1 / (2 * (2 * m : ℝ)) := by
  rw [← Finset.sum_div]
  have hnat := sum_digit_cylinder_min_even_nat m
  have hcast : (4 : ℝ) * ∑ d ∈ Finset.range (2 * m), (min d (2 * m - 1 - d) : ℝ) =
      (2 * m : ℝ) * ((2 * m : ℝ) - 2) := by
    have hsub : ((2 * m - 2 : ℕ) : ℝ) = (2 * m : ℝ) - 2 := by
      have : 2 ≤ 2 * m := by omega
      rw [Nat.cast_sub this]; push_cast; ring
    have hsum_cast : ∑ d ∈ Finset.range (2 * m), ((min d (2 * m - 1 - d) : ℕ) : ℝ) =
        ∑ d ∈ Finset.range (2 * m), (min d (2 * m - 1 - d) : ℝ) := by
      refine Finset.sum_congr rfl (fun d hd => ?_)
      have hdm : d < 2 * m := Finset.mem_range.mp hd
      rw [Nat.cast_min, Nat.cast_sub (by omega : d ≤ 2 * m - 1),
        Nat.cast_sub (by omega : 1 ≤ 2 * m)]
      push_cast; rfl
    have h1 : ((4 * ∑ d ∈ Finset.range (2 * m), min d (2 * m - 1 - d) : ℕ) : ℝ) =
        (((2 * m) * (2 * m - 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, hsum_cast, Nat.cast_mul, hsub] at h1
    push_cast at h1 ⊢
    exact h1
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp [hm_ne]
  linarith

/-- **Track B1, §6 (split-prime local-factor identity):**
For every `p ≥ 2` with `x = 1 / p`,
`(1 - x)(1 + x) + x²(3 - 2x)/(1 - x) = 1 + (2p - 1)/(p²(p - 1))`. -/
theorem split_prime_local_factor_eq {p : ℕ} (hp : 2 ≤ p) :
    let x : ℝ := 1 / (p : ℝ)
    (1 - x) * (1 + x) + x ^ 2 * (3 - 2 * x) / (1 - x) =
      1 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
  intro x
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h1x : 1 - x ≠ 0 := by
    dsimp only [x]
    rw [sub_ne_zero]
    intro heq
    have : (p : ℝ) = 1 := by
      have := (eq_div_iff hp_pos.ne').mp heq
      linarith
    linarith
  dsimp only [x] at h1x ⊢
  field_simp [hp_pos.ne', hp1_pos.ne', h1x]
  ring

/-- **Track B1, §6 (split-prime local-factor upper bound):**
For every `p ≥ 2` with `x = 1 / p`,
`(1 - x)(1 + x) + x²(3 - 2x)/(1 - x) ≤ 1 + 3 / p²`. -/
theorem split_prime_local_factor_le {p : ℕ} (hp : 2 ≤ p) :
    let x : ℝ := 1 / (p : ℝ)
    (1 - x) * (1 + x) + x ^ 2 * (3 - 2 * x) / (1 - x) ≤ 1 + 3 / (p : ℝ) ^ 2 := by
  intro x
  rw [split_prime_local_factor_eq hp]
  have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hden_pos : (0 : ℝ) < (p : ℝ) ^ 2 * ((p : ℝ) - 1) := by positivity
  have hfrac : (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) ≤ 3 / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hden_pos (by positivity)]
    nlinarith
  linarith

/-! ### Section 3: Track D3 — Mahler Binary Partitions & Signed Thue–Morse Product Identity -/

/-- Mahler's binary partition function `β(n)`, defined by `β(0) = 1` and
`β(n + 1) = β(n) + [2 ∣ n + 1] β((n + 1) / 2)`. -/
def binPart : ℕ → ℕ
  | 0 => 1
  | n + 1 => binPart n + if 2 ∣ n + 1 then binPart ((n + 1) / 2) else 0
termination_by n => n
decreasing_by all_goals omega

theorem binPart_zero : binPart 0 = 1 := by simp [binPart]

theorem binPart_two_mul_add_one (n : ℕ) : binPart (2 * n + 1) = binPart (2 * n) := by
  rw [binPart]
  have hndvd : ¬ 2 ∣ 2 * n + 1 := by omega
  simp [hndvd]

theorem binPart_two_mul_succ (n : ℕ) :
    binPart (2 * (n + 1)) = binPart (2 * n + 1) + binPart (n + 1) := by
  have hstep : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  conv_lhs => rw [hstep, binPart]
  have hdvd : 2 ∣ (2 * n + 1) + 1 := ⟨n + 1, by omega⟩
  have hdiv : ((2 * n + 1) + 1) / 2 = n + 1 := by omega
  simp [hdvd, hdiv]

/-- Exact partial-sum recurrence for Mahler's binary partition function:
`β(2 n) = ∑_{j = 0}^{n} β(j)`. -/
theorem binPart_two_mul (n : ℕ) :
    binPart (2 * n) = ∑ j ∈ Finset.range (n + 1), binPart j := by
  induction n with
  | zero => simp [binPart_zero]
  | succ k ih =>
    rw [binPart_two_mul_succ, binPart_two_mul_add_one, ih, ← Finset.sum_range_succ]

/-- Parity of Mahler's binary partition function: `β(n)` is even for every `n ≥ 2`. -/
theorem binPart_even {n : ℕ} (hn : 2 ≤ n) : Even (binPart n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rcases k with _ | _ | m
      · omega
      · refine ⟨1, ?_⟩
        have h1 : binPart 1 = 1 := by
          simpa [binPart_zero] using binPart_two_mul_add_one 0
        have h2 : binPart 2 = 2 := by
          have := binPart_two_mul_succ 0
          simpa [h1] using this
        exact h2
      · rw [show m + 2 + (m + 2) = 2 * ((m + 1) + 1) by omega,
          binPart_two_mul_succ, binPart_two_mul_add_one]
        exact (ih (2 * (m + 1)) (by omega) (by omega)).add (ih (m + 2) (by omega) (by omega))
    · rw [binPart_two_mul_add_one]
      exact ih (2 * k) (by omega) (by omega)

/-- **Track D3 (finite Mahler functional equation):**
For every integer `b` and cutoff `M : ℕ`,
`(b - 1) ∑_{n = 0}^M β(n) b^(M - n) = b ∑_{k = 0}^{⌊M/2⌋} β(k) b^(M - 2k) - β(M)`. -/
theorem binPart_mahler_finite (b : ℤ) (M : ℕ) :
    (b - 1) * ∑ n ∈ Finset.range (M + 1), (binPart n : ℤ) * b ^ (M - n) =
      b * ∑ k ∈ Finset.range (M / 2 + 1), (binPart k : ℤ) * b ^ (M - 2 * k) - (binPart M : ℤ) := by
  induction M with
  | zero =>
    simp [binPart_zero]
  | succ m ih =>
    have hS : ∑ n ∈ Finset.range (m + 2), (binPart n : ℤ) * b ^ (m + 1 - n) =
        b * (∑ n ∈ Finset.range (m + 1), (binPart n : ℤ) * b ^ (m - n)) + (binPart (m + 1) : ℤ) := by
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hnm : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [show m + 1 - n = (m - n) + 1 by omega, pow_succ]
      ring
    rw [hS]
    rcases Nat.even_or_odd (m + 1) with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hr1 : 1 ≤ r := by omega
      have hm_eq : m = 2 * (r - 1) + 1 := by omega
      have hdiv_m : m / 2 = r - 1 := by omega
      have hdiv_s : (m + 1) / 2 = r := by omega
      have hbp : (binPart (m + 1) : ℤ) = (binPart m : ℤ) + (binPart r : ℤ) := by
        have h1 : binPart (m + 1) = binPart m + binPart r := by
          rw [show m + 1 = 2 * ((r - 1) + 1) by omega, binPart_two_mul_succ]
          rw [show (r - 1) + 1 = r by omega, ← hm_eq]
        exact_mod_cast h1
      have hT : ∑ k ∈ Finset.range ((m + 1) / 2 + 1), (binPart k : ℤ) * b ^ (m + 1 - 2 * k) =
          b * (∑ k ∈ Finset.range (m / 2 + 1), (binPart k : ℤ) * b ^ (m - 2 * k)) + (binPart r : ℤ) := by
        rw [hdiv_s, Finset.sum_range_succ, show m + 1 - 2 * r = 0 by omega, pow_zero, mul_one,
          show r = m / 2 + 1 by omega, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk_le : 2 * k ≤ m := by
          have := Finset.mem_range.mp hk; omega
        rw [show m + 1 - 2 * k = (m - 2 * k) + 1 by omega, pow_succ]
        ring
      rw [hT]
      linear_combination b * ih + b * hbp
    · have hm_eq : m = 2 * r := by omega
      have hdiv_m : m / 2 = r := by omega
      have hdiv_s : (m + 1) / 2 = r := by omega
      have hbp : (binPart (m + 1) : ℤ) = (binPart m : ℤ) := by
        have h1 : binPart (m + 1) = binPart m := by
          rw [hm_eq, binPart_two_mul_add_one]
        exact_mod_cast h1
      have hT : ∑ k ∈ Finset.range ((m + 1) / 2 + 1), (binPart k : ℤ) * b ^ (m + 1 - 2 * k) =
          b * (∑ k ∈ Finset.range (m / 2 + 1), (binPart k : ℤ) * b ^ (m - 2 * k)) := by
        rw [hdiv_s, hdiv_m, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk_le : 2 * k ≤ m := by
          have := Finset.mem_range.mp hk; omega
        rw [show m + 1 - 2 * k = (m - 2 * k) + 1 by omega, pow_succ]
        ring
      rw [hT]
      linear_combination b * ih + b * hbp

/-- The signed Thue–Morse sequence `(-1)^(s₂(n))`, where `s₂(n)` is the binary digit sum of `n`. -/
def thueMorseSign (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (Nat.digits 2 n).sum

theorem thueMorseSign_zero : thueMorseSign 0 = 1 := by
  simp [thueMorseSign]

theorem thueMorseSign_two_mul (n : ℕ) : thueMorseSign (2 * n) = thueMorseSign n := by
  rcases n with _ | k
  · simp [thueMorseSign]
  · unfold thueMorseSign
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * (k + 1))]
    have hmod : 2 * (k + 1) % 2 = 0 := by omega
    have hdiv : 2 * (k + 1) / 2 = k + 1 := by omega
    simp [hmod, hdiv]

theorem thueMorseSign_two_mul_add_one (n : ℕ) :
    thueMorseSign (2 * n + 1) = - thueMorseSign n := by
  unfold thueMorseSign
  rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n + 1)]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [hmod, hdiv, pow_add]

/-- Adding `2^r` to `n < 2^r` flips the Thue–Morse sign. -/
theorem thueMorseSign_add_pow_two {r n : ℕ} (hn : n < 2 ^ r) :
    thueMorseSign (2 ^ r + n) = - thueMorseSign n := by
  induction r generalizing n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    simpa using thueMorseSign_two_mul_add_one 0
  | succ k ih =>
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm : m < 2 ^ k := by
        rw [pow_succ'] at hn; omega
      have heq : 2 ^ (k + 1) + (m + m) = 2 * (2 ^ k + m) := by rw [pow_succ']; omega
      rw [heq, thueMorseSign_two_mul, ih hm, show m + m = 2 * m by omega, thueMorseSign_two_mul]
    · have hm : m < 2 ^ k := by
        rw [pow_succ'] at hn; omega
      have heq : 2 ^ (k + 1) + (2 * m + 1) = 2 * (2 ^ k + m) + 1 := by rw [pow_succ']; omega
      rw [heq, thueMorseSign_two_mul_add_one, ih hm, thueMorseSign_two_mul_add_one]

/-- **Track D3, Theorem 3.1 (signed Thue–Morse product identity):**
For every commutative ring `R`, `q : R`, and `r : ℕ`,
`∏_{j < r} (1 - q^(2^j)) = ∑_{n < 2^r} thueMorseSign(n) · q^n`. -/
theorem prod_one_sub_pow_two_pow {R : Type*} [CommRing R] (q : R) (r : ℕ) :
    ∏ j ∈ Finset.range r, (1 - q ^ (2 ^ j)) =
      ∑ n ∈ Finset.range (2 ^ r), (thueMorseSign n : R) * q ^ n := by
  induction r with
  | zero =>
    simp [thueMorseSign_zero]
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, mul_sub, mul_one, Finset.sum_mul]
    rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by rw [pow_succ']; omega, Finset.sum_range_add]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hnk : n < 2 ^ k := Finset.mem_range.mp hn
    rw [thueMorseSign_add_pow_two hnk, Int.cast_neg, neg_mul, pow_add]
    ring

/-! ### Section 4: Track B3 — Carry-Cancellation Gauge Identity & Kernel Characterization -/

/-- **Track B3, Lemma 5.1 (finite integer coboundary telescoping):**
`∑_{m=1}^M (b Δ(m) - Δ(m + 1)) b^(M - m) = Δ(1) b^M - Δ(M + 1)`. -/
theorem radix_coboundary_sum_int (b : ℤ) (M : ℕ) (Δ : ℕ → ℤ) :
    ∑ m ∈ Finset.Icc 1 M, (b * Δ m - Δ (m + 1)) * b ^ (M - m) =
      Δ 1 * b ^ M - Δ (M + 1) := by
  induction M with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hsplit, Finset.sum_insert hnotmem, Nat.sub_self, pow_zero, mul_one]
    have htail : ∑ m ∈ Finset.Icc 1 k, (b * Δ m - Δ (m + 1)) * b ^ (k + 1 - m) =
        b * ∑ m ∈ Finset.Icc 1 k, (b * Δ m - Δ (m + 1)) * b ^ (k - m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hmk : m ≤ k := (Finset.mem_Icc.mp hm).2
      rw [show k + 1 - m = (k - m) + 1 by omega, pow_succ]
      ring
    rw [htail, ih, pow_succ]
    ring

/-- **Track B3, Theorem 5.2 (finite telescoping gauge identity, 0-indexed carry `δ`):**
For `b ≥ 2` and any `a, δ : ℕ → ℤ` with `δ 0 = 0`, setting `a'(m) = a(m) + δ(m) - b δ(m - 1)`
gives `∑_{m=1}^M a'(m) b^(-m) = ∑_{m=1}^M a(m) b^(-m) + δ(M) b^(-M)`. -/
theorem carry_gauge_telescoping {b : ℕ} (hb : 2 ≤ b) (a δ : ℕ → ℤ) (hδ0 : δ 0 = 0) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, ((a m + δ m - (b : ℤ) * δ (m - 1) : ℤ) : ℝ) * (b : ℝ) ^ (-(m : ℤ)) =
      (∑ m ∈ Finset.Icc 1 M, (a m : ℝ) * (b : ℝ) ^ (-(m : ℤ))) +
        (δ M : ℝ) * (b : ℝ) ^ (-(M : ℤ)) := by
  have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  induction M with
  | zero => simp [hδ0]
  | succ k ih =>
    have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hsplit, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, ih]
    have hpow : (b : ℝ) * (b : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = (b : ℝ) ^ (-(k : ℤ)) := by
      have hexp : (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 := by push_cast; ring
      rw [hexp, zpow_sub_one₀ hb_ne]
      field_simp [hb_ne]
    push_cast at hpow ⊢
    linear_combination -(δ k : ℝ) * hpow

/-- **Track B3, Lemma 5.1 (real telescoping gauge identity, shifted carry `Δ`):**
For `b ≥ 2` and any `a, Δ : ℕ → ℤ`, setting `a'(m) = a(m) + b Δ(m) - Δ(m + 1)` gives
`∑_{m=1}^M a'(m) b^(-m) = ∑_{m=1}^M a(m) b^(-m) + Δ(1) - Δ(M + 1) b^(-M)`. -/
theorem carry_gauge_telescoping_shift {b : ℕ} (hb : 2 ≤ b) (a Δ : ℕ → ℤ) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, ((a m + (b : ℤ) * Δ m - Δ (m + 1) : ℤ) : ℝ) * (b : ℝ) ^ (-(m : ℤ)) =
      (∑ m ∈ Finset.Icc 1 M, (a m : ℝ) * (b : ℝ) ^ (-(m : ℤ))) +
        (Δ 1 : ℝ) - (Δ (M + 1) : ℝ) * (b : ℝ) ^ (-(M : ℤ)) := by
  have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  let δ : ℕ → ℤ := fun m => Δ 1 * (b : ℤ) ^ m - Δ (m + 1)
  have hδ0 : δ 0 = 0 := by simp [δ]
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      a m + (b : ℤ) * Δ m - Δ (m + 1) = a m + δ m - (b : ℤ) * δ (m - 1) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    dsimp only [δ]
    have hpow : (b : ℤ) ^ m = (b : ℤ) * (b : ℤ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ, mul_comm]
    rw [show m - 1 + 1 = m by omega, hpow]
    ring
  have hsum_eq :
      ∑ m ∈ Finset.Icc 1 M, ((a m + (b : ℤ) * Δ m - Δ (m + 1) : ℤ) : ℝ) * (b : ℝ) ^ (-(m : ℤ)) =
        ∑ m ∈ Finset.Icc 1 M, ((a m + δ m - (b : ℤ) * δ (m - 1) : ℤ) : ℝ) * (b : ℝ) ^ (-(m : ℤ)) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [hterm m hm]
  rw [hsum_eq, carry_gauge_telescoping hb a δ hδ0 M]
  dsimp only [δ]
  push_cast
  have hcancel : (b : ℝ) ^ M * (b : ℝ) ^ (-(M : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hb_ne, add_neg_cancel, zpow_zero]
  linear_combination (Δ 1 : ℝ) * hcancel

/-- **Track B3, carry-kernel characterization (0-indexed):**
`δ m - b * δ (m - 1) = 0` for all `m ≥ 1` iff `δ m = δ 0 * b^m` for all `m`. -/
theorem carry_kernel_iff (b : ℤ) (δ : ℕ → ℤ) :
    (∀ m : ℕ, 1 ≤ m → δ m - b * δ (m - 1) = 0) ↔ ∀ m : ℕ, δ m = δ 0 * b ^ m := by
  constructor
  · intro hker m
    induction m with
    | zero => simp
    | succ k ih =>
      have h1 := hker (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h1
      have h2 : δ (k + 1) = b * δ k := by linarith
      rw [h2, ih, pow_succ]
      ring
  · intro hform m hm
    rw [hform m, hform (m - 1)]
    have hpow : b ^ m = b * b ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ, mul_comm]
    rw [hpow]
    ring

/-- **Track B3, vanishing of `o(b^m)` zero-gauge carries (0-indexed):**
If `δ m - b * δ (m - 1) = 0` for all `m ≥ 1` and `δ m / b^m → 0`, then `δ` is identically `0`. -/
theorem carry_kernel_eq_zero_of_tendsto {b : ℕ} (hb : 2 ≤ b) {δ : ℕ → ℤ}
    (hker : ∀ m : ℕ, 1 ≤ m → δ m - (b : ℤ) * δ (m - 1) = 0)
    (htend : Tendsto (fun m : ℕ => (δ m : ℝ) / (b : ℝ) ^ m) atTop (𝓝 0)) :
    ∀ m : ℕ, δ m = 0 := by
  have hform := (carry_kernel_iff (b : ℤ) δ).mp hker
  have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hconst : (fun m : ℕ => (δ m : ℝ) / (b : ℝ) ^ m) = fun _ => (δ 0 : ℝ) := by
    ext m
    rw [hform m]
    push_cast
    exact mul_div_cancel_right₀ (δ 0 : ℝ) (pow_ne_zero m hb_ne)
  rw [hconst] at htend
  have h0R : (δ 0 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds htend
  have h0 : δ 0 = 0 := by exact_mod_cast h0R
  intro m
  rw [hform m, h0, zero_mul]

/-- **Track B3, carry-kernel characterization (shifted index `Δ`):**
`b * Δ m - Δ (m + 1) = 0` for all `m ≥ 1` iff `Δ m = Δ 1 * b^(m - 1)` for all `m ≥ 1`. -/
theorem carry_kernel_shift_iff (b : ℤ) (Δ : ℕ → ℤ) :
    (∀ m : ℕ, 1 ≤ m → b * Δ m - Δ (m + 1) = 0) ↔
      ∀ m : ℕ, 1 ≤ m → Δ m = Δ 1 * b ^ (m - 1) := by
  constructor
  · intro hker m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    induction k with
    | zero => simp
    | succ j ih =>
      have h1 := hker (j + 1) (by omega)
      have hj := ih (by omega)
      have hsub1 : j + 1 - 1 = j := by omega
      have hsub2 : j + 1 + 1 - 1 = j + 1 := by omega
      rw [hsub1] at hj
      have h2 : Δ (j + 1 + 1) = b * Δ (j + 1) := by linarith
      rw [h2, hj, hsub2, pow_succ]
      ring
  · intro hform m hm
    rw [hform m hm, hform (m + 1) (by omega)]
    have hpow : b ^ (m + 1 - 1) = b * b ^ (m - 1) := by
      rw [show m + 1 - 1 = (m - 1) + 1 by omega, pow_succ, mul_comm]
    rw [hpow]
    ring

/-- **Track B3, vanishing of `o(b^m)` zero-gauge carries (shifted index `Δ`):**
If `b * Δ m - Δ (m + 1) = 0` for all `m ≥ 1` and `Δ m / b^m → 0`, then `Δ m = 0` for all `m ≥ 1`. -/
theorem carry_kernel_shift_eq_zero_of_tendsto {b : ℕ} (hb : 2 ≤ b) {Δ : ℕ → ℤ}
    (hker : ∀ m : ℕ, 1 ≤ m → (b : ℤ) * Δ m - Δ (m + 1) = 0)
    (htend : Tendsto (fun m : ℕ => (Δ m : ℝ) / (b : ℝ) ^ m) atTop (𝓝 0)) :
    ∀ m : ℕ, 1 ≤ m → Δ m = 0 := by
  have hform := (carry_kernel_shift_iff (b : ℤ) Δ).mp hker
  have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hev : (fun m : ℕ => (Δ m : ℝ) / (b : ℝ) ^ m) =ᶠ[atTop] fun _ => (Δ 1 : ℝ) / (b : ℝ) := by
    refine Filter.eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
    dsimp only
    rw [hform m hm]
    push_cast
    have hpow : (b : ℝ) ^ m = (b : ℝ) * (b : ℝ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ, mul_comm]
    rw [hpow]
    field_simp [hb_ne, pow_ne_zero (m - 1) hb_ne]
  have hlim : Tendsto (fun _ : ℕ => (Δ 1 : ℝ) / (b : ℝ)) atTop (𝓝 0) :=
    htend.congr' hev
  have hdiv0 : (Δ 1 : ℝ) / (b : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have h1R : (Δ 1 : ℝ) = 0 := (div_eq_zero_iff.mp hdiv0).resolve_right hb_ne
  have h1 : Δ 1 = 0 := by exact_mod_cast h1R
  intro m hm
  rw [hform m hm, h1, zero_mul]

/-- **Track B3, Theorem 5.5(b) (three-state zero-cost carry transitions):**
For `b ≥ 2`, `δ, δ' ∈ {-1, 0, 1}`, and `0 ≤ d < b`, the cost-free transitions
`d + b δ - δ' = 0` are precisely `(0, 0, 0)`, `(0, 1, 1)`, and `(-1, -1, b - 1)`. -/
theorem carry_zero_transition {b : ℕ} (hb : 2 ≤ b) {δ δ' : ℤ} {d : ℕ}
    (hδ : δ ∈ ({-1, 0, 1} : Finset ℤ)) (hδ' : δ' ∈ ({-1, 0, 1} : Finset ℤ)) (hd : d < b) :
    (d : ℤ) + (b : ℤ) * δ - δ' = 0 ↔
      (δ = 0 ∧ δ' = 0 ∧ d = 0) ∨ (δ = 0 ∧ δ' = 1 ∧ d = 1) ∨
        (δ = -1 ∧ δ' = -1 ∧ d = b - 1) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hδ hδ'
  rcases hδ with rfl | rfl | rfl <;> rcases hδ' with rfl | rfl | rfl <;> constructor <;>
    intro h <;> omega

/-! ### Section 5: Track E — Arithmetic Correlations and 2-Adic Peeling of `E_+` -/

/-- **Track E1.2, Theorem 2.2(1) (pointwise odd-shift anticorrelation of `a_+`):**
For every `n ≥ 1` and every odd `h`, `erdosBorweinPlusCoeff n * erdosBorweinPlusCoeff (n + h) ≤ 0`. -/
theorem erdosBorweinPlusCoeff_mul_add_odd_nonpos {n h : ℕ} (hn : 0 < n) (hh : Odd h) :
    erdosBorweinPlusCoeff n * erdosBorweinPlusCoeff (n + h) ≤ 0 := by
  have hnh : 0 < n + h := by omega
  rcases Nat.even_or_odd n with hev | hodd
  · have h1 : erdosBorweinPlusCoeff n ≤ 0 := by
      by_contra hgt
      push Not at hgt
      exact (Nat.not_odd_iff_even.mpr hev) ((erdosBorweinPlusCoeff_pos_iff hn).mp hgt)
    have h2 : 0 ≤ erdosBorweinPlusCoeff (n + h) :=
      ((erdosBorweinPlusCoeff_pos_iff hnh).mpr (hev.add_odd hh)).le
    exact mul_nonpos_of_nonpos_of_nonneg h1 h2
  · have h1 : 0 ≤ erdosBorweinPlusCoeff n :=
      ((erdosBorweinPlusCoeff_pos_iff hn).mpr hodd).le
    have h2 : erdosBorweinPlusCoeff (n + h) ≤ 0 := by
      by_contra hgt
      push Not at hgt
      exact (Nat.not_odd_iff_even.mpr (hodd.add_odd hh))
        ((erdosBorweinPlusCoeff_pos_iff hnh).mp hgt)
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- **Track E1.2, §2.3 (four-point consecutive vanishing of `a_+`):**
For every `n ≥ 1`, one of `n, n + 1, n + 2, n + 3` is `2 (mod 4)`, so
`a_+(n) * a_+(n + 1) * a_+(n + 2) * a_+(n + 3) = 0`. -/
theorem erdosBorweinPlusCoeff_four_consec_eq_zero {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n * erdosBorweinPlusCoeff (n + 1) *
      erdosBorweinPlusCoeff (n + 2) * erdosBorweinPlusCoeff (n + 3) = 0 := by
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · have hz : erdosBorweinPlusCoeff (n + 2) = 0 :=
      (erdosBorweinPlusCoeff_eq_zero_iff (by omega)).mpr (by omega)
    rw [hz]; ring
  · have hz : erdosBorweinPlusCoeff (n + 1) = 0 :=
      (erdosBorweinPlusCoeff_eq_zero_iff (by omega)).mpr (by omega)
    rw [hz]; ring
  · have hz : erdosBorweinPlusCoeff n = 0 :=
      (erdosBorweinPlusCoeff_eq_zero_iff hn).mpr h2
    rw [hz]; ring
  · have hz : erdosBorweinPlusCoeff (n + 3) = 0 :=
      (erdosBorweinPlusCoeff_eq_zero_iff (by omega)).mpr (by omega)
    rw [hz]; ring

/-- **Track E1.1, Proposition 1.1 (exact mod-2 reduction of `a_+`):**
For every `n ≥ 1`, `erdosBorweinPlusCoeff n % 2 = if IsSquare n then 1 else 0`. -/
theorem erdosBorweinPlusCoeff_emod_two {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n % 2 = if IsSquare n then 1 else 0 := by
  have hodd := erdosBorweinPlusCoeff_odd_iff hn
  by_cases hsq : IsSquare n
  · simp only [hsq, ↓reduceIte]
    rcases hodd.mpr hsq with ⟨k, hk⟩
    omega
  · simp only [hsq, ↓reduceIte]
    have hnot : ¬ Odd (erdosBorweinPlusCoeff n) := fun h => hsq (hodd.mp h)
    have hev : Even (erdosBorweinPlusCoeff n) := Int.not_odd_iff_even.mp hnot
    rcases hev with ⟨k, hk⟩
    omega

/-- **Track E1.1, Theorem 1.5 (`j = 1` theta peeling identity):**
For every `n ≥ 1`, `erdosBorweinPlusCoeff n = (if IsSquare n then 1 else 0) + 2 * (erdosBorweinPlusCoeff n / 2)`. -/
theorem erdosBorweinPlusCoeff_peel_one {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n =
      (if IsSquare n then 1 else 0) + 2 * (erdosBorweinPlusCoeff n / 2) := by
  have hmod := erdosBorweinPlusCoeff_emod_two hn
  omega

/-- **Track E1.1, §1.4 (peel difference identity):**
`⌊τ(n)/2⌋ - ⌊a_+(n)/2⌋ = [2 ∣ n] τ(n / 2)` for every `n : ℕ`. -/
theorem floor_half_tau_sub_floor_half_plus (n : ℕ) :
    (n.divisors.card : ℤ) / 2 - erdosBorweinPlusCoeff n / 2 =
      if 2 ∣ n then ((n / 2).divisors.card : ℤ) else 0 := by
  unfold erdosBorweinPlusCoeff
  split_ifs <;> omega

/-! ### Section 6: Track A3 Derivative Divisibility & `ln 2` Glaisher–Wieferich Congruence -/

/-- **Track A3, §6 (exact content 3 of `D^j E^3`):**
For every `k : ℕ` and every `j ≥ 1`, `3 ∣ (k * (k + 1) / 2) ^ j * (2 * k + 1)`. -/
theorem three_dvd_triNum_pow_mul_odd (k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    3 ∣ (k * (k + 1) / 2) ^ j * (2 * k + 1) := by
  have hbase : 3 ∣ (k * (k + 1) / 2) * (2 * k + 1) := by
    have h2 : 2 * (k * (k + 1) / 2) = k * (k + 1) := by
      have hev : Even (k * (k + 1)) := Nat.even_mul_succ_self k
      exact Nat.mul_div_cancel' (even_iff_two_dvd.mp hev)
    have h3 : 3 ∣ 2 * ((k * (k + 1) / 2) * (2 * k + 1)) := by
      have hmul : 2 * ((k * (k + 1) / 2) * (2 * k + 1)) = k * (k + 1) * (2 * k + 1) := by
        calc 2 * ((k * (k + 1) / 2) * (2 * k + 1))
            = (2 * (k * (k + 1) / 2)) * (2 * k + 1) := by ring
          _ = k * (k + 1) * (2 * k + 1) := by rw [h2]
      rw [hmul]
      have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2'
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h0) _) _
      · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _) _
    exact (show Nat.Coprime 3 2 by decide).dvd_of_dvd_mul_left h3
  have hpow : (k * (k + 1) / 2) ^ j * (2 * k + 1) =
      (k * (k + 1) / 2) ^ (j - 1) * ((k * (k + 1) / 2) * (2 * k + 1)) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  exact dvd_mul_of_dvd_right hbase _

/-- The `N`-th rational BBP prefix `s_N = ∑_{k=1}^N 2^(N - k) / k` of `ln 2`. -/
def ln2Prefix (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 N, (2 : ℚ) ^ (N - k) / (k : ℚ)

private lemma choose_pred_zmod {p : ℕ} [Fact p.Prime] :
    ∀ m < p, (((p - 1).choose m : ℕ) : ZMod p) = (-1 : ZMod p) ^ m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hp : p.Prime := Fact.out
    have hk_lt : k < p := by omega
    have hpascal : (p - 1).choose k + (p - 1).choose (k + 1) = p.choose (k + 1) := by
      have hp1 : p = (p - 1) + 1 := by have := hp.two_le; omega
      conv_rhs => rw [hp1, Nat.choose_succ_succ]
    have hdvd : p ∣ p.choose (k + 1) := Nat.Prime.dvd_choose_self hp (by omega) hk
    have hz : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hcast : (((p - 1).choose k : ℕ) : ZMod p) + (((p - 1).choose (k + 1) : ℕ) : ZMod p) = 0 := by
      rw [← Nat.cast_add, hpascal, hz]
    rw [ih hk_lt] at hcast
    rw [pow_succ]
    linear_combination hcast

private lemma choose_div_prime_zmod {p k : ℕ} [Fact p.Prime] (hk1 : 1 ≤ k) (hkp : k < p) :
    ((p.choose k / p : ℕ) : ZMod p) = (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hdvd : p ∣ p.choose k := Nat.Prime.dvd_choose_self hp (by omega) hkp
  have hmul_choose : k * p.choose k = p * (p - 1).choose (k - 1) := by
    have h1 := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
    rw [show p - 1 + 1 = p by have := hp.two_le; omega,
        show k - 1 + 1 = k by omega] at h1
    linarith
  have hdiv_eq : k * (p.choose k / p) = (p - 1).choose (k - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hp_pos
    calc p * (k * (p.choose k / p))
        = k * (p * (p.choose k / p)) := by ring
      _ = k * p.choose k := by rw [Nat.mul_div_cancel' hdvd]
      _ = p * (p - 1).choose (k - 1) := hmul_choose
  have hz : (k : ZMod p) * ((p.choose k / p : ℕ) : ZMod p) = (-1 : ZMod p) ^ (k - 1) := by
    rw [← Nat.cast_mul, hdiv_eq]
    exact choose_pred_zmod (k - 1) (by omega)
  have hk_ne : (k : ZMod p) ≠ 0 := by
    intro h0
    have hpk : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
    have hle := Nat.le_of_dvd (by omega) hpk
    omega
  calc ((p.choose k / p : ℕ) : ZMod p)
      = (k : ZMod p)⁻¹ * ((k : ZMod p) * ((p.choose k / p : ℕ) : ZMod p)) := by
          rw [inv_mul_cancel_left₀ hk_ne]
    _ = (k : ZMod p)⁻¹ * (-1 : ZMod p) ^ (k - 1) := by rw [hz]
    _ = (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹ := mul_comm _ _

private lemma prime_dvd_two_pow_sub_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    p ∣ 2 ^ (p - 1) - 1 := by
  have hp_prime : p.Prime := Fact.out
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have := (Nat.dvd_prime Nat.prime_two).mp hp2
    rcases this with h1 | h2
    · exact hp_prime.ne_one h1
    · exact hp h2
  have hflt : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2_ne
  rw [← ZMod.natCast_eq_zero_iff]
  have hge : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hflt, sub_self]

/-- **Track E2, Proposition 5.4 (Glaisher–Wieferich congruence in `ZMod p`):**
For every odd prime `p`,
`∑_{k = 1}^{p - 1} 2^(p - 1 - k) · k⁻¹ = ((2^(p - 1) - 1) / p : ZMod p)`. -/
theorem glaisher_wieferich_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (2 : ZMod p) ^ (p - 1 - k) * (k : ZMod p)⁻¹ =
      (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod p) := by
  have hp_prime : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
  have hp_odd : Odd p := hp_prime.odd_of_ne_two hp
  have hbinom : (1 : ℤ) = ∑ k ∈ Finset.range (p + 1),
      (-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * (p.choose k : ℤ) := by
    have h1 : ((-1 : ℤ) + 2) ^ p = 1 := by norm_num
    conv_lhs => rw [← h1, add_pow]
  have hsplit : ∑ k ∈ Finset.range (p + 1), (-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * (p.choose k : ℤ) =
      (2 : ℤ) ^ p +
        (∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * (p.choose k : ℤ)) - 1 := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      mul_one, hp_odd.neg_one_pow]
    have hrange : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp)]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    ring
  rw [hsplit] at hbinom
  set q : ℕ := (2 ^ (p - 1) - 1) / p
  have hflt_dvd : p ∣ 2 ^ (p - 1) - 1 := prime_dvd_two_pow_sub_one hp
  have h2p_eq : (2 : ℤ) ^ p - 2 = (p : ℤ) * (2 * (q : ℤ)) := by
    have h1 : 2 ^ p - 2 = 2 * (2 ^ (p - 1) - 1) := by
      have hpow : 2 ^ p = 2 * 2 ^ (p - 1) := by
        conv_lhs => rw [show p = (p - 1) + 1 by omega, pow_succ, mul_comm]
      omega
    have h2 : 2 * (2 ^ (p - 1) - 1) = p * (2 * q) := by
      have hmul : p * q = 2 ^ (p - 1) - 1 := Nat.mul_div_cancel' hflt_dvd
      linarith
    have hge : 2 ≤ 2 ^ p := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : ((2 ^ p - 2 : ℕ) : ℤ) = (p : ℤ) * (2 * (q : ℤ)) := by
      rw [h1, h2]; push_cast; ring
    rw [Nat.cast_sub hge] at h3
    simpa using h3
  have hdiv_sum : ∑ k ∈ Finset.Icc 1 (p - 1),
      (-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * ((p.choose k / p : ℕ) : ℤ) = -(2 * (q : ℤ)) := by
    have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
    apply mul_left_cancel₀ hp_ne
    rw [Finset.mul_sum]
    have hcongr : ∑ k ∈ Finset.Icc 1 (p - 1),
        (p : ℤ) * ((-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * ((p.choose k / p : ℕ) : ℤ)) =
        ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * (p.choose k : ℤ) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk_mem := Finset.mem_Icc.mp hk
      have hdvd : p ∣ p.choose k := Nat.Prime.dvd_choose_self hp_prime (by omega) (by omega)
      have hmul : (p : ℤ) * ((p.choose k / p : ℕ) : ℤ) = (p.choose k : ℤ) := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      calc (p : ℤ) * ((-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * ((p.choose k / p : ℕ) : ℤ))
          = (-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * ((p : ℤ) * ((p.choose k / p : ℕ) : ℤ)) := by ring
        _ = (-1 : ℤ) ^ k * (2 : ℤ) ^ (p - k) * (p.choose k : ℤ) := by rw [hmul]
    rw [hcongr]
    linarith
  have hzmod : ∑ k ∈ Finset.Icc 1 (p - 1),
      (-1 : ZMod p) ^ k * (2 : ZMod p) ^ (p - k) * ((p.choose k / p : ℕ) : ZMod p) =
      -(2 * (q : ZMod p)) := by
    have hcast := congrArg (Int.cast (R := ZMod p)) hdiv_sum
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_ofNat, Int.cast_natCast] using hcast
  have hlhs_eq : ∑ k ∈ Finset.Icc 1 (p - 1),
      (-1 : ZMod p) ^ k * (2 : ZMod p) ^ (p - k) * ((p.choose k / p : ℕ) : ZMod p) =
      -(2 * ∑ k ∈ Finset.Icc 1 (p - 1), (2 : ZMod p) ^ (p - 1 - k) * (k : ZMod p)⁻¹) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk_mem := Finset.mem_Icc.mp hk
    rw [choose_div_prime_zmod hk_mem.1 (by omega)]
    have hsign : (-1 : ZMod p) ^ k * (-1 : ZMod p) ^ (k - 1) = -1 := by
      rw [← pow_add, show k + (k - 1) = 2 * (k - 1) + 1 by omega, pow_succ, pow_mul]
      norm_num
    have hpow2 : (2 : ZMod p) ^ (p - k) = 2 * (2 : ZMod p) ^ (p - 1 - k) := by
      conv_lhs => rw [show p - k = (p - 1 - k) + 1 by omega, pow_succ, mul_comm]
    rw [hpow2]
    calc (-1 : ZMod p) ^ k * (2 * (2 : ZMod p) ^ (p - 1 - k)) *
            ((-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹)
        = ((-1 : ZMod p) ^ k * (-1 : ZMod p) ^ (k - 1)) *
            (2 * ((2 : ZMod p) ^ (p - 1 - k) * (k : ZMod p)⁻¹)) := by ring
      _ = -(2 * ((2 : ZMod p) ^ (p - 1 - k) * (k : ZMod p)⁻¹)) := by rw [hsign]; ring
  rw [hlhs_eq] at hzmod
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h1 | h2
    · exact hp_prime.ne_one h1
    · exact hp h2
  exact mul_left_cancel₀ h2_ne (neg_inj.mp hzmod)

/-- Alternate reversed form of the Glaisher–Wieferich congruence:
`((2^(p - 1) - 1) / p : ZMod p) = - ∑_{k = 1}^{p - 1} 2^(k - 1) · k⁻¹`. -/
theorem glaisher_wieferich_alt_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod p) =
      - ∑ k ∈ Finset.Icc 1 (p - 1), (2 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹ := by
  have hp_prime : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
  rw [← glaisher_wieferich_zmod hp, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
  · intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    have := Finset.mem_Icc.mp hk₁
    have := Finset.mem_Icc.mp hk₂
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact ⟨p - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro k hk
    have hk_mem := Finset.mem_Icc.mp hk
    have hsub : p - k - 1 = p - 1 - k := by omega
    have hcast : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
      rw [Nat.cast_sub (by omega : k ≤ p), ZMod.natCast_self, zero_sub]
    rw [hsub, hcast, inv_neg, mul_neg, neg_neg]

/-- **Track E2, Proposition 5.4 (Wieferich criterion in `ZMod p`):**
For an odd prime `p`, the `ZMod p` BBP sum vanishes iff `p² ∣ 2^(p - 1) - 1`. -/
theorem glaisher_wieferich_zero_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (∑ k ∈ Finset.Icc 1 (p - 1), (2 : ZMod p) ^ (p - 1 - k) * (k : ZMod p)⁻¹) = 0 ↔
      p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  rw [glaisher_wieferich_zmod hp, ZMod.natCast_eq_zero_iff]
  have hflt : p ∣ 2 ^ (p - 1) - 1 := prime_dvd_two_pow_sub_one hp
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hmul := Nat.mul_div_cancel' hflt
    rw [hm] at hmul
    calc 2 ^ (p - 1) - 1 = p * (p * m) := hmul.symm
      _ = p ^ 2 * m := by ring
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hp_pos
    rw [Nat.mul_div_cancel' hflt, hm]
    ring

/-- **Track E2, Proposition 5.4 (exact reduced numerator criterion for `ln 2`):**
For every odd prime `p`, `p ∣ A_{p - 1} ↔ p² ∣ 2^(p - 1) - 1`, where `A_{p - 1}` is the
reduced numerator of `ln2Prefix (p - 1) = ∑_{k=1}^{p-1} 2^(p - 1 - k) / k`. -/
theorem ln2Prefix_num_dvd_iff_wieferich {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    p ∣ (ln2Prefix (p - 1)).num.natAbs ↔ p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  have hp_prime : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
  set s : ℚ := ln2Prefix (p - 1)
  set F : ℕ := (p - 1).factorial
  set M : ℕ := ∑ k ∈ Finset.Icc 1 (p - 1), 2 ^ (p - 1 - k) * (F / k)
  have hFs : (F : ℚ) * s = (M : ℚ) := by
    dsimp only [s, M, ln2Prefix]
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk_mem := Finset.mem_Icc.mp hk
    have hk_dvd : k ∣ F := Nat.dvd_factorial (by omega) hk_mem.2
    have hk_ne : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hmul : (k : ℚ) * ((F / k : ℕ) : ℚ) = (F : ℚ) := by
      exact_mod_cast Nat.mul_div_cancel' hk_dvd
    push_cast
    field_simp [hk_ne]
    rw [← hmul]
  have hnat_eq : F * s.num.natAbs = M * s.den := by
    have hden_ne : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
    have hq : (F : ℚ) * (s.num : ℚ) = (M : ℚ) * (s.den : ℚ) := by
      have hs : s = (s.num : ℚ) / (s.den : ℚ) := (Rat.num_div_den s).symm
      rw [hs] at hFs
      field_simp [hden_ne] at hFs
      linarith
    have hint : (F : ℤ) * s.num = (M : ℤ) * (s.den : ℤ) := by exact_mod_cast hq
    have habs := congrArg Int.natAbs hint
    simpa [Int.natAbs_mul] using habs
  have hp_ndvd_F : ¬ p ∣ F := by
    rw [Nat.Prime.dvd_factorial hp_prime]; omega
  have hden_dvd_F : s.den ∣ F := by
    have h1 : s.den ∣ F * s.num.natAbs := ⟨M, by linarith⟩
    exact s.reduced.symm.dvd_of_dvd_mul_right h1
  have hp_ndvd_den : ¬ p ∣ s.den := fun h => hp_ndvd_F (h.trans hden_dvd_F)
  have hdvd_iff : p ∣ s.num.natAbs ↔ p ∣ M := by
    constructor
    · intro h
      have h1 : p ∣ M * s.den := by rw [← hnat_eq]; exact dvd_mul_of_dvd_right h F
      exact (hp_prime.dvd_mul.mp h1).resolve_right hp_ndvd_den
    · intro h
      have h1 : p ∣ F * s.num.natAbs := by rw [hnat_eq]; exact dvd_mul_of_dvd_left h s.den
      exact (hp_prime.dvd_mul.mp h1).resolve_left hp_ndvd_F
  have hM_zmod : (M : ZMod p) =
      (F : ZMod p) * ∑ k ∈ Finset.Icc 1 (p - 1), (2 : ZMod p) ^ (p - 1 - k) * (k : ZMod p)⁻¹ := by
    dsimp only [M]
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk_mem := Finset.mem_Icc.mp hk
    have hk_dvd : k ∣ F := Nat.dvd_factorial (by omega) hk_mem.2
    have hk_ne : (k : ZMod p) ≠ 0 := by
      intro h0
      have hpk : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
      have := Nat.le_of_dvd (by omega) hpk
      omega
    have hFk : ((F / k : ℕ) : ZMod p) = (F : ZMod p) * (k : ZMod p)⁻¹ := by
      have hmul : (k : ZMod p) * ((F / k : ℕ) : ZMod p) = (F : ZMod p) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hk_dvd]
      calc ((F / k : ℕ) : ZMod p)
          = (k : ZMod p)⁻¹ * ((k : ZMod p) * ((F / k : ℕ) : ZMod p)) := by
              rw [inv_mul_cancel_left₀ hk_ne]
        _ = (k : ZMod p)⁻¹ * (F : ZMod p) := by rw [hmul]
        _ = (F : ZMod p) * (k : ZMod p)⁻¹ := mul_comm _ _
    push_cast
    rw [hFk]
    ring
  have hF_ne : (F : ZMod p) ≠ 0 := by
    intro h0
    exact hp_ndvd_F ((ZMod.natCast_eq_zero_iff F p).mp h0)
  rw [hdvd_iff, ← ZMod.natCast_eq_zero_iff, hM_zmod, mul_eq_zero, or_iff_right hF_ne,
    glaisher_wieferich_zero_iff hp]

end NormalityChecker.Phase23Cores
