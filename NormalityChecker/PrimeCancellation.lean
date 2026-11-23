module

public import NormalityChecker.LogTwo
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

open Finset Nat

namespace NormalityChecker

/-- The unshifted first `n` terms of the logarithm series. -/
def partialLogTwo (n : ℕ) : ℚ :=
  ∑ i ∈ range n, 1 / (((i : ℚ) + 1) * 2 ^ (i + 1))

theorem shifted_partialLogTwo (n : ℕ) : 2 ^ n * partialLogTwo n = logPrefix n := by
  induction n with
  | zero => simp [partialLogTwo, logPrefix]
  | succ n ih =>
    simp only [partialLogTwo, sum_range_succ, mul_add, logPrefix] at *
    rw [_root_.pow_succ', mul_assoc, ih]
    congr 1
    field_simp

/-- The reduced denominator after shifting. -/
def logDen (n : ℕ) : ℕ := (logPrefix n).den

theorem logDen_ten : logDen 10 = 63 := by
  norm_num [logDen, logPrefix]

/-- For a common denominator `L`, this is the unreduced numerator of the shifted prefix. -/
private def scaled (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => 2 * scaled L t + L / (t+1)

lemma index_dvd_lcm {j n : ℕ} (hj : 0 < j) (hjn : j ≤ n) : j ∣ lcmUpto n :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hj, hjn⟩)

private lemma scaled_eq (L t : ℕ) (hL : ∀ j, 0 < j → j ≤ t → j ∣ L) :
    (scaled L t : ℚ) = L * logPrefix t := by
  induction t with
  | zero => simp [scaled, logPrefix]
  | succ t ih =>
    have he := congrArg (fun z : ℕ => (z : ℚ)) (Nat.div_mul_cancel (hL (t+1) (by omega) le_rfl))
    push_cast at he
    simp only [scaled, cast_add, cast_mul, cast_ofNat, logPrefix, ih (fun j hj h => hL j hj (by omega))]
    field_simp
    nlinarith

/-- Cross-multiplication before and after reducing a positive-denominator fraction. -/
lemma reduced_info {x : ℚ} {S L : ℕ} (hL : 0 < L) (he : (S : ℚ) = L * x) :
    x.den ∣ L ∧ S * x.den = L * x.num.natAbs := by
  have hx : x = Rat.divInt S L := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast, eq_div_iff (by positivity)]
    linarith
  have hd : x.den ∣ L := by
    exact_mod_cast (hx ▸ Rat.den_dvd (S : ℤ) (L : ℤ) : (x.den : ℤ) ∣ (L : ℤ))
  obtain ⟨c,h₁,h₂⟩ := Rat.num_den_mk (by exact_mod_cast hL.ne') hx
  have h₃ := congrArg Int.natAbs h₁
  have h₄ := congrArg Int.natAbs h₂
  simp only [Int.natAbs_natCast, Int.natAbs_mul] at h₃ h₄
  exact ⟨hd, by rw [h₃, h₄]; ring⟩

theorem logDen_dvd_lcm (n : ℕ) : logDen n ∣ lcmUpto n :=
  (reduced_info (lcmUpto_pos n) (scaled_eq _ n fun _ => index_dvd_lcm)).1

/-- A bound on the integer whose prime divisors can account for cancellations. -/
theorem partial_num_bound (k : ℕ) :
    (partialLogTwo k).num.natAbs ≤ lcmUpto k * 2^k := by
  let D := lcmUpto k
  have hD : 0 < D := lcmUpto_pos _
  have hs := scaled_eq D k (fun _ => index_dvd_lcm)
  have hs' : (scaled D k : ℚ) = ((D*2^k : ℕ) : ℚ) * partialLogTwo k := by
    rw [hs, ← shifted_partialLogTwo]; push_cast; ring
  obtain ⟨hd,cross⟩ := reduced_info (by positivity : 0 < D * 2^k) hs'
  have hprefix : ∀ n, logPrefix n ≤ 2^n - 1 := by
    intro n
    induction n with
    | zero => simp [logPrefix]
    | succ n ih =>
      have h : 1 / ((n : ℚ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      rw [logPrefix, pow_succ]
      linarith
  have hscaled : scaled D k ≤ D*2^k := by
    have h : (scaled D k : ℚ) ≤ (D : ℚ)*2^k :=
      hs.trans_le (mul_le_mul_of_nonneg_left (by linarith [hprefix k]) (by positivity))
    exact_mod_cast h
  have hden := Nat.le_of_dvd (show 0 < D*2^k by positivity) hd
  apply Nat.le_of_mul_le_mul_left _ (show 0 < D*2^k by positivity)
  rw [← cross]
  exact Nat.mul_le_mul hscaled hden

theorem partial_num_pos {k : ℕ} (hk : 0 < k) : 0 < (partialLogTwo k).num.natAbs := by
  have h : 0 < partialLogTwo k :=
    Finset.sum_pos (fun i _ => by positivity) (nonempty_range_iff.mpr hk.ne')
  exact Int.natAbs_pos.mpr (Rat.num_pos.mpr h).ne'

private def partialMod (p : ℕ) [Fact p.Prime] : ℕ → ZMod p
  | 0 => 0
  | j+1 => partialMod p j + 1 / (((j : ZMod p)+1) * 2^(j+1))

/-- For `L = p^a C`, terms at indices not divisible by `p^a` vanish mod `p`.
On the remaining indices Frobenius changes `2^(j*p^a)` to `2^j`. -/
private lemma scaled_mod {p : ℕ} [hp : Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (a C t : ℕ) (ht : t < p^(a+1)) (hL : ∀ j, 0 < j → j ≤ t → j ∣ p^a*C) :
    (scaled (p^a*C) t : ZMod p) = 2^t * C * partialMod p (t / p^a) := by
  have hq : 0 < p^a := pow_pos hp.out.pos _
  induction t with
  | zero => simp [scaled, partialMod]
  | succ t ih =>
    have hdiv := hL (t+1) (by omega) le_rfl
    let B := p^a*C / (t+1)
    have hb : B*(t+1) = p^a*C := Nat.div_mul_cancel hdiv
    simp only [scaled, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [ih (by omega) (fun j hj h => hL j hj (by omega))]
    change 2*(2^t * C * _) + (B : ZMod p) = _
    by_cases h : p^a ∣ t+1
    · let j := t / p^a + 1
      have hj : (t+1) / p^a = j := Nat.succ_div_of_dvd h
      have hjt : j * p^a = t+1 := hj ▸ Nat.div_mul_cancel h
      have hjp : j < p := by rw [← hj, Nat.div_lt_iff_lt_mul hq]; simpa [pow_succ, mul_comm] using ht
      have hj0 : (j : ZMod p) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hjp
      have hbj : B*j = C := Nat.mul_left_cancel hq (by rw [← hb, ← hjt]; ring)
      have hbj' : (B : ZMod p)*j = C := by rw [← Nat.cast_mul, hbj]
      have hpow : (2 : ZMod p)^(t+1) = 2^j := by
        rw [← hjt, mul_comm j, pow_mul, ZMod.pow_card_pow]
      rw [hj, show partialMod p j = partialMod p (t / p^a) + 1 / ((j : ZMod p)*2^j) by
        simp [j, partialMod]]
      rw [mul_add]
      congr 1
      · rw [pow_succ]; ring
      · rw [hpow, ← hbj']; field_simp
    · have hB : p ∣ B := by
        by_contra hB
        apply h
        apply ((hp.out.coprime_iff_not_dvd.mpr hB).pow_left a).dvd_of_dvd_mul_left
        rw [hb]; exact dvd_mul_right _ _
      rw [Nat.succ_div_of_not_dvd h, (ZMod.natCast_eq_zero_iff B p).mpr hB, pow_succ]
      ring

lemma top_power_iff {p a C S : ℕ} {x : ℚ} (hp : p.Prime) (ha : 0 < a)
    (hC : ¬ p ∣ C) (hL : 0 < p^a*C) (he : (S : ℚ) = (p^a*C : ℕ) * x) :
    p^a ∣ x.den ↔ ¬ p ∣ S := by
  have cross := (reduced_info hL he).2
  constructor
  · rintro ⟨d, hd⟩ hS
    have e : S * d = C * x.num.natAbs := Nat.mul_left_cancel (pow_pos hp.pos a) (by
      calc
        p^a * (S*d) = S*x.den := by rw [hd]; ring
        _ = _ := cross
        _ = _ := by ring)
    have hnum := (hp.dvd_mul.mp (e ▸ dvd_mul_of_dvd_left hS d : p ∣ C * x.num.natAbs)).resolve_left hC
    have hden : p ∣ x.den := hd ▸ dvd_mul_of_dvd_left (dvd_pow_self _ ha.ne') _
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hnum hden x.reduced
  · intro hS
    apply ((hp.coprime_iff_not_dvd.mpr hS).pow_left a).dvd_of_dvd_mul_left
    rw [cross, mul_assoc]; exact dvd_mul_right _ _

/-- The highest available power of an odd prime survives exactly when the much shorter
unshifted prefix has numerator nonzero modulo that prime. -/
theorem prime_cancellation {n p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hlo : p^a ≤ n) (hhi : n < p^(a+1)) :
    p^a ∣ logDen n ↔ ¬ p ∣ (partialLogTwo (n / p^a)).num.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have h2n : ¬ p ∣ 2 := fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have h2 : (2 : ZMod p) ≠ 0 := by exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr h2n
  let L := lcmUpto n
  have v : L.factorization p = a := (factorization_lcmUpto n hp).trans
    (Nat.log_eq_of_pow_le_of_lt_pow hlo hhi)
  obtain ⟨C, hC⟩ : p^a ∣ L := (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero n)).mpr v.ge
  have hCp : ¬ p ∣ C := by
    rintro ⟨d,hd⟩
    have h : p^(a+1) ∣ L := ⟨d, by rw [hC,hd,pow_succ]; ring⟩
    have := (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero n)).mp h
    change a+1 ≤ L.factorization p at this
    omega
  have hLC : ∀ j, 0 < j → j ≤ n → j ∣ p^a*C := fun _ hj hjn => hC ▸ index_dvd_lcm hj hjn
  have ht := top_power_iff hp ha hCp (hC ▸ lcmUpto_pos n) (scaled_eq _ n hLC)
  let k := n / p^a
  have hkp : k < p := (Nat.div_lt_iff_lt_mul (pow_pos hp.pos a)).mpr (by simpa [pow_succ, mul_comm] using hhi)
  let D := lcmUpto k
  have hDp : ¬ p ∣ D := by
    rw [hp.dvd_iff_one_le_factorization (lcmUpto_ne_zero k), factorization_lcmUpto _ hp,
      Nat.log_of_lt hkp]; decide
  have hD2 : ¬ p ∣ D*2^k := fun h => (hp.dvd_mul.mp h).elim hDp (fun h => h2n (hp.dvd_of_dvd_pow h))
  have hs : (scaled D k : ℚ) = ((D*2^k : ℕ) : ℚ) * partialLogTwo k := by
    rw [scaled_eq _ _ (fun _ => index_dvd_lcm), ← shifted_partialLogTwo]
    push_cast; ring
  obtain ⟨hd, cross⟩ := reduced_info (show 0 < D*2^k by dsimp [D]; positivity [lcmUpto_pos k]) hs
  have hsnum : p ∣ scaled D k ↔ p ∣ (partialLogTwo k).num.natAbs := by
    have hh := Iff.of_eq (congrArg (p ∣ ·) cross)
    simpa only [hp.dvd_mul, hDp, (show ¬ p ∣ 2^k from fun h => h2n (hp.dvd_of_dvd_pow h)), false_or, or_false, show ¬ p ∣ (partialLogTwo k).den from fun h => hD2 (h.trans hd)] using hh
  have modL := scaled_mod h2 a C n hhi hLC
  have modD := scaled_mod h2 0 D k (by simpa using hkp) (by simpa [D] using
    (show ∀ j, 0 < j → j ≤ k → j ∣ lcmUpto k from fun _ => index_dvd_lcm))
  simp only [pow_zero, one_mul, Nat.div_one] at modD
  change p^a ∣ (logPrefix n).den ↔ ¬ p ∣ (partialLogTwo k).num.natAbs
  rw [ht, ← hsnum, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, modL, modD]
  simp [k, h2, (ZMod.natCast_eq_zero_iff C p).not.mpr hCp, (ZMod.natCast_eq_zero_iff D p).not.mpr hDp]

end NormalityChecker
