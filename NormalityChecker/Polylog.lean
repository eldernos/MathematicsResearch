module

public import NormalityChecker.PrimeCancellation

@[expose] public section
open Finset Nat

namespace NormalityChecker.Polylog

def partialSum (b s n : ℕ) : ℚ :=
  ∑ i ∈ range n, 1 / (((i:ℚ)+1)^s * (b:ℚ)^(i+1))

def shifted (b s : ℕ) : ℕ → ℚ
  | 0 => 0
  | n+1 => b * shifted b s n + 1 / ((n:ℚ)+1)^s

theorem shifted_eq {b : ℕ} (hb : 0 < b) (s n : ℕ) :
    (b:ℚ)^n * partialSum b s n = shifted b s n := by
  induction n with
  | zero => simp [partialSum, shifted]
  | succ n ih =>
    simp only [partialSum, sum_range_succ, mul_add, shifted] at *
    rw [_root_.pow_succ', mul_assoc, ih]
    congr 1
    field_simp

private def scaled (b s L : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => b * scaled b s L t + (L/(t+1))^s

private lemma scaled_eq (b s L t : ℕ) (hL : ∀ j, 0 < j → j ≤ t → j ∣ L) :
    (scaled b s L t : ℚ) = (L:ℚ)^s * shifted b s t := by
  induction t with
  | zero => simp [scaled, shifted]
  | succ t ih =>
    have he := congrArg (fun z : ℕ => (z:ℚ)) (Nat.div_mul_cancel (hL (t+1) (by omega) le_rfl))
    push_cast at he
    simp only [scaled, shifted, Nat.cast_add, Nat.cast_pow, Nat.cast_mul,
      ih (fun j hj h => hL j hj (by omega))]
    rw [mul_add]
    congr 1
    · ring
    · rw [← he, mul_pow]; field_simp

def denominator (b s n : ℕ) : ℕ := (shifted b s n).den

theorem denominator_dvd (b s n : ℕ) : denominator b s n ∣ (lcmUpto n)^s := by
  apply (reduced_info (S := scaled b s (lcmUpto n) n) (pow_pos (lcmUpto_pos n) s) _).1
  exact_mod_cast scaled_eq b s (lcmUpto n) n (fun _ => index_dvd_lcm)

theorem denominator_zero_order (b n : ℕ) : denominator b 0 n = 1 :=
  Nat.dvd_one.mp (by simpa using denominator_dvd b 0 n)

private def shortMod (p b s : ℕ) [Fact p.Prime] : ℕ → ZMod p
  | 0 => 0
  | j+1 => shortMod p b s j + 1 / (((j:ZMod p)+1)^s * (b:ZMod p)^(j+1))

private lemma scaled_mod {p b s : ℕ} [hp : Fact p.Prime]
    (hb : (b:ZMod p) ≠ 0) (hs : 0 < s) (a C t : ℕ)
    (ht : t < p^(a+1)) (hL : ∀ j, 0 < j → j ≤ t → j ∣ p^a*C) :
    (scaled b s (p^a*C) t : ZMod p) = (b:ZMod p)^t * (C:ZMod p)^s * shortMod p b s (t / p^a) := by
  have hq : 0 < p^a := pow_pos hp.out.pos _
  induction t with
  | zero => simp [scaled, shortMod]
  | succ t ih =>
    let B := p^a*C / (t+1)
    have he : B*(t+1) = p^a*C := Nat.div_mul_cancel (hL _ (by omega) le_rfl)
    simp only [scaled, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    rw [ih (by omega) (fun j hj h => hL j hj (by omega))]
    change (b:ZMod p)*(_ * (C:ZMod p)^s * _) + (B:ZMod p)^s = _
    by_cases h : p^a ∣ t+1
    · let j := t / p^a + 1
      have hj : (t+1) / p^a = j := Nat.succ_div_of_dvd h
      have hjt : j * p^a = t+1 := hj ▸ Nat.div_mul_cancel h
      have hjp : j < p := by rw [← hj, Nat.div_lt_iff_lt_mul hq]; simpa [pow_succ, mul_comm] using ht
      have hj0 : (j:ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff j p).not.mpr
        (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hjp)
      have hbj : B*j = C := Nat.mul_left_cancel hq (by rw [← he, ← hjt]; ring)
      have hbj' : (B:ZMod p)*j = C := by rw [← Nat.cast_mul, hbj]
      have hpow : (b:ZMod p)^(t+1) = b^j := by
        rw [← hjt, mul_comm j, pow_mul, ZMod.pow_card_pow]
      rw [hj, show shortMod p b s j = shortMod p b s (t/p^a) + 1/((j:ZMod p)^s * (b:ZMod p)^j) by simp [j,shortMod], mul_add]
      congr 1
      · rw [pow_succ]; ring
      · rw [hpow, ← hbj',mul_pow]; field_simp
    · have hB : p ∣ B := by
        by_contra hB
        apply h
        apply ((hp.out.coprime_iff_not_dvd.mpr hB).pow_left a).dvd_of_dvd_mul_left
        rw [he]; exact dvd_mul_right _ _
      rw [Nat.succ_div_of_not_dvd h, (ZMod.natCast_eq_zero_iff B p).mpr hB,
        zero_pow hs.ne', pow_succ]; ring

private lemma lcm_split {n p a : ℕ} (hp : p.Prime) (hlo : p^a ≤ n) (hhi : n < p^(a+1)) :
    ∃ C : ℕ, lcmUpto n = p^a*C ∧ ¬ p ∣ C := by
  have v := (factorization_lcmUpto n hp).trans (Nat.log_eq_of_pow_le_of_lt_pow hlo hhi)
  obtain ⟨C,hC⟩ := (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero n)).mpr v.ge
  refine ⟨C,hC,?_⟩
  rintro ⟨d,hd⟩
  have h : p^(a+1) ∣ lcmUpto n := ⟨d, by rw [hC,hd,pow_succ]; ring⟩
  have := (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero n)).mp h
  omega

private lemma top_iff {n p a b s C : ℕ} (hp : p.Prime) (ha : 0 < a) (hs : 0 < s)
    (hC : lcmUpto n = p^a*C) (hc : ¬ p ∣ C) :
    p^(a*s) ∣ denominator b s n ↔ ¬ p ∣ scaled b s (p^a*C) n := by
  have he : p^(a*s)*C^s = (lcmUpto n)^s := by rw [hC,mul_pow,pow_mul]
  apply top_power_iff hp (Nat.mul_pos ha hs) (fun h => hc (hp.dvd_of_dvd_pow h))
  · rw [he]; positivity [lcmUpto_pos n]
  · rw [he, ← hC, Nat.cast_pow]
    exact scaled_eq _ _ _ _ (fun _ => index_dvd_lcm)

theorem prime_cancellation {n p a b s : ℕ} (hp : p.Prime) (hb : ¬ p ∣ b)
    (hs : 0 < s) (ha : 0 < a) (hlo : p^a ≤ n) (hhi : n < p^(a+1)) :
    p^(a*s) ∣ denominator b s n ↔ ¬ p ∣ (partialSum b s (n/p^a)).num.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have hb0 := (ZMod.natCast_eq_zero_iff b p).not.mpr hb
  have hbpos : 0 < b := Nat.pos_of_ne_zero fun h => hb (h ▸ dvd_zero p)
  obtain ⟨C,hC,hc⟩ := lcm_split hp hlo hhi
  let k := n/p^a
  have hkp : k < p := (Nat.div_lt_iff_lt_mul (pow_pos hp.pos a)).mpr (by simpa [pow_succ,mul_comm] using hhi)
  let D := lcmUpto k
  have hD : ¬ p ∣ D := by
    rw [hp.dvd_iff_one_le_factorization (lcmUpto_ne_zero k), factorization_lcmUpto _ hp, Nat.log_of_lt hkp]; decide
  have hDb : ¬ p ∣ D^s*b^k := fun h => (hp.dvd_mul.mp h).elim
    (fun h => hD (hp.dvd_of_dvd_pow h)) (fun h => hb (hp.dvd_of_dvd_pow h))
  have he : (scaled b s D k : ℚ) = ((D^s*b^k : ℕ):ℚ)*partialSum b s k := by
    rw [scaled_eq _ _ _ _ (fun _ => index_dvd_lcm), ← shifted_eq hbpos]; push_cast; ring
  obtain ⟨hd,cross⟩ := reduced_info (by dsimp [D]; positivity [lcmUpto_pos k] : 0 < D^s*b^k) he
  have he' : p ∣ scaled b s D k ↔ p ∣ (partialSum b s k).num.natAbs := by
    have hh := Iff.of_eq (congrArg (p ∣ ·) cross)
    rw [hp.dvd_mul, hp.dvd_mul, or_iff_left (fun h => hDb (h.trans hd)), or_iff_right hDb] at hh
    exact hh
  have hL := scaled_mod hb0 hs a C n hhi (fun _ hj hjn => hC ▸ index_dvd_lcm hj hjn)
  have hD' := scaled_mod hb0 hs 0 D k (by simpa using hkp) (by simpa [D] using
    (show ∀ j, 0 < j → j ≤ k → j ∣ lcmUpto k from fun _ => index_dvd_lcm))
  simp only [pow_zero,one_mul,Nat.div_one] at hD'
  change _ ↔ ¬ p ∣ (partialSum b s k).num.natAbs
  rw [top_iff hp ha hs hC hc, ← he', ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, hL,hD']
  simp [k,hb0,(ZMod.natCast_eq_zero_iff C p).not.mpr hc,(ZMod.natCast_eq_zero_iff D p).not.mpr hD]

/-- At primes dividing the radix only the last term can contribute at the top layer. -/
theorem prime_cancellation_of_dvd_base {n p a b s : ℕ} (hp : p.Prime) (hb : p ∣ b)
    (hs : 0 < s) (ha : 0 < a) (hlo : p^a ≤ n) (hhi : n < p^(a+1)) :
    p^(a*s) ∣ denominator b s n ↔ p^a ∣ n := by
  obtain ⟨C,hC,hc⟩ := lcm_split hp hlo hhi
  rw [top_iff hp ha hs hC hc]
  cases n with
  | zero => exact False.elim ((pow_pos hp.pos a).not_ge hlo)
  | succ t =>
    let B := p^a*C / (t+1)
    have he : B*(t+1) = p^a*C := Nat.div_mul_cancel (hC ▸ index_dvd_lcm (by omega) le_rfl)
    change (¬ p ∣ b*_ + B^s) ↔ _
    rw [Nat.dvd_add_right (dvd_mul_of_dvd_left hb _), show p ∣ B^s ↔ p ∣ B from ⟨hp.dvd_of_dvd_pow, fun h => h.trans (dvd_pow_self B hs.ne')⟩]
    constructor
    · intro h
      apply ((hp.coprime_iff_not_dvd.mpr h).pow_left a).dvd_of_dvd_mul_left
      rw [he]; exact dvd_mul_right _ _
    · rintro ⟨j,hj⟩ hB
      have h : B*j=C := Nat.mul_left_cancel (pow_pos hp.pos a) (by rw [← he,hj]; ring)
      exact hc (h ▸ dvd_mul_of_dvd_left hB j)

theorem num_pos {b s k : ℕ} (hb : 0 < b) (hk : 0 < k) :
    0 < (partialSum b s k).num.natAbs := by
  have h : 0 < partialSum b s k :=
    Finset.sum_pos (fun i _ => by positivity) (nonempty_range_iff.mpr hk.ne')
  exact Int.natAbs_pos.mpr (Rat.num_pos.mpr h).ne'

theorem num_bound {b : ℕ} (hb : 2 ≤ b) (s k : ℕ) :
    (partialSum b s k).num.natAbs ≤ (lcmUpto k)^s*b^k := by
  let D := lcmUpto k
  have hpos : 0 < D^s*b^k := by dsimp [D]; positivity [lcmUpto_pos k]
  have he : (scaled b s D k : ℚ) = ((D^s*b^k : ℕ):ℚ)*partialSum b s k := by
    rw [scaled_eq _ _ _ _ (fun _ => index_dvd_lcm), ← shifted_eq (by omega : 0<b)]
    push_cast; ring
  obtain ⟨hd,cross⟩ := reduced_info hpos he
  have bound (n : ℕ) : shifted b s n ≤ (b:ℚ)^n-1 := by
    induction n with
    | zero => simp [shifted]
    | succ n ih =>
      have h1 : 1/((n:ℚ)+1)^s ≤ 1 := (div_le_one (by positivity)).mpr
        (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℚ) n]))
      rw [shifted,pow_succ]
      have h2 : (2:ℚ) ≤ b := by exact_mod_cast hb
      nlinarith [mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg (α:=ℚ) b)]
  have hscaled : scaled b s D k ≤ D^s*b^k := by
    exact_mod_cast (scaled_eq b s D k (fun _ => index_dvd_lcm)).trans_le
      (mul_le_mul_of_nonneg_left (by linarith [bound k] : shifted b s k ≤ (b:ℚ)^k) (by positivity))
  apply Nat.le_of_mul_le_mul_left _ hpos
  rw [← cross]
  exact Nat.mul_le_mul hscaled (Nat.le_of_dvd hpos hd)

end NormalityChecker.Polylog
