module

public import NormalityChecker.PrimeCancellation

/-! The two largest powers of five in the binary localized logarithm with support
`{2,5}`. Keeping both layers detects the cancellation missed by reduction mod 5. -/
@[expose] public section
open Finset
namespace NormalityChecker.LocalizedFive

/-- Binary shift of all terms indexed by `m = 2^a * 5^j ≤ n`. -/
def shiftedPrefix (n : ℕ) : ℚ :=
  ∑ j ∈ range (Nat.log 5 n + 1), ∑ a ∈ range (Nat.log 2 n + 1),
    let m := 2^a * 5^j
    if m ≤ n then (2:ℚ)^(n-m)/m else 0

private def entry (n k j a : ℕ) : ℕ :=
  let m := 2^a * 5^j
  if m ≤ n then 2^(2*n-(m+a)) * 5^(k-j) else 0

private def numerator (n k : ℕ) : ℕ :=
  ∑ j ∈ range (k+1), ∑ a ∈ range (Nat.log 2 n + 1), entry n k j a

private lemma clear_denominator (n k : ℕ) (hk : Nat.log 5 n = k) :
    (numerator n k : ℚ) = (2:ℚ)^n * 5^k * shiftedPrefix n := by
  unfold numerator shiftedPrefix
  rw [hk]; simp only [Nat.cast_sum]; rw [mul_sum]
  apply sum_congr rfl; intro j hj; rw [mul_sum]; apply sum_congr rfl; intro a ha
  let m := 2^a * 5^j
  by_cases hm : m ≤ n
  · have hj' : j ≤ k := by simpa using mem_range.mp hj
    have ha' : a ≤ n := (Nat.le_of_lt_succ (mem_range.mp ha)).trans (Nat.log_le_self ..)
    have e2 : 2*n-(m+a)+a = n+(n-m) := by omega
    have e5 : k-j+j=k := Nat.sub_add_cancel hj'
    change ((if m≤n then 2^(2*n-(m+a)) * 5^(k-j) else 0 : ℕ):ℚ) =
      2^n*5^k*(if m≤n then (2:ℚ)^(n-m)/m else 0)
    rw [ite_eq_left hm, ite_eq_left hm, mul_div_assoc', eq_div_iff (by dsimp [m]; positivity)]
    simp only [m,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at *
    have e := congrArg (fun z : ℕ => (2:ℚ)^z) e2
    have d := congrArg (fun z : ℕ => (5:ℚ)^z) e5
    simp only [pow_add] at e d
    linear_combination (5:ℚ)^(k-j)*5^j*e + 2^n*2^(n-2^a*5^j)*d
  · simp only [entry]; simp [show ¬ 2^a*5^j ≤ n from hm]

/-- Residue after discarding the common unit `2^(2*n)` in the cleared numerator. -/
private def digitResidue (a : ℕ) : ZMod 25 := 13^a * 18^(2^a)

private lemma inverse_power (j : ℕ) : (13:ZMod 25)^(5^(j+1)) = 18 := by
  induction j with
  | zero => decide
  | succ j ih => rw [pow_succ (5:ℕ) (j+1),pow_mul,ih]; decide

private lemma entry_mod (n k j a : ℕ) (hj : 0<j) :
    (entry n k j a : ZMod 25) = (2:ZMod 25)^(2*n) *
      (if 2^a*5^j ≤ n then digitResidue a * 5^(k-j) else 0) := by
  unfold entry
  by_cases h : 2^a*5^j ≤ n
  · rw [ite_eq_left h,ite_eq_left h]; push_cast
    have ha : a ≤ n := by
      have hle := Nat.le_mul_of_pos_right (2^a) (pow_pos (by decide : 0<5) j)
      exact (Nat.lt_two_pow_self.le.trans hle).trans h
    let m := 2^a*5^j
    have H : (2:ZMod 25)^(2*n-(m+a)) = 2^(2*n)*13^(m+a) := by
      conv_rhs => rw [← Nat.sub_add_cancel (show m+a ≤ 2*n by dsimp [m]; omega),pow_add]
      rw [mul_assoc,← mul_pow,show (2:ZMod 25)*13=1 by decide,one_pow,mul_one]
    rw [H,pow_add (13:ZMod 25),show (13:ZMod 25)^m = 18^(2^a) by
      dsimp [m]; rw [Nat.mul_comm,pow_mul]; obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'; rw [inverse_power]]
    unfold digitResidue; ring
  · simp [h]

private def row (u d : ℕ) : ZMod 25 :=
  ∑ a ∈ range 5, if 2^a*d ≤ u then digitResidue a else 0

/-- For `5 ≤ u < 25` the only nonzero residues are 13, 23, 10, 15 and 9. -/
private lemma cells : ∀ u : Fin 25, 5 ≤ u.val →
    (5*row u 1 + row u 5).val =
      (if u.val < 8 then 13 else if u.val < 10 then 23 else if u.val < 16 then 10
       else if u.val < 20 then 15 else 9) := by decide

private lemma numerator_mod {n k : ℕ} (hlo : 5^(k+2) ≤ n) (hhi : n < 5^(k+3)) :
    let u := n / 5^(k+1)
    (numerator n (k+2) : ZMod 25) = 2^(2*n)*(5*row u 1 + row u 5) := by
  let u := n/5^(k+1)
  have hbase : 0 < 5^(k+1) := by positivity
  have hu : u < 25 := (Nat.div_lt_iff_lt_mul hbase).mpr (by convert hhi using 1; ring)
  have hlog : 5 ≤ Nat.log 2 n + 1 := by
    have h16 : 2^4 ≤ n := le_trans (by norm_num) ((Nat.pow_le_pow_right (by decide : 0<5) (by omega : 2≤k+2)).trans hlo)
    have := Nat.le_log_of_pow_le (by decide : 1<2) h16; omega
  let layer := fun j => ∑ a ∈ range (Nat.log 2 n + 1), (entry n (k+2) j a : ZMod 25)
  have low : ∑ j ∈ range (k+1), layer j = 0 := by
    apply sum_eq_zero; intro j hj; apply sum_eq_zero; intro a _
    have hle : 2 ≤ k+2-j := by have := mem_range.mp hj; omega
    have hz : (5:ZMod 25)^(k+2-j)=0 := by
      rw [← Nat.sub_add_cancel hle,pow_add,show (5:ZMod 25)^2=0 by decide,mul_zero]
    simp only [entry]; split_ifs <;> push_cast <;> simp [hz]
  have top (j d : ℕ) (hj : 0<j) (hd : 0<d) (hjd : 5^j=d*5^(k+1)) :
      layer j = 2^(2*n) * (row u d * 5^(k+2-j)) := by
    have cut (a : ℕ) : 2^a*5^j ≤ n ↔ 2^a*d ≤ u := by
      rw [hjd,← mul_assoc,← Nat.le_div_iff_mul_le hbase]
    dsimp only [layer]; simp_rw [entry_mod _ _ _ _ hj,cut]
    rw [← mul_sum]; congr 1
    unfold row; rw [sum_mul]
    change _ = ∑ a ∈ range 5, (if 2^a*d ≤ u then digitResidue a else 0)*_
    simp_rw [ite_mul,zero_mul]
    symm; apply sum_subset (range_mono hlog); intro a _ ha
    have h32 := Nat.pow_le_pow_right (by decide : 0<2) (not_lt.mp (mt mem_range.mpr ha))
    have hle := Nat.le_mul_of_pos_right (2^a) hd
    rw [ite_eq_right (by norm_num at h32; omega)]
  unfold numerator; push_cast
  change (∑ j ∈ range ((k+1)+1+1), layer j) = _
  rw [sum_range_succ,sum_range_succ,low,zero_add,top (k+1) 1 (by omega) (by decide) (by simp),
    top (k+2) 5 (by omega) (by decide) (by rw [pow_succ'])]
  simp [show k+2-(k+1)=1 by omega]; ring

/-- Exact exponent of five in the reduced denominator. One factor cancels precisely
on the middle cell, and no second factor ever cancels. -/
theorem denominator_fives {n k : ℕ} (hlo : 5^(k+2) ≤ n) (hhi : n < 5^(k+3)) :
    (shiftedPrefix n).den.factorization 5 =
      if 2*5^(k+2) ≤ n ∧ n < 4*5^(k+2) then k+1 else k+2 := by
  let u := n/5^(k+1)
  let s := numerator n (k+2)
  let d := 2^n * 5^(k+2)
  let x := shiftedPrefix n
  have hbase : 0 < 5^(k+1) := by positivity
  have hu : u < 25 := (Nat.div_lt_iff_lt_mul hbase).mpr (by convert hhi using 1; ring)
  have hu' : 5 ≤ u := (Nat.le_div_iff_mul_le hbase).mpr (by simpa [pow_succ',mul_assoc] using hlo)
  have hcell := cells ⟨u,hu⟩ hu'
  let R := 5*row u 1 + row u 5
  change R.val = (if u < 8 then 13 else if u < 10 then 23 else if u < 16 then 10 else if u < 20 then 15 else 9) at hcell
  have e : (s:ZMod 25) = 2^(2*n)*R := numerator_mod hlo hhi
  have unit := ((ZMod.isUnit_iff_coprime 2 25).mpr (by decide)).pow (2*n)
  have h25 : ¬ 25 ∣ s := by
    rw [← ZMod.natCast_eq_zero_iff, e]; intro h
    have H : R = 0 := unit.mul_left_cancel (by simpa using h : (2:ZMod 25)^(2*n)*R = _*0)
    rw [H] at hcell; simp only [ZMod.val_zero] at hcell; split_ifs at hcell
  have h5 : 5 ∣ s ↔ 10 ≤ u ∧ u < 20 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let red := ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)
    have he := congrArg red e
    have hr : red R = (R.val:ZMod 5) := by
      exact (map_natCast red R.val).symm ▸ congrArg red (ZMod.natCast_zmod_val R).symm
    change red (s:ZMod 25) = red (_*R) at he
    rw [map_mul, hr, map_pow] at he
    rw [map_natCast, map_ofNat] at he
    rw [← ZMod.natCast_eq_zero_iff, he, mul_eq_zero, or_iff_right (pow_ne_zero (2*n) (by decide : (2:ZMod 5)≠0)),
      ZMod.natCast_eq_zero_iff, hcell]; split_ifs <;> omega
  have hs : s ≠ 0 := fun hz => h25 (hz ▸ dvd_zero _)
  have hp : Nat.Prime 5 := by decide
  have hsv : s.factorization 5 < 2 := by
    exact not_le.mp fun h => h25 ((hp.pow_dvd_iff_le_factorization hs).mpr h)
  have hval : s.factorization 5 ≥ 1 ↔ 10 ≤ u ∧ u < 20 := (hp.dvd_iff_one_le_factorization hs).symm.trans h5
  have hd : 0 < d := by dsimp [d]; positivity
  have eqn : (s:ℚ) = (d:ℚ)*x := by
    simpa [s,d,x] using clear_denominator n (k+2) (Nat.log_eq_of_pow_le_of_lt_pow hlo hhi)
  obtain ⟨_, cross⟩ := reduced_info hd eqn
  have hnum : x.num.natAbs ≠ 0 := by intro h; simp [h,hs,x.den_ne_zero] at cross
  have hdv : d.factorization 5 = k+2 := by
    rw [show d = 2^n*5^(k+2) from rfl,Nat.factorization_mul (by positivity) (by positivity),Finsupp.add_apply,
      Nat.factorization_pow_self hp,Nat.factorization_eq_zero_of_not_dvd (fun h => (by decide : ¬5∣2) (hp.dvd_of_dvd_pow h)),zero_add]
  have eqv := congrArg (fun i : ℕ => i.factorization 5) cross
  simp only [Nat.factorization_mul hs x.den_ne_zero,Nat.factorization_mul hd.ne' hnum,Finsupp.add_apply,hdv] at eqv
  have hden : 1 ≤ x.den.factorization 5 := by omega
  have hcop : ¬ 5 ∣ x.num.natAbs := fun h => Nat.not_coprime_of_dvd_of_dvd hp.one_lt h
    ((hp.dvd_iff_one_le_factorization x.den_ne_zero).mpr hden) x.reduced
  rw [Nat.factorization_eq_zero_of_not_dvd hcop,add_zero] at eqv
  have cell_iff : (10 ≤ u ∧ u < 20) ↔ (2*5^(k+2) ≤ n ∧ n < 4*5^(k+2)) := by
    dsimp [u]; rw [Nat.le_div_iff_mul_le hbase,Nat.div_lt_iff_lt_mul hbase]
    rw [show 10*5^(k+1)=2*5^(k+2) by ring,show 20*5^(k+1)=4*5^(k+2) by ring]
  change x.den.factorization 5 = _
  split_ifs with h <;> omega

end NormalityChecker.LocalizedFive
