module

public import NormalityChecker.ShadowDenominator
public import Mathlib.Data.Nat.Prime.Factorial

/-! Exact survival test for primes between `n` and `2*n` in the fully corrected logarithm. -/
@[expose] public section
open Finset
namespace NormalityChecker

private def upperProduct (N m : ℕ) := ∏ i∈Ico (m+1) (N+1),i
private lemma factorial_split {m N : ℕ} (h : m≤N) : m.factorial*upperProduct N m=N.factorial := by
  simpa only [upperProduct,← prod_Ico_id_eq_factorial] using
    prod_Ico_consecutive (fun i => i) (show 1≤m+1 by omega) (Nat.succ_le_succ h)

/-- The numerator of the signed `j`th correction on the common denominator `(2n)!`. -/
private def correctionNum (n j : ℕ) : ℤ := (-1)^j * j.factorial * n.factorial * upperProduct (2*n) (n+j+1)
private lemma scaled_correction {n j : ℕ} (h : j<n) :
    (correctionNum n j:ℚ)=(2*n).factorial*((-1)^j*logDifference j n) := by
  have eqn := factorial_split (show n+j+1≤2*n by omega)
  have e : ((n+j+1).factorial:ℚ)*upperProduct (2*n) (n+j+1)=(2*n).factorial := by exact_mod_cast eqn
  dsimp only [correctionNum,logDifference]; push_cast; rw [← e]; field_simp

private lemma numerator_step {n j : ℕ} (h : j+1<n) :
    correctionNum n (j+1)*(n+j+2:ℤ) = -correctionNum n j*(j+1) := by
  have e := prod_eq_prod_Ico_succ_bot (show (n+j+1)+1<2*n+1 by omega) (fun i => i)
  change upperProduct (2*n) (n+j+1)=(n+j+2)*upperProduct (2*n) (n+(j+1)+1) at e
  simp only [correctionNum,e,Nat.factorial_succ,pow_succ]; push_cast; ring

private lemma prime_free_upper {p N : ℕ} (hp : p.Prime) (top : N<2*p) : ¬p∣upperProduct N p := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff (upperProduct N p) p,upperProduct,prod_natCast]; apply prod_ne_zero_iff.mpr
  intro j hj; obtain ⟨lo,hi⟩ := mem_Ico.mp hj; apply mt (ZMod.natCast_eq_zero_iff j p).mp
  rintro ⟨t,ht⟩; have g : 2≤t := by by_contra! e; interval_cases t <;> simp_all
  have := Nat.mul_le_mul_left p g; omega

private lemma numerator_residue {n p : ℕ} (hp : p.Prime) (lo : n<p) (hi : p≤2*n) :
    ((∑ j∈range n,correctionNum n j:ℤ):ZMod p) =
      (correctionNum n (p-n-1):ZMod p)*∑ j∈range (2*n-p+1),(n.choose j:ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let l := p-n-1
  have rel : n+l+1=p := by dsimp [l]; omega
  have early {j : ℕ} (hj : j<l) : (correctionNum n j:ZMod p)=0 := by
    have div : p∣upperProduct (2*n) (n+j+1) := dvd_prod_of_mem (fun i => i) (mem_Ico.mpr ⟨by omega,by omega⟩)
    simp [correctionNum,(ZMod.natCast_eq_zero_iff ..).mpr div]
  have later {a : ℕ} (ha : l+a<n) : (correctionNum n (l+a):ZMod p)=(correctionNum n l:ZMod p)*(n.choose a:ZMod p) := by
    induction a with
    | zero => simp
    | succ a ih =>
      have h := numerator_step (show l+a+1<n by omega)
      have modE := congrArg (fun z : ℤ => (z:ZMod p)) h
      simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_neg,Int.cast_one] at modE
      have peq : (n:ZMod p)+l+1=0 := by rw [← Nat.cast_one,← Nat.cast_add,← Nat.cast_add,rel,ZMod.natCast_self]
      have chooseStep := congrArg (fun z : ℕ => (z:ZMod p)) (Nat.choose_succ_right_eq n a)
      push_cast [Nat.cast_sub (by omega : a≤n)] at chooseStep
      have unit : (a:ZMod p)+1≠0 := by rw [← Nat.cast_one,← Nat.cast_add]; exact mt (ZMod.natCast_eq_zero_iff (a+1) p).mp (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      apply mul_right_cancel₀ unit
      rw [ih (by omega)] at modE
      simp only [Nat.cast_add] at modE
      linear_combination modE - (correctionNum n (l+(a+1)):ZMod p)*peq - (correctionNum n l:ZMod p)*(n.choose a:ZMod p)*peq - (correctionNum n l:ZMod p)*chooseStep
  rw [Int.cast_sum]; change _=(correctionNum n l:ZMod p)*_
  rw [show range n=range (l+(2*n-p+1)) by congr 1; omega,sum_range_add]
  rw [sum_eq_zero (fun j hj => early (mem_range.mp hj)),zero_add,mul_sum]
  apply sum_congr rfl; intro j hj; exact later (by have := mem_range.mp hj; omega)

/-- The diagonal model retains `p` precisely when a truncated binomial sum is nonzero modulo `p`. -/
theorem logShadow_binomial_prime {n p : ℕ} (hp : p.Prime) (lo : n<p) (hi : p≤2*n) :
    p∣(logShadow n n).den ↔ (∑ j∈range (2*n-p+1),(n.choose j:ZMod p))≠0 := by
  let : Fact p.Prime := ⟨hp⟩
  let V := ∑ j∈range n,correctionNum n j
  let x := logShadow n n-logPrefix n
  have cut (k : ℕ) (h : k≤n) : ((∑ j∈range k,correctionNum n j:ℤ):ℚ)=(2*n).factorial*(logShadow k n-logPrefix n) := by
    induction k with
    | zero => simp [logShadow]
    | succ k ih => rw [sum_range_succ,Int.cast_add,ih (by omega),scaled_correction (by omega),logShadow]; ring
  let C := (p-1).factorial*upperProduct (2*n) p
  have factor : p*C=(2*n).factorial := by
    dsimp [C]; have e := Nat.factorial_succ (p-1); rw [Nat.sub_add_cancel hp.one_le] at e; rw [← mul_assoc,← e,factorial_split hi]
  have pp : 0<p*C := by rw [factor]; exact Nat.factorial_pos _
  have free : ¬p∣C := by dsimp [C]; rw [hp.dvd_mul,not_or]; exact ⟨fun e => by have := (Nat.Prime.dvd_factorial hp).mp e; have := hp.pos; omega,prime_free_upper hp (by omega)⟩
  have eqn : (V.natAbs:ℚ)=(p*C:ℕ)*|x| := by
    have e := congrArg abs (cut n le_rfl); change |(V:ℚ)|=|(↑(2*n).factorial:ℚ)*x| at e
    rw [← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)] at e; rwa [factor]
  have val := top_power_iff (a:=1) (S:=V.natAbs) (x:=|x|) (C:=C) hp (by decide) free (by simpa using pp) (by simpa using eqn)
  have ad : |x|.den=x.den := by
    rcases le_total 0 x with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,Rat.neg_den]
  have prefixFree : ¬p∣(logPrefix n).den := fun h => lo.not_ge ((Nat.Prime.dvd_factorial hp).mp (h.trans ((logDen_dvd_lcm n).trans (Nat.lcmUpto_dvd_factorial n))))
  have iff : p∣(logShadow n n).den ↔ p∣x.den := by
    constructor
    · intro h; rw [show logShadow n n=x+logPrefix n by dsimp [x]; ring] at h
      exact (hp.dvd_mul.mp (h.trans (Rat.add_den_dvd ..))).resolve_right prefixFree
    · intro h; exact (hp.dvd_mul.mp (h.trans (Rat.sub_den_dvd ..))).resolve_right prefixFree
  have l : n+(p-n-1)+1=p := by omega
  have unit : (correctionNum n (p-n-1):ZMod p)≠0 := by
    simp only [correctionNum,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast,l]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) _) _) _
    · exact mt (ZMod.natCast_eq_zero_iff _ p).mp (by rw [Nat.Prime.dvd_factorial hp]; omega)
    · exact mt (ZMod.natCast_eq_zero_iff _ p).mp (by rw [Nat.Prime.dvd_factorial hp]; omega)
    · exact mt (ZMod.natCast_eq_zero_iff _ p).mp (prime_free_upper hp (by omega))
  rw [pow_one,ad] at val; rw [iff,val]
  have dv : p∣V.natAbs ↔ (V:ZMod p)=0 := by rw [ZMod.intCast_zmod_eq_zero_iff_dvd,← Int.natAbs_dvd_natAbs]; rfl
  rw [dv,numerator_residue hp lo hi,mul_eq_zero]; simp [unit]

end NormalityChecker
