module

public import NormalityChecker.LogShadow
public import Mathlib.Data.Nat.Choose.Central

/-! Consecutive diagonal approximations of the logarithm differ by an explicit
inverse central binomial coefficient after one doubling. -/
@[expose] public section
namespace NormalityChecker

/-- The magnitude of the diagonal step is `3 / (2 * (2*n+1) * centralBinom n)`. -/
theorem logShadow_diagonal_step (n : ℕ) :
    (logShadow (n+1) (n+1)-2*logShadow n n) * (2*(2*(n:ℚ)+1)*n.centralBinom) =
      (-1:ℚ)^n*3 := by
  have beta : logDifference n (n+1) = logDifference n n / 2 := by
    unfold logDifference
    rw [show n+1+n+1=(n+n+1)+1 by omega,Nat.factorial_succ (n+n+1),Nat.factorial_succ n]
    push_cast; field_simp; ring
  have fac := Nat.choose_mul_factorial_mul_factorial (show n≤2*n by omega)
  rw [show 2*n-n=n by omega,← Nat.centralBinom_eq_two_mul_choose] at fac
  have inv : logDifference n n * ((2*(n:ℚ)+1)*n.centralBinom)=1 := by
    unfold logDifference
    rw [show n+n+1=2*n+1 by omega,Nat.factorial_succ (2*n),← fac]
    push_cast; field_simp [Nat.factorial_ne_zero, Nat.centralBinom_pos n |>.ne']
  rw [logShadow,add_sub_right_comm,logShadow_step,beta]
  linear_combination 3*(-1:ℚ)^n*inv

/-- The denominator of the step constrains the least common multiple of the two
individual denominators, including prime powers and the possible loss at three. -/
theorem logShadow_diagonal_lcm (n : ℕ) :
    2*(2*n+1)*n.centralBinom ∣
      3*Nat.lcm (logShadow n n).den (logShadow (n+1) (n+1)).den := by
  let x := logShadow n n
  let y := logShadow (n+1) (n+1)
  let L := Nat.lcm x.den y.den
  let D := 2*(2*n+1)*n.centralBinom
  have clear (q : ℚ) (h : q.den ∣ L) : ∃ z : ℤ, (L:ℚ)*q=z := by
    obtain ⟨v,hv⟩ := h
    exact ⟨v*q.num,by rw [hv]; push_cast; rw [mul_right_comm, Rat.den_mul_eq_num, mul_comm]⟩
  obtain ⟨a,ha⟩ := clear x (Nat.dvd_lcm_left ..)
  obtain ⟨b,hb⟩ := clear y (Nat.dvd_lcm_right ..)
  have step : (y-2*x)*(D:ℚ)=(-1:ℚ)^n*3 := by simpa [D,x,y] using logShadow_diagonal_step n
  have cross : (D:ℤ)*(b-2*a)=(-1:ℤ)^n*(3*L) := by
    apply (Int.cast_injective (α:=ℚ)); push_cast
    linear_combination (L:ℚ)*step - D*hb + 2*D*ha
  have dvd : (D:ℤ) ∣ (-1:ℤ)^n*(3*L) := ⟨b-2*a,cross.symm⟩
  have natural := Int.natCast_dvd.mp dvd
  simpa [Int.natAbs_mul,Int.natAbs_pow] using natural

/-- Every adjacent pair contains an exponentially large denominator, even at
prescribed starts. This elementary bound works at each finite index. -/
theorem logShadow_diagonal_max (n : ℕ) :
    2^n ≤ max (logShadow n n).den (logShadow (n+1) (n+1)).den := by
  let a := (logShadow n n).den
  let b := (logShadow (n+1) (n+1)).den
  have ap : 0<a := Rat.pos _
  have bp : 0<b := Rat.pos _
  by_cases zero : n=0
  · rw [zero,pow_zero]; exact (logShadow 0 0).pos.trans_le (Nat.le_max_left ..)
  have lb := Nat.le_of_dvd (Nat.mul_pos (by decide : 0<3) (Nat.lcm_pos ap bp)) (logShadow_diagonal_lcm n)
  change 2*(2*n+1)*n.centralBinom ≤ 3*Nat.lcm a b at lb
  have cap := Nat.le_of_dvd (Nat.mul_pos ap bp) (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
  have scale : 3*4^n ≤ 2*(2*n+1)*n.centralBinom := by
    by_cases hn : 4≤n
    · have bound := Nat.four_pow_lt_mul_centralBinom n hn
      nlinarith only [bound,Nat.zero_le n.centralBinom]
    · have pos := Nat.pos_of_ne_zero zero
      interval_cases n <;> decide
  have hs : 4^n≤a*b := by omega
  have prod := Nat.mul_le_mul (Nat.le_max_left a b) (Nat.le_max_right a b)
  rw [show (4:ℕ)^n=2^n*2^n by rw [← mul_pow]; rfl] at hs
  by_contra! h
  change max a b < 2^n at h
  nlinarith only [hs,prod,Nat.mul_self_lt_mul_self h]

end NormalityChecker
