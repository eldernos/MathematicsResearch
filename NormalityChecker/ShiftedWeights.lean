module

public import NormalityChecker.Basic
public import Mathlib.NumberTheory.Fermat
public import Mathlib.Data.Rat.Lemmas

/-! New prime factors in prefixes with reciprocal successor weights. -/
@[expose] public section
open Finset
namespace NormalityChecker

private lemma odd_prime_square_add_one {x : ℕ} (hx : 2≤x) : ∃ p : ℕ,p.Prime ∧ p≠2 ∧ p∣x^2+1 := by
  let u := x/2
  have oddFactor (v : ℕ) (pos : 0<v) : ∃ p : ℕ, p.Prime ∧ p≠2 ∧ p∣2*v+1 := by
    obtain ⟨p,hp,div⟩ := Nat.exists_prime_and_dvd (by omega : 2*v+1≠1)
    exact ⟨p,hp,fun h => by subst p; omega,div⟩
  have hu : 0<u := by dsimp [u]; omega
  rcases (show x=2*u ∨ x=2*u+1 by dsimp [u]; omega) with h|h
  · rw [h,show (2*u)^2+1=2*(2*u^2)+1 by ring]; exact oddFactor _ (by positivity)
  · rw [h,show (2*u+1)^2+1=2*(2*(u^2+u)+1) by ring]
    obtain ⟨p,hp,ne,div⟩ := oddFactor (u^2+u) (by positivity)
    exact ⟨p,hp,ne,div.trans (dvd_mul_left ..)⟩

/-- Each odd prime at this insertion is new on the axis `m=c^i`. -/
private lemma first_occurrence {c p j : ℕ} (hp : p.Prime) (oddPrime : p≠2) (hit : p∣c^(2^j)+1) :
    ∀ i<2^j, ¬p∣c^i+1 := by
  have : Fact (2<p) := ⟨lt_of_le_of_ne hp.two_le oddPrime.symm⟩
  have : Fact p.Prime := ⟨hp⟩
  have minus {m : ℕ} (h : p∣c^m+1) : (c:ZMod p)^m = -1 := by
    rw [eq_neg_iff_add_eq_zero]; exact_mod_cast (ZMod.natCast_eq_zero_iff ..).mpr h
  have ord : orderOf (c:ZMod p)=2^(j+1) := by
    apply orderOf_eq_prime_pow
    · rw [minus hit]; exact ZMod.neg_one_ne_one
    · rw [pow_succ,pow_mul,minus hit,neg_one_sq]
  intro i small div
  by_cases iz : i=0
  · subst i; simp only [pow_zero] at div; exact oddPrime ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp div)
  have h := orderOf_dvd_of_pow_eq_one (show (c:ZMod p)^(i*2)=1 by rw [pow_mul,minus div,neg_one_sq])
  rw [ord,pow_succ] at h; have := Nat.le_of_dvd (by omega : 0 < i * 2) h; omega

/-- Shifted prefix at the insertion `n=c^t` for the weight `1/(m+1)`.
Multiplication by the base to that position leaves nonnegative integer exponents. -/
def successorPrefix (b c t : ℕ) : ℚ :=
  ∑ i∈range (t+1), (b:ℚ)^(c^t-c^i) / ((c^i+1:ℕ):ℚ)

/-- The reduced shifted prefix has an unbounded prime divisor for every `c≥2`
and every base. It cannot satisfy a fixed-prime-support condition throughout. -/
theorem successor_prefix_new_prime {c : ℕ} (hc : 2≤c) (b j : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 2^(j+2)<p ∧ p∣(successorPrefix b c (2^(j+1))).den := by
  let t := 2^(j+1)
  obtain ⟨p,hp,odd,hit⟩ := odd_prime_square_add_one (show 2≤c^(2^j) from hc.trans (Nat.le_self_pow (by positivity) _))
  have dvd : p∣c^t+1 := by simpa [t,pow_succ 2 j,pow_mul] using hit
  have fresh := first_occurrence hp odd dvd
  obtain ⟨a,ha⟩ := Nat.pow_pow_add_primeFactors_one_lt hp odd dvd
  have high : 2^(j+2)<p := by
    have ha' : 0<a := by by_contra! hz; have := hp.two_le; simp [Nat.eq_zero_of_le_zero hz] at ha; omega
    rw [ha]; exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_left (2^(j+2)) ha')
  let f (i : ℕ) : ℚ := (b:ℚ)^(c^t-c^i)/((c^i+1:ℕ):ℚ)
  have old : ∀ l≤t, ¬p∣(∑ i∈range l,f i).den := by
    intro l; induction l with
    | zero => simp [hp.not_dvd_one]
    | succ l ih =>
      intro le; rw [sum_range_succ]; intro q
      have last : (f l).den ∣ c^l+1 := by
        have d := Rat.mul_den_dvd ((b:ℚ)^(c^t-c^l)) (((c^l+1:ℕ):ℚ)⁻¹)
        simpa only [f,div_eq_mul_inv,← Nat.cast_pow,Rat.den_natCast,one_mul,Rat.inv_natCast_den_of_pos (Nat.succ_pos _)] using d
      exact (hp.dvd_mul.mp (q.trans (Rat.add_den_dvd ..))).elim (ih (by omega)) (fun e => fresh l le (e.trans last))
  have newest : (f t).den=c^t+1 := by
    simp only [f,Nat.sub_self,pow_zero,one_div,Rat.inv_natCast_den_of_pos (Nat.succ_pos _)]
  let prev := ∑ i∈range t,f i
  have total : successorPrefix b c t=prev+f t := sum_range_succ ..
  have sub := Rat.sub_den_dvd (successorPrefix b c t) prev
  rw [show successorPrefix b c t-prev=f t by rw [total]; ring,newest] at sub
  exact ⟨p,hp,high,(hp.dvd_mul.mp (dvd.trans sub)).resolve_right (old t le_rfl)⟩

end NormalityChecker
