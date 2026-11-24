module

public import NormalityChecker.ProductThreeFiveFlow

/-! Persistent simultaneous loss to any fixed prime-power depth in rectangular prefixes. -/
@[expose] public section
open Finset
namespace NormalityChecker.ProductThreeFive

def crossTerm (a J j : ℕ) := a^(J-(j+1))*2^(a^J-a^(j+1))
/-- Integer numerator of the unshifted one-axis prefix on denominator a^J 2^(a^J). -/
def crossNum (a J : ℕ) := ∑ j ∈ range J, crossTerm a J j

/-- When the whole rectangle is present, its two cleared one-axis numerators
factor exactly, including the unused binary shift. -/
theorem rectangle_factor {K L n : ℕ} (hk : Nat.log 3 n=K) (hl : Nat.log 5 n=L)
    (full : 3^K+5^L ≤ n) :
    commonNum n = 2^(n-(3^K+5^L))*crossNum 3 K*crossNum 5 L := by
  have loc {v : ℕ×ℕ} (hv : v∈range K ×ˢ range L) : location v≤n := by
    obtain ⟨i,j⟩ := mem_product.mp hv
    exact (Nat.add_le_add (Nat.pow_le_pow_right (by decide) (mem_range.mp i))
      (Nat.pow_le_pow_right (by decide) (mem_range.mp j))).trans full
  rw [commonNum,active,hk,hl,filter_true_of_mem (fun _ hv => loc hv),sum_product]
  simp only [crossNum,mul_sum,sum_mul]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hp := Nat.pow_le_pow_right (by decide : 0<3) (mem_range.mp hi : i+1≤K)
  have hq := Nat.pow_le_pow_right (by decide : 0<5) (mem_range.mp hj : j+1≤L)
  have split : n-(3^(i+1)+5^(j+1)) =
      n-(3^K+5^L)+(3^K-3^(i+1))+(5^L-5^(j+1)) := by omega
  change 2^(n-(3^(i+1)+5^(j+1))) * 3^(K-(i+1))*5^(L-(j+1)) = _
  rw [split]
  simp only [crossTerm,pow_add]; ring

private def periodLen (m : ℕ) := m.totient*m.totient.totient

private lemma euler_multiple {a m s : ℕ} (cop : a.Coprime m) (dv : m.totient∣s) :
    a^s ≡ 1 [MOD m] := by
  obtain ⟨k,rfl⟩ := dv
  simpa only [pow_mul,one_pow] using (Nat.ModEq.pow_totient cop).pow k

private lemma cross_period {a m J s j : ℕ} (ap : 0<a) (ha : a.Coprime m)
    (he : a.Coprime m.totient) (hb : Nat.Coprime 2 m)
    (step : periodLen m ∣ s) (bound : s+j<J) :
    (crossTerm a J (s+j):ZMod m) = crossTerm a J j := by
  have d₁ : m.totient ∣ s := (dvd_mul_right ..).trans step
  have d₂ : m.totient.totient ∣ s := (dvd_mul_left ..).trans step
  have small := Nat.pow_le_pow_right ap (by omega : j+1≤s+j+1)
  have cap := Nat.pow_le_pow_right ap (by omega : s+j+1≤J)
  have dx : m.totient ∣ a^(s+j+1)-a^(j+1) := by
    apply (Nat.modEq_iff_dvd' small).mp
    rw [show s+j+1=s+(j+1) by omega,pow_add a s (j+1)]
    simpa only [one_mul] using ((euler_multiple he d₂).mul_right (a^(j+1))).symm
  have aUnit : (a:ZMod m)^s=1 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (euler_multiple ha d₁)
  have bUnit : (2:ZMod m)^(a^(s+j+1)-a^(j+1))=1 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (euler_multiple hb dx)
  have gap (u v w : ℕ) (uv : u≤v) (vw : v≤w) : w-u=(w-v)+(v-u) := by omega
  simp only [crossTerm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show J-(j+1)=J-(s+j+1)+s by omega,
    gap _ _ _ small cap, pow_add (a:ZMod m) _ s,
    pow_add (2:ZMod m) _ (a^(s+j+1)-a^(j+1)),aUnit,bUnit,mul_one,mul_one]

/-- A complete collection of m identical blocks vanishes modulo m. The period
uses both the unit modulus and the modulus for the binary exponent. -/
theorem crossNum_dvd {a m J : ℕ} (ap : 0<a) (ha : a.Coprime m)
    (he : a.Coprime m.totient) (hb : Nat.Coprime 2 m)
    (length : m*(m.totient*m.totient.totient) ∣ J) : m ∣ crossNum a J := by
  let T := periodLen m
  let f j : ZMod m := crossTerm a J j
  have chunks (w : ℕ) (le : w*T ≤ J) : ∑ i ∈ range (w*T), f i =
      (w:ZMod m)*(∑ i ∈ range T, f i) := by
    induction w with
    | zero => simp
    | succ w ih =>
      rw [Nat.succ_mul] at le ⊢
      rw [sum_range_add,ih (by omega : w*T≤J),Nat.cast_add_one,add_mul,one_mul]
      congr 1
      apply sum_congr rfl
      intro j hj
      exact cross_period ap ha he hb (dvd_mul_left ..) (by have := mem_range.mp hj; omega)
  obtain ⟨u,hu⟩ := length
  have len : J=(m*u)*T := by dsimp [T,periodLen]; rw [hu]; ring
  rw [← ZMod.natCast_eq_zero_iff,crossNum,Nat.cast_sum]
  change ∑ i ∈ range J, f i = 0
  conv_lhs => arg 1; rw [len]
  rw [chunks _ len.ge,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_mul]

/-- For any fixed depth, both prime powers lose that many layers on every
position in a macroscopic interval, at arbitrarily late scales. -/
theorem simultaneous_deep_loss (h A : ℕ) (hp : 0<h) :
    ∃ K L : ℕ, A≤K ∧ h≤K ∧ h≤L ∧ 3^K<5^L ∧ 4*5^L<5*3^K ∧
      ∀ n, 3^K+5^L≤n → n<3*3^K →
        (pre n).den ∣ 3^(K-h)*5^(L-h) := by
  let m := 3^h
  let r := 5^h
  let T := m*periodLen m
  let S := r*periodLen r
  have pos (v : ℕ) (hv : 0<v) : 0<v*periodLen v :=
    Nat.mul_pos hv (Nat.mul_pos (Nat.totient_pos.mpr hv) (Nat.totient_pos.mpr (Nat.totient_pos.mpr hv)))
  have tp : 0<T := pos m (pow_pos (by decide) _)
  have sp : 0<S := pos r (pow_pos (by decide) _)
  obtain ⟨K,L,late,km,lm,ratio,cap⟩ := aligned_powers (T*S) (max A h) (Nat.mul_pos tp sp)
  have Lpos : 0<L := by
    by_contra! z
    simp [Nat.eq_zero_of_le_zero z] at ratio
  have d₃ : T ∣ L := (dvd_mul_right ..).trans lm
  have d₅ : S ∣ K := (dvd_mul_left ..).trans km
  have kh := (le_max_right ..).trans late
  have lh : h≤L := (Nat.lt_pow_self (by decide : 1<3)).le.trans
    (Nat.le_of_dvd Lpos (((dvd_mul_right m (periodLen m)).trans d₃)))
  have q₃ : m ∣ crossNum 5 L := crossNum_dvd (by decide) ((by decide : Nat.Coprime 5 3).pow_right h)
    (by dsimp [m]; rw [Nat.totient_prime_pow Nat.prime_three hp]
        exact ((by decide : Nat.Coprime 5 3).pow_right _).mul_right (by decide))
    ((by decide : Nat.Coprime 2 3).pow_right h) d₃
  have q₅ : r ∣ crossNum 3 K := crossNum_dvd (by decide) ((by decide : Nat.Coprime 3 5).pow_right h)
    (by dsimp [r]; rw [Nat.totient_prime_pow Nat.prime_five hp]
        exact ((by decide : Nat.Coprime 3 5).pow_right _).mul_right (by decide))
    ((by decide : Nat.Coprime 2 5).pow_right h) d₅
  refine ⟨K,L,(le_max_left ..).trans late,kh,lh,ratio,cap,fun n lo hi => ?_⟩
  have hk := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 3^K≤n)
    (by rwa [pow_succ'] : n<3^(K+1))
  have hl := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 5^L≤n)
    (by rw [pow_succ']; omega : n<5^(L+1))
  have den : 3^K*5^L=(m*r)*(3^(K-h)*5^(L-h)) := by
    dsimp only [m,r]
    calc _ = (3^h*3^(K-h))*(5^h*5^(L-h)) := by rw [← pow_add,← pow_add,Nat.add_sub_of_le kh,Nat.add_sub_of_le lh]
         _ = _ := by ring
  have div : m*r ∣ commonNum n := by
    rw [rectangle_factor hk hl lo,mul_assoc,mul_comm (crossNum 3 K)]
    exact dvd_mul_of_dvd_right (mul_dvd_mul q₃ q₅) _
  obtain ⟨v,hv⟩ := div
  have scaled : (commonNum n:ℚ) = pre n*((3^K*5^L:ℕ):ℚ) := by
    simpa only [hk,hl,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using commonNum_eq n
  rw [hv,den] at scaled
  push_cast only [Nat.cast_mul] at scaled
  apply (reduced_info (S:=v) (by positivity) _).1
  have clear : (m:ℚ)*(r:ℚ) ≠ 0 := by dsimp [m,r]; positivity
  apply mul_left_cancel₀ clear
  push_cast only [Nat.cast_mul]
  linarith only [scaled]

/-- Check persistence against the independently defined index-one prefix. -/
theorem mixed_prefix_persistent_loss : StonehamStatements.MixedPrefixPersistentLoss := by
  intro h A hp
  simpa only [mixedPrefix_eq] using simultaneous_deep_loss h A hp

end NormalityChecker.ProductThreeFive
