module

public import NormalityChecker.BBPShadow
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Prime.Basic

/-! A single uncancelled prime in a finite rational sum and its BBP application. -/
@[expose] public section
open Finset
namespace NormalityChecker

/-- A unique summand with a pole at `p` forces a pole in the reduced sum. -/
theorem unique_prime_denominator {ι : Type*} [DecidableEq ι] {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (f : ι → ℚ) {a : ι} (mem : a∈s) (pole : p∣(f a).den)
    (others : ∀ i∈s,i≠a → ¬p∣(f i).den) : p∣(∑ i∈s,f i).den := by
  have free (t : Finset ι) (ok : ∀ j∈t, ¬p∣(f j).den) : ¬p∣(∑ i∈t,f i).den := by
    induction t using Finset.induction_on with
    | empty => simpa using hp.not_dvd_one
    | insert i t hi ih =>
      rw [sum_insert hi]; intro e; exact (hp.dvd_mul.mp (e.trans (Rat.add_den_dvd ..))).elim
        (ok i (mem_insert_self ..)) (ih (fun j hj => ok j (mem_insert_of_mem hj)))
  have h := free (s.erase a) (fun j hj => others _ (mem_erase.mp hj).2 (mem_erase.mp hj).1)
  have sub := Rat.sub_den_dvd (∑ i∈s,f i) (∑ i∈s.erase a,f i)
  rw [show (∑ i∈s,f i)-(∑ i∈s.erase a,f i)=f a by linear_combination -(sum_erase_add s f mem)] at sub
  exact (hp.dvd_mul.mp (pole.trans sub)).resolve_right h

namespace BBP
private def offset (i : Fin 4) : ℕ := ![1,4,5,6] i
private def signedWeight (i : Fin 4) : ℤ := ![4,-2,-1,-1] i
private def part (k : ℕ) (i : Fin 4) : ℚ := (signedWeight i:ℚ)/(8*k+offset i:ℕ)
private lemma parts (k : ℕ) : (∑ i : Fin 4, part k i)=coefficient k := by
  simp [Fin.sum_univ_succ,part,offset,signedWeight,coefficient]; ring

private lemma explicit_prefix (n : ℕ) : radixPrefix n=∑ k∈range (n+1),(16:ℚ)^(n-k)*(∑ i : Fin 4,part k i) := by
  induction n with
  | zero => simp [radixPrefix,parts]
  | succ n ih =>
    rw [radixPrefix,ih,sum_range_succ (n:=n+1),mul_sum]; simp only [Nat.sub_self,pow_zero,one_mul,parts]
    congr 1; apply sum_congr rfl; intro k hk; have h := mem_range.mp hk
    rw [show n+1-k=(n-k)+1 by omega,pow_succ]; ring

/-- Primes in the top half with residue `1` or `5` modulo eight survive in the
uncorrected shifted prefix (including the coefficient at `n`). -/
theorem prefix_upper_prime {p n : ℕ} (hp : p.Prime) (lo : 4*n+3<p) (hi : p≤8*n+1)
    (residue : p%8=1 ∨ p%8=5) : p∣(radixPrefix n).den := by
  let h := p/8
  let a : Fin 4 := if p%8=1 then 0 else 2
  have ha : offset a=p%8 := by rcases residue with e|e <;> simp [a,offset,e]
  have he : 8*h+offset a=p := by rw [ha]; exact Nat.div_add_mod p 8
  let s := (range (n+1)) ×ˢ (univ : Finset (Fin 4))
  let f (t : ℕ × Fin 4) := (16:ℚ)^(n-t.1)*part t.1 t.2
  have val : radixPrefix n=∑ t∈s,f t := by rw [explicit_prefix,sum_product]; simp only [f,mul_sum]
  rw [val]; apply unique_prime_denominator hp s f (a:=(h,a)) (mem_product.mpr ⟨mem_range.mpr (by dsimp [h]; omega),mem_univ _⟩)
  · let U : ℤ := (16:ℤ)^(n-h)*signedWeight a
    have natCop : p.Coprime U.natAbs := hp.coprime_iff_not_dvd.mpr (by
      dsimp [U]; rw [Int.natAbs_mul,Int.natAbs_pow,hp.dvd_mul]; apply not_or.mpr
      refine ⟨fun d => ?_,?_⟩
      · have w := hp.dvd_of_dvd_pow d; norm_num at w
        have div2 : p∣2 := hp.dvd_of_dvd_pow (n:=4) (by simpa using w : p∣2^4)
        have := Nat.le_of_dvd (by decide : 0<2) div2; omega
      · rcases residue with e|e <;> simp [a,signedWeight,e,hp.ne_one]
        intro d; have div2 := hp.dvd_of_dvd_pow (n:=2) (show p∣2^2 from d); have := Nat.le_of_dvd (by decide : 0<2) div2; omega)
    have repr : f (h,a)=(U:ℚ)/(p:ℤ) := by dsimp [f,part,U]; rw [he]; push_cast; ring
    have eqDen := Rat.den_div_eq_of_coprime (a:=U) (b:=(p:ℤ)) (by exact_mod_cast hp.pos) (by simpa using natCop.symm)
    rw [repr,show ((U:ℚ)/(p:ℤ)).den=p by exact_mod_cast eqDen]
  · rintro ⟨k,i⟩ mem ne
    have kn := mem_range.mp (mem_product.mp mem).1
    have ob : 1≤offset i ∧ offset i≤6 := by fin_cases i <;> decide
    let m := 8*k+offset i
    have mp : 0<m := by dsimp [m]; omega
    have bound : m<2*p := by dsimp [m]; omega
    have fresh : ¬p∣m := by
      rintro ⟨t,ht⟩; have one : t=1 := by
        by_cases tz : t=0
        · simp [tz] at ht; omega
        by_contra! bad; have := Nat.mul_le_mul_left p (show 2≤t by omega); omega
      rw [one,mul_one] at ht
      have same : offset i=offset a := by dsimp [m] at ht; omega
      have injective : Function.Injective offset := by decide +kernel
      have idx := injective same
      exact ne (Prod.ext (by dsimp [m] at ht; omega) idx)
    let U : ℤ := (16:ℤ)^(n-k)*signedWeight i
    have repr : f (k,i)=Rat.divInt U m := by dsimp [f,part,U,m]; rw [Rat.divInt_eq_div]; push_cast; ring
    rw [repr]; exact fun e => fresh (e.trans (by exact_mod_cast Rat.den_dvd U (m:ℤ)))

end BBP
end NormalityChecker
