module

public import NormalityChecker.DiscrepancyChecker

/-! Maximal interval discrepancy for finite prime supports. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

private lemma misses_interior {y δ : ℝ} {z : ℤ} (close : |y-z|<δ) (small : δ<1/2) :
    ¬(δ≤Int.fract y ∧ Int.fract y<1-δ) := by
  rw [← Int.fract_sub_intCast y z]
  have h := abs_lt.mp close
  by_cases pos : 0≤y-z
  · rw [Int.fract_eq_self.mpr ⟨pos,by linarith⟩]; grind
  · rw [← Int.fract_add_one,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]; grind

/-- With only base primes, the orbit spends density zero in every compact
subinterval of `(0,1)`. This includes the empty support. -/
theorem interior_frequency_zero {b s : ℕ} (A : Finset ℕ) (hb : 2≤b) (hs : 0<s)
    (basePrimes : ∀ p∈A,p∣b) {δ : ℝ} (pos : 0<δ) (small : δ<1/2) :
    Tendsto (frequency (shift b (powerValue b s A)) δ (1-δ)) atTop (𝓝 0) := by
  classical
  let x := powerValue b s A
  let P := powerShifted b s A
  let f (_ : Unit) (n : ℕ) : ℂ := if δ≤shift b x n ∧ shift b x n<1-δ then 1 else 0
  obtain ⟨K,tail⟩ := eventually_atTop.mp ((power_tail hb hs A).abs.eventually_lt_const (by simpa using pos : |(0:ℝ)|<δ))
  have h := transfer_clean_blocks (c:=1) (s:=s) A hb (by decide) (by simpa using basePrimes) f
    (fun _ _ => by dsimp [f]; split <;> simp) (fun _ => 0) (fun _ => le_rfl) (by
      intro η hη; refine ⟨K,fun B n hn _ div _ orbit _ => ?_⟩
      obtain ⟨t,ht⟩ := div
      have integral : (P n).den=1 := Nat.dvd_one.mp (by simpa [P] using ht)
      have eqn : P n=((P n).num:ℤ) := by simpa [integral] using (P n).num_div_den.symm
      have vanish (i : ℕ) (hi : i∈range B) : f () (n+i)=0 := by
        have rat : P (n+i)=((b:ℤ)^i*(P n).num:ℤ) := by
          calc P (n+i) = (b:ℚ)^i*P n := orbit i (mem_range.mp hi)
               _ = _ := by
                 conv_lhs => rw [eqn]
                 push_cast
                 rfl
        have realEq : (P (n+i):ℝ)=((b:ℤ)^i*(P n).num:ℤ) := by exact_mod_cast rat
        have near : |(b:ℝ)^(n+i)*x-(P (n+i):ℝ)|<δ := tail _ (hn.trans (Nat.le_add_right ..))
        rw [realEq] at near; exact ite_eq_right (misses_interior near small)
      rw [sum_eq_zero vanish]; simp; positivity)
  rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨N,allN⟩ := eventually_atTop.mp (h (ε/2) (by positivity))
  refine ⟨N+1,fun n hn => ?_⟩
  have H := allN n (by omega) (); simp only [f,sum_boole,Complex.norm_natCast,sum_const_zero,add_zero] at H
  have np : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (frequency_bounds ..).1]
  apply (div_lt_iff₀ np).mpr
  exact H.trans_lt (mul_lt_mul_of_pos_right (by linarith : ε/2<ε) np)

/-- Maximal discrepancy when all support primes divide the radix. -/
theorem maximal_of_base_primes {b s : ℕ} (A : Finset ℕ) (hb : 2≤b) (hs : 0<s)
    (basePrimes : ∀ p∈A,p∣b) : limsup (radixDiscrepancy b (powerValue b s A)) atTop=1 := by
  let x := powerValue b s A
  have h := radix_discrepancy_bounds b x
  apply le_antisymm (limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (h N).1)) (.of_forall fun N => (h N).2))
  apply le_limsup_of_le (isBoundedUnder_of_eventually_le (.of_forall fun N => (h N).2))
  intro u ev; by_contra! lt
  let δ := min ((1-u)/4) (1/4)
  have pos : 0<δ := lt_min (by linarith) (by norm_num)
  have tiny : δ≤(1-u)/4 := min_le_left ..
  have small : δ<1/2 := (min_le_right ..).trans_lt (by norm_num)
  obtain ⟨N,upper,few⟩ := (ev.and ((interior_frequency_zero A hb hs basePrimes pos small).eventually_lt_const pos)).exists
  have interval := le_csSup (s:={d | ∃ a c : ℝ, 0≤a ∧ a<c ∧ c≤1 ∧ d=|frequency (shift b x) a c N-(c-a)|})
    (a:=|frequency (shift b x) δ (1-δ) N-(1-δ-δ)|) (show BddAbove _ from ⟨1,by
      rintro _ ⟨a,c,ha,l,hc,rfl⟩; have f := frequency_bounds (shift b x) a c N; rw [abs_le]; constructor <;> linarith [f.1,f.2]⟩)
    ⟨δ,1-δ,pos.le,by linarith,by linarith,rfl⟩
  change _ ≤ radixDiscrepancy b x N at interval
  have lower := (abs_le.mp (interval.trans upper)).1
  change frequency (shift b x) δ (1-δ) N<δ at few; linarith

/-- Complete classification of maximal discrepancy for finite prime support. -/
theorem maximal_discrepancy_iff {b s : ℕ} (A : Finset ℕ) (hb : 2≤b) (hs : 0<s) (primes : ∀ p∈A,p.Prime) :
    limsup (radixDiscrepancy b (powerValue b s A)) atTop=1 ↔ ∀ p∈A,p∣b := by
  refine ⟨?_,maximal_of_base_primes A hb hs⟩
  intro maximal p mem; by_contra h
  have hp := primes p mem
  have H := discrepancy_le_of_support_prime hb hs hp (notMem_erase p A) (hp.coprime_iff_not_dvd.mpr h).symm
    (fun r hr => primes r (mem_of_mem_erase hr))
  rw [insert_erase mem,maximal] at H
  have pp : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  linarith [one_div_pos.mpr (sub_pos.mpr pp)]

/-- Every finite prime support containing two gives normality in every odd base. -/
theorem normal_of_two_mem {b s : ℕ} (A : Finset ℕ) (hb : 2≤b) (hs : 0<s) (primes : ∀ p∈A,p.Prime)
    (mem : 2∈A) (oddBase : ¬2∣b) : NormalIn b (powerValue b s A) := by
  apply normal_of_radix_limsup_zero hb
  have H := discrepancy_le_of_support_prime hb hs Nat.prime_two (notMem_erase 2 A) (Nat.prime_two.coprime_iff_not_dvd.mpr oddBase).symm
    (fun r hr => primes r (mem_of_mem_erase hr))
  norm_num [insert_erase mem] at H
  exact H

end NormalityChecker.LocalizedSupport
