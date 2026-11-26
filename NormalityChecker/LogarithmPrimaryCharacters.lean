module

public import NormalityChecker.StrideDenominatorRate
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-! Genuine simultaneous prime-primary components of the shifted logarithm prefix. -/
@[expose] public section
open Finset
namespace NormalityChecker.LogarithmPrimaryCharacters

/-- Representative modulo integers of the primary component on the common window. -/
def primary (p n : ℕ) : ℚ := (2:ℚ)^(n-1)/p

/-- Removing this particular representative clears p from the true reduced denominator. -/
theorem primary_correct {p n : ℕ} (hp : p.Prime) (large : 3<p) (lo : 2*p≤n) (hi : n<3*p) :
    ¬p ∣ (twoStridePrefix n-primary p n).den := by
  have sq : n < p*p := hi.trans_le (Nat.mul_le_mul_right p (by omega))
  have q : n/p = 2 := le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)))
    ((Nat.le_div_iff_mul_le hp.pos).mpr lo)
  have reg := StrideDenominatorRate.short_prefix_regular hp large n sq
  rw [q, show twoStridePrefix 2 = 2 from by decide +kernel] at reg
  simpa only [primary,show n-1=n-2+1 by omega,pow_succ] using reg

private lemma den_primary_dvd (p n : ℕ) : (primary p n).den ∣ p := by
  have h := Rat.den_dvd ((2:ℤ)^(n-1)) (p:ℤ)
  rw [Rat.divInt_eq_div] at h
  apply Int.natCast_dvd_natCast.mp
  simpa [primary] using h

/-- Removing all selected primary terms simultaneously leaves a denominator prime to their product. -/
theorem joint_remainder {n : ℕ} (S : Finset ℕ) (primes : ∀ p ∈ S, p.Prime)
    (band : ∀ p ∈ S, 3<p ∧ 2*p≤n ∧ n<3*p) :
    (∏ p ∈ S, p).Coprime (twoStridePrefix n-∑ p ∈ S, primary p n).den := by
  apply Nat.Coprime.prod_left
  intro p hp
  let u := fun q => primary q n
  have pr := primes p hp
  have direct := primary_correct pr (band p hp).1 (band p hp).2.1 (band p hp).2.2
  have pairwise : p.Coprime (∏ q ∈ S.erase p, (u q).den) := by
    apply Nat.Coprime.prod_right
    intro q hq
    have cop := (Nat.coprime_primes pr (primes q (mem_of_mem_erase hq))).mpr
      (ne_of_mem_erase hq).symm
    exact cop.coprime_dvd_right (den_primary_dvd q n)
  have sumCop := pairwise.coprime_dvd_right (Finset.Rat.den_sum_dvd_prod_den (S.erase p) u)
  change p.Coprime (twoStridePrefix n-∑ q ∈ S,u q).den
  rw [←sum_erase_add S u hp,add_comm,←sub_sub]
  exact ((pr.coprime_iff_not_dvd.mpr direct).mul_right sumCop).coprime_dvd_right (Rat.sub_den_dvd ..)

/-- CRT numerator of an integer character of the vector of primary terms. -/
def coefficient (S : Finset ℕ) (h : ℕ → ℤ) : ℤ :=
  ∑ p ∈ S, h p * ((∏ q ∈ S.erase p, q : ℕ) : ℤ)

theorem primary_character_argument (S : Finset ℕ) (h : ℕ → ℤ) (pos : ∀ p ∈ S, 0<p) (n : ℕ) :
    ∑ p ∈ S, (h p : ℚ)*primary p n =
    2^(n-1)*(coefficient S h : ℚ)/((∏ p ∈ S, p : ℕ):ℚ) := by
  have nonzero : ((∏ p ∈ S, p : ℕ):ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (prod_pos pos).ne'
  rw [eq_div_iff nonzero,sum_mul,coefficient,Int.cast_sum,mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [←prod_erase_mul S (fun q : ℕ => q) hp]
  simp only [Nat.cast_mul,Int.cast_mul,Int.cast_natCast,primary]
  field_simp [(Nat.cast_ne_zero.mpr (pos p hp).ne' : (p:ℚ)≠0)]


theorem coefficient_coprime (S : Finset ℕ) (primes : ∀ p ∈ S, p.Prime) (h : ℕ → ℤ)
    (primitive : ∀ p ∈ S, ¬ (p:ℤ) ∣ h p) : (coefficient S h).natAbs.Coprime (∏ p ∈ S, p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  have pr := primes p hp
  let _ : Fact p.Prime := ⟨pr⟩
  apply Nat.Coprime.symm
  rw [pr.coprime_iff_not_dvd,← Int.natCast_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [coefficient,Int.cast_sum,Int.cast_mul,Int.cast_natCast,Nat.cast_prod,Int.cast_prod]
  rw [sum_eq_single_of_mem p hp]
  · apply mul_ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).not.mpr (primitive p hp))
    apply prod_ne_zero_iff.mpr
    intro q hq
    exact (ZMod.natCast_eq_zero_iff ..).not.mpr (pr.coprime_iff_not_dvd.mp
      ((Nat.coprime_primes pr (primes q (mem_of_mem_erase hq))).mpr (ne_of_mem_erase hq).symm))
  · intro q hq ne
    rw [prod_eq_zero (mem_erase.mpr ⟨ne.symm,hp⟩) (ZMod.natCast_self p),mul_zero]

/-- Arbitrarily accurate real approximations can retain every odd-primary
component of any prescribed rational. Their denominators change by at most
a power of two in either direction. -/
theorem dyadic_completion (y : ℚ) (target : ℝ) (m : ℕ) :
    ∃ z : ℚ, (z-y).den ∣ 2^m ∧
      z.den ∣ y.den*2^m ∧ y.den ∣ z.den*2^m ∧
      0 ≤ target-(z:ℝ) ∧ target-(z:ℝ) < 1/(2:ℝ)^m := by
  let j : ℤ := ⌊(2:ℝ)^m*(target-(y:ℝ))⌋
  let corr := (j:ℚ)/(2:ℚ)^m
  let z := y+corr
  have denom : corr.den ∣ 2^m := by
    have h := Rat.den_dvd j ((2:ℤ)^m)
    rw [Rat.divInt_eq_div] at h
    apply Int.natCast_dvd_natCast.mp
    simpa [corr] using h
  have delta : z-y = corr := by simp [z]
  have back : y = z-corr := by simp [z]
  refine ⟨z,delta ▸ denom,(Rat.add_den_dvd y corr).trans (Nat.mul_dvd_mul_left _ denom),?_,?_,?_⟩
  · exact (show y.den ∣ z.den*corr.den by
      simpa only [←back] using Rat.sub_den_dvd z corr).trans (Nat.mul_dvd_mul_left _ denom)
  · have hj : (j:ℝ) ≤ 2^m*(target-(y:ℝ)) := Int.floor_le _
    dsimp only [z,corr]
    push_cast
    have le : (j:ℝ)/2^m ≤ target-(y:ℝ) := (div_le_iff₀ (by positivity : (0:ℝ)<2^m)).mpr (by simpa [mul_comm] using hj)
    linarith
  · have hj : 2^m*(target-(y:ℝ)) < (j:ℝ)+1 := Int.lt_floor_add_one _
    dsimp only [z,corr]
    push_cast
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [sub_mul,add_mul,div_mul_cancel₀ _ (by positivity)]
    linarith

/-- The diagonal and off-diagonal contributions to a block of characters.
A common unit-modulus twist leaves the pair correlations unchanged. -/
theorem gram_bound {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset ι) (v : ι → E) (ρ : ℝ) (unit : ∀ i ∈ S, ‖v i‖ = 1)
    (off : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (inner ℂ (v i) (v j)).re ≤ ρ) :
    ‖∑ i ∈ S, v i‖^2 ≤ (S.card : ℝ) + S.card*(S.card-1 : ℕ)*ρ := by
  classical
  have row (i : ι) (hi : i ∈ S) : (∑ j ∈ S, (inner ℂ (v i) (v j)).re) ≤
      1+(S.card-1 : ℕ)*ρ := by
    rw [←sum_erase_add S _ hi]
    have dia := inner_self_eq_norm_sq (𝕜:=ℂ) (v i)
    change (inner ℂ (v i) (v i)).re = _ at dia
    rw [dia,unit i hi]
    have rest := sum_le_sum (s:=S.erase i) (g:=fun _ => ρ)
      (fun j hj => off i hi j (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm)
    simp only [sum_const,nsmul_eq_mul,card_erase_of_mem hi] at rest
    linarith
  have diag := inner_self_eq_norm_sq (𝕜:=ℂ) (∑ i ∈ S, v i)
  change (inner ℂ _ _).re = _ at diag
  rw [sum_inner,Complex.re_sum] at diag
  simp_rw [inner_sum,Complex.re_sum] at diag
  have total := sum_le_sum row
  simp only [sum_const,nsmul_eq_mul] at total
  nlinarith

/-- A family of vectors with uniformly large aligned means must be small when
its off-diagonal correlations are small. The test vector can be any unit vector. -/
theorem aligned_means {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset ι) (v : ι → E) (g : E) (ρ τ : ℝ) (hg : ‖g‖=1) (pos : 0≤τ)
    (unit : ∀ i ∈ S, ‖v i‖=1) (hits : ∀ i ∈ S, τ ≤ (inner ℂ g (v i)).re)
    (off : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (inner ℂ (v i) (v j)).re ≤ ρ) :
    ((S.card : ℝ)*τ)^2 ≤ (S.card : ℝ)+S.card*(S.card-1 : ℕ)*ρ := by
  have cnt := sum_le_sum hits
  rw [sum_const,nsmul_eq_mul,←Complex.re_sum,←inner_sum] at cnt
  have L := cnt.trans ((Complex.re_le_norm _).trans (norm_inner_le_norm g _))
  rw [hg,one_mul] at L
  exact (pow_le_pow_left₀ (mul_nonneg (by positivity) pos) L 2).trans
    (gram_bound S v ρ unit off)

end NormalityChecker.LogarithmPrimaryCharacters
