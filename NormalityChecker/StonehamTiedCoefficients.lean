module

public import NormalityChecker.StonehamPolynomial
public import NormalityChecker.StonehamTiedStatements

/-! Normality for a family of coefficients even when several monomials have
the same largest degree. -/
@[expose] public section
open Finset
namespace NormalityChecker.StonehamPolynomial

private lemma scale_denominator {p m H : ℕ} {x : ℚ} (hp : 0<p)
    (le : H≤m) (dv : x.den ∣ p^m) :
    ((p:ℚ)^H*x).den ∣ p^(m-H) := by
  obtain ⟨w,hw⟩ := dv
  let z : ℤ := x.num*w
  have cross : (p:ℚ)^m*x=(z:ℚ) := by
    have h : (p:ℚ)^m=(x.den:ℚ)*w := by exact_mod_cast hw
    rw [h,mul_right_comm,Rat.den_mul_eq_num]; simp [z]
  have e : (p:ℚ)^H*x=Rat.divInt z (p^(m-H):ℕ) := by
    rw [Rat.divInt_eq_div,Int.cast_natCast,Nat.cast_pow,eq_div_iff (by positivity),← cross]
    calc (p:ℚ)^H*x*p^(m-H) = p^(H+(m-H))*x := by rw [pow_add]; ring
         _ = _ := by rw [Nat.add_sub_of_le le]
  exact_mod_cast (e ▸ Rat.den_dvd z (p^(m-H):ℕ) : (((p:ℚ)^H*x).den:ℤ) ∣ (p^(m-H):ℕ))

/-- In the index-zero normalization the coefficient precision depends only
on the distinguished monomial, uniformly over integral perturbations of no
larger degree. -/
theorem tied_axis_normal {b p : ℕ} (hb : 2≤b) (hp : p.Prime) (odd : 3≤p)
    (cop : b.Coprime p) (t : Monomial) (degree : 0<t.degree) :
    ∃ H : ℕ, ∀ {ι : Type} (s : Finset ι) (u : ι → Monomial) (a : ι → ℤ),
      (∀ i ∈ s, (u i).degree ≤ t.degree) →
      NormalIn b (t.value b p + (p:ℝ)^H * ∑ i ∈ s, (a i:ℝ)*(u i).value b p) := by
  obtain ⟨C,K,retain⟩ := retained_denominator hp odd cop t.stride t.parameter
  refine ⟨C+1,fun s u a le => ?_⟩
  let z (i : _) : ℤ := (p:ℤ)^(C+1)*a i
  have res := sum_normal_of_retained hb hp cop t degree 1 s u z le
  simp only [Int.cast_one,one_mul] at res
  have form (n : ℕ) : (∑ i ∈ s, (z i:ℚ)*(u i).model b p n) =
      (p:ℚ)^(C+1)*(∑ i ∈ s, (a i:ℚ)*(u i).model b p n) := by
    simp [z,mul_sum,mul_assoc]
  have actual : (∑ i ∈ s, (z i:ℝ)*(u i).value b p) =
      (p:ℝ)^(C+1)*(∑ i ∈ s, (a i:ℝ)*(u i).value b p) := by
    simp [z,mul_sum,mul_assoc]
  rw [← actual]
  apply res
  refine ⟨C,max K (C+1),fun n late pos => ?_⟩
  let m := t.degree*Nat.log p n
  have big : C+1≤m := (le_max_right ..).trans
    (late.trans (Nat.le_mul_of_pos_left _ degree))
  let x := t.model b p n
  let y := (p:ℚ)^(C+1)*(∑ i ∈ s,(a i:ℚ)*(u i).model b p n)
  have bot : p^(m-C) ∣ x.den := retain n ((le_max_left ..).trans late) pos
  have top : y.den ∣ p^(m-(C+1)) := scale_denominator hp.pos big
    (combination_denominator hp.pos s u a le n)
  rw [form]
  change p^(m-C) ∣ (x+y).den
  have d := bot.trans (show x.den ∣ Nat.lcm (x+y).den y.den by
    simpa using Rat.sub_den_dvd_lcm (x+y) y)
  have high := (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero (x+y).den_ne_zero y.den_ne_zero)).mp d
  rw [Nat.factorization_lcm (x+y).den_ne_zero y.den_ne_zero,Finsupp.sup_apply] at high
  have small := (Nat.factorization_prime_le_iff_dvd y.den_ne_zero (pow_pos hp.pos _).ne').mpr top p hp
  rw [hp.factorization_pow,Finsupp.single_eq_same] at small
  exact (hp.pow_dvd_iff_le_factorization (x+y).den_ne_zero).mpr (by omega)

/-- Fix any finite list of standard monomials of at most the top degree.
After multiplying their integer coefficients by a sufficiently high common
power of p, every combination with the distinguished monomial is normal. -/
theorem tied_standard_normal {ι : Type} {b p : ℕ} (hb : 2≤b) (hp : p.Prime) (odd : 3≤p)
    (cop : b.Coprime p) (t : Monomial) (degree : 0<t.degree)
    (s : Finset ι) (u : ι → Monomial) (le : ∀ i ∈ s, (u i).degree ≤ t.degree) :
    ∃ H : ℕ, ∀ a : ι → ℤ,
      NormalIn b (t.standardValue b p + (p:ℝ)^H * ∑ i ∈ s,(a i:ℝ)*(u i).standardValue b p) := by
  let W (v : Monomial) : ℕ := ∑ i, (v.stride i:ℕ)
  let D := s.sup (fun i => W (u i))
  obtain ⟨h,normal⟩ := tied_axis_normal hb hp odd cop (t.shifted hp.pos) degree
  refine ⟨h+D,fun a => ?_⟩
  let z i : ℤ := (p:ℤ)^(W t+(D-W (u i)))*a i
  have res := normal s (fun i => (u i).shifted hp.pos) z le
  apply (normal_mul_nat_iff hb (pow_pos hp.pos (W t)) _).mp
  rw [Nat.cast_pow,mul_add]
  have eqn (i : ι) (hi : i∈s) : (z i:ℝ)*((u i).shifted hp.pos).value b p =
      (p:ℝ)^(W t+D)*((a i:ℝ)*(u i).standardValue b p) := by
    have lt : W (u i) ≤ D := le_sup (f:=fun i => W (u i)) hi
    rw [(u i).shifted_value hp.pos]
    simp only [z,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
    change _*((p:ℝ)^(W (u i))*_) = _
    rw [show W t+D=(W t+(D-W (u i)))+W (u i) by omega,pow_add (p:ℝ) _ (W (u i))]
    ring
  rw [sum_congr rfl eqn,← mul_sum,t.shifted_value hp.pos] at res
  convert res using 2
  simp only [pow_add,W]; ring

/-- A one-step radix dilation gives an exact affine dependence between
distinct standard generators. This produces ties with complete cancellation. -/
theorem radix_stride_identity {b c : ℕ} (hb : 2≤b) (hc : 2≤c) :
    alpha (b^c) c = (c:ℝ)*alpha b c - 1/(b:ℝ)^c := by
  let f (j : ℕ) : ℝ := 1/((c:ℝ)^(j+1)*(b:ℝ)^(c^(j+1):ℕ))
  have cr : (1:ℝ)<c := by exact_mod_cast hc
  have br : (1:ℝ)≤b := by exact_mod_cast (by omega : 1≤b)
  have geom := (summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (by positivity : 0≤1/(c:ℝ))
      ((div_lt_one (by positivity)).mpr cr))
  have summ : Summable f := geom.of_nonneg_of_le (fun j => by dsimp [f]; positivity) (fun j => by
    dsimp [f]; rw [one_div_pow,← div_div]
    exact div_le_self (by positivity) (one_le_pow₀ br))
  have cut := summ.sum_add_tsum_nat_add 1
  change (∑ j ∈ range 1,f j) + ∑' j,f (j+1) = alpha b c at cut
  have tail : alpha (b^c) c = (c:ℝ)*∑' j,f (j+1) := by
    rw [alpha,← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [f]
    rw [Nat.cast_pow,← pow_mul,pow_succ' c (j+1),pow_succ (c:ℝ)]
    field_simp; ring
  have initial : (c:ℝ)*f 0=1/(b:ℝ)^c := by simp [f]; field_simp
  rw [Finset.sum_range_one] at cut
  rw [← cut,mul_add,initial,tail]; ring

/-- Independent formulation using the standard series and positive parameters. -/
theorem tied_coefficient_statement : StonehamStatements.TiedCoefficientNormality := by
  intro b p d hb hp odd cop degree m e s ds ms es le
  let mk {D : ℕ} (m e : Fin D → ℕ+) : Monomial := ⟨D,fun i => m i,fun i => (m i).pos,e⟩
  exact tied_standard_normal hb hp odd cop (mk m e) degree univ (fun i => mk (ms i) (es i))
    (fun i _ => le i)

end NormalityChecker.StonehamPolynomial
