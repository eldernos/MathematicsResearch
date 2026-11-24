module

public import NormalityChecker.MaskClassification

/-! Prime divisors of nonmonomial polynomial denominators on a prime-power axis. -/
@[expose] public section
open Filter Finset Polynomial
namespace NormalityChecker.LocalizedSupport

private theorem abs_eval_grows {p : ℕ} (hp : p.Prime) (G : ℤ[X]) (deg : 0 < G.natDegree) :
    Tendsto (fun k : ℕ => (G.eval ((p : ℤ)^k)).natAbs) atTop atTop := by
  have abs_tend : Tendsto Int.natAbs cofinite atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [(Set.finite_Icc (-(n : ℤ)) n).compl_mem_cofinite] with z hz
    simp only [Set.mem_compl_iff, Set.mem_Icc] at hz
    omega
  let _ := G.tendstoCofinite_of_natDegree_ne_zero deg.ne'
  have grow : Tendsto (fun k : ℕ => (p : ℤ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp.one_lt)
  exact abs_tend.comp ((TendstoCofinite.tendsto_cofinite G.eval).comp (grow.mono_right atTop_le_cofinite))

private lemma eval_modEq {x y n : ℤ} (xy : x ≡ y [ZMOD n]) (G : ℤ[X]) :
    G.eval x ≡ G.eval y [ZMOD n] :=
  Int.modEq_iff_dvd.mpr (xy.dvd.trans (sub_dvd_eval_sub y x G))

/-- A nonconstant integer polynomial with nonzero constant term acquires primes
outside every finite set on arbitrarily late powers of p, at nonzero values. -/
theorem polynomial_prime_outside_axis {p : ℕ} (hp : p.Prime) (G : ℤ[X])
    (deg : 0 < G.natDegree) (g0 : G.eval 0 ≠ 0) (S : Finset ℕ) (K : ℕ) :
    ∃ k ≥ K, G.eval ((p : ℤ)^k) ≠ 0 ∧ ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ (q : ℤ) ∣ G.eval ((p : ℤ)^k) := by
  let y (k : ℕ) := G.eval ((p : ℤ)^k)
  have grow := abs_eval_grows hp G deg
  obtain ⟨j, hj⟩ := (grow.eventually_gt_atTop 0).exists
  let L := max (G.eval 0).natAbs (y j).natAbs + 1
  let T := S.filter Nat.Prime
  let M := ∏ q ∈ T.erase p, q^L
  have mpos : 0 < M := prod_pos fun q h => pow_pos (mem_filter.mp (mem_of_mem_erase h)).2.pos _
  have cop : p.Coprime M := Nat.Coprime.prod_right fun q h =>
    Nat.Coprime.pow_right L (hp.coprime_iff_not_dvd.mpr fun hq =>
      (ne_of_mem_erase h) ((Nat.prime_dvd_prime_iff_eq hp (mem_filter.mp (mem_of_mem_erase h)).2).mp hq).symm)
  let B := ∏ q ∈ T, q^L
  obtain ⟨J, large⟩ := eventually_atTop.mp (grow.eventually_gt_atTop B)
  let u := max K (max J L)
  let k := j + M.totient * u
  have uk : u ≤ k := (Nat.le_mul_of_pos_left u (Nat.totient_pos.mpr mpos)).trans (Nat.le_add_left ..)
  have lk : L ≤ k := (le_max_right J L).trans ((le_max_right K _).trans uk)
  have big : B < (y k).natAbs := large k ((le_max_left J L).trans ((le_max_right K _).trans uk))
  have yn : y k ≠ 0 := Int.natAbs_ne_zero.mp (Nat.zero_lt_of_lt big).ne'
  refine ⟨k, (le_max_left ..).trans uk, yn, ?_⟩
  have residue : p^k ≡ p^j [MOD M] := by
    simpa [k, pow_add, pow_mul] using (Nat.ModEq.pow_totient cop).pow u |>.mul_left (p^j)
  have small (q : ℕ) (hq : q ∈ T) : ¬ q^L ∣ (y k).natAbs := by
    have hprime := (mem_filter.mp hq).2
    have bound := Nat.lt_pow_self (n := L) hprime.two_le
    intro fail
    have div : (q : ℤ)^L ∣ y k := by
      simpa using ((Int.natAbs_dvd_natAbs (a := ((q^L : ℕ) : ℤ)) (b := y k)).mp (by simpa using fail))
    by_cases eq : q = p
    · subst q
      have congruence : (p : ℤ)^k ≡ 0 [ZMOD (p : ℤ)^L] :=
        Int.modEq_zero_iff_dvd.mpr (pow_dvd_pow (p : ℤ) lk)
      have d0 := ((eval_modEq congruence G).dvd_iff).mp div
      have cap := Nat.le_of_dvd (Int.natAbs_pos.mpr g0) (Int.natAbs_dvd_natAbs.mpr d0)
      simp only [Int.natAbs_pow, Int.natAbs_natCast] at cap
      have lt : (G.eval 0).natAbs < L := Nat.lt_succ_of_le (le_max_left ..)
      exact (lt.trans bound).not_ge cap
    · have dM : q^L ∣ M := dvd_prod_of_mem _ (mem_erase.mpr ⟨eq, hq⟩)
      have cong := Int.natCast_modEq_iff.mpr (residue.of_dvd dM)
      push_cast at cong
      have dj := ((eval_modEq cong G).dvd_iff).mp div
      have cap := Nat.le_of_dvd hj (Int.natAbs_dvd_natAbs.mpr dj)
      simp only [Int.natAbs_pow, Int.natAbs_natCast] at cap
      change _ ≤ (y j).natAbs at cap
      have lt : (y j).natAbs < L := Nat.lt_succ_of_le (le_max_right ..)
      exact (lt.trans bound).not_ge cap
  by_contra! all
  let n := (y k).natAbs
  have sub : n.primeFactors ⊆ T := by
    intro q hq
    have prime := Nat.prime_of_mem_primeFactors hq
    have div : (q : ℤ) ∣ y k := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors hq)
    exact mem_filter.mpr ⟨by_contra fun out => all q prime out div, prime⟩
  have hpos : n ≠ 0 := Int.natAbs_ne_zero.mpr yn
  have bound : n ≤ B := calc
    n = ∏ q ∈ n.primeFactors, q^(n.factorization q) := Nat.prod_primeFactors_pow_factorization hpos
    _ ≤ ∏ q ∈ n.primeFactors, q^L := by
      apply prod_le_prod (fun q hq => ?_)
      have pr := Nat.prime_of_mem_primeFactors hq
      exact Nat.pow_le_pow_right pr.pos (lt_of_not_ge fun h =>
        small q (sub hq) ((pr.pow_dvd_iff_le_factorization hpos).mpr h)).le
    _ ≤ B := prod_le_prod_of_subset_of_one_le sub fun q hq _ => Nat.one_le_pow _ _ (mem_filter.mp hq).2.one_le
  exact big.not_ge bound

/-- Clearing a polynomial Bézout identity gives one nonzero integer common to
the evaluation ideals at all nonnegative integer arguments. -/
private theorem eval_bezout (A G : ℤ[X])
    (cop : IsCoprime (A.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ))) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ m : ℕ, ∃ u v : ℤ, u * A.eval (m : ℤ) + v * G.eval (m : ℤ) = D := by
  obtain ⟨U, V, iden⟩ := cop
  obtain ⟨e, U', he, evalU⟩ := PolynomialMasks.normalize U
  obtain ⟨f, V', hf, evalV⟩ := PolynomialMasks.normalize V
  refine ⟨e*f, mul_ne_zero he hf, fun m => ⟨f * U'.eval (m : ℤ), e * V'.eval (m : ℤ), ?_⟩⟩
  have evalA : (A.map (algebraMap ℤ ℚ)).eval (m : ℚ) = ((A.eval (m : ℤ) : ℤ) : ℚ) :=
    eval_map_apply (algebraMap ℤ ℚ) (m : ℤ)
  have evalG : (G.map (algebraMap ℤ ℚ)).eval (m : ℚ) = ((G.eval (m : ℤ) : ℤ) : ℚ) :=
    eval_map_apply (algebraMap ℤ ℚ) (m : ℤ)
  have hm := congrArg (Polynomial.eval (m : ℚ)) iden
  simp only [eval_add, eval_mul, evalA, evalG, eval_one] at hm
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [show ((U'.eval (m : ℤ) : ℤ) : ℚ) = _ from evalU m,
    show ((V'.eval (m : ℤ) : ℤ) : ℚ) = _ from evalV m]
  linear_combination ((e : ℚ)*f)*hm

/-- The rational coefficient A(m)/(mᵘ G(m)) at m = pᵏ. -/
def rationalAxisCoefficient (p u : ℕ) (A G : ℤ[X]) (k : ℕ) : ℚ :=
  let m : ℤ := (p : ℤ)^k
  ((A.eval m : ℤ) : ℚ) / (m : ℚ)^u / ((G.eval m : ℤ) : ℚ)

/-- For A(X)/(Xᵘ G(X)) with A,G coprime over the rationals, a nonconstant
denominator factor G nonzero at zero forces infinitely many different primes in
the *reduced* denominators on any full prime-power axis. -/
theorem rational_denominator_prime_outside {p : ℕ} (hp : p.Prime) (A G : ℤ[X])
    (cop : IsCoprime (A.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)))
    (deg : 0 < G.natDegree) (g0 : G.eval 0 ≠ 0) (u : ℕ) (S : Finset ℕ) (K : ℕ) :
    ∃ k ≥ K, ∃ q : ℕ, q.Prime ∧ q ∉ S ∧
      q ∣ (rationalAxisCoefficient p u A G k).den := by
  obtain ⟨D, dn, bezout⟩ := eval_bezout A G cop
  obtain ⟨k, hk, gn, q, prime, out, div⟩ :=
    polynomial_prime_outside_axis hp G deg g0 (S ∪ D.natAbs.primeFactors) K
  refine ⟨k, hk, q, prime, fun h => out (mem_union_left _ h), ?_⟩
  let m : ℤ := (p : ℤ)^k
  have coeff : ¬ (q : ℤ) ∣ A.eval m := by
    intro da
    obtain ⟨v, w, eqD⟩ := bezout (p^k)
    push_cast at eqD
    have dD : (q : ℤ) ∣ D := eqD ▸ dvd_add (da.trans (dvd_mul_left ..)) (div.trans (dvd_mul_left ..))
    exact out (mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨prime, by simpa using Int.natAbs_dvd_natAbs.mpr dD, Int.natAbs_ne_zero.mpr dn⟩))
  let y := ((A.eval m : ℤ) : ℚ) / ((m : ℚ)^u) / ((G.eval m : ℤ) : ℚ)
  have den_ne : ((m : ℚ)^u) ≠ 0 := pow_ne_zero _ (by dsimp [m]; exact_mod_cast pow_ne_zero k hp.ne_zero)
  have cross : A.eval m * (y.den : ℤ) = y.num * (m^u * G.eval m) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← Rat.mul_den_eq_num]
    change _ = (((A.eval m : ℤ) : ℚ) / (m : ℚ)^u / ((G.eval m : ℤ) : ℚ) * _) * _
    field_simp [den_ne, show ((G.eval m : ℤ) : ℚ) ≠ 0 by exact_mod_cast gn]
  have dprod : (q : ℤ) ∣ A.eval m * (y.den : ℤ) := by
    rw [cross]
    exact (div.trans (dvd_mul_left ..)).trans (dvd_mul_left ..)
  have dy := (Nat.prime_iff_prime_int.mp prime).dvd_or_dvd dprod |>.resolve_left coeff
  exact Int.natCast_dvd_natCast.mp dy

/-- A fixed finite set of reduced denominator primes exists exactly when the
denominator remaining after removal of its power of X is constant. -/
theorem finite_denominator_primes_iff {p : ℕ} (hp : p.Prime) (A G : ℤ[X])
    (cop : IsCoprime (A.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)))
    (g0 : G.eval 0 ≠ 0) (u : ℕ) :
    (∃ S : Finset ℕ, ∀ k, (rationalAxisCoefficient p u A G k).den.primeFactors ⊆ S) ↔
      G.natDegree = 0 := by
  constructor
  · rintro ⟨S, support⟩
    by_contra ne
    obtain ⟨k, _, q, prime, out, div⟩ := rational_denominator_prime_outside hp A G cop
      (Nat.pos_of_ne_zero ne) g0 u S 0
    exact out (support k (Nat.mem_primeFactors.mpr ⟨prime, div, Rat.den_ne_zero _⟩))
  · intro degree
    obtain ⟨g, rfl⟩ : ∃ g, G = C g := ⟨_, eq_C_of_natDegree_eq_zero degree⟩
    refine ⟨insert p g.natAbs.primeFactors, ?_⟩
    intro k q hq
    let m := (p : ℤ)^k
    have eqn : rationalAxisCoefficient p u A (C g) k = Rat.divInt (A.eval m) (m^u * g) := by
      simp [rationalAxisCoefficient, m, Rat.divInt_eq_div, div_div]
    rw [eqn] at hq
    have d := (Nat.dvd_of_mem_primeFactors hq).trans (Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd _ _))
    simp only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow, m] at d
    have prime := Nat.prime_of_mem_primeFactors hq
    rcases prime.dvd_mul.mp d with pow | cg
    · exact mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq prime hp).mp
        (prime.dvd_of_dvd_pow (prime.dvd_of_dvd_pow pow))))
    · exact mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨prime, cg, Int.natAbs_ne_zero.mpr (by simpa using g0)⟩)

end NormalityChecker.LocalizedSupport
