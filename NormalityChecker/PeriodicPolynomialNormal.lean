module

public import NormalityChecker.PeriodicPolynomialPrecision
public import NormalityChecker.StonehamPolynomial
public import NormalityChecker.StonehamJoint
import all NormalityChecker.StonehamPolynomialPrefix
import all NormalityChecker.StonehamPolynomial

/-! Rational polynomial images of Stoneham numbers for every coprime parameter greater than two. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

/-- On a late shell, the exact reflected numerator is the radix unit times the
periodic mass of the actual cut, modulo the specified prime power. -/
private theorem reflected_numerator_eq {b c p d m k n L : ℕ} [Fact p.Prime]
    (pc : p ∣ c) (late : L ≤ k) (u : ℕ → ℤ_[p])
    (cancel : ∀ v < L, ((b^m : ℕ) : ZMod (p^L))^(c^(k-v)) * PadicInt.toZModPow L (u v) = 1) :
    (numerator b c (fun _ : Fin d => 1) (fun _ => m) k n : ZMod (p^L)) =
    PadicInt.toZModPow L (boxProductSum (fun j => (c : ℤ_[p])^j * u j)
      (cut c (fun _ : Fin d => 1) (fun _ => m) k n) L) * (b : ZMod (p^L))^n := by
  classical
  let e : Strides d := fun _ => 1
  let t : Vector d := fun _ => m
  let s (v : Vector d) := position c e t (reflect e k v)
  have cancelProd (v : Vector d) (hv : v ∈ box d L) :
      (b : ZMod (p^L))^(s v) * (∏ i, PadicInt.toZModPow L (u (v i))) = 1 := by
    simp only [s, position, e, t, reflect, stretch, caps, PNat.val_ofNat, Nat.div_one, one_mul]
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    apply prod_eq_one
    intro i _
    simpa only [Nat.cast_pow, pow_mul] using cancel (v i) (mem_box.mp hv i)
  have eqWt (v : Vector d) : weight (stretch e v) = ∑ i, v i := by simp [weight,stretch,e]
  change (numerator b c e t k n : ZMod (p^L)) = _
  simp only [numerator, boxProductSum, map_sum, map_prod, map_mul, map_pow, map_natCast,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, sum_mul]
  symm
  apply sum_subset_zero_on_sdiff
  · intro v hv
    obtain ⟨hx,hw⟩ := mem_filter.mp hv
    refine mem_filter.mpr ⟨mem_rectangle.mpr (fun i => ?_),?_⟩
    · simpa [e,caps] using ((mem_box.mp hx i).le.trans late)
    · exact hw
  · intro v hv
    obtain ⟨ha,hf⟩ := mem_sdiff.mp hv
    have hv' : v ∉ box d L := fun h => hf (mem_filter.mpr ⟨h,(mem_filter.mp ha).2⟩)
    obtain ⟨i,hi⟩ : ∃ i, L ≤ v i := by simpa using hv'
    have w := hi.trans (le_stretched_weight e v i)
    have zero : (c : ZMod (p^L))^weight (stretch e v) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact (pow_dvd_pow_of_dvd pc L).trans (pow_dvd_pow c w)
    simp [zero]
  · intro v hv
    obtain ⟨hx,hw⟩ := mem_filter.mp hv
    have le : s v ≤ n := hw
    rw [prod_mul_distrib, prod_pow_eq_pow_sum, eqWt, mul_assoc]
    change _ * ((∏ i, PadicInt.toZModPow L (u (v i))) * (b : ZMod (p^L))^n) =
      _ * (b : ZMod (p^L))^(n-s v)
    congr 1
    calc
      _ = (∏ i, PadicInt.toZModPow L (u (v i))) * (b : ZMod (p^L))^(n-s v+s v) := by
        rw [Nat.sub_add_cancel le]
      _ = (b : ZMod (p^L))^(n-s v) * ((b : ZMod (p^L))^(s v) * ∏ i, PadicInt.toZModPow L (u (v i))) := by
        rw [pow_add]; ring
      _ = _ := by rw [cancelProd v hx, mul_one]

/-- After removing the radix unit and clearing the common denominator, the actual
rational prefix agrees with the reflected box mass to the prescribed p-adic precision. -/
theorem reflected_prefix_error {b c p d m n L : ℕ} [Fact p.Prime]
    (hc : 0 < c) (pc : p ∣ c) (cop : b.Coprime p) (late : L ≤ Nat.log c n)
    (u : ℕ → ℤ_[p]) (cancel : ∀ v < L,
      ((b^m : ℕ) : ZMod (p^L))^(c^(Nat.log c n-v)) * PadicInt.toZModPow L (u v) = 1) :
    let k := Nat.log c n
    let U := {v : Vector d | (∑ i, m*c^(k-v i)) ≤ n}
    ‖(c : ℚ_[p])^(d*k) * (productPrefix b c (fun _ : Fin d => 1) (fun _ => m) n : ℚ_[p]) /
      (b : ℚ_[p])^n - ((boxProductSum (fun j => (c : ℤ_[p])^j * u j) U L : ℤ_[p]) : ℚ_[p])‖
        ≤ (p : ℝ)^(-(L : ℤ)) := by
  let k := Nat.log c n
  let e : Strides d := fun _ => 1
  let t : Vector d := fun _ => m
  let A := numerator b c e t k n
  let U := cut c e t k n
  let M := boxProductSum (fun j => (c : ℤ_[p])^j * u j) U L
  have cutEq : U = {v : Vector d | (∑ i, m*c^(k-v i)) ≤ n} := by
    ext v; simp [U,cut,position,stretch,reflect,caps,e,t]
  have modEq := reflected_numerator_eq (b:=b) (d:=d) (n:=n) pc late u cancel
  have err : ‖(A : ℤ_[p]) - M*(b : ℤ_[p])^n‖ ≤ (p : ℝ)^(-(L : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, map_mul, map_pow, map_natCast, map_natCast, sub_eq_zero]
    exact modEq
  have scaleEq : (A : ℚ_[p]) = (c : ℚ_[p])^(d*k) * (productPrefix b c e t n : ℚ_[p]) := by
    have eqn := congrArg (algebraMap ℚ ℚ_[p]) (scaled (b:=b) (n:=n) hc e t)
    simpa [A,scale,weight,stretch,caps,e,k] using eqn
  have unit : ‖(b : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr cop.symm
  have bn : (b : ℚ_[p]) ≠ 0 := norm_ne_zero_iff.mp (unit.trans_ne one_ne_zero)
  dsimp only
  rw [← cutEq]
  change ‖(c : ℚ_[p])^(d*k) * (productPrefix b c e t n : ℚ_[p]) / (b : ℚ_[p])^n - (M : ℚ_[p])‖ ≤ _
  rw [← scaleEq, div_sub' (pow_ne_zero n bn), mul_comm ((b : ℚ_[p])^n) (M : ℚ_[p]), norm_div, norm_pow, unit, one_pow, div_one]
  simpa only [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
    PadicInt.coe_natCast] using err

/-- For every prime divisor of the parameter, the prefix of a power of a
single axis retains the full expected pole order up to a bounded loss. -/
theorem periodic_power_retained_denominator {b c p d : ℕ} (hc : 2 < c) (hp : p.Prime)
    (pc : p ∣ c) (cop : b.Coprime p) (m : ℕ) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log c n → 0 < n →
      p^(c.factorization p * (d*Nat.log c n) - L) ∣
        (productPrefix b c (fun _ : Fin d => 1) (fun _ => m) n).den := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let e : Strides d := fun _ => 1
  let t : Vector d := fun _ => m
  let anchor := d*m
  obtain ⟨h,N,phase,u,_,_,_,cancel,_,conv⟩ := exists_reflected_cycles hc pc (cop.pow_left m)
  have uniform (r : Fin h) := uniform_padic_box_precision pc (fun _ : Fin d => anchor)
    (u r) (fun U upper hit => conv r U upper ⟨_,hit⟩)
  choose bound pass using uniform
  let L := univ.sup bound
  refine ⟨L,max (N+2*L) anchor, fun n big pos => ?_⟩
  let k := Nat.log c n
  have ak : anchor ≤ k := (le_max_right ..).trans big
  have late : N+2*L ≤ k := (le_max_left ..).trans big
  have hit : (fun _ => anchor) ∈ cut c e t k n := by
    have h : anchor*c^(k-anchor) ≤ c^k := calc
      _ ≤ c^anchor * c^(k-anchor) := Nat.mul_le_mul_right _ (Nat.lt_pow_self (by omega : 1<c)).le
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le ak]
    simpa [cut, position, stretch, reflect, caps, e, t, anchor, mul_assoc] using
      h.trans (Nat.pow_log_le_self c pos.ne')
  have mass := pass (phase k) L (le_sup (mem_univ (phase k))) _ (cut_upper (by omega : 0<c) e t k n) hit
  have eqn := reflected_numerator_eq (b:=b) (n:=n) (d:=d) (m:=m) pc (by omega : L ≤ k) (u (phase k))
    (fun v hv => cancel L k v (by omega))
  have unit := ((ZMod.isUnit_iff_coprime b (p^L)).mpr (cop.pow_right L)).pow n
  have nz : (numerator b c e t k n : ZMod (p^L)) ≠ 0 := by
    rw [eqn]
    intro zero
    exact mass (unit.mul_right_cancel (zero.trans (zero_mul _).symm))
  have le := factorization_le_of_numerator hp (by omega : 0<c) e t nz
  apply (hp.pow_dvd_iff_le_factorization (productPrefix b c e t n).pos.ne').mpr
  simpa [scale, weight, stretch, caps, e] using Nat.sub_le_of_le_add le

/-- Every nonconstant rational polynomial of the positive-index Stoneham number
is normal in base `b` for coprime `b ≥ 2` and `c > 2`. -/
theorem coprime_polynomial_normal {b c : ℕ} (hb : 2 ≤ b) (hc : 2 < c) (cop : b.Coprime c)
    (P : ℚ[X]) (degree : 0 < P.natDegree) :
    NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) := by
  obtain ⟨p,hp,pc⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
  let term (d : ℕ) : Monomial := ⟨d, fun _ => c, fun _ => by omega, fun _ => 1⟩
  let a (d : ℕ) := P.coeff d / (c : ℚ)^d
  have lead : a P.natDegree ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.mpr (fun h => by simp [h] at degree))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega)))
  have retention : (term P.natDegree).RetainsAt b c p :=
    periodic_power_retained_denominator hc hp pc (cop.coprime_dvd_right pc) c
  have result := rational_sum_normal_of_retainsAt hb hc hp pc cop (term P.natDegree) retention
    degree _ lead (range P.natDegree) term a (fun _ hi => mem_range.mp hi)
  have shifted : axis b c c = (c : ℝ) * alpha b c := by
    simpa using axis_shift (b:=b) (p:=c) (by omega) 1
  have val (d : ℕ) : (a d : ℝ) * (term d).value b c = (P.coeff d : ℝ) * alpha b c ^ d := by
    simp [a, Monomial.value, term, shifted, mul_pow]
    field_simp
  rw [Polynomial.eval₂_eq_sum_range, sum_range_succ, add_comm]
  simpa only [val, show ∀ q : ℚ, (algebraMap ℚ ℝ) q = (q:ℝ) from fun _ => rfl] using result

theorem coprime_polynomial_statement_checked : StonehamStatements.CoprimePolynomialNormality :=
  fun hb hc cop => coprime_polynomial_normal hb hc cop

/-- Simultaneous rectangle frequencies for distinct powers of any generator with c > 2. -/
theorem coprime_joint_powers {b c d : ℕ} (hb : 2 ≤ b) (hc : 2 < c) (cop : b.Coprime c)
    (r : Fin d → ℕ) (pos : ∀ i, 0 < r i) (inj : Function.Injective r) (u v : Fin d → ℝ)
    (hu : ∀ i, 0 ≤ u i) (huv : ∀ i, u i ≤ v i) (hv : ∀ i, v i ≤ 1) :
    Tendsto (StonehamStatements.rectangleFrequency (fun n i => shift b (alpha b c ^ r i) n) u v)
      atTop (𝓝 (∏ i, (v i - u i))) :=
  joint_powers_of_polynomial_normal (coprime_polynomial_normal hb hc cop) r pos inj u v hu huv hv

end NormalityChecker.StonehamPolynomial
