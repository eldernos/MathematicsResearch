module

public import NormalityChecker.StonehamPolynomialOrthant
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.Tactic

/-! Algebraic obstruction to cancellation in the periodic Stoneham mass. -/
@[expose] public section
open Finset Polynomial Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

/-- Rational continuation of a one-dimensional periodic geometric series. -/
noncomputable def periodicGeometricValue {K : Type*} [Field K] (c h : ℕ) (u : ℕ → K) : K :=
  (∑ i ∈ range h, (c : K)^i * u i) / (1 - (c : K)^h)

private lemma geometric_sum_lt {c : ℕ} (hc : 2 ≤ c) (k : ℕ) :
    ∑ i ∈ range k, c^i < c^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    exact (Nat.add_lt_add_right ih _).trans_le (by nlinarith [Nat.mul_le_mul_left (c^k) hc])

/-- For a nonempty cycle of roots of unity and `c > 2`, every complex conjugate of the
geometric value has absolute value strictly between zero and one. Thus it is nonintegral. -/
theorem periodicGeometricValue_not_isIntegral {K : Type*} [Field K] [NumberField K]
    {c h : ℕ} (hc : 2 < c) (hh : 0 < h) (u : ℕ → K)
    (unit : ∀ (σ : K →+* ℂ) i, i < h → ‖σ (u i)‖ = 1) :
    ¬ IsIntegral ℤ (periodicGeometricValue c h u) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  let A (σ : K →+* ℂ) (j : ℕ) := ∑ i ∈ range j, (c : ℂ)^i * σ (u i)
  have term (σ : K →+* ℂ) (i : ℕ) (hi : i ≤ k) :
      ‖(c : ℂ)^i * σ (u i)‖ = (c : ℝ)^i := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, unit _ _ (by omega), mul_one]
  have upper (σ : K →+* ℂ) (j : ℕ) (hj : j ≤ k+1) :
      ‖A σ j‖ ≤ ∑ i ∈ range j, (c : ℝ)^i := by
    apply (norm_sum_le ..).trans_eq
    exact sum_congr rfl (fun i hi => term σ i (by have := mem_range.mp hi; omega))
  have top (σ : K →+* ℂ) : A σ (k+1) ≠ 0 := by
    intro z
    have eqn : A σ k = -((c : ℂ)^k * σ (u k)) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [A, sum_range_succ] using z
    have small := upper σ k (by omega)
    rw [eqn, norm_neg, term σ k le_rfl] at small
    have lt : ∑ i ∈ range k, (c : ℝ)^i < (c:ℝ)^k := by
      exact_mod_cast geometric_sum_lt (by omega : 2 ≤ c) k
    exact lt.not_ge small
  have big : 1 < (c : ℝ)^(k+1) := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < c)) (by omega)
  have den : ‖1 - (c : ℂ)^(k+1)‖ = (c:ℝ)^(k+1) - 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have eval (σ : K →+* ℂ) : σ (periodicGeometricValue c (k+1) u) =
      A σ (k+1) / (1-(c:ℂ)^(k+1)) := by simp [periodicGeometricValue, A]
  have small (σ : K →+* ℂ) : ‖σ (periodicGeometricValue c (k+1) u)‖ < 1 := by
    rw [eval, norm_div, den, div_lt_one (by linarith)]
    apply (upper σ _ le_rfl).trans_lt
    have lt := geometric_sum_lt (by omega : 2 ≤ c) k
    rw [sum_range_succ]
    have h' : (∑ i ∈ range k, c^i) + c^k + 1 < c^(k+1) := by
      rw [pow_succ]
      have pos : 0 < c^k := pow_pos (by omega) _
      have bound := Nat.mul_le_mul_left (c^k) (show 3 ≤ c from hc)
      omega
    have cast : (∑ i ∈ range k, (c : ℝ)^i) + c^k + 1 < (c : ℝ)^(k+1) := by exact_mod_cast h'
    linarith
  intro integr
  have ne : periodicGeometricValue c (k+1) u ≠ 0 := by
    let σ := Classical.arbitrary (K →+* ℂ)
    intro z
    have ez := eval σ
    rw [z, map_zero] at ez
    exact div_ne_zero (top σ) (fun h => by simp [h] at den; linarith) ez.symm
  obtain ⟨σ,le⟩ := NumberField.exists_conjugate_one_le_norm (K:=K)
    (α:=⟨_,integr⟩) (fun z => ne (congrArg Subtype.val z))
  exact (small σ).not_ge le

/-- The sum of the products of the coordinate weights over a truncated upper set. -/
noncomputable def boxProductSum {R : Type*} [CommRing R] {d : ℕ} (f : ℕ → R)
    (U : Set (Vector d)) (L : ℕ) : R := by
  classical exact ∑ v ∈ (box d L).filter (· ∈ U), ∏ i, f (v i)

private theorem orthant_product_eventually {R : Type*} [CommRing R] {d : ℕ}
    (f : ℕ → R) (a : Vector d) :
    ∀ᶠ L in atTop, boxProductSum f (Set.Ici a) L =
      ∏ i, ((∑ j ∈ range L, f j) - ∑ j ∈ range (a i), f j) := by
  classical
  filter_upwards [eventually_ge_atTop (univ.sup a)] with L hL
  have bounds (i : Fin d) : a i ≤ L := (le_sup (f:=a) (mem_univ i)).trans hL
  have cells : @Finset.filter _ (· ∈ Set.Ici a) (fun _ => Classical.propDecidable _) (box d L) =
      Fintype.piFinset fun i => Ico (a i) L := by
    ext v
    simp only [mem_filter, mem_box, Set.mem_Ici, Fintype.mem_piFinset, mem_Ico, Pi.le_def]
    grind
  rw [boxProductSum, cells, ← prod_univ_sum]
  exact prod_congr rfl (fun i _ => sum_Ico_eq_sub _ (bounds i))

private lemma box_union {R : Type*} [CommRing R] {d : ℕ}
    (f : ℕ → R) (a : Vector d) (s : List (Vector d)) (L : ℕ) :
    boxProductSum f (orthants (a::s)) L = boxProductSum f (Set.Ici a) L +
      boxProductSum f (orthants s) L - boxProductSum f (orthants (s.map (a ⊔ ·))) L := by
  classical
  simp only [boxProductSum, sum_filter, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  have h : v ∈ orthants (s.map (a ⊔ ·)) ↔ a ≤ v ∧ v ∈ orthants s := by
    simp [orthants, sup_le_iff]; grind
  have h' : v ∈ orthants (a::s) ↔ a ≤ v ∨ v ∈ orthants s := by simp [orthants]
  simp only [h,h',Set.mem_Ici]
  split_ifs <;> grind

private theorem list_box_polynomial {R : Type*} [CommRing R] [Nontrivial R] {d n : ℕ}
    (f : ℕ → R) (s : List (Vector d)) (len : s.length = n) :
    ∃ P : R[X], P.natDegree ≤ d ∧ P.coeff d = (if s = [] then 0 else 1) ∧
      ∀ᶠ L in atTop, boxProductSum f (orthants s) L = P.eval (∑ j ∈ range L, f j) := by
  classical
  induction n generalizing s with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.mp len
    exact ⟨0, by simp, by simp, .of_forall fun L => by simp [boxProductSum, orthants]⟩
  | succ n ih =>
    obtain ⟨a,s,rfl⟩ := List.exists_cons_of_ne_nil (l:=s) (by intro z; simp [z] at len)
    simp only [List.length_cons, Nat.succ.injEq] at len
    obtain ⟨P,degP,lcP,valP⟩ := ih s len
    obtain ⟨Q,degQ,lcQ,valQ⟩ := ih (s.map (a ⊔ ·)) (by simpa using len)
    let O : R[X] := ∏ i, (X - C (∑ j ∈ range (a i), f j))
    have mon : O.Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
    have deg : O.natDegree = d := by
      dsimp only [O]
      rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
      simp only [natDegree_X_sub_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    refine ⟨O + P - Q, by simpa using natDegree_sub_le_of_le (natDegree_add_le_of_le deg.le degP) degQ, ?_, ?_⟩
    · have lcO : O.coeff d = 1 := deg ▸ mon.coeff_natDegree
      simp [lcO, lcP, lcQ]
    · filter_upwards [orthant_product_eventually f a, valP, valQ] with L ho hP hQ
      rw [box_union, ho, hP, hQ]
      simp only [O, eval_sub, eval_add, eval_prod, eval_X, eval_C]

/-- For all sufficiently large boxes, their mass is a monic polynomial in the
one-dimensional partial sum. The polynomial is independent of the box size. -/
theorem upper_box_monic_polynomial {R : Type*} [CommRing R] [Nontrivial R] {d : ℕ}
    (f : ℕ → R) (U : Set (Vector d)) (upper : IsUpperSet U) (hit : U.Nonempty) :
    ∃ P : R[X], P.Monic ∧ P.natDegree = d ∧
      ∀ᶠ L in atTop, boxProductSum f U L = P.eval (∑ j ∈ range L, f j) := by
  classical
  obtain ⟨s,ne,rfl⟩ := exists_orthants_eq U upper hit
  obtain ⟨P,deg,lc,val⟩ := list_box_polynomial f s rfl
  simp only [ite_eq_right ne] at lc
  exact ⟨P, monic_of_natDegree_le_of_coeff_eq_one d deg lc,
    le_antisymm deg (le_natDegree_of_ne_zero (lc ▸ one_ne_zero)), val⟩

/-- If integral coordinate weights sum to a nonintegral element, every nonempty upper
set has a nonzero limiting mass. This applies in the p-adic field with integrality over ℤ. -/
theorem upper_box_nonzero_limit {E : Type*} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    {d : ℕ} (f : ℕ → integralClosure ℤ E) (U : Set (Vector d)) (upper : IsUpperSet U)
    (hit : U.Nonempty) {S : E} (nonintegral : ¬ IsIntegral ℤ S)
    (conv : Tendsto (fun L => ((∑ j ∈ range L, f j : integralClosure ℤ E) : E)) atTop (𝓝 S)) :
    ∃ z : E, z ≠ 0 ∧
      Tendsto (fun L => ((boxProductSum f U L : integralClosure ℤ E) : E)) atTop (𝓝 z) := by
  obtain ⟨P,mon,_,eqn⟩ := upper_box_monic_polynomial f U upper hit
  let emb := (integralClosure ℤ E).val.toRingHom
  refine ⟨P.eval₂ emb S, fun zero => nonintegral (isIntegral_trans (A:=integralClosure ℤ E) S
    ⟨P,mon,zero⟩), ?_⟩
  refine (((P.continuous_eval₂ emb).tendsto S).comp conv).congr' ?_
  filter_upwards [eqn] with L hL
  rw [hL]
  exact eval₂_at_apply emb _

/-- For a periodic cycle of roots of unity from a number field, the mass of every
nonempty upper set has a nonzero limit in any complete normed field where `‖c‖ < 1`. -/
theorem periodic_upper_mass_nonzero {K E : Type*} [Field K] [NumberField K]
    [NormedField E] [CompleteSpace E] (φ : K →+* E) {c h d : ℕ}
    (hc : 2 < c) (hh : 0 < h) (small : ‖(c : E)‖ < 1)
    (u : ℕ → K) (cycle : Function.Periodic u h) (unit : ∀ j, IsOfFinOrder (u j))
    (U : Set (Vector d)) (upper : IsUpperSet U) (hit : U.Nonempty) :
    ∃ z : E, z ≠ 0 ∧ Tendsto (boxProductSum (fun j => (c : E)^j * φ (u j)) U) atTop (𝓝 z) := by
  let S := periodicGeometricValue c h u
  have notInt := periodicGeometricValue_not_isIntegral hc hh u
    (fun σ j _ => (σ.toMonoidHom.isOfFinOrder (unit j)).norm_eq_one)
  have ni : ¬ IsIntegral ℤ (φ S) := fun hi =>
    notInt ((isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hi)
  let f (j : ℕ) := (c : E)^j * φ (u j)
  have un (j : ℕ) : IsOfFinOrder (φ (u j)) := φ.toMonoidHom.isOfFinOrder (unit j)
  have summ : Summable f :=
    (summable_geometric_of_lt_one (norm_nonneg _) small).of_norm_bounded (fun j => by
      simp only [f, norm_mul, norm_pow, (un j).norm_eq_one, mul_one, le_refl])
  have tail (j : ℕ) : f (j+h) = (c:E)^h * f j := by
    simp only [f, cycle j, pow_add]; ring
  have eqn := summ.sum_add_tsum_nat_add h
  simp only [tail, tsum_mul_left] at eqn
  have den : 1-(c:E)^h ≠ 0 := by
    intro z
    have normeq := congrArg norm (sub_eq_zero.mp z)
    rw [norm_one, norm_pow] at normeq
    exact (pow_lt_one₀ (norm_nonneg _) small hh.ne').ne normeq.symm
  have value : ∑' j, f j = φ S := by
    simp only [S, periodicGeometricValue, map_div₀, map_sum, map_mul, map_pow, map_natCast, map_sub, map_one]
    apply (eq_div_iff den).mpr
    change (∑' j, f j) * (1-(c:E)^h) = ∑ i ∈ range h, f i
    linear_combination -eqn
  have intF (j : ℕ) : IsIntegral ℤ (f j) := by
    obtain ⟨n,pos,hn⟩ := isOfFinOrder_iff_pow_eq_one.mp (un j)
    have iu : IsIntegral ℤ (φ (u j)) := ⟨X^n-1, monic_X_pow_sub_C 1 pos.ne', by
      simp [hn]⟩
    exact ((isIntegral_natCast (R:=ℤ) c).pow j).mul iu
  let F (j : ℕ) : integralClosure ℤ E := ⟨f j,intF j⟩
  obtain ⟨z,nz,lim⟩ := upper_box_nonzero_limit F U upper hit ni (by
    simpa [F, ← value] using summ.hasSum.tendsto_sum_nat)
  refine ⟨z,nz,?_⟩
  change Tendsto (fun L => boxProductSum f U L) atTop (𝓝 z)
  simpa [F,boxProductSum] using lim

end NormalityChecker.StonehamPolynomial
