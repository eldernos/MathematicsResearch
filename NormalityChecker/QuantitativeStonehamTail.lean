module

public import NormalityChecker.StonehamPolynomialExpansion

/-! A uniform real error bound at every cutoff of a product of Stoneham series. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

private lemma geom_bound {q : ℕ} (hq : 2 ≤ q) (L : ℕ) :
    ∑ j ∈ range L, ((q : ℝ)⁻¹)^j ≤ 2 := by
  refine (sum_le_sum fun j _ => pow_le_pow_left₀ (by positivity) ?_ j).trans
    (sum_geometric_two_le L)
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq)

/-- Once the first admissible exponent is reached, the remaining geometric sum
is at most twice its first term. The finite cutoff may precede the first hit. -/
private lemma geom_tail_bound {q : ℕ} (hq : 2 ≤ q) (W n L : ℕ) :
    ∑ j ∈ range L, (if n < W*q^j then (n+1 : ℕ)*((q : ℝ)⁻¹)^j else 0) ≤ 2*W := by
  classical
  let f (j : ℕ) : ℝ := if n < W*q^j then (n+1 : ℕ)*((q : ℝ)⁻¹)^j else 0
  change ∑ j ∈ range L, f j ≤ _
  by_cases hit : ∃ j : ℕ, n < W*q^j
  · let K := Nat.find hit
    have first : (n+1 : ℕ) ≤ W*q^K := Nat.find_spec hit
    have zero : ∑ j ∈ range K, f j = 0 := sum_eq_zero (fun j hj =>
      ite_eq_right (Nat.find_min hit (mem_range.mp hj)))
    have nonneg (j : ℕ) : 0 ≤ f j := by dsimp [f]; split <;> positivity
    have bound (j : ℕ) : f (K+j) ≤ W*((q : ℝ)⁻¹)^j := by
      dsimp [f]; split
      · rw [pow_add, ← mul_assoc]
        gcongr
        rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        exact_mod_cast first
      · positivity
    have le := sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_add_left L K))
      (fun i _ _ => nonneg i)
    apply (show ∑ j ∈ range L, f j ≤ ∑ j ∈ range (K+L), f j from le).trans
    rw [sum_range_add, zero, zero_add]
    apply (sum_le_sum fun j _ => bound j).trans
    rw [← mul_sum, mul_comm (2 : ℝ)]
    gcongr
    exact geom_bound hq L
  · simp [f, fun j => not_exists.mp hit j]

/-- Union bound for the weights beyond a sum of geometric insertion positions.
The constant is deliberately coarse and applies to every finite index box. -/
private lemma box_tail_mass {d : ℕ} (q m : Fin d → ℕ) (hq : ∀ i, 2 ≤ q i) (n L : ℕ) :
    ∑ v ∈ box d L, (if n < ∑ i, m i * q i ^ v i then
      (n+1 : ℕ) * ∏ i, ((q i : ℝ)⁻¹) ^ v i else 0) ≤
      d * (2 * (max 1 (∑ i, m i) : ℕ))^d := by
  classical
  let W := ∑ i, m i
  let g (t i : Fin d) (j : ℕ) : ℝ := if i = t then
    (if n < W * q i ^ j then (n+1 : ℕ) * ((q i : ℝ)⁻¹)^j else 0)
    else ((q i : ℝ)⁻¹)^j
  have pos (t i : Fin d) (j : ℕ) : 0 ≤ g t i j := by dsimp [g]; split_ifs <;> positivity
  have hit (v : Vector d) (large : n < ∑ i, m i * q i ^ v i) :
      ∃ t, n < W*q t ^ v t := by
    by_contra! small
    have le := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin d))) =>
      Nat.mul_le_mul_left (m i) (small i)
    simp_rw [← Nat.mul_left_comm W] at le
    rw [← mul_sum, ← sum_mul] at le
    have hW : W ≠ 0 := by
      intro z
      have zero : ∀ i, m i = 0 := fun i => Nat.eq_zero_of_le_zero
        ((single_le_sum (fun j _ => Nat.zero_le (m j)) (mem_univ i)).trans z.le)
      simp [zero] at large
    exact (Nat.not_lt_of_ge (Nat.le_of_mul_le_mul_left le (Nat.pos_of_ne_zero hW))) large
  have term (v : Vector d) : (if n < ∑ i, m i * q i ^ v i then
        (n+1 : ℕ) * ∏ i, ((q i : ℝ)⁻¹)^v i else 0) ≤ ∑ t, ∏ i, g t i (v i) := by
    split_ifs with large
    · obtain ⟨t, ht⟩ := hit v large
      apply le_trans _ (single_le_sum (fun u _ => prod_nonneg (fun i _ => pos u i _)) (mem_univ t))
      have eqn (i : Fin d) : g t i (v i) =
          (if i=t then ((n+1 : ℕ) : ℝ) else 1) * ((q i : ℝ)⁻¹)^v i := by
        by_cases h : i=t <;> simp_all [g]
      simp only [eqn, prod_mul_distrib, prod_ite_eq', mem_univ, ite_true, le_refl]
    · exact sum_nonneg (fun t _ => prod_nonneg (fun i _ => pos t i _))
  have factor (t i : Fin d) : ∑ j ∈ range L, g t i j ≤ 2 * (max 1 W : ℕ) := by
    by_cases h : i = t
    · simpa [g, h] using (geom_tail_bound (hq t) W n L).trans
        (show (2 : ℝ)*W ≤ 2*(max 1 W : ℕ) by gcongr; exact le_max_right ..)
    · simpa [g, h] using (geom_bound (hq i) L).trans
        (show (2 : ℝ) ≤ 2*(max 1 W : ℕ) by
          have h1 : (1 : ℝ) ≤ (max 1 W : ℕ) := by exact_mod_cast le_max_left 1 W
          linarith)
  apply (sum_le_sum fun v _ => term v).trans
  rw [sum_comm]
  have each (t : Fin d) : ∑ v ∈ box d L, ∏ i, g t i (v i) ≤ (2*(max 1 W : ℕ) : ℝ)^d := by
    rw [box, ← prod_univ_sum]
    calc
      _ ≤ ∏ _i : Fin d, (2*(max 1 W : ℕ) : ℝ) := by
        gcongr with i
        exact factor t i
      _ = _ := by simp
  simpa [W] using sum_le_sum (s:=univ) (fun t _ => each t)

/-- For every cutoff, the absolute real tail is at most a computable constant
divided by `n+1`. The zero-index convention and the prefix agree with `axis`. -/
theorem product_tail_bound {b p d : ℕ} (hb : 1 < b) (hp : 1 < p)
    (e : Strides d) (m : Vector d) (hm : ∀ i, 0 < m i) (n : ℕ) :
    |(b : ℝ)^n * (∏ i, axis b (p^(e i : ℕ)) (m i)) - (productPrefix b p e m n : ℝ)| ≤
      d * (2 * (max 1 (∑ i, m i) : ℕ))^d / (n+1) := by
  classical
  let q (i : Fin d) := p^(e i : ℕ)
  have hq (i : Fin d) : 2 ≤ q i := hp.trans_le (Nat.le_self_pow (e i).pos.ne' _)
  let w (i : Fin d) (j : ℕ) := ((q i : ℝ)⁻¹)^j
  let f (i : Fin d) (j : ℕ) := w i j / (b : ℝ)^(m i * q i ^ j)
  let s (v : Vector d) := ∑ i, m i * q i ^ v i
  have eqs (v : Vector d) : s v = position p e m v := by simp [s, q, position, stretch, pow_mul]
  have hsum (i : Fin d) : Summable (f i) := by
    have r : (q i : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hq i)
    apply Summable.of_nonneg_of_le (f:=w i) (fun j => by dsimp [f,w]; positivity)
      (fun j => div_le_self (by dsimp [w]; positivity)
        (one_le_pow₀ (by exact_mod_cast hb.le)))
    exact summable_geometric_of_lt_one (by positivity) r
  have conv := tendsto_finsetProd univ (fun i _ => (hsum i).hasSum.tendsto_sum_nat)
  let A := active p e m n
  have active_box : ∀ᶠ L : ℕ in atTop, A ⊆ box d L := by
    filter_upwards [eventually_gt_atTop (A.sup weight)] with L big v hv
    apply mem_box.mpr
    intro i
    exact (single_le_sum (fun j _ => Nat.zero_le (v j)) (mem_univ i)).trans_lt
      ((le_sup (f:=weight) hv).trans_lt big)
  let y (L : ℕ) := (b : ℝ)^n * ∏ i, ∑ j ∈ range L, f i j
  have limit : Tendsto y atTop (𝓝 ((b : ℝ)^n * ∏ i, axis b (q i) (m i))) :=
    conv.const_mul _
  apply le_of_tendsto ((limit.sub_const (productPrefix b p e m n : ℝ)).abs)
  filter_upwards [active_box] with L incl
  let full (v : Vector d) := (b : ℝ)^n * ∏ i, f i (v i)
  have full_eq (v : Vector d) : full v =
      (∏ i, w i (v i)) * ((b : ℝ)^n / (b : ℝ)^s v) := by
    dsimp [full, f, s]; rw [prod_div_distrib, prod_pow_eq_pow_sum]; ring
  have pref : (productPrefix b p e m n : ℝ) = ∑ v ∈ A, full v := by
    unfold productPrefix
    push_cast
    apply sum_congr rfl
    intro v hv
    rw [full_eq, pow_sub₀ (b : ℝ) (by positivity) ((mem_active hp hm).mp hv), ← eqs]
    simp [w, q, weight, stretch, ← pow_mul, ← prod_pow_eq_pow_sum, div_eq_mul_inv,
      mul_comm, inv_pow, ← prod_inv_distrib]
  have rest : y L - (productPrefix b p e m n : ℝ) = ∑ v ∈ box d L \ A, full v := by
    dsimp only [y]
    rw [prod_univ_sum, mul_sum, pref]
    exact (sum_sdiff_eq_sub incl).symm
  rw [rest, abs_of_nonneg (sum_nonneg (fun v _ => by rw [full_eq]; dsimp [w]; positivity))]
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_comm, mul_sum]
  let G (v : Vector d) := if n < s v then (n+1 : ℕ) * ∏ i, w i (v i) else 0
  have term (v : Vector d) (hv : v ∈ box d L \ A) : (n+1 : ℝ)*full v ≤ G v := by
    have late : n < s v := lt_of_not_ge (fun h =>
      (mem_sdiff.mp hv).2 ((mem_active hp hm).mpr ((eqs v) ▸ h)))
    have le : (b : ℝ)^n / (b : ℝ)^s v ≤ 1 := (div_le_one (by positivity)).mpr
      (pow_le_pow_right₀ (by exact_mod_cast hb.le) late.le)
    dsimp only [G]; rw [ite_eq_left late, full_eq]; push_cast
    gcongr
    exact mul_le_of_le_one_right (by dsimp [w]; positivity) le
  apply (sum_le_sum term).trans
  apply (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun v _ _ => by dsimp [G,w]; split <;> positivity)).trans
  exact box_tail_mass q m hq n L

end NormalityChecker.StonehamPolynomial
