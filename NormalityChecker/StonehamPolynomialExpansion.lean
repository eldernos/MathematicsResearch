module

public import NormalityChecker.StonehamPolynomialPrefix
public import NormalityChecker.StonehamComponents
public import Mathlib.Analysis.Normed.Group.Tannery

/-! Real convergence and clean-block propagation for products of Stoneham series. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

variable {d : ℕ}

private lemma boxes_cofinal : Tendsto (box d) atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  filter_upwards [eventually_gt_atTop (s.sup weight)] with L hL v hv
  exact mem_box.mpr (fun i =>
    (single_le_sum (fun t _ => Nat.zero_le (v t)) (mem_univ i)).trans_lt
      ((le_sup (f:=weight) hv).trans_lt hL))

private lemma product_sums (f : Fin d → ℕ → ℝ) (nonneg : ∀ i j, 0 ≤ f i j)
    (summ : ∀ i, Summable (f i)) :
    HasSum (fun v : Vector d => ∏ i, f i (v i)) (∏ i, ∑' j, f i j) := by
  have factor (k : ℕ) : (∑ v ∈ box d k, ∏ i, f i (v i)) = ∏ i, ∑ j ∈ range k, f i j :=
    (prod_univ_sum _ _).symm
  have conv : Summable (fun v : Vector d => ∏ i, f i (v i)) := by
    apply summable_of_sum_le (c := ∏ i, ∑' j, f i j) (fun v => prod_nonneg (fun i _ => nonneg i _))
    intro s
    obtain ⟨k,hk⟩ := (boxes_cofinal.eventually_ge_atTop s).exists
    apply (sum_le_sum_of_subset_of_nonneg hk (fun _ _ _ => prod_nonneg (fun i _ => nonneg i _))).trans
    rw [factor]
    gcongr with i
    · exact fun _ _ => sum_nonneg (fun _ _ => nonneg _ _)
    · exact (summ i).sum_le_tsum _ (fun _ _ => nonneg _ _)
  have lim := tendsto_finsetProd (univ : Finset (Fin d)) (fun i _ => (summ i).hasSum.tendsto_sum_nat)
  have e := tendsto_nhds_unique (conv.hasSum.comp boxes_cofinal) (lim.congr (fun k => (factor k).symm))
  exact e ▸ conv.hasSum

/-- The factors indexed from zero have weights `p⁻ʲ`. Multiplication by
`m` changes the repository's `radixComponent b p m` into this normalization. -/
noncomputable def axis (b p m : ℕ) : ℝ :=
  ∑' j : ℕ, (p:ℝ)⁻¹^j / (b:ℝ)^(m*p^j)

theorem axis_eq {b p m : ℕ} (hm : 0 < m) :
    axis b p m = (m:ℝ) * radixComponent b p m := by
  rw [axis,radixComponent,← tsum_mul_left]
  apply tsum_congr
  intro j; rw [one_div_pow, inv_pow]; field_simp

private lemma series_sums {b p : ℕ} (hb : 1 < b) (hp : 1 < p) (m : Vector d) :
    HasSum (fun j => (p:ℝ)⁻¹^weight j / (b:ℝ)^position p m j) (∏ i, axis b p (m i)) := by
  let r := (p:ℝ)⁻¹
  have pos : 0 ≤ r := by dsimp [r]; positivity
  have geo := summable_geometric_of_lt_one pos (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp))
  have h := product_sums (fun i j => r^j / (b:ℝ)^(m i*p^j)) (fun _ _ => by positivity)
    (fun i => Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun j => div_le_self (pow_nonneg pos _) (one_le_pow₀ (by exact_mod_cast hb.le))) geo)
  apply h.congr_fun
  intro v
  simp only [position, weight, prod_div_distrib, ← prod_pow_eq_pow_sum, r]

theorem product_tail {b p : ℕ} (hb : 1 < b) (hp : 1 < p) {m : Vector d} (hm : ∀ i, 0 < m i) :
    Tendsto (fun n => (b:ℝ)^n * (∏ i, axis b p (m i)) - (productPrefix b p m n:ℝ)) atTop (𝓝 0) := by
  classical
  let r := (p:ℝ)⁻¹
  let coeff (j : Vector d) := r^weight j
  let term (j : Vector d) := coeff j / (b:ℝ)^position p m j
  let tail (n : ℕ) (j : Vector d) := if position p m j ≤ n then 0 else (b:ℝ)^n * term j
  have pos : 0 ≤ r := by dsimp [r]; positivity
  have bp : (0:ℝ)<b := by exact_mod_cast (by omega : 0<b)
  have b1 : (1:ℝ)≤b := by exact_mod_cast hb.le
  have geo := summable_geometric_of_lt_one pos (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp))
  have cs : Summable coeff := by
    have h := (product_sums (d:=d) (fun _ j => r^j) (fun _ _ => pow_nonneg pos _) (fun _ => geo)).summable
    simpa only [coeff,weight,prod_pow_eq_pow_sum] using h
  have ts : HasSum term (∏ i, axis b p (m i)) := series_sums hb hp m
  have bound (n : ℕ) (j : Vector d) : ‖tail n j‖ ≤ coeff j := by
    dsimp only [tail]
    split_ifs with le
    · simpa only [norm_zero] using pow_nonneg pos (weight j)
    change ‖(b:ℝ)^n * (r^weight j / (b:ℝ)^position p m j)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_div_assoc', div_le_iff₀ (by positivity)]
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ b1 (by omega)) (pow_nonneg pos _)
  have conv := tendsto_tsum_of_dominated_convergence (g:=fun _ => (0:ℝ)) cs
    (f:=tail) (fun j => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop (position p m j)] with n hn
      simp [tail,hn])) (.of_forall bound)
  simp only [tsum_zero] at conv
  apply conv.congr
  intro n
  let part (j : Vector d) := if position p m j ≤ n then (b:ℝ)^n * term j else 0
  have supported : ∀ j ∉ active p m n, part j = 0 := fun j hj =>
    ite_eq_right (fun le => hj ((mem_active hp hm).mpr le))
  have finite : HasSum part (∑ j ∈ active p m n, part j) := hasSum_sum_of_ne_finset_zero supported
  have tf := (cs.of_norm_bounded (bound n)).hasSum
  have e := (finite.add tf).tsum_eq
  have es : (fun j => part j + tail n j) = (fun j => (b:ℝ)^n * term j) := by
    funext j; simp [part,tail]; split <;> simp
  change (∑' j, (part j + tail n j)) = _ at e
  rw [es,(ts.mul_left _).tsum_eq] at e
  have pr : (productPrefix b p m n:ℝ) = ∑ j ∈ active p m n, part j := by
    unfold productPrefix
    push_cast
    apply sum_congr rfl
    intro j hj
    have le := (mem_active hp hm).mp hj
    dsimp only [part,term,coeff,r]; rw [ite_eq_left le,pow_sub₀ (b:ℝ) bp.ne' le,inv_pow]; ring
  rw [pr]; linarith only [e]

theorem prefix_follows {b p : ℕ} (hp : 1 < p) {m : Vector d}
    (hm : ∀ i, 0 < m i) {n i : ℕ} (free : ∀ j, n < position p m j → n+i < position p m j) :
    productPrefix b p m (n+i) = (b:ℚ)^i * productPrefix b p m n := by
  have same : active p m (n+i) = active p m n := by
    ext j
    rw [mem_active hp hm, mem_active hp hm]
    constructor
    · intro le; exact le_of_not_gt (fun h => (free j h).not_ge le)
    · omega
  simp only [productPrefix,same,mul_sum]; apply sum_congr rfl
  intro j hj
  have le := (mem_active hp hm).mp hj
  rw [show n+i-position p m j=i+(n-position p m j) by omega,pow_add,mul_div_assoc]

end NormalityChecker.StonehamPolynomial
