module

public import NormalityChecker.FourierTest
public import NormalityChecker.RectangleFrequency
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Pi

/-! The multidimensional Weyl criterion for simultaneous radix shifts. -/
@[expose] public section
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace NormalityChecker.JointWeyl

variable {d : ℕ}
private abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
private local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

private abbrev Character := @UnitAddTorus.mFourier (Fin d) _
private def Good (u : ℕ → Torus d) (f : C(Torus d, ℂ)) : Prop :=
  Tendsto (mean (fun n => f (u n))) atTop (𝓝 (∫ x, f x))

private lemma good_continuous (u : ℕ → Torus d) (h : ∀ t, Good u (Character t))
    (f : C(Torus d, ℂ)) : Good u f := by
  classical
  let V := Submodule.span ℂ (Set.range (Character (d := d)))
  have integrable (v : C(Torus d, ℂ)) : Integrable v := v.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace v)
  have spanGood (g : C(Torus d, ℂ)) (hg : g ∈ V) : Good u g := by
    induction hg using Submodule.span_induction with
    | mem x hx => obtain ⟨t,rfl⟩ := hx; exact h t
    | zero => simp [Good, show mean (fun _ => 0) = (fun _ => 0) by funext N; simp [mean]]
    | add x y _ _ hx hy =>
      unfold Good at hx hy ⊢
      simpa only [ContinuousMap.add_apply, funext (fun N => (show mean (fun n => x (u n)+y (u n)) N =
        mean (fun n => x (u n)) N + mean (fun n => y (u n)) N by simp [mean, sum_add_distrib, add_div])),
        integral_add (integrable x) (integrable y)] using hx.add hy
    | smul z x _ hx =>
      unfold Good at hx ⊢
      simpa only [ContinuousMap.smul_apply, smul_eq_mul, funext (fun N => (show
        mean (fun n => z*x (u n)) N = z*mean (fun n => x (u n)) N by simp [mean, ← mul_sum, mul_div_assoc])),
        integral_const_mul] using hx.const_mul z
  have dense : f ∈ closure (V : Set _) := by
    rw [← Submodule.topologicalClosure_coe, show V.topologicalClosure = ⊤ from
      UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  rw [Good, Metric.tendsto_atTop]
  intro ε he
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.mp dense (ε/3) (by positivity)
  obtain ⟨M,hM⟩ := Metric.tendsto_atTop.mp (spanGood g hg) (ε/3) (by positivity)
  have bound (z : Torus d) : ‖f z - g z‖ ≤ ‖f-g‖ := (f-g).norm_coe_le_norm z
  have intBound : ‖(∫ x, f x) - ∫ x, g x‖ ≤ ‖f-g‖ := by
    rw [← integral_sub (integrable f) (integrable g)]
    simpa using norm_integral_le_of_norm_le_const (μ := volume) (Filter.Eventually.of_forall bound)
  refine ⟨max M 1, fun N hN => ?_⟩
  have pos : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have avgBound : ‖mean (fun n => f (u n)) N - mean (fun n => g (u n)) N‖ ≤ ‖f-g‖ := by
    rw [mean, mean, ← sub_div, ← sum_sub_distrib, norm_div, Complex.norm_natCast, div_le_iff₀ pos]
    exact (norm_sum_le _ _).trans ((sum_le_sum (fun i _ => bound (u i))).trans_eq (by simp [mul_comm]))
  have tri := dist_triangle4 (mean (fun n => f (u n)) N) (mean (fun n => g (u n)) N)
    (∫ x, g x) (∫ x, f x)
  rw [dist_comm (∫ x, g x)] at tri
  simp only [dist_eq_norm] at tri hfg ⊢
  have close := hM N (by omega)
  rw [dist_eq_norm] at close
  linarith

private lemma fourier_good {b : ℕ} (x : Fin d → ℝ)
    (normal : ∀ t : Fin d → ℤ, t ≠ 0 → NormalIn b (∑ i, (t i : ℝ) * x i))
    (t : Fin d → ℤ) :
    Good (fun n i => ((shift b (x i) n : ℝ) : UnitAddCircle)) (Character t) := by
  classical
  by_cases zero : t = 0
  · subst t
    simp only [Character, UnitAddTorus.mFourier_zero, Good, ContinuousMap.one_apply, integral_const,
      probReal_univ, one_smul]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp [mean, hn.ne']
  obtain ⟨j,hj⟩ := Function.ne_iff.mp zero
  change t j ≠ 0 at hj
  have cancel := fourier_of_normal (normal t zero) 1 one_ne_zero
  rw [Good]
  have integralZero : (∫ z, Character t z) = 0 := by
    rw [show (fun z => Character t z) = (fun z : Torus d => ∏ i, fourier (t i) (z i)) from rfl,
      integral_fintype_prod_volume_eq_prod]
    apply prod_eq_zero (mem_univ j)
    simpa [Weyl.cInt, ← UnitAddCircle.intervalIntegral_preimage 0] using Weyl.cInt_fourier_ne (t j) hj
  rw [integralZero]
  convert cancel using 1
  apply congrArg mean; funext n
  change (∏ i, fourier (t i) ((shift b (x i) n : ℝ) : UnitAddCircle)) =
    phase ((1 : ℤ) * ((b : ℝ)^n * (∑ i, (t i : ℝ) * x i)))
  simp only [Int.cast_one,one_mul,mul_sum]
  rw [phase, Complex.ofReal_sum, mul_sum, Complex.exp_sum]
  apply prod_congr rfl
  intro i _
  trans phase ((t i : ℝ)*shift b (x i) n)
  · rw [fourier_coe_apply,phase]; push_cast; ring_nf
  · rw [shift, phase_fract, phase]; push_cast; ring_nf


private def productAverage (u : ℕ → Fin d → ℝ) (g : Fin d → C(UnitAddCircle, ℝ)) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, ∏ i, g i (u n i : UnitAddCircle)) / N

private lemma product_limit {u : ℕ → Fin d → ℝ}
    (h : ∀ f, Good (fun n i => (u n i : UnitAddCircle)) f) (g : Fin d → C(UnitAddCircle, ℝ)) :
    Tendsto (productAverage u g) atTop (𝓝 (∏ i, ∫ z, g i z)) := by
  let f : C(Torus d, ℂ) := ⟨fun z => ((∏ i, g i (z i) : ℝ) : ℂ), by fun_prop⟩
  have H := Complex.continuous_re.continuousAt.tendsto.comp (h f)
  change Tendsto (fun n => (mean (fun j => f (fun i => (u j i : UnitAddCircle))) n).re)
    atTop (𝓝 (∫ z, f z).re) at H
  have re_mean (n : ℕ) : (mean (fun j => f (fun i => (u j i : UnitAddCircle))) n).re =
      productAverage u g n := by
    change ((∑ j ∈ range n, ((∏ i, g i (u j i : UnitAddCircle) : ℝ) : ℂ)) / (n : ℂ)).re = _
    rw [← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
    rfl
  simp_rw [re_mean] at H
  simpa only [f,ContinuousMap.coe_mk,integral_complex_ofReal,Complex.ofReal_re,
    integral_fintype_prod_volume_eq_prod] using H

private lemma rectangle_limit (u : ℕ → Fin d → ℝ) (unit : ∀ n i, u n i ∈ Set.Ico (0 : ℝ) 1)
    (h : ∀ t, Good (fun n i => (u n i : UnitAddCircle)) (Character t))
    (a c : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (hac : ∀ i, a i ≤ c i) (hc : ∀ i, c i ≤ 1) :
    Tendsto (rectangleFrequency u a c) atTop (𝓝 (∏ i, (c i - a i))) := by
  classical
  let len := fun i => c i - a i
  let δ (k : ℕ) := 1 / ((k : ℝ)+1)
  have pos (k) : 0 < δ k := by dsimp [δ]; positivity
  have small : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let lower (k : ℕ) (i : Fin d) := Weyl.trapLo (a i) (c i) (δ k)
  let upper (k : ℕ) (i : Fin d) := Weyl.trapUp (a i) (c i) (δ k)
  have sandwich k N : productAverage u (lower k) N ≤ rectangleFrequency u a c N ∧
      rectangleFrequency u a c N ≤ productAverage u (upper k) N := by
    simp only [productAverage,rectangleFrequency, card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    constructor <;> apply div_le_div_of_nonneg_right _ (by positivity) <;> apply sum_le_sum <;> intro n _
    · split_ifs with hit
      · exact prod_le_one₀ (fun i _ => Weyl.trapLo_nonneg ..) (fun i _ => Weyl.trapLo_le_one ..)
      · push Not at hit
        obtain ⟨i,hi⟩ := hit
        have out : ¬ (a i ≤ u n i ∧ u n i < c i) := by grind
        exact le_of_eq (prod_eq_zero (mem_univ i) (Weyl.trapLo_eq_zero_outside _ _ _ _ (ha i)
          (hac i) (hc i) (unit n i).1 (unit n i).2 out (pos k)))
    · split_ifs with hit
      · exact one_le_prod₀ (fun i _ => Weyl.trapUp_ge_indicator _ _ _ _ (pos k) (hit i))
      · exact prod_nonneg (fun i _ => Weyl.trapUp_nonneg _ _ _ (pos k) _)
  have lowerBound k : (∏ i, max 0 (len i - 2*δ k)) ≤ ∏ i, ∫ z, lower k i z := by
    apply prod_le_prod₀ (fun _ _ => le_max_left ..)
    intro i _
    apply max_le
    · exact integral_nonneg (fun z => Weyl.trapLo_nonneg ..)
    · simpa [lower, len, ← UnitAddCircle.intervalIntegral_preimage 0] using
        Weyl.le_integral_trapLo _ _ _ (ha i) (hac i) (hc i) (pos k)
  have upperBound k : (∏ i, ∫ z, upper k i z) ≤ ∏ i, (len i + 2*δ k) := by
    apply prod_le_prod₀ (fun i _ => integral_nonneg (fun z => Weyl.trapUp_nonneg _ _ _ (pos k) _))
    intro i _
    simpa [upper, len, ← UnitAddCircle.intervalIntegral_preimage 0] using
      Weyl.integral_trapUp_le _ _ _ (ha i) (hac i) (hc i) (pos k)
  have lowerLimit : Tendsto (fun k => ∏ i, max 0 (len i - 2*δ k)) atTop (𝓝 (∏ i, len i)) := by
    apply tendsto_finsetProd
    intro i _
    simpa [max_eq_right (sub_nonneg.mpr (hac i)),len] using
      (tendsto_const_nhds (x := (0:ℝ))).max (tendsto_const_nhds (x := len i) |>.sub (small.const_mul 2))
  have upperLimit : Tendsto (fun k => ∏ i, (len i + 2*δ k)) atTop (𝓝 (∏ i, len i)) := by
    apply tendsto_finsetProd
    intro i _
    simpa using (tendsto_const_nhds (x := len i)).add (small.const_mul 2)
  apply tendsto_order.mpr
  constructor
  · intro y hy
    obtain ⟨k,hk⟩ := (lowerLimit.eventually_const_lt hy).exists
    filter_upwards [(product_limit (good_continuous _ h) (lower k)).eventually_const_lt
      (hk.trans_le (lowerBound k))] with N hN
    exact hN.trans_le (sandwich k N).1
  · intro y hy
    obtain ⟨k,hk⟩ := (upperLimit.eventually_lt_const hy).exists
    filter_upwards [(product_limit (good_continuous _ h) (upper k)).eventually_lt_const
      ((upperBound k).trans_lt hk)] with N hN
    exact (sandwich k N).2.trans_lt hN

/-- Scalar normality for every nonzero integer linear combination implies convergence
of the actual simultaneous rectangle frequencies in every finite dimension. -/
theorem rectangle_of_scalar_normal {b d : ℕ} (x : Fin d → ℝ)
    (normal : ∀ t : Fin d → ℤ, t ≠ 0 → NormalIn b (∑ i, (t i : ℝ) * x i)) :
    JointUniform b x :=
  rectangle_limit _ (fun _ _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
    (fourier_good x normal)

end NormalityChecker.JointWeyl
