module

public import NormalityChecker.SharpTranslation

/-! # The exact addition spectrum of radix discrepancy

For an integer radix `b` write `D_N(x)` for the extreme interval discrepancy
`radixDiscrepancy b x N` of the first `N` radix shifts of `x`.

**Necessity.** For every `N > 0` and all reals `x, y` the triple
`(D_N(x), D_N(y), D_N(x+y))` lies in the polytope
`P = {(α,β,γ) : 0 ≤ α, β, γ, α+β ≤ 1+γ, β+γ ≤ 1+α, α+γ ≤ 1+β}`
(`finite_necessity`). Equivalently `max(0, α+β-1) ≤ γ ≤ 1-|α-β|` with `α, β ∈ [0,1]`
(`mem_polytope_iff`). This is two applications of the Phase 18 sharp translation law. Limits
and cluster points stay in `P` (`limit_necessity`, `clusterPt_necessity`).

**Geometry.** `P` is the convex hull of the five cube vertices
`(1,1,1), (0,1,0), (1,0,0), (0,0,1), (0,0,0)` and these are exactly its extreme points
(`polytope_eq_convexHull`, `isExtremeIn_polytope_iff`). The explicit convex weights are
`h, β-h, α-h, γ-h, 1-α-β-γ+2h` with `h = max(0,(α+β+γ-1)/2)` (`fiveWeights`).

**Reduction.** A realization of the five-type mixtures gives every point of `P` as a limiting
triple (`polytope_subset_addSpectrum_of_realizable`).
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.AdditionSpectrum

open NormalityChecker.SharpTranslation

/-! ## The polytope -/

/-- The six facets allowed by the sharp translation law. -/
def polytope : Set (ℝ × ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧ v.1 + v.2.1 ≤ 1 + v.2.2 ∧
    v.2.1 + v.2.2 ≤ 1 + v.1 ∧ v.1 + v.2.2 ≤ 1 + v.2.1}

theorem mem_polytope {α β γ : ℝ} : (α, β, γ) ∈ polytope ↔
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β ≤ 1 + γ ∧ β + γ ≤ 1 + α ∧ α + γ ≤ 1 + β := Iff.rfl

/-- The form `max(0, α+β-1) ≤ γ ≤ 1-|α-β|`. -/
theorem mem_polytope_iff {α β γ : ℝ} : (α, β, γ) ∈ polytope ↔
    0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 ∧ max 0 (α + β - 1) ≤ γ ∧ γ ≤ 1 - |α - β| := by
  rw [mem_polytope]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, by linarith, h2, by linarith, max_le h3 (by linarith), ?_⟩
    have : |α - β| ≤ 1 - γ := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · rintro ⟨h1, -, h2, -, h3, h4⟩
    have h3' := (max_le_iff.mp h3)
    have e1 := le_abs_self (α - β)
    have e2 := neg_abs_le (α - β)
    refine ⟨h1, h2, h3'.1, by linarith [h3'.2], by linarith, by linarith⟩

theorem polytope_le_one {v : ℝ × ℝ × ℝ} (hv : v ∈ polytope) :
    v.1 ≤ 1 ∧ v.2.1 ≤ 1 ∧ v.2.2 ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  exact ⟨by linarith, by linarith, by linarith⟩

theorem isClosed_polytope : IsClosed polytope := by
  have h : polytope = {v : ℝ × ℝ × ℝ | 0 ≤ v.1} ∩ {v | 0 ≤ v.2.1} ∩ {v | 0 ≤ v.2.2} ∩
      {v | v.1 + v.2.1 ≤ 1 + v.2.2} ∩ {v | v.2.1 + v.2.2 ≤ 1 + v.1} ∩
      {v | v.1 + v.2.2 ≤ 1 + v.2.1} := by
    ext v; simp only [polytope, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [h]
  repeat' apply IsClosed.inter
  all_goals exact isClosed_le (by fun_prop) (by fun_prop)

theorem convex_polytope : Convex ℝ polytope := by
  intro u hu v hv a c ha hc hac
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := hu
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hv
  simp only [polytope, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_left u4 ha, mul_le_mul_of_nonneg_left v4 hc,
      mul_le_mul_of_nonneg_left u5 ha, mul_le_mul_of_nonneg_left v5 hc,
      mul_le_mul_of_nonneg_left u6 ha, mul_le_mul_of_nonneg_left v6 hc]

/-! ## Five vertices and five weights -/

/-- The five vertices, in the order of the five realization types: both numbers retired,
only `x` active, only `y` active, inverse active states, equal active states. -/
def fiveVertex : Fin 5 → ℝ × ℝ × ℝ := ![(1, 1, 1), (0, 1, 0), (1, 0, 0), (0, 0, 1), (0, 0, 0)]

/-- The common excess `h = max(0, (α+β+γ-1)/2)`. -/
noncomputable def commonExcess (α β γ : ℝ) : ℝ := max 0 ((α + β + γ - 1) / 2)

/-- The convex weights `h, β-h, α-h, γ-h, 1-α-β-γ+2h`. -/
noncomputable def fiveWeights (α β γ : ℝ) : Fin 5 → ℝ :=
  ![commonExcess α β γ, β - commonExcess α β γ, α - commonExcess α β γ,
    γ - commonExcess α β γ, 1 - α - β - γ + 2 * commonExcess α β γ]

theorem fiveWeights_nonneg {α β γ : ℝ} (hv : (α, β, γ) ∈ polytope) (i : Fin 5) :
    0 ≤ fiveWeights α β γ i := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  have m0 : 0 ≤ commonExcess α β γ := le_max_left _ _
  have m1 : (α + β + γ - 1) / 2 ≤ commonExcess α β γ := le_max_right _ _
  fin_cases i <;> simp only [fiveWeights, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] <;> try linarith
  all_goals
    rw [sub_nonneg]
    exact max_le (by linarith) (by linarith)

theorem sum_fiveWeights (α β γ : ℝ) : ∑ i, fiveWeights α β γ i = 1 := by
  simp only [Fin.sum_univ_five, fiveWeights, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The weights reproduce the triple. -/
theorem sum_fiveWeights_smul (α β γ : ℝ) :
    ∑ i, fiveWeights α β γ i • fiveVertex i = (α, β, γ) := by
  simp only [Fin.sum_univ_five, fiveWeights, fiveVertex, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one, mul_zero]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem fiveVertex_mem (i : Fin 5) : fiveVertex i ∈ polytope := by
  fin_cases i <;> simp [fiveVertex, polytope]

theorem polytope_eq_convexHull : polytope = convexHull ℝ (Set.range fiveVertex) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨α, β, γ⟩ := v
    rw [← sum_fiveWeights_smul α β γ]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => fiveWeights_nonneg hv i)
      (sum_fiveWeights α β γ) (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
  · exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact fiveVertex_mem i) convex_polytope

/-- Extreme points of a set of triples, stated directly: the point is in the set and is not
an interior point of a segment with both ends in the set. -/
def IsExtremeIn (S : Set (ℝ × ℝ × ℝ)) (v : ℝ × ℝ × ℝ) : Prop :=
  v ∈ S ∧ ∀ u ∈ S, ∀ w ∈ S, ∀ a c : ℝ, 0 < a → 0 < c → a + c = 1 → a • u + c • w = v →
    u = v ∧ w = v

/-- A coordinate equal to `0` or `1` in a segment of the cube forces both ends. -/
private lemma seg_coord {a c p q z : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h : a * p + c * q = z)
    (hz : z = 0 ∨ z = 1) : p = z ∧ q = z := by
  rcases hz with rfl | rfl
  · constructor <;> nlinarith [mul_nonneg ha.le hp0, mul_nonneg hc.le hq0]
  · constructor <;> nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hp1),
      mul_nonneg hc.le (sub_nonneg.mpr hq1)]

theorem fiveVertex_extreme (i : Fin 5) : IsExtremeIn polytope (fiveVertex i) := by
  refine ⟨fiveVertex_mem i, ?_⟩
  intro u hu v hv a c ha hc hac huv
  have bu := polytope_le_one hu
  have bv := polytope_le_one hv
  obtain ⟨u1, u2, u3, -⟩ := hu
  obtain ⟨v1, v2, v3, -⟩ := hv
  have e1 : a * u.1 + c * v.1 = (fiveVertex i).1 := by rw [← huv]; simp
  have e2 : a * u.2.1 + c * v.2.1 = (fiveVertex i).2.1 := by rw [← huv]; simp
  have e3 : a * u.2.2 + c * v.2.2 = (fiveVertex i).2.2 := by rw [← huv]; simp
  have z : ∀ j : Fin 5, ((fiveVertex j).1 = 0 ∨ (fiveVertex j).1 = 1) ∧
      ((fiveVertex j).2.1 = 0 ∨ (fiveVertex j).2.1 = 1) ∧
      ((fiveVertex j).2.2 = 0 ∨ (fiveVertex j).2.2 = 1) := by
    intro j; fin_cases j <;> simp [fiveVertex]
  obtain ⟨z1, z2, z3⟩ := z i
  obtain ⟨p1, q1⟩ := seg_coord ha hc hac u1 bu.1 v1 bv.1 e1 z1
  obtain ⟨p2, q2⟩ := seg_coord ha hc hac u2 bu.2.1 v2 bv.2.1 e2 z2
  obtain ⟨p3, q3⟩ := seg_coord ha hc hac u3 bu.2.2 v3 bv.2.2 e3 z3
  exact ⟨Prod.ext p1 (Prod.ext p2 p3), Prod.ext q1 (Prod.ext q2 q3)⟩

/-- Every extreme point of the polytope is one of the five vertices. -/
theorem extreme_mem_fiveVertex {v : ℝ × ℝ × ℝ} (hv : IsExtremeIn polytope v) :
    v ∈ Set.range fiveVertex := by
  obtain ⟨α, β, γ⟩ := v
  set w := fiveWeights α β γ
  have hw0 := fiveWeights_nonneg hv.1
  have hw1 : ∑ i, w i = 1 := sum_fiveWeights α β γ
  have hsum : ∑ i, w i • fiveVertex i = (α, β, γ) := sum_fiveWeights_smul α β γ
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have : ∑ i, w i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    linarith
  have hsplit : ∑ i, w i • fiveVertex i =
      w i • fiveVertex i + ∑ j ∈ univ.erase i, w j • fiveVertex j :=
    (Finset.add_sum_erase _ _ (mem_univ i)).symm
  have hwsplit : ∑ j, w j = w i + ∑ j ∈ univ.erase i, w j :=
    (Finset.add_sum_erase _ _ (mem_univ i)).symm
  rcases (show w i ≤ 1 by
      have : ∑ j ∈ univ.erase i, w j ≥ 0 := Finset.sum_nonneg (fun j _ => hw0 j)
      linarith).lt_or_eq with hlt | heq
  · -- a genuine segment through the vertex `i`
    set q := ∑ j ∈ univ.erase i, ((1 - w i)⁻¹ * w j) • fiveVertex j
    have hq : q ∈ polytope := by
      refine convex_polytope.sum_mem (fun j _ => mul_nonneg (inv_nonneg.mpr (by linarith))
        (hw0 j)) ?_ (fun j _ => fiveVertex_mem j)
      rw [← Finset.mul_sum]
      field_simp
      linarith
    have hv' : w i • fiveVertex i + (1 - w i) • q = (α, β, γ) := by
      rw [← hsum, hsplit]
      congr 1
      simp only [q, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      field_simp
    exact ⟨i, (hv.2 _ (fiveVertex_mem i) _ hq _ _ hi (by linarith) (by ring) hv').1⟩
  · -- all other weights vanish
    have hzero : ∀ j ∈ univ.erase i, w j = 0 := by
      have : ∑ j ∈ univ.erase i, w j = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw0 j)).mp this
    refine ⟨i, ?_⟩
    rw [← hsum, hsplit, heq, one_smul, Finset.sum_eq_zero (fun j hj => by rw [hzero j hj, zero_smul]),
      add_zero]

/-- **The exact five-vertex polytope.** Its extreme points are exactly the five vertices. -/
theorem isExtremeIn_polytope_iff (v : ℝ × ℝ × ℝ) :
    IsExtremeIn polytope v ↔ v ∈ Set.range fiveVertex :=
  ⟨extreme_mem_fiveVertex, by rintro ⟨i, rfl⟩; exact fiveVertex_extreme i⟩

/-! ## Necessity -/

/-- **Finite necessity.** At every cutoff the discrepancy triple of `x`, `y`, `x+y` lies in
the polytope. -/
theorem finite_necessity (b : ℕ) (x y : ℝ) {N : ℕ} (hN : 0 < N) :
    (radixDiscrepancy b x N, radixDiscrepancy b y N, radixDiscrepancy b (x + y) N) ∈ polytope := by
  have h1 := sharp_translation b x y hN
  have h2 := sharp_translation b y x hN
  rw [add_comm y x] at h2
  have n1 : 0 ≤ radixDiscrepancy b x N := sampleDisc_nonneg _ N
  have n2 : 0 ≤ radixDiscrepancy b y N := sampleDisc_nonneg _ N
  have n3 : 0 ≤ radixDiscrepancy b (x + y) N := sampleDisc_nonneg _ N
  rw [abs_le] at h1 h2
  exact ⟨n1, n2, n3, by linarith [h1.1], by linarith [h1.2], by linarith [h2.2]⟩

/-- The finite statement in the form `max(0, α+β-1) ≤ γ ≤ 1-|α-β|`. -/
theorem finite_necessity' (b : ℕ) (x y : ℝ) {N : ℕ} (hN : 0 < N) :
    max 0 (radixDiscrepancy b x N + radixDiscrepancy b y N - 1) ≤ radixDiscrepancy b (x + y) N ∧
      radixDiscrepancy b (x + y) N ≤ 1 - |radixDiscrepancy b x N - radixDiscrepancy b y N| := by
  obtain ⟨-, -, -, -, h1, h2⟩ := mem_polytope_iff.mp (finite_necessity b x y hN)
  exact ⟨h1, h2⟩

/-- Every joint cluster point of the discrepancy triples lies in the polytope. -/
theorem clusterPt_necessity (b : ℕ) (x y : ℝ) {v : ℝ × ℝ × ℝ}
    (hv : MapClusterPt v atTop
      (fun N => (radixDiscrepancy b x N, radixDiscrepancy b y N, radixDiscrepancy b (x + y) N))) :
    v ∈ polytope :=
  isClosed_polytope.mem_of_mapClusterPt hv
    (eventually_atTop.mpr ⟨1, fun _N hN => finite_necessity b x y hN⟩)

/-- **Limiting necessity.** -/
theorem limit_necessity (b : ℕ) (x y : ℝ) {α β γ : ℝ}
    (hx : Tendsto (radixDiscrepancy b x) atTop (𝓝 α))
    (hy : Tendsto (radixDiscrepancy b y) atTop (𝓝 β))
    (hxy : Tendsto (radixDiscrepancy b (x + y)) atTop (𝓝 γ)) :
    (α, β, γ) ∈ polytope :=
  isClosed_polytope.mem_of_tendsto (hx.prodMk_nhds (hy.prodMk_nhds hxy))
    (eventually_atTop.mpr ⟨1, fun _N hN => finite_necessity b x y hN⟩)

/-! ## The spectrum and the realization reduction -/

/-- The exact addition spectrum in radix `b`: triples of limiting discrepancies of
`x`, `y` and `x+y`. -/
def addSpectrum (b : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {v | ∃ x y : ℝ, Tendsto (radixDiscrepancy b x) atTop (𝓝 v.1) ∧
    Tendsto (radixDiscrepancy b y) atTop (𝓝 v.2.1) ∧
    Tendsto (radixDiscrepancy b (x + y)) atTop (𝓝 v.2.2)}

theorem addSpectrum_subset_polytope (b : ℕ) : addSpectrum b ⊆ polytope := by
  rintro ⟨α, β, γ⟩ ⟨x, y, hx, hy, hxy⟩
  exact limit_necessity b x y hx hy hxy

/-- The limiting discrepancy predicted for an integer form `c` by a weighted mixture of
rank-one rational types `m i`: the total weight of the types annihilated by `c`. -/
noncomputable def mixtureValue {d r : ℕ} (m : Fin r → Fin d → ℤ) (w : Fin r → ℝ)
    (c : Fin d → ℤ) : ℝ :=
  ∑ i, if ∑ j, c j * m i j = 0 then w i else 0

/-- Realization of a mixture: reals whose integer forms have the predicted limits. -/
def MixtureRealizable (b : ℕ) {d r : ℕ} (m : Fin r → Fin d → ℤ) (w : Fin r → ℝ) : Prop :=
  ∃ x : Fin d → ℝ, ∀ c : Fin d → ℤ,
    Tendsto (radixDiscrepancy b (∑ j, (c j : ℝ) * x j)) atTop (𝓝 (mixtureValue m w c))

/-- The five types as integer vectors for `(x, y)`: retired, `x` only, `y` only, inverse,
equal. -/
def fiveTypes : Fin 5 → Fin 2 → ℤ := ![![0, 0], ![1, 0], ![0, 1], ![1, -1], ![1, 1]]

theorem mixtureValue_x (w : Fin 5 → ℝ) : mixtureValue fiveTypes w ![1, 0] = w 0 + w 2 := by
  simp [mixtureValue, fiveTypes, Fin.sum_univ_five, Fin.sum_univ_two]

theorem mixtureValue_y (w : Fin 5 → ℝ) : mixtureValue fiveTypes w ![0, 1] = w 0 + w 1 := by
  simp [mixtureValue, fiveTypes, Fin.sum_univ_five, Fin.sum_univ_two]

theorem mixtureValue_xy (w : Fin 5 → ℝ) : mixtureValue fiveTypes w ![1, 1] = w 0 + w 3 := by
  simp [mixtureValue, fiveTypes, Fin.sum_univ_five, Fin.sum_univ_two]

/-- **Realization reduction.** If the five-type mixtures with the weights `fiveWeights` are
realizable, the polytope lies in the addition spectrum. -/
theorem polytope_subset_addSpectrum_of_realizable (b : ℕ)
    (H : ∀ α β γ : ℝ, (α, β, γ) ∈ polytope → MixtureRealizable b fiveTypes (fiveWeights α β γ)) :
    polytope ⊆ addSpectrum b := by
  rintro ⟨α, β, γ⟩ hv
  obtain ⟨x, hx⟩ := H α β γ hv
  refine ⟨x 0, x 1, ?_, ?_, ?_⟩
  · have := hx ![1, 0]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one,
      Int.cast_zero, one_mul, zero_mul, add_zero, mixtureValue_x] at this
    convert this using 2
    simp [fiveWeights]
  · have := hx ![0, 1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one,
      Int.cast_zero, one_mul, zero_mul, zero_add, mixtureValue_y] at this
    convert this using 2
    simp [fiveWeights]
  · have := hx ![1, 1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one,
      one_mul, mixtureValue_xy] at this
    convert this using 2
    simp [fiveWeights]

end NormalityChecker.AdditionSpectrum
