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

/-! ## Finite comparison and mixtures of model samples -/

private lemma fract_le_self' {y : ℝ} (hy : 0 ≤ y) : Int.fract y ≤ y := by
  have h1 := Int.fract_add_floor y
  have h2 : (0 : ℝ) ≤ ⌊y⌋ := by exact_mod_cast Int.floor_nonneg.mpr hy
  linarith

/-- **Finite comparison.** Paired samples `q n ≡ p n + r n (mod 1)` have discrepancies within
`E/N + 2ε`, where `E` counts the positions with `|r n| ≥ ε`. This is Phase 18's
`paired_arc_le` applied to the arc `[-ε, ε)`. -/
theorem sampleDisc_compare {p q r : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n ∧ p n < 1)
    (hq : ∀ n, 0 ≤ q n ∧ q n < 1) (pair : ∀ n, ∃ i : ℤ, q n = p n + r n + i) {N : ℕ}
    (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    |sampleDisc q N - sampleDisc p N| ≤
      (((range N).filter (fun n => ε ≤ |r n|)).card : ℝ) / N + 2 * ε := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set E := ((range N).filter (fun n => ε ≤ |r n|)).card with hE
  have hgood : ((N : ℝ) - E) / N ≤ (arcCount r (-ε) (2 * ε) N : ℝ) / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    have h1 : ((range N).filter (fun n => ¬ (ε ≤ |r n|))).card ≤ arcCount r (-ε) (2 * ε) N := by
      unfold arcCount
      apply card_le_card
      intro n hn
      simp only [mem_filter, not_le] at hn ⊢
      refine ⟨hn.1, ?_⟩
      have h := abs_lt.mp hn.2
      calc Int.fract (r n - -ε) ≤ r n - -ε := fract_le_self' (by linarith)
        _ < 2 * ε := by linarith
    have h2 := Finset.card_filter_add_card_filter_not (s := range N) (fun n => ε ≤ |r n|)
    rw [card_range] at h2
    have h3 : (((range N).filter (fun n => ¬ (ε ≤ |r n|))).card : ℝ) = N - E := by
      rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast h2
    rw [← h3]; exact_mod_cast h1
  have hsplit : ((N : ℝ) - E) / N = 1 - (E : ℝ) / N := by field_simp
  have u1 := paired_arc_le (p := p) (q := q) (r := r) (s := 1) (Or.inl rfl) hp hq
    (fun n => by obtain ⟨i, hi⟩ := pair n; exact ⟨i, by rw [hi]; ring⟩) hN (-ε)
    (by linarith : (0 : ℝ) ≤ 2 * ε)
  have u2 := paired_arc_le (p := q) (q := p) (r := r) (s := -1) (Or.inr rfl) hq hp
    (fun n => by obtain ⟨i, hi⟩ := pair n; exact ⟨-i, by rw [hi]; push_cast; ring⟩) hN (-ε)
    (by linarith : (0 : ℝ) ≤ 2 * ε)
  rw [abs_le]; constructor <;> linarith

/-- **Mixture of a retired and an active part.** If the retired positions carry the model
value `0` and the active positions have interval counting error at most `H`, the discrepancy
lies between the retired proportion and the retired proportion plus `H/N`. -/
theorem sampleDisc_mixture {y : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (ret : ℕ → Prop)
    [DecidablePred ret] (hret : ∀ n, ret n → y n = 0) {H : ℝ}
    (hact : ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
      |∑ n ∈ range N, (if ret n then 0 else
        ((if a ≤ y n ∧ y n < c then 1 else 0) - (c - a)))| ≤ H) :
    (∑ n ∈ range N, if ret n then (1 : ℝ) else 0) / N ≤ sampleDisc y N ∧
      sampleDisc y N ≤ ((∑ n ∈ range N, if ret n then (1 : ℝ) else 0) + H) / N := by
  classical
  set Z := ∑ n ∈ range N, if ret n then (1 : ℝ) else 0 with hZ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfreq : ∀ a c, frequency y a c N * N =
      ∑ n ∈ range N, if a ≤ y n ∧ y n < c then (1 : ℝ) else 0 := by
    intro a c
    unfold frequency
    rw [div_mul_cancel₀ _ hNr.ne', Finset.natCast_card_filter]
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun n _ => by split_ifs <;> norm_num)
  have hZN : Z ≤ N := by
    calc Z ≤ ∑ n ∈ range N, (1 : ℝ) := Finset.sum_le_sum (fun n _ => by split_ifs <;> norm_num)
      _ = N := by simp
  constructor
  · apply le_of_forall_pos_le_add
    intro η hη
    rcases lt_or_ge η 1 with h1 | h1
    · have hI := (abs_le.mp (interval_le_sampleDisc y N le_rfl hη h1.le)).2
      have hge : Z ≤ frequency y 0 η N * N := by
        rw [hfreq]
        apply Finset.sum_le_sum
        intro n _
        by_cases hr : ret n
        · simp [hr, hret n hr, hη]
        · simp only [hr, ↓reduceIte]; split_ifs <;> norm_num
      have : Z / N ≤ frequency y 0 η N := by rw [div_le_iff₀ hNr]; linarith
      linarith
    · have : Z / N ≤ 1 := (div_le_one hNr).mpr hZN
      linarith [sampleDisc_nonneg y N]
  · apply sampleDisc_le_of
    intro a c ha hac hc
    have hS := abs_le.mp (hact a c ha hac hc)
    set S := ∑ n ∈ range N, (if ret n then 0 else
        ((if a ≤ y n ∧ y n < c then 1 else 0) - (c - a))) with hSdef
    set K := ∑ n ∈ range N,
      (if ret n then (if a ≤ y n ∧ y n < c then (1 : ℝ) else 0) else 0) with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg (fun n _ => by split_ifs <;> norm_num)
    have hKZ : K ≤ Z := Finset.sum_le_sum (fun n _ => by split_ifs <;> norm_num)
    have hNZ : (N : ℝ) - Z = ∑ n ∈ range N, if ret n then (0 : ℝ) else 1 := by
      rw [hZ, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
      rw [show (N : ℝ) = ∑ n ∈ range N, (1 : ℝ) by simp]
      exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> norm_num)
    have hsplit : frequency y a c N * N = K + S + (N - Z) * (c - a) := by
      rw [hfreq, hNZ, Finset.sum_mul, hK, hSdef, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      split_ifs <;> ring
    have hfr : frequency y a c N - (c - a) = (K + S - Z * (c - a)) / N := by
      field_simp
      linarith
    have hca : Z * (c - a) ≤ Z := mul_le_of_le_one_right hZ0 (by linarith)
    have hca0 : 0 ≤ Z * (c - a) := mul_nonneg hZ0 (by linarith)
    rw [hfr, abs_div, abs_of_pos hNr]
    apply div_le_div_of_nonneg_right _ hNr.le
    rw [abs_le]; constructor <;> linarith

/-! ## Segment schedules -/

section Segments

variable (ℓ : ℕ → ℕ)

/-- Start of segment `σ` for segment lengths `ℓ`. -/
def segStart (σ : ℕ) : ℕ := ∑ τ ∈ range σ, ℓ τ

theorem segStart_zero : segStart ℓ 0 = 0 := by simp [segStart]

theorem segStart_succ (σ : ℕ) : segStart ℓ (σ + 1) = segStart ℓ σ + ℓ σ := by
  simp [segStart, Finset.sum_range_succ]

/-- The segment containing position `n` (meaningful for positive lengths). -/
noncomputable def locate (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ σ, n < segStart ℓ (σ + 1) then Nat.find h else 0

variable {ℓ}

theorem segStart_mono : Monotone (segStart ℓ) :=
  monotone_nat_of_le_succ (fun σ => by rw [segStart_succ]; exact Nat.le_add_right _ _)

theorem segStart_strictMono (hℓ : ∀ σ, 0 < ℓ σ) : StrictMono (segStart ℓ) :=
  strictMono_nat_of_lt_succ (fun σ => by rw [segStart_succ]; exact Nat.lt_add_of_pos_right (hℓ σ))

theorem locate_spec (hℓ : ∀ σ, 0 < ℓ σ) (n : ℕ) :
    segStart ℓ (locate ℓ n) ≤ n ∧ n < segStart ℓ (locate ℓ n + 1) := by
  classical
  have h : ∃ σ, n < segStart ℓ (σ + 1) :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) ((segStart_strictMono hℓ).id_le _)⟩
  have e : locate ℓ n = Nat.find h := by unfold locate; simp only [h, ↓reduceDIte]
  rw [e]
  refine ⟨?_, Nat.find_spec h⟩
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
  · rw [h0, segStart_zero]; exact Nat.zero_le _
  · have := Nat.find_min h (Nat.sub_lt h0 one_pos)
    rw [Nat.sub_add_cancel (show 1 ≤ Nat.find h from h0)] at this
    exact not_lt.mp this

theorem locate_eq (hℓ : ∀ σ, 0 < ℓ σ) {n σ : ℕ} (h1 : segStart ℓ σ ≤ n)
    (h2 : n < segStart ℓ (σ + 1)) : locate ℓ n = σ := by
  obtain ⟨a1, a2⟩ := locate_spec hℓ n
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := segStart_mono (ℓ := ℓ) (show locate ℓ n + 1 ≤ σ by omega)
    omega
  · have := segStart_mono (ℓ := ℓ) (show σ + 1 ≤ locate ℓ n by omega)
    omega

theorem sum_Ico_segStart (f : ℕ → ℝ) {a c : ℕ} (hac : a ≤ c) :
    ∑ n ∈ Ico (segStart ℓ a) (segStart ℓ c), f n =
      ∑ σ ∈ Ico a c, ∑ j ∈ range (ℓ σ), f (segStart ℓ σ + j) := by
  induction c, hac using Nat.le_induction with
  | base => simp
  | succ c hac ih =>
    rw [Finset.sum_Ico_succ_top hac, ← ih,
      ← Finset.sum_Ico_consecutive f (segStart_mono hac) (segStart_mono (Nat.le_succ c))]
    congr 1
    rw [segStart_succ, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

end Segments

/-! ## Averaging over blocks -/

private lemma sum_Ico_blocks {S : ℕ → ℕ} (hS : Monotone S) (g : ℕ → ℝ) {a c : ℕ} (hac : a ≤ c) :
    ∑ n ∈ Ico (S a) (S c), g n = ∑ k ∈ Ico a c, ∑ n ∈ Ico (S k) (S (k + 1)), g n := by
  induction c, hac using Nat.le_induction with
  | base => simp
  | succ c hac ih =>
    rw [Finset.sum_Ico_succ_top hac, ← ih,
      Finset.sum_Ico_consecutive g (hS hac) (hS (Nat.le_succ c))]

private lemma sum_Ico_telescope {S : ℕ → ℕ} {a c : ℕ} (hac : a ≤ c) :
    ∑ k ∈ Ico a c, ((S (k + 1) : ℝ) - S k) = (S c : ℝ) - S a := by
  induction c, hac using Nat.le_induction with
  | base => simp
  | succ c hac ih => rw [Finset.sum_Ico_succ_top hac, ih]; ring

private lemma abs_sum_Ico_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {a c : ℕ} (hac : a ≤ c) :
    |∑ n ∈ Ico a c, f n| ≤ (c : ℝ) - a := by
  calc |∑ n ∈ Ico a c, f n| ≤ ∑ n ∈ Ico a c, |f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ico a c, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hf n)
    _ = (c : ℝ) - a := by simp [Nat.cast_sub hac]

/-- **Block Cesàro lemma.** Suppose consecutive blocks `[S k, S (k+1))` have lengths negligible
against their starts, and that a family of functions bounded by one has block sums that are
eventually a vanishing proportion of the block lengths, uniformly in the family. Then all
prefix sums are `o(N)`, uniformly in the family. -/
theorem block_cesaro {S : ℕ → ℕ} (hS : StrictMono S) (hS0 : S 0 = 0)
    (hratio : ∀ η > 0, ∀ᶠ k in atTop, ((S (k + 1) : ℝ) - S k) ≤ η * S k)
    {ι : Type*} (f : ι → ℕ → ℝ) (hf : ∀ i n, |f i n| ≤ 1)
    (hblock : ∀ η > 0, ∀ᶠ k in atTop, ∀ i,
      |∑ n ∈ Ico (S k) (S (k + 1)), f i n| ≤ η * ((S (k + 1) : ℝ) - S k)) :
    ∀ η > 0, ∀ᶠ N in atTop, ∀ i, |∑ n ∈ range N, f i n| ≤ η * N := by
  classical
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp (hratio (η / 3) hη3)
  obtain ⟨k2, hk2⟩ := eventually_atTop.mp (hblock (η / 3) hη3)
  set k0 := max k1 k2
  obtain ⟨N1, hN1⟩ := exists_nat_gt (3 * S k0 / η)
  refine eventually_atTop.mpr ⟨max N1 (S k0), fun N hN i => ?_⟩
  have hNk0 : S k0 ≤ N := le_of_max_le_right hN
  have hN1' : (3 * S k0 / η : ℝ) < N :=
    lt_of_lt_of_le hN1 (by exact_mod_cast le_of_max_le_left hN)
  have hSk0 : (S k0 : ℝ) ≤ η / 3 * N := by
    rw [div_lt_iff₀ hη] at hN1'; linarith
  have hex : ∃ k, N < S (k + 1) :=
    ⟨N, lt_of_lt_of_le (Nat.lt_succ_self N) (hS.id_le (N + 1))⟩
  set K := Nat.find hex
  have hK1 : N < S (K + 1) := Nat.find_spec hex
  have hK0 : S K ≤ N := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, hS0]; exact Nat.zero_le _
    · have := Nat.find_min hex (Nat.sub_lt h0 one_pos)
      rw [Nat.sub_add_cancel (show 1 ≤ K from h0)] at this
      exact not_lt.mp this
  have hkK : k0 ≤ K := by
    by_contra h
    push Not at h
    have := hS.monotone (show K + 1 ≤ k0 by omega)
    omega
  have hmono := hS.monotone
  have decomp : ∑ n ∈ range N, f i n = ∑ n ∈ Ico 0 (S k0), f i n +
      ∑ n ∈ Ico (S k0) (S K), f i n + ∑ n ∈ Ico (S K) N, f i n := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) (hmono hkK),
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hK0]
  have t1 : |∑ n ∈ Ico 0 (S k0), f i n| ≤ η / 3 * N := by
    have := abs_sum_Ico_le (hf i) (Nat.zero_le (S k0))
    simp only [Nat.cast_zero, sub_zero] at this
    linarith
  have hSKk0 : ((S K : ℝ) - S k0) ≤ N := by
    have : (S K : ℝ) ≤ N := by exact_mod_cast hK0
    have : (0 : ℝ) ≤ S k0 := Nat.cast_nonneg _
    linarith
  have t2 : |∑ n ∈ Ico (S k0) (S K), f i n| ≤ η / 3 * N := by
    rw [sum_Ico_blocks hmono _ hkK]
    calc |∑ k ∈ Ico k0 K, ∑ n ∈ Ico (S k) (S (k + 1)), f i n|
        ≤ ∑ k ∈ Ico k0 K, |∑ n ∈ Ico (S k) (S (k + 1)), f i n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Ico k0 K, η / 3 * ((S (k + 1) : ℝ) - S k) :=
          Finset.sum_le_sum (fun k hk =>
            hk2 k (le_trans (le_max_right _ _) (Finset.mem_Ico.mp hk).1) i)
      _ = η / 3 * ((S K : ℝ) - S k0) := by rw [← Finset.mul_sum, sum_Ico_telescope hkK]
      _ ≤ η / 3 * N := by gcongr
  have t3 : |∑ n ∈ Ico (S K) N, f i n| ≤ η / 3 * N := by
    have h1 := abs_sum_Ico_le (hf i) hK0
    have h2 := hk1 K (le_trans (le_max_left _ _) hkK)
    have h3 : (N : ℝ) < S (K + 1) := by exact_mod_cast hK1
    have h4 : (S K : ℝ) ≤ N := by exact_mod_cast hK0
    have h5 : η / 3 * (S K : ℝ) ≤ η / 3 * N := by gcongr
    linarith
  rw [decomp]
  calc |∑ n ∈ Ico 0 (S k0), f i n + ∑ n ∈ Ico (S k0) (S K), f i n + ∑ n ∈ Ico (S K) N, f i n|
      ≤ |∑ n ∈ Ico 0 (S k0), f i n| + |∑ n ∈ Ico (S k0) (S K), f i n| +
        |∑ n ∈ Ico (S K) N, f i n| := abs_add_three _ _ _
    _ ≤ η * N := by linarith

/-! ## Programming radix states -/

section Series

variable (b : ℕ) (s : ℕ → ℕ) (u : ℕ → ℝ)

/-- Coefficients programming the states `u σ` at the positions `s σ`: the representative in
`[0,1)` of `u σ - b^(s σ - s (σ-1)) u (σ-1)`. -/
noncomputable def coef : ℕ → ℝ
  | 0 => Int.fract (u 0)
  | σ + 1 => Int.fract (u (σ + 1) - (b : ℝ) ^ (s (σ + 1) - s σ) * u σ)

/-- The programmed real number `∑ coef σ · b^(-s σ)`. -/
noncomputable def programmed : ℝ := ∑' σ, coef b s u σ / (b : ℝ) ^ s σ

/-- The tail after segment `σ`. -/
noncomputable def tailAfter (σ : ℕ) : ℝ :=
  ∑' i, coef b s u (i + (σ + 1)) / (b : ℝ) ^ s (i + (σ + 1))

theorem coef_mem (σ : ℕ) : 0 ≤ coef b s u σ ∧ coef b s u σ < 1 := by
  cases σ <;> exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

variable {b s}

private lemma strictMono_add_le (hs : StrictMono s) (k i : ℕ) : s k + i ≤ s (i + k) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : s (i + k) < s (i + 1 + k) := hs (by omega)
    omega

theorem coef_term_summable (hb : 2 ≤ b) (hs : StrictMono s) :
    Summable (fun σ => coef b s u σ / (b : ℝ) ^ s σ) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  refine Summable.of_nonneg_of_le (fun σ => div_nonneg (coef_mem b s u σ).1 (by positivity))
    (fun σ => ?_) (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1))
  calc coef b s u σ / (b : ℝ) ^ s σ ≤ 1 / (b : ℝ) ^ s σ :=
        div_le_div_of_nonneg_right (coef_mem b s u σ).2.le (by positivity)
    _ ≤ 1 / (b : ℝ) ^ σ :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hb1.le (hs.id_le σ))
    _ = (b : ℝ)⁻¹ ^ σ := by rw [one_div, inv_pow]

/-- Prefix sums hit the programmed states modulo one. -/
theorem prefix_state (hb : 0 < b) (hs : Monotone s) (σ : ℕ) : ∃ M : ℤ,
    (b : ℝ) ^ s σ * ∑ τ ∈ range (σ + 1), coef b s u τ / (b : ℝ) ^ s τ = u σ + M := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  induction σ with
  | zero =>
    refine ⟨-⌊u 0⌋, ?_⟩
    have hne : (b : ℝ) ^ s 0 ≠ 0 := by positivity
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, coef]
    rw [mul_div_cancel₀ _ hne]
    have := Int.fract_add_floor (u 0)
    push_cast; linarith
  | succ σ ih =>
    obtain ⟨M, hM⟩ := ih
    set Δ := s (σ + 1) - s σ
    have hpow : (b : ℝ) ^ s (σ + 1) = (b : ℝ) ^ Δ * (b : ℝ) ^ s σ := by
      rw [← pow_add, Nat.sub_add_cancel (hs (Nat.le_succ σ))]
    have hne : (b : ℝ) ^ s (σ + 1) ≠ 0 := by positivity
    refine ⟨(b : ℤ) ^ Δ * M - ⌊u (σ + 1) - (b : ℝ) ^ Δ * u σ⌋, ?_⟩
    rw [Finset.sum_range_succ, mul_add, mul_div_cancel₀ _ hne, hpow, mul_assoc, hM]
    have := Int.fract_add_floor (u (σ + 1) - (b : ℝ) ^ Δ * u σ)
    simp only [coef]
    push_cast
    linarith

theorem programmed_split (hb : 2 ≤ b) (hs : StrictMono s) (σ : ℕ) :
    programmed b s u =
      ∑ τ ∈ range (σ + 1), coef b s u τ / (b : ℝ) ^ s τ + tailAfter b s u σ :=
  ((coef_term_summable u hb hs).sum_add_tsum_nat_add (σ + 1)).symm

/-- The real tail after segment `σ` is at most `b/(b-1) · b^(-s (σ+1))`. -/
theorem tailAfter_bound (hb : 2 ≤ b) (hs : StrictMono s) (σ : ℕ) :
    0 ≤ tailAfter b s u σ ∧
      tailAfter b s u σ ≤ (b : ℝ) / (b - 1) / (b : ℝ) ^ s (σ + 1) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hsum := (coef_term_summable u hb hs).comp_injective (add_left_injective (σ + 1))
  have hgeo : Summable (fun i : ℕ => (1 / (b : ℝ) ^ s (σ + 1)) * (b : ℝ)⁻¹ ^ i) :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)).mul_left _
  constructor
  · exact tsum_nonneg (fun i => div_nonneg (coef_mem b s u _).1 (by positivity))
  · calc tailAfter b s u σ
        ≤ ∑' i : ℕ, (1 / (b : ℝ) ^ s (σ + 1)) * (b : ℝ)⁻¹ ^ i := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsum hgeo
          calc coef b s u (i + (σ + 1)) / (b : ℝ) ^ s (i + (σ + 1))
              ≤ 1 / (b : ℝ) ^ s (i + (σ + 1)) :=
                div_le_div_of_nonneg_right (coef_mem b s u _).2.le (by positivity)
            _ ≤ 1 / (b : ℝ) ^ (s (σ + 1) + i) :=
                one_div_le_one_div_of_le (by positivity)
                  (pow_le_pow_right₀ hb1.le (strictMono_add_le hs _ _))
            _ = (1 / (b : ℝ) ^ s (σ + 1)) * (b : ℝ)⁻¹ ^ i := by
                rw [pow_add, inv_pow]; field_simp
      _ = (b : ℝ) / (b - 1) / (b : ℝ) ^ s (σ + 1) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)]
          have : (b : ℝ) - 1 ≠ 0 := by linarith
          field_simp

/-- **Pairing for integer forms.** Inside segment `σ`, the radix shift of an integer form of
programmed numbers is the shifted form of the states plus an integer plus the shifted tails. -/
theorem form_pairing (hb : 2 ≤ b) (hs : StrictMono s) {d : ℕ} (u : Fin d → ℕ → ℝ)
    (cf : Fin d → ℤ) {σ n : ℕ} (h1 : s σ ≤ n) :
    ∃ K : ℤ, (b : ℝ) ^ n * ∑ j, (cf j : ℝ) * programmed b s (u j) =
      (b : ℝ) ^ (n - s σ) * ∑ j, (cf j : ℝ) * u j σ + K +
        (b : ℝ) ^ n * ∑ j, (cf j : ℝ) * tailAfter b s (u j) σ := by
  choose M hM using fun j => prefix_state (u j) (by omega : 0 < b) hs.monotone σ
  refine ⟨∑ j, cf j * (b : ℤ) ^ (n - s σ) * M j, ?_⟩
  have hpow : (b : ℝ) ^ n = (b : ℝ) ^ (n - s σ) * (b : ℝ) ^ s σ := by
    rw [← pow_add, Nat.sub_add_cancel h1]
  have key : ∀ j, (b : ℝ) ^ n * ((cf j : ℝ) * programmed b s (u j)) =
      (b : ℝ) ^ (n - s σ) * ((cf j : ℝ) * u j σ) +
        ((cf j * (b : ℤ) ^ (n - s σ) * M j : ℤ) : ℝ) +
        (b : ℝ) ^ n * ((cf j : ℝ) * tailAfter b s (u j) σ) := by
    intro j
    rw [programmed_split (u j) hb hs σ]
    have h := hM j
    rw [hpow]
    push_cast
    linear_combination (cf j : ℝ) * (b : ℝ) ^ (n - s σ) * h
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  ring

end Series

/-! ## Prime-power segments -/

/-- **Arithmetic interface.** Over one full period `n < t p^g`, the samples
`fract (bⁿ a' / p^(v+g))` with a unit numerator `a'` and `v = v_p(b^t - 1)` have interval
counting error at most `t`. This is exactly the conclusion of
`NormalityChecker.PrimePowerGrid.primePower_period_count`. -/
def PeriodCount (b p t : ℕ) : Prop :=
  ∀ (a' : ℤ), ¬ (p : ℤ) ∣ a' → ∀ (g : ℕ) {a c : ℝ}, 0 ≤ a → a < c → c ≤ 1 →
    |((((Finset.range (t * p ^ g)).filter fun n : ℕ =>
        a ≤ Int.fract ((b : ℝ) ^ n * a' / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) ∧
        Int.fract ((b : ℝ) ^ n * a' / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) < c).card :
          ℕ) : ℝ) - ((t * p ^ g : ℕ) : ℝ) * (c - a)| ≤ t

private lemma card_sub_eq_sum (P : ℕ → Prop) [DecidablePred P] (L : ℕ) (x : ℝ) :
    ((((range L).filter P).card : ℕ) : ℝ) - (L : ℝ) * x =
      ∑ n ∈ range L, ((if P n then 1 else 0) - x) := by
  rw [Finset.natCast_card_filter, Finset.sum_sub_distrib]
  simp

private lemma sum_range_mul' (F : ℕ → ℝ) (L Q : ℕ) :
    ∑ n ∈ range (L * Q), F n = ∑ q ∈ range Q, ∑ j ∈ range L, F (L * q + j) := by
  induction Q with
  | zero => simp
  | succ Q ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **Segment count.** A segment of `M p^ρ` periods of the orbit of `A / p^(v+g)`, where
`A = p^ρ a'` with `a'` a unit and `ρ ≤ g`, has interval counting error at most `t p^ρ M`. -/
theorem segment_count {b p t : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) (hgrid : PeriodCount b p t)
    {A a' : ℤ} {ρ g : ℕ} (hA : A = (p : ℤ) ^ ρ * a') (ha' : ¬ (p : ℤ) ∣ a') (hρg : ρ ≤ g)
    (M : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hac : a < c) (hc : c ≤ 1) :
    |∑ j ∈ range (t * p ^ g * M),
      ((if a ≤ Int.fract ((b : ℝ) ^ j * A / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) ∧
          Int.fract ((b : ℝ) ^ j * A / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) < c
        then 1 else 0) - (c - a))| ≤ t * p ^ ρ * M := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + ρ := ⟨g - ρ, (Nat.sub_add_cancel hρg).symm⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hlen : t * p ^ (g' + ρ) * M = (t * p ^ g') * (p ^ ρ * M) := by rw [pow_add]; ring
  rw [hlen, sum_range_mul']
  have chunk : ∀ q, |∑ j ∈ range (t * p ^ g'),
      ((if a ≤ Int.fract ((b : ℝ) ^ (t * p ^ g' * q + j) * A /
            (p : ℝ) ^ (padicValNat p (b ^ t - 1) + (g' + ρ))) ∧
          Int.fract ((b : ℝ) ^ (t * p ^ g' * q + j) * A /
            (p : ℝ) ^ (padicValNat p (b ^ t - 1) + (g' + ρ))) < c then 1 else 0) - (c - a))|
      ≤ t := by
    intro q
    have ha'' : ¬ (p : ℤ) ∣ (b : ℤ) ^ (t * p ^ g' * q) * a' := by
      intro h
      rcases hpZ.dvd_or_dvd h with h1 | h1
      · exact hpb (Int.natCast_dvd_natCast.mp (hpZ.dvd_of_dvd_pow h1))
      · exact ha' h1
    have hsample : ∀ j, (b : ℝ) ^ (t * p ^ g' * q + j) * A /
        (p : ℝ) ^ (padicValNat p (b ^ t - 1) + (g' + ρ)) =
        (b : ℝ) ^ j * (((b : ℤ) ^ (t * p ^ g' * q) * a' : ℤ) : ℝ) /
          (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g') := by
      intro j
      rw [hA]
      push_cast
      rw [show padicValNat p (b ^ t - 1) + (g' + ρ) = (padicValNat p (b ^ t - 1) + g') + ρ by ring,
        pow_add, pow_add]
      field_simp
    have h := hgrid _ ha'' g' ha hac hc
    rw [card_sub_eq_sum] at h
    simp_rw [hsample]
    exact h
  calc _ ≤ ∑ q ∈ range (p ^ ρ * M), |∑ j ∈ range (t * p ^ g'),
        ((if a ≤ Int.fract ((b : ℝ) ^ (t * p ^ g' * q + j) * A /
              (p : ℝ) ^ (padicValNat p (b ^ t - 1) + (g' + ρ))) ∧
            Int.fract ((b : ℝ) ^ (t * p ^ g' * q + j) * A /
              (p : ℝ) ^ (padicValNat p (b ^ t - 1) + (g' + ρ))) < c then 1 else 0) - (c - a))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ range (p ^ ρ * M), (t : ℝ) := Finset.sum_le_sum (fun q _ => chunk q)
    _ = t * p ^ ρ * M := by simp; ring

private lemma int_pow_decomp {p : ℕ} (hp : p.Prime) {A : ℤ} (hA : A ≠ 0) :
    ∃ ρ : ℕ, ∃ a' : ℤ, A = (p : ℤ) ^ ρ * a' ∧ ¬ (p : ℤ) ∣ a' := by
  have hfin : FiniteMultiplicity (p : ℤ) A :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.one_lt.ne', hA⟩
  obtain ⟨c, hc1, hc2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hc1, hc2⟩

/-! ## The mixture schedule

Block `k` consists of `r` segments, one per type, of `t p^(⌊log_p (k+1)⌋) (⌊w_i (k+1)⌋ + 1)`
positions each. On type `i` the state of coordinate `j` is `m i j / p^(v + ⌊log_p (k+1)⌋)`
modulo one. -/

/-- The type `σ mod r` of segment `σ`. -/
def typeOf (r : ℕ) [NeZero r] (σ : ℕ) : Fin r := ⟨σ % r, Nat.mod_lt _ (NeZero.pos r)⟩

/-- The block size exponent `⌊log_p (k+1)⌋`. -/
def gexp (p k : ℕ) : ℕ := Nat.log p (k + 1)

/-- The number of periods of type `i` in block `k`. -/
noncomputable def mult {r : ℕ} (w : Fin r → ℝ) (k : ℕ) (i : Fin r) : ℕ :=
  ⌊w i * (k + 1)⌋₊ + 1

/-- Segment `σ` carries type `σ mod r` in block `σ / r`. -/
noncomputable def segLen (p t r : ℕ) [NeZero r] (w : Fin r → ℝ) (σ : ℕ) : ℕ :=
  t * p ^ gexp p (σ / r) * mult w (σ / r) (typeOf r σ)

/-- Start of block `k`. -/
noncomputable def blockStart (p t r : ℕ) [NeZero r] (w : Fin r → ℝ) (k : ℕ) : ℕ :=
  segStart (segLen p t r w) (r * k)

/-- The state of coordinate `j` on segment `σ`. -/
noncomputable def mixState (b p t r : ℕ) [NeZero r] {d : ℕ} (m : Fin r → Fin d → ℤ)
    (j : Fin d) (σ : ℕ) : ℝ :=
  Int.fract ((m (typeOf r σ) j : ℝ) / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (σ / r)))

/-- The realizing reals. -/
noncomputable def mixPoint (b p t r : ℕ) [NeZero r] {d : ℕ} (m : Fin r → Fin d → ℤ)
    (w : Fin r → ℝ) (j : Fin d) : ℝ :=
  programmed b (segStart (segLen p t r w)) (mixState b p t r m j)

/-- The numerator of the integer form `cf` on type `i`. -/
def formNum {d r : ℕ} (m : Fin r → Fin d → ℤ) (cf : Fin d → ℤ) (i : Fin r) : ℤ :=
  ∑ j, cf j * m i j

/-- The model sample of the form `cf` at position `n`. -/
noncomputable def mixModel (b p t r : ℕ) [NeZero r] {d : ℕ} (m : Fin r → Fin d → ℤ)
    (w : Fin r → ℝ) (cf : Fin d → ℤ) (n : ℕ) : ℝ :=
  Int.fract ((b : ℝ) ^ (n - segStart (segLen p t r w) (locate (segLen p t r w) n)) *
    (formNum m cf (typeOf r (locate (segLen p t r w) n)) : ℝ) /
    (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (locate (segLen p t r w) n / r)))

/-- The shifted real tail of the form `cf` at position `n`. -/
noncomputable def mixTail (b p t r : ℕ) [NeZero r] {d : ℕ} (m : Fin r → Fin d → ℤ)
    (w : Fin r → ℝ) (cf : Fin d → ℤ) (n : ℕ) : ℝ :=
  (b : ℝ) ^ n * ∑ j, (cf j : ℝ) *
    tailAfter b (segStart (segLen p t r w)) (mixState b p t r m j) (locate (segLen p t r w) n)

section ScheduleFacts

variable {p t r : ℕ} [NeZero r] {w : Fin r → ℝ}

theorem segLen_pos (hp : p.Prime) (ht : 0 < t) (σ : ℕ) : 0 < segLen p t r w σ := by
  have := hp.pos
  unfold segLen mult
  positivity

theorem div_block (k : ℕ) (i : Fin r) : (r * k + (i : ℕ)) / r = k := by
  rw [Nat.mul_add_div (NeZero.pos r), Nat.div_eq_of_lt i.isLt, add_zero]

theorem fin_block (k : ℕ) (i : Fin r) : typeOf r (r * k + (i : ℕ)) = i := by
  apply Fin.ext
  simp only [typeOf]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

theorem segLen_block (k : ℕ) (i : Fin r) :
    segLen p t r w (r * k + i) = t * p ^ gexp p k * mult w k i := by
  simp only [segLen, div_block, fin_block]

theorem blockStart_zero : blockStart p t r w 0 = 0 := by
  simp [blockStart, segStart_zero]

theorem blockStart_strictMono (hp : p.Prime) (ht : 0 < t) : StrictMono (blockStart p t r w) :=
  fun _ _ h => segStart_strictMono (segLen_pos hp ht)
    (Nat.mul_lt_mul_of_pos_left h (NeZero.pos r))

/-- Block sums split into the `r` typed segments. -/
theorem blockStart_sum (f : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ Ico (blockStart p t r w k) (blockStart p t r w (k + 1)), f n =
      ∑ i : Fin r, ∑ j ∈ range (t * p ^ gexp p k * mult w k i),
        f (segStart (segLen p t r w) (r * k + i) + j) := by
  unfold blockStart
  rw [sum_Ico_segStart f (Nat.mul_le_mul_left r (Nat.le_succ k)), Finset.sum_Ico_eq_sum_range,
    show r * (k + 1) - r * k = r by rw [Nat.mul_succ]; omega, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [segLen_block]

theorem blockStart_len (k : ℕ) :
    ((blockStart p t r w (k + 1) : ℕ) : ℝ) - blockStart p t r w k =
      ∑ i : Fin r, ((t * p ^ gexp p k * mult w k i : ℕ) : ℝ) := by
  have h := blockStart_sum (p := p) (t := t) (w := w) (fun _ => (1 : ℝ)) k
  simp only [Finset.sum_const, card_range, Nat.card_Ico, nsmul_eq_mul, mul_one] at h
  have hle : blockStart p t r w k ≤ blockStart p t r w (k + 1) :=
    segStart_mono (Nat.mul_le_mul_left r (Nat.le_succ k))
  rw [← h, Nat.cast_sub hle]

/-- The block containing a position of segment `r k + i`. -/
theorem locate_block (hp : p.Prime) (ht : 0 < t) (k : ℕ) (i : Fin r) {j : ℕ}
    (hj : j < t * p ^ gexp p k * mult w k i) :
    locate (segLen p t r w) (segStart (segLen p t r w) (r * k + i) + j) = r * k + i := by
  apply locate_eq (segLen_pos hp ht) (Nat.le_add_right _ _)
  rw [segStart_succ, segLen_block]
  omega

omit [NeZero r] in
theorem mult_sum_bounds (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (k : ℕ) :
    (k : ℝ) + 1 ≤ ∑ i, (mult w k i : ℝ) ∧ ∑ i, (mult w k i : ℝ) ≤ k + 1 + r := by
  have hy : ∀ i, 0 ≤ w i * ((k : ℝ) + 1) := fun i => mul_nonneg (hw0 i) (by positivity)
  have e1 : ∀ i, w i * ((k : ℝ) + 1) ≤ (mult w k i : ℝ) := by
    intro i
    unfold mult
    push_cast
    linarith [Nat.lt_floor_add_one (w i * ((k : ℝ) + 1))]
  have e2 : ∀ i, (mult w k i : ℝ) ≤ w i * ((k : ℝ) + 1) + 1 := by
    intro i
    unfold mult
    push_cast
    linarith [Nat.floor_le (hy i)]
  have hsum : ∑ i, w i * ((k : ℝ) + 1) = k + 1 := by rw [← Finset.sum_mul, hw1, one_mul]
  constructor
  · rw [← hsum]; exact Finset.sum_le_sum (fun i _ => e1 i)
  · calc ∑ i, (mult w k i : ℝ) ≤ ∑ i, (w i * ((k : ℝ) + 1) + 1) :=
          Finset.sum_le_sum (fun i _ => e2 i)
      _ = k + 1 + r := by rw [Finset.sum_add_distrib, hsum]; simp

omit [NeZero r] in
theorem gexp_bounds (hp : p.Prime) (k : ℕ) :
    ((p ^ gexp p k : ℕ) : ℝ) ≤ k + 1 ∧ (k : ℝ) + 1 < p * ((p ^ gexp p k : ℕ) : ℝ) := by
  constructor
  · exact_mod_cast Nat.pow_log_le_self p (Nat.succ_ne_zero k)
  · have := Nat.lt_pow_succ_log_self hp.one_lt (k + 1)
    rw [Nat.pow_succ] at this
    have h' : ((k + 1 : ℕ) : ℝ) < ((p ^ Nat.log p (k + 1) * p : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    unfold gexp
    push_cast
    linarith

private lemma cube_le_sum_sq (k : ℕ) :
    (k : ℝ) ^ 3 ≤ 3 * ∑ k' ∈ range k, ((k' : ℝ) + 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [sq_nonneg (k : ℝ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Block lengths are negligible against block starts. -/
theorem blockStart_ratio (hp : p.Prime) (ht : 0 < t) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ∀ η > 0, ∀ᶠ k in atTop,
      ((blockStart p t r w (k + 1) : ℕ) : ℝ) - blockStart p t r w k ≤
        η * blockStart p t r w k := by
  intro η hη
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hT : ∀ k, ((blockStart p t r w (k + 1) : ℕ) : ℝ) - blockStart p t r w k =
      t * ((p ^ gexp p k : ℕ) : ℝ) * ∑ i, (mult w k i : ℝ) := by
    intro k
    rw [blockStart_len, Finset.mul_sum]
    push_cast
    rfl
  -- lower bound for every block length
  have hlow : ∀ k : ℕ, t * ((k : ℝ) + 1) ^ 2 / p ≤
      ((blockStart p t r w (k + 1) : ℕ) : ℝ) - blockStart p t r w k := by
    intro k
    rw [hT]
    obtain ⟨g1, g2⟩ := gexp_bounds hp k
    obtain ⟨m1, -⟩ := mult_sum_bounds hw0 hw1 k
    rw [div_le_iff₀ hp0]
    have hG0 : (0 : ℝ) ≤ ((p ^ gexp p k : ℕ) : ℝ) := Nat.cast_nonneg _
    have : ((k : ℝ) + 1) * ((k : ℝ) + 1) ≤ (p * ((p ^ gexp p k : ℕ) : ℝ)) * ∑ i, (mult w k i : ℝ) :=
      mul_le_mul g2.le m1 (by positivity) (by positivity)
    nlinarith
  have hstart : ∀ k : ℕ, t * (k : ℝ) ^ 3 / (3 * p) ≤ blockStart p t r w k := by
    intro k
    have htel := sum_Ico_telescope (S := blockStart p t r w) (Nat.zero_le k)
    rw [blockStart_zero, Nat.cast_zero, sub_zero] at htel
    rw [← htel, ← Finset.range_eq_Ico]
    calc t * (k : ℝ) ^ 3 / (3 * p) ≤ ∑ k' ∈ range k, t * ((k' : ℝ) + 1) ^ 2 / p := by
          rw [← Finset.sum_div, ← Finset.mul_sum, div_le_div_iff₀ (by positivity) hp0]
          have := mul_le_mul_of_nonneg_left (cube_le_sum_sq k) (le_of_lt (mul_pos ht0 hp0))
          nlinarith
      _ ≤ _ := Finset.sum_le_sum (fun k' _ => hlow k')
  filter_upwards [eventually_ge_atTop (r + 1), eventually_ge_atTop ⌈12 * p / η⌉₊] with k hk1 hk2
  have hk1' : (r : ℝ) + 1 ≤ k := by exact_mod_cast hk1
  have hk2' : 12 * p / η ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk2)
  have hk0 : (1 : ℝ) ≤ k := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg _; linarith
  obtain ⟨g1, -⟩ := gexp_bounds hp k
  obtain ⟨-, m2⟩ := mult_sum_bounds hw0 hw1 k
  have hup : ((blockStart p t r w (k + 1) : ℕ) : ℝ) - blockStart p t r w k ≤ 4 * t * (k : ℝ) ^ 2 := by
    rw [hT]
    have hG0 : (0 : ℝ) ≤ ((p ^ gexp p k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ ∑ i, (mult w k i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
    have h1 : ((p ^ gexp p k : ℕ) : ℝ) * ∑ i, (mult w k i : ℝ) ≤ (2 * k) * (2 * k) :=
      mul_le_mul (by linarith) (by linarith) hm0 (by linarith)
    nlinarith
  have hηk : 12 * p ≤ η * k := by
    have := (div_le_iff₀ hη).mp hk2'
    linarith [mul_comm (k : ℝ) η]
  calc _ ≤ 4 * t * (k : ℝ) ^ 2 := hup
    _ ≤ η * (t * (k : ℝ) ^ 3 / (3 * p)) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        have : 0 ≤ (t : ℝ) * (k : ℝ) ^ 2 := by positivity
        nlinarith
    _ ≤ η * blockStart p t r w k := by gcongr; exact hstart k

end ScheduleFacts

theorem mixtureValue_mem {d r : ℕ} {m : Fin r → Fin d → ℤ} {w : Fin r → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (cf : Fin d → ℤ) :
    0 ≤ mixtureValue m w cf ∧ mixtureValue m w cf ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hw0 i])
  · rw [← hw1]
    exact Finset.sum_le_sum (fun i _ => by split_ifs <;> simp [hw0 i])

theorem mult_balance {d r : ℕ} {m : Fin r → Fin d → ℤ} {w : Fin r → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (cf : Fin d → ℤ) (k : ℕ) :
    |∑ i, (mult w k i : ℝ) * ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf)| ≤ r := by
  obtain ⟨hW0, hW1⟩ := mixtureValue_mem hw0 hw1 (m := m) cf
  have hzero : ∑ i, w i * ((k : ℝ) + 1) *
      ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf) = 0 := by
    have hWsum : ∑ i, w i * (if formNum m cf i = 0 then (1 : ℝ) else 0) =
        mixtureValue m w cf := by
      unfold mixtureValue formNum
      exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
    have e : ∑ i, w i * ((k : ℝ) + 1) *
        ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf) =
        ((k : ℝ) + 1) * (∑ i, w i * (if formNum m cf i = 0 then (1 : ℝ) else 0)) -
          ((k : ℝ) + 1) * mixtureValue m w cf * ∑ i, w i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hWsum, hw1]; ring
  have hsplit : ∑ i, (mult w k i : ℝ) *
      ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf) =
      ∑ i, ((mult w k i : ℝ) - w i * ((k : ℝ) + 1)) *
        ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf) +
      ∑ i, w i * ((k : ℝ) + 1) *
        ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit, hzero, add_zero]
  calc _ ≤ ∑ i, |((mult w k i : ℝ) - w i * ((k : ℝ) + 1)) *
        ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin r, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        have hy : 0 ≤ w i * ((k : ℝ) + 1) := mul_nonneg (hw0 i) (by positivity)
        have e1 : w i * ((k : ℝ) + 1) ≤ mult w k i := by
          unfold mult; push_cast; linarith [Nat.lt_floor_add_one (w i * ((k : ℝ) + 1))]
        have e2 : (mult w k i : ℝ) ≤ w i * ((k : ℝ) + 1) + 1 := by
          unfold mult; push_cast; linarith [Nat.floor_le hy]
        have a1 : |(mult w k i : ℝ) - w i * ((k : ℝ) + 1)| ≤ 1 :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        have a2 : |(if formNum m cf i = 0 then (1 : ℝ) else 0) - mixtureValue m w cf| ≤ 1 := by
          split_ifs <;> rw [abs_le] <;> constructor <;> linarith
        calc _ ≤ (1 : ℝ) * 1 := mul_le_mul a1 a2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1)
    _ = r := by simp

section Pairing

variable {b p t r d : ℕ} [NeZero r]

/-- The true radix samples of an integer form of the realizing reals are the model samples
plus the shifted tails, modulo one. -/
theorem mix_pairing (hb : 2 ≤ b) (hp : p.Prime) (ht : 0 < t) (m : Fin r → Fin d → ℤ)
    (w : Fin r → ℝ) (cf : Fin d → ℤ) (n : ℕ) :
    ∃ i : ℤ, shift b (∑ j, (cf j : ℝ) * mixPoint b p t r m w j) n =
      mixModel b p t r m w cf n + mixTail b p t r m w cf n + i := by
  have hℓ := segLen_pos (w := w) hp ht
  have hs := segStart_strictMono hℓ
  obtain ⟨K, hK⟩ := form_pairing hb hs (mixState b p t r m) cf (locate_spec hℓ n).1
  unfold mixModel mixTail shift
  simp only [mixPoint]
  generalize locate (segLen p t r w) n = σ at hK ⊢
  have hstate : ∑ j, (cf j : ℝ) * mixState b p t r m j σ =
      (formNum m cf (typeOf r σ) : ℝ) / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (σ / r)) -
      ((∑ j, cf j * ⌊(m (typeOf r σ) j : ℝ) /
        (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (σ / r))⌋ : ℤ) : ℝ) := by
    simp only [mixState, Int.fract, formNum]
    push_cast
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hK, hstate]
  refine ⟨⌊(b : ℝ) ^ (n - segStart (segLen p t r w) σ) * (formNum m cf (typeOf r σ) : ℝ) /
      (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (σ / r))⌋ +
      (K - (b : ℤ) ^ (n - segStart (segLen p t r w) σ) *
        ∑ j, cf j * ⌊(m (typeOf r σ) j : ℝ) /
          (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (σ / r))⌋) -
      ⌊(b : ℝ) ^ (n - segStart (segLen p t r w) σ) *
        ((formNum m cf (typeOf r σ) : ℝ) / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (σ / r)) -
          ((∑ j, cf j * ⌊(m (typeOf r σ) j : ℝ) /
            (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p (σ / r))⌋ : ℤ) : ℝ)) + K +
        (b : ℝ) ^ n * ∑ j, (cf j : ℝ) *
          tailAfter b (segStart (segLen p t r w)) (mixState b p t r m j) σ⌋, ?_⟩
  rw [Int.fract, Int.fract]
  push_cast
  ring

/-- The shifted tail at position `n` is at most `C b/(b-1) b^(-(distance to the segment end)))`
with `C = ∑ |cf j|`. -/
theorem mixTail_bound (hb : 2 ≤ b) (hp : p.Prime) (ht : 0 < t) (m : Fin r → Fin d → ℤ)
    (w : Fin r → ℝ) (cf : Fin d → ℤ) (n : ℕ) :
    |mixTail b p t r m w cf n| ≤ (∑ j, |(cf j : ℝ)|) * ((b : ℝ) / (b - 1)) /
      (b : ℝ) ^ (segStart (segLen p t r w) (locate (segLen p t r w) n + 1) - n) := by
  have hℓ := segLen_pos (w := w) hp ht
  have hs := segStart_strictMono hℓ
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (b : ℝ) - 1 ≠ 0 := by linarith
  have hlt := (locate_spec hℓ n).2
  unfold mixTail
  generalize locate (segLen p t r w) n = σ at hlt ⊢
  have hpow : (b : ℝ) ^ segStart (segLen p t r w) (σ + 1) =
      (b : ℝ) ^ (segStart (segLen p t r w) (σ + 1) - n) * (b : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hlt.le]
  rw [abs_mul, abs_of_pos (pow_pos hb0 n)]
  calc (b : ℝ) ^ n * |∑ j, (cf j : ℝ) *
        tailAfter b (segStart (segLen p t r w)) (mixState b p t r m j) σ|
      ≤ (b : ℝ) ^ n * ∑ j, |(cf j : ℝ)| *
          ((b : ℝ) / (b - 1) / (b : ℝ) ^ segStart (segLen p t r w) (σ + 1)) := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
        have h := tailAfter_bound (mixState b p t r m j) hb hs σ
        rw [abs_mul, abs_of_nonneg h.1]
        exact mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
    _ = _ := by
        rw [← Finset.sum_mul, hpow]
        field_simp

theorem mixModel_block (hp : p.Prime) (ht : 0 < t) (m : Fin r → Fin d → ℤ) (w : Fin r → ℝ)
    (cf : Fin d → ℤ) (k : ℕ) (i : Fin r) {j : ℕ} (hj : j < t * p ^ gexp p k * mult w k i) :
    mixModel b p t r m w cf (segStart (segLen p t r w) (r * k + i) + j) =
      Int.fract ((b : ℝ) ^ j * (formNum m cf i : ℝ) /
        (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p k)) := by
  unfold mixModel
  rw [locate_block hp ht k i hj, Nat.add_sub_cancel_left, div_block, fin_block]

end Pairing

/-! ## Unconditional realization of rank-one mixtures -/

/-- **Mixture realization.** Given the arithmetic period count, for every weighted family of
integer type vectors the reals `mixPoint` have, for **every** integer form `cf`, limiting
discrepancy equal to the total weight of the types annihilated by `cf`. -/
theorem mixPoint_tendsto {b p t r d : ℕ} [NeZero r] (hb : 2 ≤ b) (hp : p.Prime) (hpb : ¬ p ∣ b)
    (ht : 0 < t) (hgrid : PeriodCount b p t) (m : Fin r → Fin d → ℤ) (w : Fin r → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (cf : Fin d → ℤ) :
    Tendsto (radixDiscrepancy b (∑ j, (cf j : ℝ) * mixPoint b p t r m w j)) atTop
      (𝓝 (mixtureValue m w cf)) := by
  classical
  have hℓ := segLen_pos (w := w) hp ht
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have ht0 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  obtain ⟨hW0, hW1⟩ := mixtureValue_mem hw0 hw1 (m := m) cf
  have hSmono := blockStart_strictMono (w := w) hp ht
  have hS0 := blockStart_zero (p := p) (t := t) (w := w)
  have hratio := blockStart_ratio (w := w) hp ht hw0 hw1
  -- every block is long: `Σ_i t p^g mult ≥ k + 1`
  have hBlong : ∀ k : ℕ, (k : ℝ) + 1 ≤ ∑ i, ((t * p ^ gexp p k * mult w k i : ℕ) : ℝ) := by
    intro k
    obtain ⟨m1, -⟩ := mult_sum_bounds hw0 hw1 k
    have hG1 : (1 : ℝ) ≤ ((p ^ gexp p k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hp.pos
    calc (k : ℝ) + 1 ≤ ∑ i, (mult w k i : ℝ) := m1
      _ ≤ ∑ i, ((t * p ^ gexp p k * mult w k i : ℕ) : ℝ) := Finset.sum_le_sum (fun i _ => by
          push_cast
          have h0 : (0 : ℝ) ≤ mult w k i := Nat.cast_nonneg _
          have : (1 : ℝ) ≤ (t : ℝ) * (p : ℝ) ^ gexp p k := by
            have := mul_le_mul ht0 (by exact_mod_cast hG1 : (1 : ℝ) ≤ (p : ℝ) ^ gexp p k)
              zero_le_one (by linarith)
            linarith
          nlinarith)
  -- the decomposition of the form numerators
  have hdec : ∀ i, ∃ ρ : ℕ, ∃ a' : ℤ, formNum m cf i = 0 ∨
      (formNum m cf i = (p : ℤ) ^ ρ * a' ∧ ¬ (p : ℤ) ∣ a') := by
    intro i
    by_cases h : formNum m cf i = 0
    · exact ⟨0, 0, Or.inl h⟩
    · obtain ⟨ρ, a', h1, h2⟩ := int_pow_decomp hp h
      exact ⟨ρ, a', Or.inr ⟨h1, h2⟩⟩
  choose ρ a' hρ using hdec
  have hρR : ∀ i, ρ i ≤ ∑ i, ρ i := fun i =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  -- the samples
  let y : ℕ → ℝ := mixModel b p t r m w cf
  let ret : ℕ → Prop := fun n => formNum m cf (typeOf r (locate (segLen p t r w) n)) = 0
  have hret_at : ∀ (k : ℕ) (i : Fin r) {j : ℕ}, j < t * p ^ gexp p k * mult w k i →
      (ret (segStart (segLen p t r w) (r * k + i) + j) ↔ formNum m cf i = 0) := by
    intro k i j hj
    simp only [ret, locate_block hp ht k i hj, fin_block]
  /- (1) the active counting error -/
  let ι := {ac : ℝ × ℝ // 0 ≤ ac.1 ∧ ac.1 < ac.2 ∧ ac.2 ≤ 1}
  let fA : ι → ℕ → ℝ := fun I n => if ret n then 0 else
    ((if I.1.1 ≤ y n ∧ y n < I.1.2 then 1 else 0) - (I.1.2 - I.1.1))
  have hfA : ∀ I n, |fA I n| ≤ 1 := by
    intro I n
    obtain ⟨h1, h2, h3⟩ := I.2
    simp only [fA]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hA := block_cesaro hSmono hS0 hratio fA hfA (by
    intro η hη
    filter_upwards [eventually_ge_atTop (p ^ ∑ i, ρ i),
      eventually_ge_atTop ⌈(p : ℝ) ^ (∑ i, ρ i + 1) / η⌉₊] with k hk1 hk2
    intro I
    obtain ⟨hI1, hI2, hI3⟩ := I.2
    have hgk : ∑ i, ρ i ≤ gexp p k := by
      unfold gexp
      exact Nat.le_log_of_pow_le hp.one_lt (by omega)
    have hGk : (p : ℝ) ^ (∑ i, ρ i) ≤ η * ((p ^ gexp p k : ℕ) : ℝ) := by
      obtain ⟨-, g2⟩ := gexp_bounds hp k
      have hk2' : (p : ℝ) ^ (∑ i, ρ i + 1) / η ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk2)
      rw [div_le_iff₀ hη] at hk2'
      rw [pow_succ] at hk2'
      have : (p : ℝ) * ((p : ℝ) ^ (∑ i, ρ i)) ≤ (p : ℝ) * (η * ((p ^ gexp p k : ℕ) : ℝ)) := by
        nlinarith
      exact le_of_mul_le_mul_left this hp0
    rw [blockStart_sum, blockStart_len, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rcases hρ i with h0 | ⟨hAi, hai⟩
    · -- a retired type contributes nothing
      have : ∀ j ∈ range (t * p ^ gexp p k * mult w k i),
          fA I (segStart (segLen p t r w) (r * k + i) + j) = 0 := by
        intro j hj
        simp only [fA, (hret_at k i (mem_range.mp hj)).mpr h0, ↓reduceIte]
      rw [Finset.sum_eq_zero this, abs_zero]
      positivity
    · have hne : formNum m cf i ≠ 0 := by
        rw [hAi]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
          (fun h => hai (h ▸ dvd_zero _))
      have hrw : ∀ j ∈ range (t * p ^ gexp p k * mult w k i),
          fA I (segStart (segLen p t r w) (r * k + i) + j) =
            (if I.1.1 ≤ Int.fract ((b : ℝ) ^ j * (formNum m cf i : ℝ) /
                (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p k)) ∧
              Int.fract ((b : ℝ) ^ j * (formNum m cf i : ℝ) /
                (p : ℝ) ^ (padicValNat p (b ^ t - 1) + gexp p k)) < I.1.2 then 1 else 0) -
              (I.1.2 - I.1.1) := by
        intro j hj
        have hj' := mem_range.mp hj
        have hnr : ¬ ret (segStart (segLen p t r w) (r * k + i) + j) :=
          fun h => hne ((hret_at k i hj').mp h)
        simp only [fA, hnr, ↓reduceIte, y, mixModel_block hp ht m w cf k i hj']
      rw [Finset.sum_congr rfl hrw]
      have hcount := segment_count (b := b) hp hpb hgrid hAi hai
        ((hρR i).trans hgk) (mult w k i) hI1 hI2 hI3
      refine hcount.trans ?_
      have hpow : (p : ℝ) ^ ρ i ≤ (p : ℝ) ^ (∑ i, ρ i) := pow_le_pow_right₀ hp1.le (hρR i)
      push_cast
      have h0 : (0 : ℝ) ≤ t * mult w k i := by positivity
      calc (t : ℝ) * (p : ℝ) ^ ρ i * mult w k i ≤ (t : ℝ) * (p : ℝ) ^ (∑ i, ρ i) * mult w k i := by
            gcongr
        _ ≤ (t : ℝ) * (η * (p : ℝ) ^ gexp p k) * mult w k i := by
            gcongr
            exact_mod_cast hGk
        _ = η * ((t : ℝ) * (p : ℝ) ^ gexp p k * mult w k i) := by ring)
  /- (2) the retired proportion -/
  let fZ : Unit → ℕ → ℝ := fun _ n => (if ret n then 1 else 0) - mixtureValue m w cf
  have hfZ : ∀ u n, |fZ u n| ≤ 1 := by
    intro u n
    simp only [fZ]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hZ := block_cesaro hSmono hS0 hratio fZ hfZ (by
    intro η hη
    filter_upwards [eventually_ge_atTop ⌈(r : ℝ) / η⌉₊] with k hk
    intro u
    have hk' : (r : ℝ) / η ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rw [div_le_iff₀ hη] at hk'
    have hseg : ∀ i : Fin r, ∑ j ∈ range (t * p ^ gexp p k * mult w k i),
        fZ u (segStart (segLen p t r w) (r * k + i) + j) =
        (t : ℝ) * (p : ℝ) ^ gexp p k * ((mult w k i : ℝ) *
          ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf)) := by
      intro i
      rw [Finset.sum_congr rfl (fun j hj => by
        simp only [fZ]
        rw [if_congr (hret_at k i (mem_range.mp hj)) rfl rfl])]
      simp only [Finset.sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [blockStart_sum, blockStart_len, Finset.sum_congr rfl (fun i _ => hseg i), ← Finset.mul_sum,
      abs_mul, abs_of_nonneg (by positivity)]
    have hbal := mult_balance (m := m) hw0 hw1 cf k
    have hlong := hBlong k
    have hG0 : (0 : ℝ) ≤ (t : ℝ) * (p : ℝ) ^ gexp p k := by positivity
    calc (t : ℝ) * (p : ℝ) ^ gexp p k * |∑ i, (mult w k i : ℝ) *
          ((if formNum m cf i = 0 then 1 else 0) - mixtureValue m w cf)|
        ≤ (t : ℝ) * (p : ℝ) ^ gexp p k * r := by gcongr
      _ ≤ (t : ℝ) * (p : ℝ) ^ gexp p k * (η * ∑ i, (mult w k i : ℝ)) := by
          gcongr
          obtain ⟨m1, -⟩ := mult_sum_bounds hw0 hw1 k
          nlinarith
      _ = η * ∑ i, ((t * p ^ gexp p k * mult w k i : ℕ) : ℝ) := by
          push_cast
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => by ring))
  /- conclusion -/
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set C : ℝ := ∑ j, |(cf j : ℝ)| with hC
  set B0 : ℝ := (b : ℝ) / (b - 1) with hB0
  have hε : 0 < δ / 8 := by positivity
  obtain ⟨L, hL⟩ : ∃ L : ℕ, C * B0 / (δ / 8) < (b : ℝ) ^ L := pow_unbounded_of_one_lt _ hb1
  /- (3) the tail windows -/
  let fE : Unit → ℕ → ℝ := fun _ n => if δ / 8 ≤ |mixTail b p t r m w cf n| then 1 else 0
  have hfE : ∀ u n, |fE u n| ≤ 1 := by
    intro u n; simp only [fE]; split_ifs <;> simp
  have hE := block_cesaro hSmono hS0 hratio fE hfE (by
    intro η hη
    filter_upwards [eventually_ge_atTop ⌈(r : ℝ) * L / η⌉₊] with k hk
    intro u
    have hk' : (r : ℝ) * L / η ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rw [div_le_iff₀ hη] at hk'
    have hseg : ∀ i : Fin r, ∑ j ∈ range (t * p ^ gexp p k * mult w k i),
        fE u (segStart (segLen p t r w) (r * k + i) + j) ≤ L := by
      intro i
      set Ls := t * p ^ gexp p k * mult w k i
      have hbad : ∀ j ∈ range Ls, fE u (segStart (segLen p t r w) (r * k + i) + j) ≤
          if Ls < j + L then 1 else 0 := by
        intro j hj
        have hj' := mem_range.mp hj
        simp only [fE]
        split_ifs with h1 h2 <;> try norm_num
        exfalso
        push Not at h2
        have hb := mixTail_bound hb hp ht m w cf (segStart (segLen p t r w) (r * k + i) + j)
        rw [locate_block hp ht k i hj', segStart_succ, segLen_block] at hb
        have hexp : L ≤ segStart (segLen p t r w) (r * k + i) + Ls -
            (segStart (segLen p t r w) (r * k + i) + j) := by omega
        have hpowL : (b : ℝ) ^ L ≤ (b : ℝ) ^ (segStart (segLen p t r w) (r * k + i) + Ls -
            (segStart (segLen p t r w) (r * k + i) + j)) := pow_le_pow_right₀ hb1.le hexp
        have hCB : 0 ≤ C * B0 := by
          have : 0 ≤ B0 := by rw [hB0]; apply div_nonneg <;> linarith
          exact mul_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)) this
        have : C * B0 / (b : ℝ) ^ (segStart (segLen p t r w) (r * k + i) + Ls -
            (segStart (segLen p t r w) (r * k + i) + j)) < δ / 8 := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hL
          nlinarith
        linarith
      calc _ ≤ ∑ j ∈ range Ls, (if Ls < j + L then (1 : ℝ) else 0) := Finset.sum_le_sum hbad
        _ = (((range Ls).filter (fun j => Ls < j + L)).card : ℝ) := by
            rw [Finset.natCast_card_filter]
        _ ≤ L := by
            have : (range Ls).filter (fun j => Ls < j + L) ⊆ Ico (Ls - L) Ls := by
              intro j hj
              simp only [mem_filter, mem_range] at hj
              simp only [mem_Ico]
              omega
            have h := card_le_card this
            rw [Nat.card_Ico] at h
            exact_mod_cast h.trans (by omega : Ls - (Ls - L) ≤ L)
    rw [blockStart_sum, blockStart_len]
    have hnn : 0 ≤ ∑ i : Fin r, ∑ j ∈ range (t * p ^ gexp p k * mult w k i),
        fE u (segStart (segLen p t r w) (r * k + i) + j) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
        simp only [fE]; split_ifs <;> norm_num))
    rw [abs_of_nonneg hnn]
    calc _ ≤ ∑ _i : Fin r, (L : ℝ) := Finset.sum_le_sum (fun i _ => hseg i)
      _ = r * L := by simp
      _ ≤ η * (k + 1) := by nlinarith
      _ ≤ η * ∑ i, ((t * p ^ gexp p k * mult w k i : ℕ) : ℝ) := by gcongr; exact hBlong k)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    ((hA (δ / 8) hε).and ((hZ (δ / 8) hε).and ((hE (δ / 8) hε).and (eventually_ge_atTop 1))))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, hN1⟩ := hN0 N hN
  have hNpos : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have cmp := sampleDisc_compare (p := y) (q := shift b (∑ j, (cf j : ℝ) * mixPoint b p t r m w j))
    (r := mixTail b p t r m w cf) (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
    (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) (mix_pairing hb hp ht m w cf) hNpos hε
  have mix := sampleDisc_mixture (y := y) hNpos ret (fun n hn => by
      simp only [y, mixModel]
      rw [show formNum m cf (typeOf r (locate (segLen p t r w) n)) = 0 from hn]
      simp) (H := δ / 8 * N)
    (fun a c ha hac hc => h1 ⟨(a, c), ha, hac, hc⟩)
  have hEN : (((range N).filter (fun n => δ / 8 ≤ |mixTail b p t r m w cf n|)).card : ℝ) ≤
      δ / 8 * N := by
    have := (abs_le.mp (h3 ())).2
    simp only [fE] at this
    rw [Finset.natCast_card_filter]
    exact this
  have hZN : |(∑ n ∈ range N, if ret n then (1 : ℝ) else 0) - mixtureValue m w cf * N| ≤
      δ / 8 * N := by
    have := h2 ()
    simp only [fZ] at this
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul] at this
    rwa [mul_comm] at this
  rw [Real.dist_eq, radixDiscrepancy_eq_sampleDisc]
  set Z := ∑ n ∈ range N, if ret n then (1 : ℝ) else 0
  have e1 : (((range N).filter (fun n => δ / 8 ≤ |mixTail b p t r m w cf n|)).card : ℝ) / N ≤
      δ / 8 := by rw [div_le_iff₀ hNr]; exact hEN
  have e2 : |Z / N - mixtureValue m w cf| ≤ δ / 8 := by
    rw [show Z / N - mixtureValue m w cf = (Z - mixtureValue m w cf * N) / N by field_simp,
      abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
    exact hZN
  have e3 : (Z + δ / 8 * N) / N = Z / N + δ / 8 := by field_simp
  rw [e3] at mix
  obtain ⟨m1, m2⟩ := mix
  rw [abs_le] at cmp e2
  rw [abs_lt]
  constructor <;> linarith [cmp.1, cmp.2, e2.1, e2.2]

/-- **Unconditional form, given a prime.** -/
theorem mixtureRealizable_of_periodCount {b p t : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (hpb : ¬ p ∣ b) (ht : 0 < t) (hgrid : PeriodCount b p t) {d r : ℕ}
    (m : Fin r → Fin d → ℤ) (w : Fin r → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    MixtureRealizable b m w := by
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hw1
  have : NeZero r := ⟨hr⟩
  exact ⟨mixPoint b p t r m w, fun cf => mixPoint_tendsto hb hp hpb ht hgrid m w hw0 hw1 cf⟩

/-- **The exact addition spectrum, given the arithmetic period count.** -/
theorem addSpectrum_eq_of_periodCount {b p t : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (hpb : ¬ p ∣ b)
    (ht : 0 < t) (hgrid : PeriodCount b p t) : addSpectrum b = polytope :=
  le_antisymm (addSpectrum_subset_polytope b)
    (polytope_subset_addSpectrum_of_realizable b (fun α β γ hv =>
      mixtureRealizable_of_periodCount hb hp hpb ht hgrid fiveTypes (fiveWeights α β γ)
        (fiveWeights_nonneg hv) (sum_fiveWeights α β γ)))

end NormalityChecker.AdditionSpectrum
