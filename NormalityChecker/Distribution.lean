module

public import NormalityChecker.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

public section

open Filter Finset
open scoped Topology

namespace NormalityChecker

/-- Signed count of integer translates of `[a,c)` containing `x`. For `0 ≤ a ≤ c ≤ 1`
this is the ordinary zero-one indicator on the fractional part of `x`. -/
private noncomputable def crossings (a c x : ℝ) : ℝ := (⌊x - a⌋ : ℝ) - ⌊x - c⌋

private noncomputable def average (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ range N, f i

private abbrev HasAverage (f : ℕ → ℝ) (t : ℝ) := Tendsto (average f) atTop (𝓝 t)

private lemma average_add {f g : ℕ → ℝ} {s t : ℝ} (hf : HasAverage f s) (hg : HasAverage g t) :
    HasAverage (fun i => f i + g i) (s+t) := by
  unfold HasAverage average at *
  simpa [sum_add_distrib, mul_add] using hf.add hg

private lemma average_sub {f g : ℕ → ℝ} {s t : ℝ} (hf : HasAverage f s) (hg : HasAverage g t) :
    HasAverage (fun i => f i - g i) (s-t) := by
  unfold HasAverage average at *
  simpa [sum_sub_distrib, mul_sub] using hf.sub hg

private lemma average_const (t : ℝ) : HasAverage (fun _ => t) t := tendsto_const_nhds.cesaro

private lemma average_mono {f g : ℕ → ℝ} (h : ∀ i, f i ≤ g i) (N : ℕ) :
    average f N ≤ average g N := by
  exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => h i) (by positivity)

private lemma crossings_mono_right (a x : ℝ) {c d : ℝ} (h : c ≤ d) :
    crossings a c x ≤ crossings a d x := by
  apply sub_le_sub_left
  exact_mod_cast Int.floor_mono (show x - d ≤ x - c by linarith)

private lemma floor_sub_endpoint {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (x : ℝ) :
    ⌊x - t⌋ = ⌊x⌋ - (if Int.fract x < t then 1 else 0) := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  unfold Int.fract at *
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  · simp only [sub_zero]
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith

private lemma average_crossings_eq_frequency (u : ℕ → ℝ) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    average (fun i => crossings a c (u i)) =
      frequency (fun i => Int.fract (u i)) a c := by
  funext N
  have h (x : ℝ) : crossings a c x = if a ≤ Int.fract x ∧ Int.fract x < c then 1 else 0 := by
    rw [crossings, floor_sub_endpoint ha (hac.trans hc), floor_sub_endpoint (ha.trans hac) hc]
    split_ifs <;> push_cast <;> first | (exfalso; grind) | ring
  simp only [average, h, frequency, sum_boole, div_eq_inv_mul]

/-- All translated half-open intervals have the limiting frequency given by their length.
The floor difference counts integer translates, so endpoints may cross an integer. -/
@[expose] def UniformModOne (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
    ∑ i ∈ range N, ((⌊u i - a⌋ : ℝ) - ⌊u i - c⌋)) atTop (𝓝 (c - a))

private lemma uniform_blocks {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hu : UniformModOne (fun n => (b : ℝ)^n * x)) : NormalIn b x := by
  refine ⟨hb, fun k m _ hm => ?_⟩
  let d : ℝ := (b : ℝ)^k
  have hd : 0 < d := by dsimp [d]; positivity
  have hmd : (m : ℝ) + 1 ≤ d := by dsimp [d]; exact_mod_cast (show m+1 ≤ b^k from hm)
  have H : HasAverage (fun i => crossings (m/d) ((m+1)/d) ((b : ℝ)^i * x))
      ((m+1)/d - m/d) := hu _ _
  unfold HasAverage at H
  simp_rw [average_crossings_eq_frequency (a := m/d) (c := (m+1)/d) _ (by positivity) (div_le_div_of_nonneg_right (by linarith) hd.le)
    ((div_le_one hd).mpr hmd)] at H
  convert H using 2 <;> first | rfl | ring

private lemma grid_average {b : ℕ} {x : ℝ} (hn : NormalIn b x) (k : ℕ) (hk : 0 < k)
    (m : ℕ) (hm : m ≤ b ^ k) :
    HasAverage (fun i => crossings 0 (m / (b : ℝ)^k) ((b : ℝ)^i * x)) (m / (b : ℝ)^k) := by
  have hb := hn.1
  let d : ℝ := (b : ℝ)^k
  have hd : 0 < d := by dsimp [d]; positivity
  induction m with
  | zero => simpa [crossings] using average_const 0
  | succ m ih =>
    have hm' : m < b^k := hm
    have hmd : (m : ℝ)+1 ≤ d := by dsimp [d]; exact_mod_cast hm
    have H : HasAverage (fun i => crossings (m/d) ((m+1)/d) ((b : ℝ)^i * x)) (1/d) := by
      unfold HasAverage
      simp_rw [average_crossings_eq_frequency (a := m/d) (c := (m+1)/d) _ (by positivity) (div_le_div_of_nonneg_right (by linarith) hd.le)
        ((div_le_one hd).mpr hmd)]
      exact hn.2 k m hk hm'
    have hsum := average_add (ih hm'.le) H
    simpa [crossings, d, add_div] using hsum

/-- The radix grids have points strictly between any two reals. -/
private lemma grid_between {b : ℕ} (hb : 2 ≤ b) {a c : ℝ} (hac : a < c) :
    ∃ (k : ℕ) (z : ℤ), 0 < k ∧ a < z / (b : ℝ)^k ∧ z / (b : ℝ)^k < c := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (c-a)) hb'
  let d : ℝ := (b : ℝ)^(k+1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hstep : 1 < (c-a)*d := by
    have hle : (b : ℝ)^k ≤ d := pow_le_pow_right₀ hb'.le (by omega)
    have := (div_lt_iff₀ (sub_pos.mpr hac)).mp (hk.trans_le hle)
    linarith
  refine ⟨k+1, ⌊a*d⌋+1, by omega, ?_, ?_⟩
  · rw [lt_div_iff₀ hd]; push_cast; exact Int.lt_floor_add_one _
  · rw [div_lt_iff₀ hd]; push_cast; linarith [Int.floor_le (a*d)]

private lemma signed_grid_average {b : ℕ} {x : ℝ} (hn : NormalIn b x)
    (k : ℕ) (hk : 0 < k) (z : ℤ) :
    HasAverage (fun i => crossings 0 (z / (b : ℝ)^k) ((b : ℝ)^i * x)) (z / (b : ℝ)^k) := by
  let D : ℤ := (b : ℤ)^k
  have hb := hn.1
  have hD : 0 < D := by dsimp [D]; positivity
  let m := (z % D).toNat
  let w := z / D
  have hm : (m : ℤ) = z % D := Int.toNat_of_nonneg (Int.emod_nonneg _ hD.ne')
  have hm' : m ≤ b^k := by
    have h : (m : ℤ) ≤ D := by rw [hm]; exact (Int.emod_lt_of_pos _ hD).le
    dsimp [D] at h
    exact_mod_cast h
  let d : ℝ := (b : ℝ)^k
  have hd : 0 < d := by dsimp [d]; positivity
  have he : (z : ℝ) / d = m/d + w := by
    have e : (z : ℤ) = m + D*w := by rw [hm]; exact (Int.emod_add_mul_ediv _ _).symm
    have e' : (z : ℝ) = m + d * w := by dsimp [D] at e; dsimp [d]; exact_mod_cast e
    rw [e']; field_simp
  have H := average_add (grid_average hn k hk m hm') (average_const (w : ℝ))
  change HasAverage (fun i => crossings 0 (z / d) ((b : ℝ)^i * x)) (z / d)
  rw [he]
  convert H using 2 with i
  simp only [crossings, ← sub_sub, Int.floor_sub_intCast, Int.cast_sub]
  ring

/-- Equidistribution modulo one is equivalent to the overlapping digit-block definition. -/
theorem normalIn_iff_uniform {b : ℕ} (hb : 2 ≤ b) (x : ℝ) :
    NormalIn b x ↔ UniformModOne (fun n => (b : ℝ)^n * x) := by
  refine ⟨fun hn => ?_, uniform_blocks hb⟩
  have anchored (t : ℝ) : HasAverage (fun i => crossings 0 t ((b : ℝ)^i * x)) t := by
    rw [HasAverage, tendsto_order]
    constructor
    · intro a ha
      obtain ⟨k, z, hk, h₁, h₂⟩ := grid_between hb ha
      filter_upwards [(tendsto_order.mp (signed_grid_average hn k hk z)).1 _ h₁] with N hN
      exact hN.trans_le (average_mono (fun i => crossings_mono_right _ _ h₂.le) N)
    · intro c hc
      obtain ⟨k, z, hk, h₁, h₂⟩ := grid_between hb hc
      filter_upwards [(tendsto_order.mp (signed_grid_average hn k hk z)).2 _ h₂] with N hN
      exact (average_mono (fun i => crossings_mono_right _ _ h₁.le) N).trans_lt hN
  intro a c
  change HasAverage (fun i => crossings a c ((b : ℝ)^i * x)) (c-a)
  have H := average_sub (anchored c) (anchored a)
  convert H using 2 with i
  unfold crossings
  ring

private lemma average_congr_eventually {f g : ℕ → ℝ} {t : ℝ} (hf : HasAverage f t)
    (h : f =ᶠ[atTop] g) : HasAverage g t := by
  have hz : Tendsto (fun i => g i - f i) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [h] with i hi
    simp [hi]
  simpa using average_add hf hz.cesaro

private lemma crossings_sandwich {x y ε : ℝ} (h : |y-x| ≤ ε) (a c : ℝ) :
    crossings (a+ε) (c-ε) x ≤ crossings a c y ∧
    crossings a c y ≤ crossings (a-ε) (c+ε) x := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  constructor <;> apply sub_le_sub <;> exact_mod_cast Int.floor_mono (by linarith)

/-- Vanishing perturbations of the unwrapped sequence preserve equidistribution,
including shifts which wrap across zero after taking their fractional part. -/
theorem uniformModOne_of_error {u v : ℕ → ℝ}
    (hu : UniformModOne u) (he : Tendsto (fun n => v n - u n) atTop (𝓝 0)) :
    UniformModOne v := by
  intro a c
  change HasAverage (fun i => crossings a c (v i)) (c-a)
  rw [HasAverage, tendsto_order]
  have hs (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ i in atTop, crossings (a+ε) (c-ε) (u i) ≤ crossings a c (v i) ∧
        crossings a c (v i) ≤ crossings (a-ε) (c+ε) (u i) := by
    have h := (Metric.tendsto_nhds.mp he) ε hε
    filter_upwards [h] with i hi
    rw [Real.dist_eq, sub_zero] at hi
    exact crossings_sandwich hi.le _ _
  constructor
  · intro r hr
    let ε := (c-a-r)/4
    have hε : 0 < ε := by dsimp [ε]; linarith
    let f i := crossings (a+ε) (c-ε) (u i)
    let g i := crossings a c (v i)
    have H : HasAverage f ((c-ε)-(a+ε)) := hu _ _
    have H' : HasAverage (fun i => min (f i) (g i)) ((c-ε)-(a+ε)) := by
      apply average_congr_eventually H
      filter_upwards [hs ε hε] with i hi using (min_eq_left hi.1).symm
    filter_upwards [(tendsto_order.mp H').1 r (by dsimp [ε]; linarith)] with N hN
    exact hN.trans_le (average_mono (fun i => min_le_right (f i) (g i)) N)
  · intro r hr
    let ε := (r-(c-a))/4
    have hε : 0 < ε := by dsimp [ε]; linarith
    let f i := crossings (a-ε) (c+ε) (u i)
    let g i := crossings a c (v i)
    have H : HasAverage f ((c+ε)-(a-ε)) := hu _ _
    have H' : HasAverage (fun i => max (f i) (g i)) ((c+ε)-(a-ε)) := by
      apply average_congr_eventually H
      filter_upwards [hs ε hε] with i hi using (max_eq_left hi.2).symm
    filter_upwards [(tendsto_order.mp H').2 r (by dsimp [ε]; linarith)] with N hN
    exact (average_mono (fun i => le_max_right (f i) (g i)) N).trans_lt hN

/-- A general test for a formula admitting approximations to its shifted values. -/
theorem normalIn_iff_uniform_approx {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (u : ℕ → ℝ)
    (he : Tendsto (fun n => (b : ℝ)^n * x - u n) atTop (𝓝 0)) :
    NormalIn b x ↔ UniformModOne u := by
  rw [normalIn_iff_uniform hb]
  exact ⟨fun h => uniformModOne_of_error h (by simpa using he.neg),
    fun h => uniformModOne_of_error h he⟩

/-- Convergence on any anchored interval, including the endpoints 0 and 1. -/
theorem anchored_frequency_of_normal {b : ℕ} {x : ℝ} (hn : NormalIn b x) {t : ℝ}
    (ht : 0≤t) (ht' : t≤1) : Tendsto (frequency (shift b x) 0 t) atTop (𝓝 t) := by
  have H : HasAverage (fun n => crossings 0 t ((b:ℝ)^n*x)) (t-0) :=
    (normalIn_iff_uniform hn.1 x).mp hn 0 t
  unfold HasAverage at H
  rw [average_crossings_eq_frequency _ le_rfl ht ht',sub_zero] at H
  exact H

end NormalityChecker
