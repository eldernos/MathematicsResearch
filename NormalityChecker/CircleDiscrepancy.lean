module

public import NormalityChecker.SupportDiscrepancy

/-! Extreme interval discrepancy under signed perturbations of circle samples. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.CircleDiscrepancy

/-- Extreme interval discrepancy of a prefix of real lifts, reduced modulo one. -/
noncomputable def disc (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup {v | ∃ a d : ℝ, 0 ≤ a ∧ a < d ∧ d ≤ 1 ∧
    v = |frequency (fun i => Int.fract (u i)) a d N - (d-a)|}

private lemma bounded (u : ℕ → ℝ) (N : ℕ) : ∀ v ∈
    {v | ∃ a d : ℝ, 0 ≤ a ∧ a < d ∧ d ≤ 1 ∧
    v = |frequency (fun i => Int.fract (u i)) a d N - (d-a)|}, v ≤ 1 := by
  rintro _ ⟨a,d,ha,lt,hd,rfl⟩
  have := frequency_bounds (fun i => Int.fract (u i)) a d N
  rw [abs_le]; constructor <;> linarith [this.1,this.2]

theorem test_le (u : ℕ → ℝ) (N : ℕ) {a d : ℝ} (ha : 0≤a) (lt : a<d) (hd : d≤1) :
    |frequency (fun i => Int.fract (u i)) a d N - (d-a)| ≤ disc u N :=
  le_csSup ⟨1,bounded u N⟩ ⟨a,d,ha,lt,hd,rfl⟩

theorem disc_le {u : ℕ → ℝ} {N : ℕ} {C : ℝ} (h : ∀ a d : ℝ, 0≤a → a<d → d≤1 →
    |frequency (fun i => Int.fract (u i)) a d N - (d-a)| ≤ C) : disc u N ≤ C := by
  unfold disc
  refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
  rintro _ ⟨a,d,ha,lt,hd,rfl⟩; exact h a d ha lt hd

/-- A uniform error for interval counts transfers to the discrepancy of a
mixture of Lebesgue measure and a finite sample, even at atoms. -/
theorem disc_mixture_bound (u v : ℕ → ℝ) (N L : ℕ) {z η : ℝ} (hz : 0≤z)
    (H : ∀ a d : ℝ, 0≤a → a<d → d≤1 →
      |(frequency (fun i => Int.fract (u i)) a d N - (d-a)) -
        z*(frequency (fun i => Int.fract (v i)) a d L - (d-a))| ≤ η) :
    |disc u N - z*disc v L| ≤ η := by
  have bounds (a d : ℝ) (ha : 0≤a) (lt : a<d) (hd : d≤1) := abs_abs_sub_abs_le_abs_sub
    (frequency (fun i => Int.fract (u i)) a d N - (d-a))
    (z*(frequency (fun i => Int.fract (v i)) a d L - (d-a)))
  have diff (a d : ℝ) (ha : 0≤a) (lt : a<d) (hd : d≤1) :=
    (bounds a d ha lt hd).trans (H a d ha lt hd)
  simp only [abs_mul,abs_of_nonneg hz,abs_le] at diff
  have up : disc u N ≤ z*disc v L+η := disc_le (fun a d ha lt hd => by
    linarith [(diff a d ha lt hd).2,mul_le_mul_of_nonneg_left (test_le v L ha lt hd) hz])
  rw [abs_le]
  refine ⟨?_,by linarith⟩
  rcases hz.eq_or_lt with rfl | pos
  · simp only [zero_mul,sub_zero]
    have := (diff 0 1 le_rfl zero_lt_one le_rfl).1
    linarith [(test_le u N le_rfl zero_lt_one le_rfl)]
  · have low : disc v L ≤ (disc u N + η)/z := disc_le (fun a d ha lt hd => by
      rw [le_div_iff₀ pos]; linarith [(diff a d ha lt hd).1,test_le u N ha lt hd])
    linarith [(le_div_iff₀ pos).mp low]

private noncomputable def saw (t : ℝ) := (⌈t⌉ : ℝ) - t

private lemma saw_bounds (t : ℝ) : 0 ≤ saw t ∧ saw t ≤ 1 :=
  ⟨sub_nonneg.mpr (Int.le_ceil _), by dsimp [saw]; linarith [Int.ceil_lt_add_one t]⟩

private lemma saw_fract (t x : ℝ) : saw (t-Int.fract x) = saw (t-x) := by
  rw [Int.fract,sub_sub_eq_add_sub,show t + ↑⌊x⌋ - x = t-x+↑⌊x⌋ by ring]
  simp [saw,Int.ceil_add_intCast]

private lemma fract_saw (t x : ℝ) : saw (Int.fract t-x) = saw (t-x) := by
  rw [Int.fract,sub_right_comm]; simp [saw,Int.ceil_sub_intCast]

private noncomputable def primitive (u : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ range N, saw (t-u i)) / N

private lemma primitive_fract (u : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    primitive u N (Int.fract t) = primitive u N t := by simp [primitive,fract_saw]

private lemma increment (u : ℕ → ℝ) {N : ℕ} (hn : 0<N) {a d : ℝ}
    (ha : 0≤a) (had : a≤d) (hd : d≤1) :
    primitive u N d - primitive u N a = frequency (fun i => Int.fract (u i)) a d N - (d-a) := by
  classical
  have point (t x : ℝ) (ht : 0≤t) (ht' : t≤1) :
      (⌈t-Int.fract x⌉:ℝ) = if Int.fract x < t then 1 else 0 := by
    have xl := Int.fract_nonneg x; have xr := Int.fract_lt_one x
    split_ifs with h
    · have e : ⌈t-Int.fract x⌉ = 1 := Int.ceil_eq_iff.mpr ⟨by push_cast; linarith,by push_cast; linarith⟩
      simp [e]
    · have e : ⌈t-Int.fract x⌉ = 0 := Int.ceil_eq_iff.mpr ⟨by push_cast; linarith,by push_cast; linarith⟩
      simp [e]
  have each (i : ℕ) : saw (d-u i) - saw (a-u i) =
      (if a ≤ Int.fract (u i) ∧ Int.fract (u i) < d then (1:ℝ) else 0) - (d-a) := by
    rw [← saw_fract d,← saw_fract a,saw,saw,point d _ (ha.trans had) hd,point a _ ha (had.trans hd)]
    split_ifs <;> grind
  unfold primitive
  rw [← sub_div,← sum_sub_distrib]
  simp only [each,sum_sub_distrib,← sum_filter,
    sum_const,card_range,nsmul_eq_mul,mul_one,frequency]
  field_simp

private lemma increment_le (u : ℕ → ℝ) {N : ℕ} (hn : 0<N) (a d : ℝ) :
    primitive u N d - primitive u N a ≤ disc u N := by
  rw [← primitive_fract u N d,← primitive_fract u N a]
  rcases lt_trichotomy (Int.fract a) (Int.fract d) with h|h|h
  · rw [increment u hn (Int.fract_nonneg _) h.le (Int.fract_lt_one _).le]
    exact (le_abs_self _).trans (test_le _ _ (Int.fract_nonneg _) h (Int.fract_lt_one _).le)
  · rw [h,sub_self]; exact (abs_nonneg _).trans (test_le u N le_rfl zero_lt_one le_rfl)
  · have e := increment u hn (Int.fract_nonneg _) h.le (Int.fract_lt_one _).le
    linarith [(neg_le_abs _).trans (test_le u N (Int.fract_nonneg _) h (Int.fract_lt_one _).le)]

private lemma transport {u v : ℕ → ℝ} {N K : ℕ} (hn : 0<N) {δ : ℝ} (pos : 0≤δ)
    (near : ∀ i, K ≤ i → |u i-v i| ≤ δ) : disc u N ≤ disc v N + 2*δ + 2*K/N := by
  classical
  have upper (a d : ℝ) : primitive u N d - primitive u N a ≤ disc v N + 2*δ + 2*K/N := by
    have each (i : ℕ) : saw (d-u i)-saw (a-u i) ≤
        saw (d+δ-v i)-saw (a-δ-v i) + 2*δ + (if i<K then 2 else 0) := by
      split_ifs with h
      · linarith [(saw_bounds (d-u i)).2,(saw_bounds (a-u i)).1,
          (saw_bounds (d+δ-v i)).1,(saw_bounds (a-δ-v i)).2]
      · have H := abs_le.mp (near i (by omega))
        have U := Int.ceil_mono (show d-u i ≤ d+δ-v i by linarith [H.1])
        have L := Int.ceil_mono (show a-δ-v i ≤ a-u i by linarith [H.2])
        dsimp only [saw]; linarith [Int.cast_le (R:=ℝ).mpr U,Int.cast_le (R:=ℝ).mpr L]
    have S := sum_le_sum (s:=range N) (fun i _ => each i)
    simp only [sum_add_distrib,sum_sub_distrib,← sum_filter,sum_const,nsmul_eq_mul,card_range] at S
    have cnt : (((range N).filter (·<K)).card:ℝ) ≤ K := by
      exact_mod_cast (card_le_card (show (range N).filter (·<K) ⊆ range K from
        fun _ h => mem_range.mpr (mem_filter.mp h).2)).trans_eq (card_range K)
    have nr : (0:ℝ)<N := by exact_mod_cast hn
    have V := increment_le v hn (a-δ) (d+δ)
    simp only [primitive,← sub_div,div_le_iff₀ nr] at V ⊢
    rw [add_mul,div_mul_cancel₀ _ nr.ne',add_mul]
    linarith
  apply disc_le; intro a d ha lt hd
  rw [← increment u hn ha lt.le hd, abs_le]
  exact ⟨by linarith [upper d a],upper a d⟩

/-- Vanishing signed differences of lifts leave the full prefix discrepancy
unchanged asymptotically. The empirical measures may have atomic limits. -/
theorem disc_sub_tendsto {u v : ℕ → ℝ} (tail : Tendsto (fun i => u i-v i) atTop (𝓝 0)) :
    Tendsto (fun N => disc u N-disc v N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]; intro ε he
  obtain ⟨K,near⟩ := Metric.tendsto_atTop.mp tail (ε/8) (by positivity)
  have h (i : ℕ) (hi : K ≤ i) : |u i-v i| ≤ ε/8 := by simpa [Real.dist_eq] using (near i hi).le
  obtain ⟨N₀,price⟩ := eventually_atTop.mp ((tendsto_const_div_atTop_nhds_zero_nat (2*(K:ℝ))).eventually_lt_const
    (show 0<ε/2 by positivity))
  refine ⟨max 1 N₀,fun N hN => ?_⟩
  have hn : 0<N := by omega
  have A := transport (N:=N) hn (by positivity) h
  have B := transport (N:=N) hn (by positivity) (fun i hi => (abs_sub_comm _ _).trans_le (h i hi))
  have P := price N (by omega)
  rw [Real.dist_eq,sub_zero,abs_lt]; constructor <;> linarith

end NormalityChecker.CircleDiscrepancy
