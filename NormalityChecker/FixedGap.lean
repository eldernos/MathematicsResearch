module

public import NormalityChecker.AggregateGaps

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

open Classical in
/-- Starts before `N` with no hit at any of the `k+1` offsets `0,...,k`.
The final window may extend past `N`. -/
noncomputable def missCount (P : ℕ → Prop) (N k : ℕ) :=
  ((range N).filter (fun n => ¬∃ j≤k, P (n+j))).card

open Classical in
/-- A hit covers at most `k+1` starts. The final `k` starts may use later hits. -/
theorem fixed_window_count (P : ℕ → Prop) (N k : ℕ) :
    N ≤ missCount P N k + k + (k+1)*((range N).filter P).card := by
  let H (n : ℕ) := ∃ j≤k, P (n+j)
  have h := count_within_steps (P:=H) (Q:=P) N k (fun _ h => h)
  have part := card_filter_add_card_filter_not (s:=range N) H
  change ((range N).filter H).card + missCount P N k = _ at part
  rw [card_range] at part; omega

open Classical in
/-- An eventual upper bound `ρ` on one fixed window's miss fraction gives
middle-third hit density at least `(1-ρ)/(k+1)` for the logarithmic recurrence. -/
theorem logTwo_density_of_fixed_window (k : ℕ) {ρ : ℝ}
    (h : ∀ᶠ N : ℕ in atTop, (missCount MiddleHit N k:ℝ) ≤ ρ*N) :
    (1-ρ)/(k+1) ≤ liminf middleFrequency atTop := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  let c := (1-ρ)/((k:ℝ)+1)
  let a := (k:ℝ)/((k:ℝ)+1)
  have bound : ∀ᶠ N : ℕ in atTop, c-a/(N:ℝ) ≤ middleFrequency N := by
    filter_upwards [h,eventually_gt_atTop 0] with N hn hN
    have hN' : (0:ℝ)<N := by exact_mod_cast hN
    have fin : (N:ℝ) ≤ (missCount MiddleHit N k:ℝ)+k+((k:ℝ)+1)*((range N).filter MiddleHit).card := by
      exact_mod_cast fixed_window_count MiddleHit N k
    unfold middleFrequency; dsimp [c,a]; field_simp; nlinarith only [hn,fin]
  have lim : Tendsto (fun N : ℕ => c-a/(N:ℝ)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x:=c)).sub (tendsto_const_div_atTop_nhds_zero_nat a)
  have ub (N : ℕ) : middleFrequency N ≤ 1 := by
    obtain rfl | hn := Nat.eq_zero_or_pos N
    · simp [middleFrequency]
    · apply (div_le_one (by exact_mod_cast hn : (0:ℝ)<N)).mpr
      exact_mod_cast (card_filter_le (range N) MiddleHit).trans_eq (card_range _)
  change c ≤ _
  exact lim.liminf_eq ▸ liminf_le_liminf bound lim.isBoundedUnder_ge (isCoboundedUnder_ge_of_le _ ub)

/-- The fixed-window estimate gives an explicit conditional discrepancy bound. -/
theorem logTwo_discrepancy_of_fixed_window (k : ℕ) {ρ : ℝ}
    (h : ∀ᶠ N : ℕ in atTop, (missCount MiddleHit N k:ℝ) ≤ ρ*N) :
    asymptoticDiscrepancy (Real.log 2) ≤ max (2/3) (1-(1-ρ)/(k+1)) :=
  logTwo_discrepancy_le_middle.trans (max_le_max_left _ (sub_le_sub_left (logTwo_density_of_fixed_window k h) 1))

/-- Missing the closed middle third for `k+1` successive binary shifts confines the
starting value to either end of the unit interval, with exact endpoint conventions. -/
theorem middle_miss_intervals (x : ℝ) (n k : ℕ) :
    (∀ j≤k, ¬(1/3 ≤ shift 2 x (n+j) ∧ shift 2 x (n+j) ≤ 2/3)) ↔
    shift 2 x n < (1/2:ℝ)^k/3 ∨ 1-(1/2:ℝ)^k/3 < shift 2 x n := by
  induction k generalizing n with
  | zero => simp; constructor <;> intro h <;> rcases lt_or_ge (shift 2 x n) (1/3) with h'|h' <;> grind
  | succ k ih =>
    let v := shift 2 x n
    let c := (1/2:ℝ)^k/3
    have hc : 0<c := by dsimp [c]; positivity
    have hc' : c≤1/3 := by dsimp [c]; gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
    have split : (∀ j≤k+1, ¬(1/3 ≤ shift 2 x (n+j) ∧ shift 2 x (n+j) ≤ 2/3)) ↔
      ¬(1/3≤v ∧ v≤2/3) ∧ ∀ j≤k, ¬(1/3 ≤ shift 2 x (n+1+j) ∧ shift 2 x (n+1+j) ≤ 2/3) := by
      constructor
      · intro H; refine ⟨by simpa [v] using H 0 (by omega),fun j hj => ?_⟩
        simpa [Nat.add_assoc,Nat.add_comm 1 j] using H (j+1) (by omega)
      · rintro ⟨h,H⟩ (_|j) hj
        · simpa [v] using h
        · simpa [Nat.add_assoc,Nat.add_comm 1 j] using H j (by omega)
    rw [split,ih,binary_shift_step,pow_succ]
    change (¬(1/3≤v ∧ v≤2/3) ∧ ((if v<1/2 then 2*v else 2*v-1)<c ∨ 1-c<(if v<1/2 then 2*v else 2*v-1))) ↔ _
    have e : (1/2:ℝ)^k*(1/2)/3 = c/2 := by dsimp [c]; ring
    rw [e]; change _ ↔ v<c/2 ∨ 1-c/2<v
    split_ifs <;> grind

open MeasureTheory in
/-- Lebesgue probability of `k+1` consecutive misses, for a uniform starting point. -/
theorem middle_miss_volume (k : ℕ) :
    volume {x : ℝ | x ∈ Set.Ico 0 1 ∧ ∀ j≤k, ¬(1/3 ≤ shift 2 x j ∧ shift 2 x j ≤ 2/3)} =
      ENNReal.ofReal ((2/3:ℝ)*(1/2)^k) := by
  let c := (1/2:ℝ)^k/3
  have hc : 0<c := by dsimp [c]; positivity
  have hc' : c≤1/3 := by dsimp [c]; gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
  have set_eq : {x : ℝ | x ∈ Set.Ico 0 1 ∧ ∀ j≤k, ¬(1/3 ≤ shift 2 x j ∧ shift 2 x j ≤ 2/3)} =
      Set.Ico 0 c ∪ Set.Ioo (1-c) 1 := by
    ext x
    have H := middle_miss_intervals x 0 k
    simp only [zero_add] at H
    by_cases hx : x ∈ Set.Ico (0:ℝ) 1
    · have he : shift 2 x 0=x := by simpa [shift] using Int.fract_eq_self.mpr hx
      simp only [Set.mem_ofPred_eq,H,he,true_and,Set.mem_union,Set.mem_Ico,Set.mem_Ioo,c, hx.1,hx.2,and_true]
    · simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_Ico,Set.mem_Ioo]
      change ¬ (0≤x ∧ x<1) at hx; grind
  have disj : Disjoint (Set.Ico 0 c) (Set.Ioo (1-c) 1) := Set.disjoint_left.mpr (by
    intro x hx hy; have := hx.2; have := hy.1; linarith)
  rw [set_eq,measure_union disj measurableSet_Ioo,Real.volume_Ioo,Real.volume_Ico,sub_zero,sub_sub_cancel,
    ← ENNReal.ofReal_add hc.le hc.le]; congr 1; dsimp [c]; ring

end NormalityChecker
