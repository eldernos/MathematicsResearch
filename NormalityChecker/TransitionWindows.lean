module

public import NormalityChecker.LogTwoTransitions
public import NormalityChecker.LogShadowIntegral

/-! Internal transitions of overlapping binary words on dyadic shells. -/

@[expose] public section
open Finset Filter
namespace NormalityChecker.TransitionWindows

/-- Positions whose two binary digits differ, using the terminating convention. -/
def Hit (x : ℝ) (t : ℕ) : Prop := 1/4 ≤ shift 2 x t ∧ shift 2 x t < 3/4

noncomputable instance (x : ℝ) : DecidablePred (Hit x) := Classical.decPred _

/-- Changes internal to the `T` bits at positions `n,...,n+T-1`. -/
noncomputable def changes (x : ℝ) (n T : ℕ) : ℕ :=
  ((range (T-1)).filter (fun j => Hit x (n+j))).card

/-- The integral for ln 2 gives a block of `T-1` consecutive starts with at least
one change, for every late `B` and `2 ≤ T ≤ B`. -/
theorem logTwo_one_change_blocks : ∀ᶠ B : ℕ in atTop, ∀ T, 2 ≤ T → T ≤ B →
    ∃ a : ℕ, B ≤ a ∧ a+(T-1) ≤ 68*B ∧
      ∀ n ∈ Ico a (a+(T-1)), 1 ≤ changes (Real.log 2) n T := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp logTwo_window_hit
  filter_upwards [eventually_ge_atTop K] with B hB
  intro T hT hTB
  obtain ⟨t, lo, hi, _, bits⟩ := hK (2*B) (by omega)
  refine ⟨t+2-T, by omega, by omega, ?_⟩
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_Ico.mp hn
  apply card_pos.mpr
  refine ⟨t-n, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩⟩
  rw [Nat.add_sub_of_le (by omega : n ≤ t)]
  exact (transition_iff_bits _ _).mpr bits

/-- The corrected numerator at `N` certifies individual true transitions through
two further shell lengths by a fixed interior test on its rational orbit. -/
theorem logTwo_hit_of_diagonal {N j : ℕ} (hN : 256 ≤ N) (hj : j ≤ 2*N)
    (interior : let z := Int.fract ((2:ℝ)^j * logShadow N N)
      5/16 ≤ z ∧ z ≤ 11/16) : Hit (Real.log 2) (N+j) := by
  let u := (2:ℝ)^j * logShadow N N
  let d := (2:ℝ)^(N+j)*Real.log 2-u
  change 5/16 ≤ Int.fract u ∧ Int.fract u ≤ 11/16 at interior
  have err := logShadow_double_length (n:=N) hj
  change d^2*((N:ℝ)+1) ≤ 1 at err
  have hn : (256:ℝ) ≤ N := by exact_mod_cast hN
  have small : d^2*257 ≤ 1 := (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg d)).trans err
  have dl : -(1/16:ℝ) < d := by
    by_contra! h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (show d+1/16 ≤ 0 by linarith)
      (show d-1/16 ≤ 0 by linarith)]
  have du : d < (1/16:ℝ) := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ d-1/16 by linarith) (show 0 ≤ d+1/16 by linarith)]
  have shift_eq : shift 2 (Real.log 2) (N+j) = Int.fract u+d := by
    change Int.fract ((2:ℝ)^(N+j)*Real.log 2) = _
    have split : (2:ℝ)^(N+j)*Real.log 2 = (Int.fract u+d)+⌊u⌋ := by
      dsimp [d]
      linarith [Int.fract_add_floor u]
    rw [split, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith [interior.1], by linarith [interior.2]⟩
  unfold Hit
  rw [shift_eq]
  exact ⟨by linarith [interior.1], by linarith [interior.2]⟩

/-- Two four-bit CRT cells suffice to force a true transition. The equality of
fractional parts follows from the CRT identity for the chosen numerator. -/
theorem logTwo_hit_of_crt_cells {N j i k : ℕ} {a b : ℝ} (hN : 256 ≤ N) (hj : j ≤ 2*N)
    (joint : Int.fract ((2:ℝ)^j * logShadow N N) = Int.fract (a+b))
    (ha : i ≤ 16*a ∧ 16*a < i+1) (hb : k ≤ 16*b ∧ 16*b < k+1)
    (cells : 5 ≤ (i+k)%16 ∧ (i+k)%16 ≤ 9) : Hit (Real.log 2) (N+j) := by
  apply logTwo_hit_of_diagonal hN hj
  dsimp only
  rw [joint]
  let q := (i+k)/16
  have eqn : (↑((i+k)%16):ℝ) + 16*(q:ℝ) = i+k := by
    exact_mod_cast Nat.mod_add_div (i+k) 16
  have lo : (5:ℝ) ≤ ↑((i+k)%16) := by exact_mod_cast cells.1
  have hi : (↑((i+k)%16):ℝ) ≤ 9 := by exact_mod_cast cells.2
  let z := a+b-(q:ℝ)
  have lower : 5/16 ≤ z := by dsimp [z]; linarith [ha.1, hb.1]
  have upper : z < 11/16 := by dsimp [z]; linarith [ha.2, hb.2]
  have split : a+b = z+(q:ℤ) := by simp [z]
  rw [split, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact ⟨lower, upper.le⟩

/-- The number of incidences, including all overlaps among the `N` words. -/
noncomputable def aggregate (x : ℝ) (N T : ℕ) : ℕ :=
  ∑ n ∈ Ico N (2*N), changes x n T

/-- Each transition is charged at most once per internal offset. The last possible
transition is at `2*N+T-3` when `N≥1` and `T≥2`. -/
theorem aggregate_le (x : ℝ) (N T : ℕ) :
    aggregate x N T ≤ (T-1) * ((Ico N (2*N-1+(T-1))).filter (Hit x)).card := by
  classical
  let S := Ico N (2*N)
  let H := (Ico N (2*N-1+(T-1))).filter (Hit x)
  have col (j : ℕ) (hj : j ∈ range (T-1)) :
      (S.filter (fun n => Hit x (n+j))).card ≤ H.card := by
    apply card_le_card_of_injOn (fun n => n+j)
    · intro n hn
      obtain ⟨hn, ht⟩ := mem_filter.mp hn
      obtain ⟨lo, hi⟩ := mem_Ico.mp hn
      have off := mem_range.mp hj
      change n+j ∈ H
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ht⟩
    · intro a _ b _ eq
      exact Nat.add_right_cancel eq
  calc
    aggregate x N T = ∑ n ∈ S, ∑ j ∈ range (T-1), if Hit x (n+j) then 1 else 0 := by
      simp [aggregate, changes, S, sum_boole]
    _ = ∑ j ∈ range (T-1), (S.filter (fun n => Hit x (n+j))).card := by
      rw [sum_comm]
      simp [sum_boole]
    _ ≤ ∑ _j ∈ range (T-1), H.card := sum_le_sum col
    _ = _ := by simp [H]

/-- For every sufficiently large dyadic shell suppose the mean number of changes
per word is at least `α*T`, for any positive word length at most the shell size.
The frequency bound holds at every sufficiently large integer cutoff. -/
theorem frequency_of_dyadic_aggregate (x : ℝ) (width : ℕ → ℕ) {α : ℝ} (hα : 0 ≤ α)
    (hyp : ∀ᶠ k : ℕ in atTop, let N := 2^k; let T := width N
      0 < T ∧ T ≤ N ∧ α * N * T ≤ (aggregate x N T : ℝ)) :
    ∀ᶠ M : ℕ in atTop, α/6 ≤ transitionFrequency x M := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hyp
  filter_upwards [eventually_ge_atTop (3*2^K)] with M hM
  let k := Nat.log 2 (M/3)
  let N := 2^k
  let T := width N
  have large : 2^K ≤ M/3 := by omega
  have pos : 0 < M/3 := (pow_pos (by decide : 0 < 2) K).trans_le large
  have fits := Nat.pow_log_le_self 2 pos.ne'
  have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (M/3)
  change N ≤ M/3 at fits
  rw [pow_succ] at upper
  change M/3 < N*2 at upper
  have hMN : M ≤ 6*N := by omega
  obtain ⟨hT, hTN, hmean⟩ := hK k (Nat.le_log_of_pow_le (by decide) large)
  change 0 < T at hT
  change T ≤ N at hTN
  change α * N * T ≤ (aggregate x N T : ℝ) at hmean
  let P := ((range M).filter (Hit x)).card
  have inside : ((Ico N (2*N-1+(T-1))).filter (Hit x)).card ≤ P := by
    apply card_le_card
    intro t ht
    obtain ⟨ht, hit⟩ := mem_filter.mp ht
    have endpt := (mem_Ico.mp ht).2
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hit⟩
  have cap : aggregate x N T ≤ T*P := (aggregate_le x N T).trans
    (Nat.mul_le_mul (by omega) inside)
  have count : α * N ≤ P := by
    apply le_of_mul_le_mul_right (a:=(T:ℝ)) _ (by exact_mod_cast hT)
    exact hmean.trans (by exact_mod_cast cap.trans_eq (Nat.mul_comm T P))
  have freq : transitionFrequency x M = (P:ℝ)/M := by
    unfold transitionFrequency frequency P
    congr 3
    ext t
    simp [Hit]
  rw [freq]
  rw [le_div_iff₀ (by exact_mod_cast (show 0 < M by omega))]
  have scaled := mul_le_mul_of_nonneg_left (show (M:ℝ) ≤ 6*N by exact_mod_cast hMN) hα
  linarith

/-- Positive aggregate on all late dyadic shells gives a positive lower density
and an explicit strict bound on the upper limiting interval discrepancy. -/
theorem density_discrepancy_of_dyadic_aggregate (x : ℝ) (width : ℕ → ℕ) {α : ℝ} (hα : 0 < α)
    (hyp : ∀ᶠ k : ℕ in atTop, let N := 2^k; let T := width N
      0 < T ∧ T ≤ N ∧ α * N * T ≤ (aggregate x N T : ℝ)) :
    α/6 ≤ transitionDensity x ∧ asymptoticDiscrepancy x ≤ max (2/3) (1-α/6) ∧
      asymptoticDiscrepancy x < 1 := by
  have den : α/6 ≤ transitionDensity x := le_liminf_of_le
    (isCoboundedUnder_ge_of_le _ fun M => (frequency_bounds (shift 2 x) (1/4) (3/4) M).2)
    (frequency_of_dyadic_aggregate x width hα.le hyp)
  exact ⟨den, (sharp_asymptotic_discrepancy x).trans (max_le_max_left _ (by linarith)),
    (discrepancy_lt_one_iff_transitions x).2 (by linarith)⟩

/-- At least `η*N` starts on the shell have at least `ρ*T` internal changes. -/
def ManyRich (x : ℝ) (η ρ : ℝ) (N T : ℕ) : Prop :=
  η*N ≤ (((Ico N (2*N)).filter (fun n => ρ*T ≤ (changes x n T : ℝ))).card : ℝ)

private theorem aggregate_of_manyRich {x η ρ : ℝ} {N T : ℕ} (hρ : 0 ≤ ρ)
    (h : ManyRich x η ρ N T) : (η*ρ)*N*T ≤ (aggregate x N T : ℝ) := by
  let S := Ico N (2*N)
  let G := S.filter (fun n => ρ*T ≤ (changes x n T : ℝ))
  change η*N ≤ (G.card:ℝ) at h
  calc
    (η*ρ)*N*T = (η*N)*(ρ*T) := by ring
    _ ≤ G.card*(ρ*T) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = ∑ _n ∈ G, ρ*T := by simp
    _ ≤ ∑ n ∈ G, (changes x n T : ℝ) := sum_le_sum fun n hn => (mem_filter.mp hn).2
    _ ≤ ∑ n ∈ S, (changes x n T : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by simp [aggregate, S]

/-- The requested power-length criterion for the actual binary words of ln 2.
The case `δ=1` permits words extending almost a full shell past its right edge. -/
theorem logTwo_of_many_rich_windows {δ η ρ : ℝ} (hδ : 0 < δ) (δ1 : δ ≤ 1)
    (hη : 0 < η) (hρ : 0 < ρ)
    (rich : ∀ᶠ k : ℕ in atTop, let N := 2^k
      ManyRich (Real.log 2) η ρ N ⌊(N:ℝ)^δ⌋₊) :
    η*ρ/6 ≤ transitionDensity (Real.log 2) ∧
      asymptoticDiscrepancy (Real.log 2) ≤ max (2/3) (1-η*ρ/6) ∧
      asymptoticDiscrepancy (Real.log 2) < 1 := by
  apply density_discrepancy_of_dyadic_aggregate (Real.log 2) (fun N => ⌊(N:ℝ)^δ⌋₊)
    (mul_pos hη hρ)
  filter_upwards [rich] with k hk
  let N : ℕ := 2^k
  have one : (1:ℝ) ≤ N := by exact_mod_cast (Nat.one_le_pow k 2 (by decide))
  refine ⟨Nat.floor_pos.mpr (Real.one_le_rpow one hδ.le), ?_, aggregate_of_manyRich hρ.le hk⟩
  exact Nat.floor_le_of_le (Real.rpow_le_self_of_one_le one δ1)

end NormalityChecker.TransitionWindows
