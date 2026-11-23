module

public import NormalityChecker.Correlations

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- The first-order drift of the rational recurrence has a uniform second-order
error even when the lag depends on the starting position. -/
theorem logPrefix_drift_bounds (n r : ℕ) :
    let D := logPrefix (n+r)-2^r*logPrefix n
    let B := (2^r-1)/((n:ℚ)+1)
    0 ≤ B-D ∧ B-D ≤ (2^r-(r:ℚ)-1)/((n:ℚ)+1)^2 := by
  dsimp only
  constructor
  · exact sub_nonneg.mpr (logPrefix_steps_bounds n r).2
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [logPrefix, pow_succ' (2:ℚ) r]
    change _ - (2*logPrefix (n+r)+1/(((n+r:ℕ):ℚ)+1)-_) ≤ _
    push_cast
    have hj : 1/((n:ℚ)+1)-1/(n+r+1) ≤ r/(n+1)^2 := by
      have eqn : 1/((n:ℚ)+1)-1/(n+r+1) = r/((n+1)*(n+r+1)) := by field_simp; ring
      rw [eqn]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [sq]; gcongr; linarith [Nat.cast_nonneg (α:=ℚ) r]
    linarith only [show (2*(2:ℚ)^r-1)/(n+1) = 2*((2^r-1)/(n+1))+1/(n+1) by ring,
      show (2*(2:ℚ)^r-((r:ℚ)+1)-1)/(n+1)^2 = 2*((2^r-r-1)/(n+1)^2)+r/(n+1)^2 by ring,
      ih,hj]

/-- Centering by the drift gives a usable joint-character estimate up to
lags with 2^r = o(n²). Frequencies h and g are fixed integers. -/
theorem logPrefix_centered_lag_bound (n r : ℕ) (h g : ℤ) :
    ‖phase (h*(logPrefix n:ℝ))*phase (g*(logPrefix (n+r):ℝ)) -
      phase (((h:ℝ)+2^r*g)*(logPrefix n:ℝ) + g*((2^r-1)/((n:ℝ)+1)))‖ ≤
        2*Real.pi*|(g:ℝ)| *((2^r-(r:ℝ)-1)/((n:ℝ)+1)^2) := by
  obtain ⟨hl,hu⟩ := logPrefix_drift_bounds n r
  let E := (2^r-1)/((n:ℝ)+1)-((logPrefix (n+r):ℝ)-2^r*(logPrefix n:ℝ))
  have h₁ : 0≤E := by dsimp [E]; exact_mod_cast hl
  have h₂ : E≤(2^r-(r:ℝ)-1)/((n:ℝ)+1)^2 := by dsimp [E]; exact_mod_cast hu
  rw [← phase_add]
  apply (phase_sub_le _ _).trans
  rw [show (h:ℝ)*logPrefix n + g*logPrefix (n+r) -
      ((h+2^r*g)*logPrefix n+g*((2^r-1)/((n:ℝ)+1))) = -(g*E) by dsimp [E]; ring,
    abs_neg,abs_mul,abs_of_nonneg h₁,← mul_assoc]
  exact mul_le_mul_of_nonneg_left h₂ (by positivity)

/-- A concrete critical scale: at n=a·2^k and lag k, the unwrapped drift
tends to 1/a. This is independent of any normality hypothesis. -/
theorem logPrefix_dyadic_lag_limit (a : ℕ) (ha : 0<a) :
    Tendsto (fun k : ℕ => (logPrefix (a*2^k+k):ℝ) - (2:ℝ)^k*logPrefix (a*2^k)) atTop (𝓝 (1/(a:ℝ))) := by
  let n (k : ℕ) := a*2^k
  let D (k : ℕ) : ℝ := (logPrefix (n k+k):ℝ)-2^k*(logPrefix (n k):ℝ)
  let B (k : ℕ) : ℝ := (2^k-1)/((n k:ℝ)+1)
  have hg : Tendsto n atTop atTop := by
    apply tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left (2^k) ha)
    exact tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ))
  have hsmall : Tendsto (fun k : ℕ => 1/((n k:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hg
  have hB : Tendsto B atTop (𝓝 (1/(a:ℝ))) := by
    have H := (tendsto_const_nhds (x:=1/(a:ℝ))).sub ((tendsto_const_nhds (x:=1+1/(a:ℝ))).mul hsmall)
    simpa using H.congr (f₂:=B) (fun k => by dsimp [B,n]; push_cast; field_simp; ring)
  have error : Tendsto (fun k => B k-D k) atTop (𝓝 0) := by
    have bounds (k : ℕ) : 0≤B k-D k ∧ B k-D k≤(2^k-(k:ℝ)-1)/((n k:ℝ)+1)^2 := by
      dsimp [B,D]; exact_mod_cast logPrefix_drift_bounds (n k) k
    apply squeeze_zero (fun k => (bounds k).1) _ hsmall
    intro k
    apply (bounds k).2.trans
    have hden : (0:ℝ)<n k+1 := by positivity
    rw [div_le_div_iff₀ (sq_pos_of_pos hden) hden,one_mul,sq]
    apply mul_le_mul_of_nonneg_right _ hden.le
    have H : (2:ℝ)^k ≤ n k := by exact_mod_cast Nat.le_mul_of_pos_left (2^k) ha
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  simpa [B,D,n] using hB.sub error

end NormalityChecker
