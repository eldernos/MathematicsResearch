module

public import NormalityChecker.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section
open Finset Filter
open scoped Topology

namespace NormalityChecker

/-- Positive rational multiples of any prescribed positive generators can sum to
any prescribed positive real. Choosing the generators from a jointly normal
family therefore gives a rational total without weakening finite compatibility. -/
theorem hasSum_positive_rational_multiples (g : ℕ → ℝ) (hg : ∀ n, 0 < g n)
    {R : ℝ} (hR : 0 < R) :
    ∃ c : ℕ → ℚ, (∀ n, 0 < c n) ∧ HasSum (fun n => (c n : ℝ) * g n) R := by
  classical
  have step (n : ℕ) (r : {x : ℝ // 0 < x}) :
      ∃ q : ℚ, r.val / 2 < (q : ℝ) * g n ∧ (q : ℝ) * g n < r.val := by
    have gap : (r.val / 2) / g n < r.val / g n :=
      div_lt_div_of_pos_right (by linarith [r.property]) (hg n)
    obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn gap
    exact ⟨q, (div_lt_iff₀ (hg n)).mp hlo, (lt_div_iff₀ (hg n)).mp hhi⟩
  choose weight hlo hhi using step
  let rem : ℕ → {x : ℝ // 0 < x} := Nat.rec ⟨R, hR⟩
    (fun n r => ⟨r.val - (weight n r : ℝ) * g n, sub_pos.mpr (hhi n r)⟩)
  let c (n : ℕ) := weight n (rem n)
  have next (n : ℕ) : (rem (n+1)).val = (rem n).val - (c n : ℝ) * g n := rfl
  have hc (n : ℕ) : 0 < c n := by
    have h : 0 < (c n : ℝ) * g n :=
      lt_trans (half_pos (rem n).property) (hlo n (rem n))
    exact_mod_cast (pos_of_mul_pos_left h (hg n).le)
  have bound (n : ℕ) : (rem n).val ≤ R * (1/2:ℝ)^n := by
    induction n with
    | zero => simp [rem]
    | succ n ih =>
      rw [next, pow_succ]
      have h := hlo n (rem n)
      change (rem n).val / 2 < (c n : ℝ) * g n at h
      linarith
  have conv : Tendsto (fun n => (rem n).val) atTop (𝓝 0) := by
    have limit := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ) < 1)).const_mul R
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using limit) (fun n => (rem n).property.le) bound
  have partialSum (n : ℕ) : ∑ i ∈ range n, (c i : ℝ) * g i = R - (rem n).val := by
    induction n with
    | zero => simp [rem]
    | succ n ih => rw [sum_range_succ, ih, next]; ring
  refine ⟨c, hc, (hasSum_iff_tendsto_nat_of_nonneg (fun n => ?_) R).mpr ?_⟩
  · exact mul_nonneg (by exact_mod_cast (hc n).le) (hg n).le
  · simp_rw [partialSum]
    simpa only [sub_zero] using
      (show Tendsto (fun n => R - (rem n).val) atTop (𝓝 (R - 0)) from
        tendsto_const_nhds.sub conv)

end NormalityChecker
