module

public import NormalityChecker.FourierTest

/-! Rational certificates for simplifying radix coefficients. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- A checkable identity for the coefficients simplifies every partial sum,
including both boundary terms. Indices here start at zero. -/
theorem radix_telescope_prefix {b : ℕ} (hb : 0<b) (a r H : ℕ → ℚ)
    (step : ∀ n, a n=r n+H n-H (n+1)/b) (N : ℕ) :
    ∑ n∈range N, a n/(b:ℚ)^n = (∑ n∈range N,r n/(b:ℚ)^n) + H 0-H N/(b:ℚ)^N := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ,sum_range_succ,ih,step,pow_succ]; field_simp [hb.ne']; ring

/-- A rational endpoint preserves normality under weighted telescoping. Absolute
summability of the simpler expansion and of the weighted antiderivative suffices. -/
theorem normal_radix_telescope_iff {b : ℕ} (hb : 2≤b) (a r H : ℕ → ℚ)
    (step : ∀ n, a n=r n+H n-H (n+1)/b)
    (hr : Summable (fun n => (r n:ℝ)/(b:ℝ)^n)) (hH : Summable (fun n => (H n:ℝ)/(b:ℝ)^n)) :
    NormalIn b (∑' n,(a n:ℝ)/(b:ℝ)^n) ↔ NormalIn b (∑' n,(r n:ℝ)/(b:ℝ)^n) := by
  let f (n : ℕ) := (H n:ℝ)/(b:ℝ)^n
  have sh : Summable (fun n => f (n+1)) := (summable_nat_add_iff 1).mpr hH
  have id (n : ℕ) : (a n:ℝ)/(b:ℝ)^n=(r n:ℝ)/(b:ℝ)^n+f n-f (n+1) := by
    rw [step]; dsimp [f]; push_cast; rw [pow_succ]; field_simp [show b≠0 by omega]
  simp_rw [id]; rw [(hr.add hH).tsum_sub sh,hr.tsum_add hH]
  have total := hH.sum_add_tsum_nat_add 1
  change _ + ∑' n,f (n+1)=∑' n,f n at total
  simp only [Finset.sum_range_one,f,pow_zero,div_one] at total
  convert normal_add_rat_iff hb (∑' n,(r n:ℝ)/(b:ℝ)^n) (H 0) using 2
  dsimp [f]; linarith only [total]

/-- Regroup a summable weighted sequence along the half-open power intervals. -/
theorem radix_plateau_regroup {c : ℕ} (hc : 1<c) (a f : ℕ → ℝ)
    (conv : Summable (fun i : ℕ => a (Nat.log c (i+1))*f (i+1))) :
    (∑' i : ℕ, a (Nat.log c (i+1))*f (i+1)) =
      ∑' j : ℕ, a j * ∑ n ∈ Ico (c^j) (c^(j+1)), f n := by
  classical
  let g (i : ℕ) := Nat.log c (i+1)
  let F (i : ℕ) := a (g i)*f (i+1)
  change (∑' i, F i) = _
  have H := conv.hasSum.tsum_fiberwise g
  rw [← H.tsum_eq]; apply tsum_congr; intro j
  let A := c^j; let B := c^(j+1)
  have ap : 0<A := pow_pos (by omega : 0<c) _
  have bp : 0<B := pow_pos (by omega : 0<c) _
  have hit (i : ℕ) : i ∈ Ico (A-1) (B-1) ↔ g i=j := by
    dsimp only [g]; rw [Nat.log_eq_iff (Or.inr ⟨hc,Nat.succ_ne_zero i⟩),mem_Ico]
    change (_ ∧ _) ↔ A ≤ i + 1 ∧ i + 1 < B
    omega
  change (∑' x : (g ⁻¹' {j}), F x) = _
  rw [_root_.tsum_subtype,tsum_eq_sum (s:=Ico (A-1) (B-1)) (fun i hi => Set.indicator_of_notMem (fun h => hi ((hit i).mpr h)) _)]
  calc _ = ∑ i∈Ico (A-1) (B-1), a j*f (i+1) := by
             apply sum_congr rfl; intro i hi; have h := (hit i).mp hi
             rw [Set.indicator_of_mem (show i∈g ⁻¹' {j} from h)]; simp [F,h]
       _ = a j * ∑ i∈Ico A B, f i := by
             rw [← mul_sum, Finset.sum_Ico_add' f,Nat.sub_add_cancel ap,Nat.sub_add_cancel bp]


/-- Coefficients constant between consecutive powers of `c` can be regrouped
exactly into a lacunary series. The dense expansion starts at position one. -/
theorem radix_plateau_sum {c : ℕ} (hc : 1<c) {z : ℝ} (hz : z≠1) (a : ℕ → ℝ)
    (conv : Summable (fun i : ℕ => a (Nat.log c (i+1))*z^(i+1))) :
    (∑' i : ℕ, a (Nat.log c (i+1))*z^(i+1)) =
      ∑' j : ℕ, a j*((z^(c^j)-z^(c^(j+1)))/(1-z)) := by
  rw [radix_plateau_regroup hc a (fun n => z^n) conv]
  apply tsum_congr; intro j
  rw [geom_sum_Ico' hz (Nat.pow_le_pow_right hc.le (Nat.le_succ j))]

end NormalityChecker
