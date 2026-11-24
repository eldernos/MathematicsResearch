module

public import NormalityChecker.TypicalShadow

/-! Upper Banach density of the exceptional diagonal logarithm models. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ShadowCancellations

/-- The exceptional fraction tends to zero uniformly over the starting index. -/
def ZeroUpperBanachDensity (B : ℕ → Prop) [DecidablePred B] : Prop :=
  ∀ η : ℝ, 0<η → ∀ᶠ T : ℕ in atTop, ∀ A : ℕ, (((Ico A (A+T)).filter B).card:ℝ) ≤ η*T

private theorem sparse_windows (B : ℕ → Prop) [DecidablePred B] {δ : ℝ} (hd : 0<δ)
    (initial : Tendsto (fun N : ℕ => (((range N).filter B).card:ℝ)/N) atTop (𝓝 0))
    (price : ∀ᶠ n : ℕ in atTop, B n → δ*n≤lostWeight n) : ZeroUpperBanachDensity B := by
  intro η he
  have pos : 0<η*δ := mul_pos he hd
  obtain ⟨H,hH⟩ := exists_nat_gt (24/(η*δ))
  let C : ℝ := 1+(H:ℝ)^2+2*H+4
  have frac : 12/((H:ℝ)+1) < η*δ/2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith only [(div_lt_iff₀ pos).mp hH,pos]
  obtain ⟨K,hK⟩ := eventually_atTop.mp price
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (initial.eventually_lt_const (half_pos he))
  have grow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (24*C/(η*δ))
  filter_upwards [grow,eventually_ge_atTop (max J K),eventually_gt_atTop 0] with T size late tp
  intro A
  let E := (Ico A (A+T)).filter B
  by_cases early : A≤T
  · have sub : E⊆(range (2*T)).filter B := by
      intro n hn; obtain ⟨mem,bad⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨mem_range.mpr (by have := (mem_Ico.mp mem).2; omega),bad⟩
    have h := hJ (2*T) (by omega)
    change (((range (2*T)).filter B).card:ℝ)/(2*T:ℕ) < η/2 at h
    push_cast at h; rw [div_lt_iff₀ (by positivity)] at h
    change (E.card:ℝ) ≤ _
    linarith only [Nat.cast_le (α:=ℝ).mpr (card_le_card sub),h]
  · have ar : (0:ℝ)<A := by exact_mod_cast (by omega : 0<A)
    have tr : (T:ℝ)≤A := by exact_mod_cast (by omega : T≤A)
    have sumPrice := sum_le_sum (s:=E) (f:=fun _ => δ*(A:ℝ)) (g:=lostWeight) (fun n hn => by
      obtain ⟨mem,bad⟩ := mem_filter.mp hn
      have lo := (mem_Ico.mp mem).1
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr lo) hd.le).trans (hK n (by omega) bad))
    rw [sum_const,nsmul_eq_mul] at sumPrice
    have sumCap := sum_le_sum_of_subset_of_nonneg (s:=E) (t:=Ico A (A+T)) (filter_subset ..)
      (fun n _ _ => nonneg_weight n)
    have mass := (sumPrice.trans sumCap).trans (window_lost_weight A T H)
    push_cast at mass
    have bound := Chebyshev.theta_le_log4_mul_x (x:=2*((A:ℝ)+T)) (by positivity)
    have coeff := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)) (show 0≤2*((A:ℝ)+T) by positivity)
    have theta : Chebyshev.theta (2*((A:ℝ)+T)) ≤ 12*A := by linarith only [bound,coeff,tr]
    have factor : 0≤(T:ℝ)/(H+1)+C := by dsimp [C]; positivity
    have weight : (E.card:ℝ)*(δ*A)≤12*A*((T:ℝ)/(H+1)+C) := by
      apply mass.trans; convert mul_le_mul_of_nonneg_right theta factor using 1; dsimp [C]; ring
    have h₁ := mul_le_mul_of_nonneg_right frac.le (Nat.cast_nonneg (α:=ℝ) T)
    have h₂ := (div_lt_iff₀ pos).mp size
    have total : 12*((T:ℝ)/(H+1)+C) ≤ η*δ*T := by
      rw [div_mul_eq_mul_div] at h₁; ring_nf at h₁ ⊢; linarith only [h₁,h₂]
    have scaled := mul_le_mul_of_nonneg_left total ar.le
    apply (le_of_mul_le_mul_right (a:=δ*A) _ (mul_pos hd ar))
    change (E.card:ℝ)*(δ*A) ≤ η*T*(δ*A)
    linarith only [weight,scaled]

/-- For each fixed tolerance the small diagonal denominators have upper Banach density zero. -/
theorem small_denominators_uniformly_sparse {ε : ℝ} (pos : 0<ε) :
    ZeroUpperBanachDensity (fun n => Real.log (logShadow n n).den≤(1-ε)*n) :=
  sparse_windows _ (half_pos pos) (diagonal_small_denominators_density_zero pos) (small_denominator_price pos)

/-- Losing a fixed fraction of upper-interval primes is rare even in moving windows. -/
theorem missing_fraction_uniformly_sparse {ε : ℝ} (pos : 0<ε) :
    ZeroUpperBanachDensity (fun n => ε*((2*n).primesLE \ n.primesLE).card≤(missing n).card) :=
  sparse_windows _ (by positivity : 0<ε/4) (missing_prime_fraction_density_zero pos) (missing_fraction_price pos)

end NormalityChecker.ShadowCancellations
