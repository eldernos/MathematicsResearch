module

public import NormalityChecker.IntervalCoverage
public import NormalityChecker.DyadicEscape

/-! Fixed local quality on disjoint pieces and Fourier escape on intermittent dyadic shells. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.Coverage

/-- The finite saving is the covered share times one minus the certified local cost. -/
theorem fixed_quality_cover {ι : Type*} [DecidableEq ι] {b N : ℕ} {x d : ℝ}
    (J : Finset ι) (piece : ι → Finset ℕ) (pos : 0<N)
    (inside : ∀ j∈J, piece j ⊆ range N) (disjoint : (J:Set ι).PairwiseDisjoint piece)
    (cert : ∀ a c : ℝ, 0≤a → a<c → c≤1 → ∀ j∈J,
      ‖∑ i∈piece j, Localized.centered (shift b x) a c i‖≤d*(piece j).card) :
    radixDiscrepancy b x N ≤ 1-(1-d)*((J.biUnion piece).card/N:ℝ) := by
  have sub : J.biUnion piece ⊆ range N := by
    intro i hi; obtain ⟨j,hj,h⟩ := mem_biUnion.mp hi; exact inside j hj h
  have sz : ((range N \ J.biUnion piece).card:ℝ)+(J.biUnion piece).card=N := by
    exact_mod_cast (card_sdiff_add_card_eq_card sub).trans (card_range N)
  have nr : (0:ℝ)<N := by exact_mod_cast pos
  unfold radixDiscrepancy
  refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
  rintro _ ⟨a,c,ha,ac,hc,rfl⟩
  have H := disjoint_cover _ (Localized.centered_norm (shift b x) ha ac.le hc) J piece
    (fun j => d*(piece j).card) N inside disjoint (cert a c ha ac hc)
  rw [← mul_sum, ← Nat.cast_sum, ← card_biUnion disjoint] at H
  have cent := Localized.centered_sum (shift b x) a c 0 N
  simp only [Nat.zero_add] at cent
  unfold partialSum at H; rw [cent] at H
  change |(IntervalFourier.count _ _ _ N:ℝ)/N-(c-a)|≤_
  rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_iff₀ nr]
  convert H using 1; field_simp; nlinarith

/-- Every sufficiently long prefix may choose its own disjoint local certificates. -/
theorem asymptotic_fixed_quality {b : ℕ} {x g d : ℝ} (hd : d≤1)
    (cover : ∀ e : ℝ, 0<e → ∀ᶠ N : ℕ in atTop, ∃ (J : Finset ℕ) (piece : ℕ → Finset ℕ),
      (∀ j∈J, piece j ⊆ range N) ∧ (J:Set ℕ).PairwiseDisjoint piece ∧
      g-e≤((J.biUnion piece).card/N:ℝ) ∧
      ∀ a c : ℝ, 0≤a → a<c → c≤1 → ∀ j∈J,
        ‖∑ i∈piece j, Localized.centered (shift b x) a c i‖≤d*(piece j).card) :
    limsup (radixDiscrepancy b x) atTop ≤ 1-g*(1-d) := by
  apply (limsup_le_iff (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds b x N).1))
    (isBoundedUnder_of_eventually_le (.of_forall (fun N => (radix_discrepancy_bounds b x N).2)))).mpr
  intro z hz
  let e := (z-(1-g*(1-d)))/(2+|1-d|)
  have ep : 0<e := div_pos (by linarith) (by positivity)
  have eqn : e*(2+|1-d|)=z-(1-g*(1-d)) := div_mul_cancel₀ _ (by positivity)
  rw [abs_of_nonneg (sub_nonneg.mpr hd)] at eqn
  filter_upwards [cover e ep,eventually_gt_atTop 0] with N ⟨J,S,sub,dis,share,cert⟩ pos
  exact (fixed_quality_cover J S pos sub dis cert).trans_lt (by
    nlinarith only [mul_le_mul_of_nonneg_left share (sub_nonneg.mpr hd),eqn,ep])

/-- Among h consecutive late shells, one has a certified mean at least e.
Only the most recent h *completed* shells are used in this finite prefix bound. -/
theorem intermittent_dyadic_lower (f : ℕ → ℝ) (nn : ∀ i,0≤f i) {e : ℝ} (he : 0≤e)
    {h : ℕ} (good : ∀ᶠ k : ℕ in atTop, ∃ j, k≤j ∧ j<k+h ∧
      e*(2:ℝ)^j≤∑ i∈range (2^j),f (2^j+i)) :
    ∀ᶠ N : ℕ in atTop, e/(2:ℝ)^(h+1)≤(∑ i∈range N,f i)/N := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp good
  filter_upwards [eventually_ge_atTop (2^(K+h))] with N large
  let k := Nat.log 2 N
  have kl : K+h≤k := Nat.le_log_of_pow_le (by decide) large
  have np : 0<N := (pow_pos (by decide : 0<2) _).trans_le large
  obtain ⟨j,lo,hi,cert⟩ := hK (k-h) (by omega)
  have jk : j+1≤k := by omega
  have ends : 2^(j+1)≤N := (Nat.pow_le_pow_right (by decide) jk).trans (Nat.pow_log_le_self 2 np.ne')
  have all := sum_le_sum_of_subset_of_nonneg (range_mono ends) (fun i _ _ => nn i)
  rw [pow_succ,mul_two,sum_range_add] at all
  have lower := cert.trans ((le_add_of_nonneg_left (sum_nonneg (s:=range (2^j)) (fun i _ => nn i))).trans all)
  have upper : (N:ℝ)≤(2:ℝ)^j*2^(h+1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) N).le.trans
      ((Nat.pow_le_pow_right (by decide : 0<2) (show k+1≤j+(h+1) by omega)).trans_eq (pow_add 2 j (h+1)))
  rw [le_div_iff₀ (by exact_mod_cast np : (0:ℝ)<N),div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_left upper he,
    mul_le_mul_of_nonneg_right lower (pow_nonneg (by norm_num : (0:ℝ)≤2) (h+1))]

/-- One certified first-frequency mean of 0.0128 in each four late shells suffices. -/
theorem binary_discrepancy_of_four_shells (x : ℝ)
    (good : ∀ᶠ k : ℕ in atTop, ∃ j, k≤j ∧ j<k+4 ∧
      (8/625:ℝ)*2^j≤∑ i∈range (2^j),cosineEscape ((2:ℝ)^(2^j+i)*x)) :
    asymptoticDiscrepancy x ≤ 9999/10000 := by
  have bound := intermittent_dyadic_lower (f:=fun i => cosineEscape ((2:ℝ)^i*x))
    (fun _ => sub_nonneg.mpr (Real.cos_le_one _)) (by norm_num : (0:ℝ)≤8/625) good
  have trans := (first_frequency_bounds x (fun n => (2:ℝ)^n*x) (by simp)).2
  have E : IsCoboundedUnder (· ≥ ·) atTop (escapeAverage (fun i => (2:ℝ)^i*x)) :=
    isCoboundedUnder_ge_of_le _ (fun N => by
      unfold escapeAverage
      by_cases h : N=0
      · simp [h]; exact (show (0:ℝ)≤2 by norm_num)
      · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
        simpa [mul_comm] using sum_le_sum (s:=range N) (fun i _ =>
          show cosineEscape ((2:ℝ)^i*x)≤2 by unfold cosineEscape; linarith [Real.neg_one_le_cos (2*Real.pi*((2:ℝ)^i*x))]))
  have lo := le_liminf_of_le E bound
  apply (sharp_asymptotic_discrepancy x).trans
  apply max_le (by norm_num)
  norm_num at lo
  linarith

end NormalityChecker.Coverage
