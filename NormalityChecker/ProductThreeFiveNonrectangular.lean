module

public import NormalityChecker.ProductThreeFiveRectangleValuation
public import NormalityChecker.ProductThreeFiveCoverage
import all NormalityChecker.ProductThreeFiveCoverage

/-! Binary discrepancy from simultaneous top failures outside full rectangles. -/

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ProductThreeFive

/-- A position costs one precisely when its rectangle is incomplete and both
endpoint tests fail. -/
def nonrectangularCost (n : ℕ) : ℕ :=
  if 3^Nat.log 3 n + 5^Nat.log 5 n ≤ n then 0 else jointCost n

private lemma cost_den {n M : ℕ} (late : 5^(2*M+2) ≤ n) (good : nonrectangularCost n=0) :
    M ≤ (pre n).den := by
  unfold nonrectangularCost at good
  split at good
  · exact (Nat.lt_pow_self (by decide : 1<3)).le.trans
      (Nat.le_of_dvd (pre n).pos (rectangle_denominator_growth late ‹_›))
  · exact good_den ((Nat.pow_le_pow_right (by decide : 0<5) (by omega : M+1≤2*M+2)).trans late) good

/-- At every sufficiently late ordinary cutoff, the true binary interval
discrepancy is at most the frequency of nonrectangular joint failures plus ε. -/
theorem nonrectangular_prefix_discrepancy {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, radixDiscrepancy 2 (alpha 3 * alpha 5) N ≤
      (∑ n ∈ range N, (nonrectangularCost n:ℝ))/N + ε := by
  obtain ⟨M,K,block⟩ := smooth_interval_block (b:=2) (c:=15) (d:=6)
    (fixed_support_orbit_estimate (by decide) (by decide) (by decide))
    (alpha 3*alpha 5) pre (by simpa only [Nat.cast_ofNat] using shifted_tail)
    (show 0<ε/2 by positivity)
  have err := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)).const_mul 18
  simp only [mul_zero] at err
  obtain ⟨k₀,threshold⟩ := eventually_atTop.mp ((eventually_ge_atTop 1).and
    (((tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<2)).eventually_ge_atTop
      (max (max K (5^(2*M+2))) 4)).and (err.eventually_le_const (show 0<ε/2 by positivity))))
  filter_upwards [eventually_ge_atTop (4^k₀)] with N hN
  let k := Nat.log 4 N
  let B := 2^k
  have pos : 0<N := (pow_pos (by decide : 0<4) _).trans_le hN
  obtain ⟨hk,large,small⟩ := threshold k (Nat.le_log_of_pow_le (by decide) hN)
  have sq : 4^k=B*B := by dsimp [B]; rw [← mul_pow]; rfl
  have bot : B*B≤N := sq ▸ Nat.pow_log_le_self 4 pos.ne'
  have top : N<4^(k+1) := Nat.lt_pow_succ_log_self (by decide) _
  have upper : N ≤ 4*(B*B) := by simpa only [pow_succ',sq] using top.le
  have bp : 0<B := pow_pos (by decide) _
  have spend : ((exceptions N B).card+1:ℝ)*B ≤ ε/2*N := by
    have exc : ((exceptions N B).card+1:ℝ) ≤ 18*(k:ℝ)^2 := by
      exact_mod_cast exception_count (B:=B) hk top pos.ne'
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at small
    have ss : 18*(k:ℝ)^2 ≤ ε/2*(B:ℝ) := by simpa [B] using small
    have nn : (B:ℝ)*B ≤ N := by exact_mod_cast bot
    nlinarith only [mul_le_mul_of_nonneg_right (exc.trans ss) (Nat.cast_nonneg B),
      mul_le_mul_of_nonneg_left nn (by positivity : 0≤ε/2)]
  unfold radixDiscrepancy
  refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
  rintro _ ⟨a,c,ha,ac,hc,rfl⟩
  let f := Localized.centered (shift 2 (alpha 3*alpha 5)) a c
  have unit := Localized.centered_norm (shift 2 (alpha 3*alpha 5)) ha ac.le hc
  have H := charged_prefix_bound f unit (fun n => (nonrectangularCost n:ℝ))
    (fun _ => Nat.cast_nonneg _) bp (exceptions N B) (show 0≤ε/2 by positivity) (by
      intro l hl free
      have ne : l≠0 := fun h => free (h ▸ mem_insert_self ..)
      have lo := Nat.le_mul_of_pos_left B (Nat.pos_of_ne_zero ne)
      have endpt := (Nat.le_div_iff_mul_le bp).mp hl
      have den := prefix_denominator (n:=l*B) (bp.trans_le lo)
      have orb := clean bp hl free
      by_cases good : ∃ i<B, nonrectangularCost (l*B+i)=0
      · obtain ⟨i,hi,ok⟩ := good
        have survives := cost_den (M:=M) (by omega) ok
        have dv := Rat.mul_den_dvd ((2:ℚ)^i) (pre (l*B))
        have integral : ((2:ℚ)^i).den=1 := by exact_mod_cast Rat.den_natCast (2^i)
        rw [← orb i hi,integral,one_mul] at dv
        have high : (pre (l*B)).den ≤ B^6 := calc
          _ ≤ (l*B)^2 := den.2
          _ ≤ (B^3)^2 := Nat.pow_le_pow_left (by
            calc l*B ≤ (l+1)*B := Nat.mul_le_mul_right _ (by omega)
                 _ ≤ 4*(B*B) := endpt.trans upper
                 _ ≤ B*(B*B) := Nat.mul_le_mul_right _ (by omega)
                 _ = B^3 := by ring) _
          _ = B^6 := by ring
        apply (block B (l*B) (by omega) (survives.trans (Nat.le_of_dvd (pre _).pos dv))
          den.1 high orb a c ha ac.le hc).trans
        exact le_add_of_nonneg_right (sum_nonneg fun _ _ => Nat.cast_nonneg _)
      · have ones (i : ℕ) (hi : i ∈ range B) : (nonrectangularCost (l*B+i):ℝ)=1 := by
          have h : nonrectangularCost (l*B+i)≠0 := fun e => good ⟨i,mem_range.mp hi,e⟩
          unfold nonrectangularCost jointCost columnCost at *
          split_ifs at * <;> simp_all
        rw [sum_congr rfl ones]
        apply (norm_sum_le ..).trans
        apply (sum_le_sum (s:=range B) fun i _ => unit (l*B+i)).trans
        simp [show 0 ≤ ε/2*(B:ℝ) by positivity])
  dsimp only [f] at H
  have centered := Localized.centered_sum (shift 2 (alpha 3*alpha 5)) a c 0 N
  simp only [Nat.zero_add] at centered
  rw [centered] at H
  change |(IntervalFourier.count _ _ _ N:ℝ)/N-(c-a)| ≤ _
  have nr : (0:ℝ)<N := by exact_mod_cast pos
  rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_iff₀ nr,add_mul,div_mul_cancel₀ _ nr.ne']
  change |(IntervalFourier.count _ _ _ N:ℝ)-N*(c-a)| ≤ _ at H
  linarith only [H,spend]

end NormalityChecker.ProductThreeFive
