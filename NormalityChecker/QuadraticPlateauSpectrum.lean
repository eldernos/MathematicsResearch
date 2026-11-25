module

public import NormalityChecker.QuadraticPlateauCycle
public import NormalityChecker.PlateauEnvelope
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The exact all-prefix discrepancy and its limsup for a rational quadratic
image of the positive-index dyadic Stoneham number in every odd radix. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.QuadraticOrbit
open CircleDiscrepancy

/-- Use the true lifts on lower halves and the rational prefix on upper halves.
This preserves extreme discrepancy asymptotically, including at cycle atoms. -/
private noncomputable def plateauLift (b D : ℕ) (A B C : ℤ) (n : ℕ) : ℝ :=
  if OnPlateau (shellIndex n) n then (model b A B C n:ℝ)/D
  else (b:ℝ)^n*(value b A B C/D)

private theorem lift_close {b : ℕ} (hb : 2 ≤ b) (D : ℕ) (A B C : ℤ) :
    Tendsto (fun n => (b:ℝ)^n*(value b A B C/D) - plateauLift b D A B C n) atTop (𝓝 0) := by
  have H := (shifted_tail hb A B C).div_const (D:ℝ)
  rw [zero_div] at H
  rw [Metric.tendsto_nhds]; intro ε ep
  filter_upwards [(Metric.tendsto_nhds.mp H) ε ep] with n hn
  unfold plateauLift; split_ifs
  · simpa only [sub_div,mul_div_assoc] using hn
  · simpa using ep

private noncomputable def intervalBias (b D : ℕ) (A B C : ℤ) (a d : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else cycleMass b (clearingShift b D) (plateauSeed b D A B C r) a d - (d-a)

private theorem bias_bound {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) {a d : ℝ} (ha : 0 ≤ a) (had : a < d) (hd' : d ≤ 1) (r : ℕ) :
    |intervalBias b D A B C a d r| ≤ orbitFactor b (plateauSeed b D A B C r) := by
  unfold intervalBias; split_ifs with h
  · simpa using (orbitFactor_bounds b _).1
  · exact cycleMass_error_le hb odd hd A B C nz (by omega) ha had hd'

private theorem profile_counts {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a d : ℝ, 0 ≤ a → a < d → d ≤ 1 →
      let u := plateauLift b D A B C
      let bias := intervalBias b D A B C a d
      |(frequency (fun n => Int.fract (u n)) a d N - (d-a)) -
        (∑ n ∈ range N, plateauProfile bias n)/N| ≤ ε := by
  let δ := ε/12
  have dp : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨_,lower⟩ := rational_good_halves hb odd hd A B C nz δ dp
  obtain ⟨K,cells⟩ := eventually_atTop.mp
    ((lower.and (plateau_counts hb odd hd A B C nz dp)).and (eventually_ge_atTop 1))
  let L := 2*2^K
  have price := (tendsto_const_div_atTop_nhds_zero_nat (2*(L:ℝ))).eventually_le_const (half_pos ep)
  filter_upwards [eventually_ge_atTop L,price,eventually_gt_atTop 0] with N late init pos a d ha had hd'
  let u := plateauLift b D A B C
  let bias := intervalBias b D A B C a d
  let g (n : ℕ) : ℝ := (if a ≤ Int.fract (u n) ∧ Int.fract (u n) < d then 1 else 0) -
    (d-a) - plateauProfile bias n
  have bd (n : ℕ) : |g n| ≤ 2 := by
    have prof : |plateauProfile bias n| ≤ 1 := by
      unfold plateauProfile; split_ifs
      · exact (bias_bound hb odd hd A B C nz ha had hd' _).trans (orbitFactor_bounds b _).2
      · norm_num
    dsimp only [g]; split_ifs <;> rw [abs_le] at * <;> constructor <;> linarith [prof.1,prof.2]
  have H := prefix_of_radix_cells (c:=2) (S:=2) (f:=fun n => (g n:ℂ)) (by decide) (by decide) dp late (by
    intro r hr w hw T ht
    obtain ⟨⟨good,cycle⟩,rp⟩ := cells r hr
    have mem := mem_Ico.mp hw
    by_cases low : w = 2
    · subst w
      have each (i : ℕ) (hi : i ∈ range T) : (g (2*2^r+i):ℂ) =
          Localized.centered (shift b (value b A B C/D)) a d (2*2^r+i) := by
        have it := (mem_range.mp hi).trans_le ht
        have idx := cell_index (Or.inl rfl) it
        have out : ¬ OnPlateau r (2*2^r+i) := by unfold OnPlateau; omega
        simp only [g,u,plateauProfile,plateauLift,idx,out,ite_false,sub_zero,Localized.centered,shift]
        congr! 4
      rw [sum_congr rfl each]
      exact good 2 (Or.inl rfl) T ht a d ha had.le hd'
    · have top : w = 3 := by omega
      subst w
      let y := plateauSeed b D A B C r
      let m := cycleMass b (clearingShift b D) y a d
      have each (i : ℕ) (hi : i ∈ range T) : g (3*2^r+i) =
          (if a ≤ shift b y i ∧ shift b y i < d then 1 else 0)-m := by
        have it := (mem_range.mp hi).trans_le ht
        have idx := cell_index (Or.inr rfl) it
        have hit : OnPlateau r (3*2^r+i) := ⟨by omega,by omega⟩
        have orbit : Int.fract (u (3*2^r+i)) = shift b y i := by
          simp only [u,plateauLift,idx,hit,ite_true,upper_follows (by omega : 0<b) A B C it,
            Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,shift,y,plateauSeed,Rat.cast_div,mul_div_assoc]
        simp only [g,orbit,bias,plateauProfile,idx,hit,ite_true,intervalBias,
          ite_eq_right (by omega : r ≠ 0)]
        dsimp only [m,y]; ring
      rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,sum_congr rfl each,sum_sub_distrib]
      simp only [← sum_filter,sum_const,card_range,nsmul_eq_mul,mul_one]
      exact cycle T ht a d ha had hd')
  have start : |∑ n ∈ range L, g n| ≤ 2*L := (Finset.abs_sum_le_sum_abs ..).trans
    ((sum_le_sum (fun n _ => bd n)).trans_eq (by simp; ring))
  simp only [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs] at H
  change |∑ n ∈ range N, g n| ≤ |∑ n ∈ range L, g n| + _ at H
  have nr : (0:ℝ)<N := by exact_mod_cast pos
  have total : |∑ n ∈ range N, g n| ≤ ε*N := by
    dsimp only [δ] at H
    linarith only [H,start,(div_le_iff₀ nr).mp init]
  simp only [g,sum_sub_distrib,← sum_filter,sum_const,card_range,nsmul_eq_mul,mul_one] at total
  dsimp only
  unfold frequency
  rw [div_sub' nr.ne', ← sub_div,abs_div,abs_of_pos nr,div_le_iff₀ nr]
  simpa only [u,bias,mul_sub,mul_comm (d-a)] using total

/-- At every cutoff the discrepancy of the true irrational orbit differs by
o(1) from the largest included plateau weight times its own eventual cycle
discrepancy. No denominator-growth hypothesis is required. -/
theorem quadratic_all_prefix {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) :
    let F := fun r => orbitFactor b (plateauPoint b D A B C r)
    Tendsto (fun N => radixDiscrepancy b (value b A B C/D) N - plateauEnvelope F N) atTop (𝓝 0) := by
  simp only [plateauPoint,orbitFactor_advance]
  let F := fun r => orbitFactor b (plateauSeed b D A B C r)
  let u := plateauLift b D A B C
  have bd (r : ℕ) : 0 ≤ F r ∧ F r ≤ 1 := orbitFactor_bounds _ _
  have model : Tendsto (fun N => disc u N - plateauEnvelope F N) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]; intro ε ep
    let η := ε/8
    have he : 0 < η := by dsimp [η]; positivity
    have iso := isolated_plateau (q:=upperDen b A B C) (F:=F)
      (ParameterTwoQuadratic.midpoint_window_unique hb odd A B C nz)
      (fun _ => plateau_factor_decay hb odd hd A B C nz) he
    filter_upwards [iso,profile_counts hb odd hd A B C nz he,eventually_gt_atTop 0]
      with N ⟨E,j,jp,cost,recent⟩ approx np
    let s := clearingShift b D
    let y := plateauSeed b D A B C j
    let L := periodLength b s y
    let v (i : ℕ) := (b:ℝ)^(s+i)*y
    have nr : (0:ℝ)<N := by exact_mod_cast np
    have mix := disc_mixture_bound u v N L (plateauWeight_bounds j N).1 (η:=3*η) (by
      intro a d ha had hd'
      let f := intervalBias b D A B C a d
      let P := ∑ n ∈ range N, plateauProfile f n
      have h₁ : |(frequency (fun n => Int.fract (u n)) a d N - (d-a)) - P/N| ≤ η :=
        approx a d ha had hd'
      have h₂ := profile_mass_error (f:=f) (fun i => (bd i).2)
        (bias_bound hb odd hd A B C nz ha had hd') he.le recent
      have err : |P/N - plateauWeight j N*f j| ≤ 2*η := by
        rw [plateauWeight,div_mul_eq_mul_div,← sub_div,abs_div,abs_of_pos nr,div_le_iff₀ nr]
        linarith only [h₂,cost]
      have hj : f j = frequency (fun i => Int.fract (v i)) a d L - (d-a) := by
        simp only [f,intervalBias,ite_eq_right (by omega : j≠0)]; rfl
      rw [← hj]
      exact (abs_sub_le _ (P/N) _).trans ((add_le_add h₁ err).trans_eq (by ring)))
    have fac : F j = disc v L := plateau_orbitFactor hb odd hd A B C nz jp
    rw [← fac] at mix
    have upper := envelope_excess bd he.le np cost recent
    have low := le_plateauEnvelope (fun r => (bd r).2) j N
    rw [Real.dist_eq,sub_zero,abs_lt]
    obtain ⟨l,h⟩ := abs_le.mp mix
    dsimp only [η] at *; constructor <;> linarith
  have transfer := disc_sub_tendsto (lift_close (by omega : 2≤b) D A B C)
  have allN := transfer.add model
  change Tendsto (fun N => disc (fun i => (b:ℝ)^i*(value b A B C/D)) N - plateauEnvelope F N) _ _
  simpa only [u,zero_add,sub_add_sub_cancel] using allN

/-- The exact quarter law for arbitrary rational coefficients of a genuine
quadratic. The factor at each shell uses the actual rational prefix. -/
theorem quadratic_exact_limsup {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) :
    limsup (radixDiscrepancy b (value b A B C/D)) atTop =
      (1/4)*limsup (fun r => orbitFactor b (plateauPoint b D A B C r)) atTop := by
  simp only [plateauPoint,orbitFactor_advance]
  let F := fun r => orbitFactor b (plateauSeed b D A B C r)
  let E := plateauEnvelope F
  let Y := radixDiscrepancy b (value b A B C/D)
  let e := fun n => Y n - E n
  have h : Tendsto e atTop (𝓝 0) := by
    simpa only [plateauPoint,orbitFactor_advance] using quadratic_all_prefix hb odd hd A B C nz
  have bd := plateauEnvelope_bounds (fun r => orbitFactor_bounds b (plateauSeed b D A B C r))
  have lo := isBoundedUnder_of_eventually_ge (f:=atTop) (.of_forall fun r => (bd r).1)
  have hi := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall fun r => (bd r).2)
  have eqn : E+e = Y := by funext n; change E n + (Y n-E n) = Y n; ring
  have up := limsup_add_le (u:=E) (v:=e) lo hi h.isBoundedUnder_ge.isCoboundedUnder_le h.isBoundedUnder_le
  have low := le_limsup_add (u:=E) (v:=e) hi lo.isCoboundedUnder_le h.isBoundedUnder_le h.isBoundedUnder_ge
  rw [eqn,h.limsup_eq,add_zero] at up
  rw [eqn,h.liminf_eq,add_zero] at low
  exact (le_antisymm up low).trans (plateauEnvelope_limsup (fun r => orbitFactor_bounds b _))

end NormalityChecker.QuadraticOrbit
