module

public import NormalityChecker.AlternateBaseCoverage
public import NormalityChecker.AlternateBaseDilation
public import NormalityChecker.Concentration

/-! Integer concentration on geometric windows in an alternate radix. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.AlternateBase

/-- A signed approximation is allowed. Both ends of the unit interval represent zero. -/
def IntegerWindows (B c : ℕ) (x l h : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, l*(c:ℝ)^k ≤ n → (n:ℝ)<h*c^k →
    ∃ z : ℤ, |(B:ℝ)^n*x-z| < ε

theorem not_normal_of_integerWindows {B c : ℕ} {x l h : ℝ} (hc : 1<c) (hl : 0<l)
    (lh : l<h) (w : IntegerWindows B c x l h) : ¬NormalIn B x := by
  classical
  let t := min h (c*l)
  have cp : (1:ℝ)<c := by exact_mod_cast hc
  have lt : l<t := lt_min lh (by simpa using mul_lt_mul_of_pos_right cp hl)
  let s := (t-l)/(((c:ℝ)-1)*l)
  have sp : 0<s := div_pos (sub_pos.mpr lt) (mul_pos (sub_pos.mpr cp) hl)
  apply not_normal_of_concentration (C:={0}) (η:=s/2) (half_pos sp)
  intro ε pos
  let p (n : ℕ) := nearResidues {0} ε ((B:ℝ)^n*x)
  have cert : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, l*(c:ℝ)^k ≤ n → (n:ℝ)<t*c^k → p n := by
    filter_upwards [w ε pos] with k hk n lo up
    obtain ⟨z,hz⟩ := hk n lo (up.trans_le (mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity)))
    exact ⟨0,by simp,z,by simpa using hz⟩
  have freq := (geometric_window_shares hc hl lt (min_le_right ..) p cert).1 (s/2) (half_pos sp)
  apply Eventually.frequently
  filter_upwards [freq] with N enough
  change s-s/2 ≤ _ at enough
  change s/2 ≤ (((range N).filter p).card:ℝ)/N
  linarith

/-- The entire union of windows contributes. Integer dilation pulls an interval
back to D disjoint intervals, costing at most the factor D in discrepancy. -/
theorem discrepancy_of_grid_windows {B c D : ℕ} {x l h : ℝ} (hc : 1<c) (hd : 0<D)
    (hl : 0<l) (lh : l<h) (sep : h≤c*l) (w : IntegerWindows B c (D*x) l h) :
    (h-l)/(((c:ℝ)-1)*l)/D ≤ liminf (radixDiscrepancy B x) atTop ∧
    ((c:ℝ)*(h-l)/(((c:ℝ)-1)*h))/D ≤ limsup (radixDiscrepancy B x) atTop := by
  classical
  let du := (h-l)/(((c:ℝ)-1)*l)
  let dv := (c:ℝ)*(h-l)/(((c:ℝ)-1)*h)
  have dp : (0:ℝ)<D := by exact_mod_cast hd
  suffices bounds : ∀ ε : ℝ, 0<ε →
      (∀ᶠ N : ℕ in atTop, du/D-ε ≤ radixDiscrepancy B x N) ∧
      (∃ᶠ N : ℕ in atTop, dv/D-ε ≤ radixDiscrepancy B x N) by
    constructor <;> apply le_of_forall_pos_le_add <;> intro ε pos
    · have h := le_liminf_of_le (isCoboundedUnder_ge_of_le _ fun N => (radix_discrepancy_bounds B x N).2)
          (bounds ε pos).1
      linarith
    · have h := le_limsup_of_frequently_le (bounds ε pos).2
          (isBoundedUnder_of_eventually_le (.of_forall fun N => (radix_discrepancy_bounds B x N).2))
      linarith
  intro ε ep
  let y := (D:ℝ)*x
  let δ := min (ε*D/4) (1/4)
  have pos : 0<δ := lt_min (by positivity) (by norm_num)
  have ds : δ≤1/4 := min_le_right ..
  have de : δ≤ε*D/4 := min_le_left ..
  let outside (n : ℕ) := ¬(δ≤shift B y n ∧ shift B y n<1-δ)
  have cert : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, l*(c:ℝ)^k ≤ n → (n:ℝ)<h*c^k → outside n := by
    filter_upwards [w δ pos] with k hk n lo up
    obtain ⟨z,hz⟩ := hk n lo up
    change |(B:ℝ)^n*y-z| < δ at hz
    rintro ⟨a,b⟩
    simp only [shift,Int.fract] at a b
    have t := abs_lt.mp hz
    have bad : (0:ℝ)<z-⌊(B:ℝ)^n*y⌋ ∧ (z:ℝ)-⌊(B:ℝ)^n*y⌋<1 := by
      constructor <;> linarith [t.1,t.2]
    have : (0:ℤ)<z-⌊(B:ℝ)^n*y⌋ ∧ z-⌊(B:ℝ)^n*y⌋<1 := by exact_mod_cast bad
    omega
  have shares := geometric_window_shares hc hl lh sep outside cert
  have bound (N : ℕ) (hn : 0<N) (s : ℝ)
      (enough : s-ε*D/2 ≤ (((range N).filter outside).card:ℝ)/N) :
      s/D-ε ≤ radixDiscrepancy B x N := by
    have np : (0:ℝ)<N := by exact_mod_cast hn
    have tot := card_filter_add_card_filter_not (s:=range N) (fun n => δ≤shift B y n ∧ shift B y n<1-δ)
    rw [card_range] at tot
    have freq : frequency (shift B y) δ (1-δ) N + (((range N).filter outside).card:ℝ)/N = 1 := by
      rw [frequency,← add_div,div_eq_iff np.ne',one_mul]; exact_mod_cast tot
    have I := (abs_le.mp (PolynomialMasks.interval_le_radix (b:=B) (N:=N) y pos.le
      (by linarith : δ<1-δ) (by linarith))).1
    have dil := discrepancy_dilation hd B x N
    change radixDiscrepancy B y N ≤ _ at dil
    rw [sub_le_iff_le_add,div_le_iff₀ dp]
    linarith only [enough,freq,I,dil,de,
      show (radixDiscrepancy B x N+ε)*D=D*radixDiscrepancy B x N+ε*D by ring]
  constructor
  · filter_upwards [shares.1 (ε*D/2) (by positivity), eventually_gt_atTop 0] with N enough hn
    exact bound N hn du enough
  · exact ((shares.2 (ε*D/2) (by positivity)).and_eventually (eventually_gt_atTop 0)).mono
      (fun N ⟨enough,hn⟩ => bound N hn dv enough)

end NormalityChecker.AlternateBase
