module

public import NormalityChecker.MaskAxis
public import NormalityChecker.CellProfile

/-! Exact lower densities of first-cell unions, including intermittent masks. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

def Covered (u : ℕ → ℕ) (n : ℕ) := ∃ j, u j≤n ∧ n<2*u j

noncomputable def coveredCount (u : ℕ → ℕ) (N : ℕ) : ℕ := by
  classical exact ((range N).filter (Covered u)).card

noncomputable def coveredShare (u : ℕ → ℕ) (N : ℕ) := (coveredCount u N : ℝ)/N

theorem window_cutoff (u : ℕ → ℕ) (inc : StrictMono u)
    (apart : ∀ i, 2*u i≤u (i+1)) (j N : ℕ) (lo : u j≤N) (hi : N≤u (j+1)) :
    coveredCount u N = coveredCount u (u j) + min (N-u j) (u j) := by
  classical
  have iff (i : ℕ) (h : i<N-u j) : Covered u (u j+i) ↔ i<u j := by
    constructor
    · rintro ⟨k,low,high⟩
      rcases lt_trichotomy k j with lt|rfl|gt
      · have := (apart k).trans (inc.monotone (show k+1≤j by omega)); omega
      · omega
      · have := inc.monotone (show j+1≤k by omega); omega
    · intro v; exact ⟨j,by omega,by omega⟩
  have cnt (n : ℕ) : coveredCount u n = ∑ i∈range n, if Covered u i then (1:ℕ) else 0 := by simp [coveredCount]
  rw [cnt,cnt,show N=u j+(N-u j) by omega,sum_range_add]
  congr 1
  simp only [sum_boole,Nat.cast_id]
  have sets : (range (N-u j)).filter (fun i => Covered u (u j+i)) = range (min (N-u j) (u j)) := by
    ext i; simp only [mem_filter,mem_range,lt_min_iff]; exact and_congr_right (iff i)
  rw [sets,card_range]; omega

theorem window_endpoint_count (u : ℕ → ℕ) (inc : StrictMono u) (apart : ∀ i, 2*u i≤u (i+1))
    (j : ℕ) : coveredCount u (u j) = ∑ i∈range j,u i := by
  classical
  induction j with
  | zero =>
    have empty : (range (u 0)).filter (Covered u)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr; intro i h
      obtain ⟨lt,j,lo,_⟩ := mem_filter.mp h
      have := inc.monotone (Nat.zero_le j); have := mem_range.mp lt; omega
    simp [coveredCount,empty]
  | succ j ih =>
    rw [window_cutoff u inc apart j _ (inc.monotone (Nat.le_succ j)) le_rfl,ih,sum_range_succ]
    change _ + min (u (j+1)-u j) (u j) = _ + u j; have := apart j; omega

private lemma share_bounds (u : ℕ → ℕ) (N : ℕ) : 0≤coveredShare u N ∧ coveredShare u N≤1 := by
  classical
  have cap := card_filter_le (range N) (Covered u)
  rw [card_range] at cap
  by_cases z : N=0
  · simp [coveredShare,z]
  exact ⟨by unfold coveredShare; positivity,(div_le_one (by exact_mod_cast Nat.pos_of_ne_zero z : (0:ℝ)<N)).mpr
    (by exact_mod_cast cap)⟩

/-- The lower density is attained along the left endpoints, for arbitrary gaps.
The ratio there is the sum of all preceding window lengths divided by uⱼ. -/
theorem exact_window_density (u : ℕ → ℕ) (inc : StrictMono u) (positive : 0<u 0)
    (apart : ∀ i, 2*u i≤u (i+1)) :
    liminf (coveredShare u) atTop = liminf (fun j => ((∑ i∈range j,u i : ℕ):ℝ)/u j) atTop := by
  let F := coveredShare u
  have endpt (j : ℕ) : ((∑ i∈range j,u i : ℕ):ℝ)/u j = F (u j) := by rw [← window_endpoint_count u inc apart j]; rfl
  simp_rw [endpt]
  change liminf F atTop = liminf (F ∘ u) atTop
  have nn (n : ℕ) := (share_bounds u n).1
  have cap (n : ℕ) := (share_bounds u n).2
  apply le_antisymm (inc.tendsto_atTop.liminf_le_liminf_comp (isCoboundedUnder_ge_of_le _ cap)
    (isBoundedUnder_of_eventually_ge (.of_forall nn)))
  apply le_of_forall_lt_imp_le_of_dense
  intro z hz
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hz
    (isBoundedUnder_of_eventually_ge (.of_forall (fun j => nn (u j)))))
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le _ cap)
  filter_upwards [eventually_ge_atTop (u K)] with N big
  obtain ⟨j,late,lo,hi⟩ := inc.tendsto_atTop.exists_le_lt_succ big
  have up : (0:ℝ)<u j := by exact_mod_cast positive.trans_le (inc.monotone (Nat.zero_le j))
  have np : (0:ℝ)<N := up.trans_le (by exact_mod_cast lo)
  have next : (0:ℝ)<u (j+1) := up.trans (by exact_mod_cast inc (Nat.lt_succ_self j))
  have lhs := hK j late; have rhs := hK (j+1) (by omega)
  change z<(coveredCount u (u j):ℝ)/u j at lhs
  change z<(coveredCount u (u (j+1)):ℝ)/u (j+1) at rhs
  change z≤(coveredCount u N:ℝ)/N
  rw [le_div_iff₀ np]
  by_cases inside : N≤2*u j
  · rw [window_cutoff u inc apart j N lo hi.le,min_eq_left (by omega),Nat.cast_add,Nat.cast_sub lo]
    have one : z≤1 := lhs.le.trans (cap (u j))
    have h := (lt_div_iff₀ up).mp lhs
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr (by exact_mod_cast lo : (u j:ℝ)≤N))]
  · have h := window_cutoff u inc apart j N lo hi.le
    have e := window_cutoff u inc apart j _ (inc.monotone (Nat.le_succ j)) le_rfl
    rw [min_eq_right (by omega)] at h
    change coveredCount u (u (j+1)) = coveredCount u (u j) + min (u (j+1)-u j) (u j) at e
    rw [min_eq_right (by have := apart j; omega)] at e
    rw [← h] at e; rw [e] at rhs
    by_cases zn : 0≤z
    · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hi.le : (N:ℝ)≤u (j+1)) zn).trans ((lt_div_iff₀ next).mp rhs).le
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge zn) np.le).trans (Nat.cast_nonneg _)

/-- A single retained residue class has exact window density 1/(pʰ-1),
including arbitrary starting exponent. -/
theorem residue_class_density {p h : ℕ} (hp : 1<p) (hh : 0<h) (a : ℕ) :
    liminf (coveredShare (fun j => p^(a+h*j))) atTop = 1/((p:ℝ)^h-1) := by
  let R := p^h
  have rp : 1<R := one_lt_pow₀ hp hh.ne'
  let u (j : ℕ) := p^(a+h*j)
  have step (j : ℕ) : u (j+1)=R*u j := by dsimp [u,R]; rw [Nat.mul_succ,← pow_add]; congr 1; omega
  have pos (j : ℕ) : 0<u j := pow_pos (by omega) _
  have apart (j : ℕ) : 2*u j≤u (j+1) := by rw [step]; exact Nat.mul_le_mul_right _ rp
  have inc : StrictMono u := strictMono_nat_of_lt_succ (fun j => (by have := apart j; have := pos j; omega))
  have exactCount (j : ℕ) : (R-1)*(∑ i∈range j,u i)+u 0=u j := by
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ,Nat.mul_add,step]; have e : R*u j = (R-1)*u j+u j := by rw [← Nat.succ_mul]; congr 1; omega
                   omega
  rw [exact_window_density u inc (pos 0) apart]
  apply Tendsto.liminf_eq
  have zp := (tendsto_const_div_atTop_nhds_zero_nat (u 0:ℝ)).comp inc.tendsto_atTop
  have den : (0:ℝ)<R-1 := sub_pos.mpr (by exact_mod_cast rp)
  have H := (tendsto_const_nhds (x:=(1:ℝ)) |>.sub zp).div_const ((R:ℝ)-1)
  simp only [sub_zero] at H
  change Tendsto _ atTop (𝓝 (1/((p:ℝ)^h-1)))
  rw [← Nat.cast_pow]; apply H.congr; intro j
  have uj : (u j:ℝ)≠0 := by exact_mod_cast (pos j).ne'
  have e : (((R-1:ℕ):ℝ)*(∑ i∈range j,u i : ℕ)+u 0)=(u j:ℝ) := by exact_mod_cast exactCount j
  rw [Nat.cast_sub rp.le,Nat.cast_one] at e
  change (1-(u 0:ℝ)/u j)/((R:ℝ)-1)=_
  field_simp [uj,den.ne']; linarith


/-- Window density for arbitrary retained exponent sequences directly bounds the
discrepancy of the full series, regardless of the other retained indices. -/
theorem discrepancy_of_density {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b) (ht : 0<t)
    (P : ℚ[X]) (p0 : P.eval 0≠0) (S : Finset ℕ) (primes : ∀ q∈S,q.Prime) (mem : p∈S)
    (keep : ℕ → Bool) (u : ℕ → ℕ)
    (retained : ∀ᶠ n : ℕ in atTop, Covered u n → Window p keep n) :
    limsup (radixDiscrepancy b (maskedValue b S keep P t)) atTop ≤ 1-liminf (coveredShare u) atTop := by
  classical
  apply rational_window_bound hb hp off ht p0 S primes mem keep (fun n => decide (¬Covered u n))
    (by simpa using retained)
  intro ε pos
  let g := liminf (coveredShare u) atTop
  filter_upwards [eventually_gt_atTop 0,eventually_lt_of_lt_liminf (show g-ε<g by linarith)
    (isBoundedUnder_of_eventually_ge (.of_forall fun N => (share_bounds u N).1))] with N hn lower
  have sz := card_filter_add_card_filter_not (s:=range N) (Covered u)
  rw [card_range] at sz
  have realSz : (coveredCount u N:ℝ)+(((range N).filter (fun i => ¬Covered u i)).card:ℝ)=N := by exact_mod_cast sz
  change g-ε < (coveredCount u N:ℝ)/N at lower
  simp only [decide_eq_true_eq,sum_boole]
  change _ ≤ (1-g+ε)*N
  linarith [(lt_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<N)).mp lower]

/-- Arbitrarily large jumps between successive retained exponents force lower
window density zero. This applies even if the support on that axis is normal. -/
theorem unbounded_gaps_zero {p : ℕ} (hp : 1<p) (e : ℕ → ℕ) (inc : StrictMono e)
    (gaps : ∀ H K : ℕ, ∃ j≥K, e j+H ≤ e (j+1)) :
    liminf (coveredShare (fun j => p^(e j))) atTop = 0 := by
  let u (j : ℕ) := p^(e j)
  have pos (j : ℕ) : 0<u j := pow_pos (by omega) _
  have mono : StrictMono u := (pow_right_strictMono₀ hp).comp inc
  have apart (j : ℕ) : 2*u j ≤ u (j+1) := by
    calc 2*u j ≤ p*u j := Nat.mul_le_mul_right _ hp
         _ = p^(e j+1) := (pow_succ' ..).symm
         _ ≤ u (j+1) := Nat.pow_le_pow_right (by omega) (inc (Nat.lt_succ_self j))
  refine le_antisymm ?_ (le_liminf_of_le (isCoboundedUnder_ge_of_le _ (fun N => (share_bounds u N).2))
    (.of_forall (fun N => (share_bounds u N).1)))
  apply le_of_forall_pos_le_add; intro ε he
  simp only [zero_add]
  have grow : Tendsto (fun j : ℕ => p^j) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hp
  obtain ⟨H,hH⟩ := (((tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp grow).eventually_lt_const he).exists
  apply liminf_le_of_frequently_le _ (isBoundedUnder_of_eventually_ge (.of_forall fun N => (share_bounds u N).1))
  rw [frequently_atTop]; intro K
  obtain ⟨j,jk,gap⟩ := gaps H K
  refine ⟨u (j+1),jk.trans ((Nat.le_succ j).trans (mono.id_le _)),?_⟩
  have chunk := window_cutoff u mono apart j _ (mono.monotone (Nat.le_succ j)) le_rfl
  have cap : coveredCount u (u j) ≤ u j := by classical exact (card_filter_le _ _).trans_eq (card_range _)
  have lim : coveredCount u (u (j+1)) ≤ 2*u j := by
    change coveredCount u (u (j+1)) = coveredCount u (u j)+min (u (j+1)-u j) (u j) at chunk; omega
  have scales : u j*p^H ≤ u (j+1) := by dsimp [u]; rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) gap
  apply le_trans _ (le_of_lt hH)
  change (coveredCount u (u (j+1)):ℝ)/u (j+1) ≤ 2/((p^H:ℕ):ℝ)
  apply (div_le_div_iff₀ (by exact_mod_cast pos _) (by exact_mod_cast pow_pos (by omega : 0<p) H)).mpr
  exact_mod_cast (Nat.mul_le_mul_right (p^H) lim).trans ((Nat.mul_assoc ..).le.trans (Nat.mul_le_mul_left 2 scales))

end NormalityChecker.PolynomialMasks
