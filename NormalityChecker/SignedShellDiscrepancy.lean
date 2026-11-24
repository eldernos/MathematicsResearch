module

public import NormalityChecker.SignedPhases
public import NormalityChecker.SupportDiscrepancy
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Exact interval discrepancy of bounded signed phases, including incomplete shells. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.SignedPhases

/-- Positions outside the zero shells. Position zero precedes the first shell. -/
def regularPositions (p : ℕ) (c : ℕ → ℤ) (N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => n = 0 ∨ c (Nat.log p n) ≠ 0)

/-- The fraction of the first `N` positions in a shell with zero phase. -/
noncomputable def zeroDensity (p : ℕ) (c : ℕ → ℤ) (N : ℕ) : ℝ :=
  ((N : ℝ) - (regularPositions p c N).card) / N

/-- Interval counts on nonzero shells are uniform, with error measured relative to
the full prefix length. The same cutoff works for every interval and partial shell. -/
theorem nonzero_shells_uniform {b p C : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C)
    {ε : ℝ} (pos : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a d : ℝ, 0 ≤ a → a ≤ d → d ≤ 1 →
      let G := regularPositions p c N
      let u := shift b (value b p c)
      |((G.filter (fun n => a ≤ u n ∧ u n < d)).card : ℝ) - G.card*(d-a)| ≤ ε*N := by
  classical
  let x := value b p c
  let P := pre b p c
  obtain ⟨M, K, block⟩ := smooth_interval_block (d:=3)
    (fixed_support_orbit_estimate hb hp.one_lt cop) x P (shifted_tail_tendsto_zero hb hp c cap)
      (half_pos pos)
  obtain ⟨T, hT⟩ := exists_nat_gt (4/ε)
  let k₀ := max 2 (max T (max K (C*M)))
  have ppos := hp.pos
  have p2 : 1 < p^2 := one_lt_pow₀ hp.one_lt (by decide)
  filter_upwards [eventually_ge_atTop ((p^2)^k₀)] with N hN a d ha had hd
  let k := Nat.log (p^2) N
  let B := p^k
  have hk : k₀ ≤ k := Nat.le_log_of_pow_le p2 hN
  have kb : k ≤ B := (Nat.lt_pow_self hp.two_le).le
  have bp : 0 < B := pow_pos ppos k
  have np : 0 < N := (pow_pos (pow_pos ppos _) _).trans_le hN
  have square : B*B ≤ N := by
    calc B*B = (p^2)^k := by dsimp only [B]; rw [← sq, pow_right_comm]
         _ ≤ N := Nat.pow_log_le_self _ np.ne'
  have cube : N ≤ B^3 := by
    have k2 : 2 ≤ k := (le_max_left ..).trans hk
    calc N ≤ (p^2)^(k+1) := (Nat.lt_pow_succ_log_self p2 N).le
         _ ≤ B^3 := by
           dsimp only [B]; rw [← pow_mul, ← pow_mul]
           exact Nat.pow_le_pow_right ppos (by omega)
  let active (n : ℕ) := n = 0 ∨ c (Nat.log p n) ≠ 0
  let f (n : ℕ) := if active n then Localized.centered (shift b x) a d n else 0
  have unit (n : ℕ) : ‖f n‖ ≤ 1 := by
    dsimp [f]; split_ifs <;> simp [Localized.centered_norm _ ha had hd]
  have estimate := charged_prefix_bound f unit (fun _ => 0) (fun _ => le_rfl)
    (N:=N) bp {0} (half_pos pos).le (by
      intro l hl good
      simp only [sum_const_zero, add_zero]
      have lp : 0 < l := Nat.pos_of_ne_zero (by simpa using good)
      let n := l*B
      let j := Nat.log p n
      have bn : B ≤ n := Nat.le_mul_of_pos_left B lp
      have npos := bp.trans_le bn
      have lo : p^j ≤ n := Nat.pow_log_le_self p npos.ne'
      have hi : n < p^(j+1) := Nat.lt_pow_succ_log_self hp.one_lt n
      have kj : k ≤ j := Nat.le_log_of_pow_le hp.one_lt bn
      obtain ⟨t, ht⟩ : B ∣ p^(j+1) := pow_dvd_pow p (by omega)
      have same (i : ℕ) (bi : i < B) : Nat.log p (n+i) = j := by
        apply Nat.log_eq_of_pow_le_of_lt_pow (lo.trans (Nat.le_add_right ..))
        rw [ht, mul_comm B] at hi ⊢
        have lt : l < t := Nat.lt_of_mul_lt_mul_right hi
        calc n+i < (l+1)*B := by dsimp only [n]; rw [Nat.succ_mul]; omega
             _ ≤ t*B := Nat.mul_le_mul_right B lt
      have large : k₀ ≤ n := hk.trans (kb.trans bn)
      by_cases zero : c j = 0
      · have vanish (i : ℕ) (h : i ∈ range B) : f (l*B+i) = 0 := by
          change (if n+i=0 ∨ c (Nat.log p (n+i))≠0 then _ else _) = _
          simp [same i (mem_range.mp h),zero,npos.ne']
        rw [sum_eq_zero vanish]; simp; positivity
      · have surv (i : ℕ) (h : i ∈ range B) :
            f (l*B+i) = Localized.centered (shift b x) a d (n+i) := by
          change (if n+i=0 ∨ c (Nat.log p (n+i))≠0 then _ else _) = _
          simp [same i (mem_range.mp h),zero,n]
        rw [sum_congr rfl surv]
        have minDen : C*M ≤ p^j :=
          (show C*M ≤ k₀ by simp [k₀]).trans (hk.trans (kb.trans (Nat.pow_le_pow_right ppos kj)))
        obtain ⟨low,dv⟩ := denominator_within_nonzero_shell hb hp cop c cap lo hi zero minDen
        have nN := (Nat.mul_le_mul_right B hl.le).trans (Nat.div_mul_le_self N B)
        apply block B n ((show K ≤ k₀ by simp [k₀]).trans large) low ⟨j,dv⟩
          ((Nat.le_of_dvd (pow_pos ppos j) dv).trans (lo.trans (nN.trans cube))) _ _ _ ha had hd
        intro i bi
        simp only [P, pre, ite_eq_right npos.ne', ite_eq_right (show n+i≠0 by omega),same i bi,j,pow_add]
        ring)
  have TB : T ≤ B := (show T ≤ k₀ by simp [k₀]).trans (hk.trans kb)
  have huge := (div_lt_iff₀ pos).mp (hT.trans_le (Nat.cast_le.mpr TB))
  have budget : 2*(B:ℝ) ≤ ε/2*N := by
    have sqr : (B:ℝ)*B ≤ N := by exact_mod_cast square
    nlinarith only [mul_le_mul_of_nonneg_left sqr (half_pos pos).le,
      mul_le_mul_of_nonneg_right huge.le (Nat.cast_nonneg (α:=ℝ) B)]
  simp only [sum_const_zero,add_zero,card_singleton,Nat.cast_one] at estimate
  have total : ‖∑ n∈range N, f n‖ ≤ ε*N := by linarith
  rw [show (∑ n∈range N, f n) = ∑ n∈regularPositions p c N, Localized.centered (shift b x) a d n
    by simp [f,regularPositions,active,sum_filter]] at total
  simpa only [Localized.centered,← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
    sum_sub_distrib,← sum_filter,sum_const,one_mul,nsmul_eq_mul,mul_one,mul_sub] using total

/-- A zero shell eventually avoids every fixed central interval. A negative
remainder can put the fractional part near one. -/
theorem zero_shells_miss_interior {b p C : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C)
    {δ : ℝ} (pos : 0 < δ) (small : δ < 1/2) :
    ∀ᶠ n : ℕ in atTop, c (Nat.log p n) = 0 →
      ¬ (δ ≤ shift b (value b p c) n ∧ shift b (value b p c) n < 1-δ) := by
  filter_upwards [(Metric.tendsto_nhds.mp (shifted_tail_tendsto_zero hb hp c cap)) δ pos,
    eventually_gt_atTop 0] with n near hn zero
  have lo := Nat.pow_log_le_self p hn.ne'
  have hi := Nat.lt_pow_succ_log_self hp.one_lt n
  obtain ⟨z,hz⟩ := phase_within_shell hb hp cop c lo hi
  simp only [zero,Int.cast_zero,mul_zero,zero_div,add_zero] at hz
  simp only [Real.dist_eq,sub_zero,hz,Rat.cast_intCast] at near
  let y := (b:ℝ)^n*value b p c
  change ¬ (δ ≤ Int.fract y ∧ Int.fract y < 1-δ)
  change |y-z| < δ at near
  rw [← Int.fract_sub_intCast y z]
  obtain ⟨lo,hi⟩ := abs_lt.mp near
  by_cases h : 0 ≤ y-z
  · rw [Int.fract_eq_self.mpr ⟨h,by linarith⟩]; grind
  · rw [← Int.fract_add_one,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]; grind

private lemma split_count {N : ℕ} (G : Finset ℕ) (sub : G ⊆ range N)
    (test : ℕ → Prop) [DecidablePred test] :
    ((range N).filter test).card = (G.filter test).card + (((range N \ G).filter test).card) := by
  rw [← card_union_of_disjoint (Finset.disjoint_sdiff.mono (filter_subset ..) (filter_subset ..)),
    ← filter_union,union_sdiff_of_subset sub]

/-- The full sequence of prefix discrepancies tracks the proportion of zero-shell
positions. This also covers cutoffs inside a shell. -/
theorem discrepancy_sub_zeroDensity_tendsto {b p C : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) :
    Tendsto (fun N => radixDiscrepancy b (value b p c) N - zeroDensity p c N) atTop (𝓝 0) := by
  classical
  let x := value b p c
  let u := shift b x
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := min (ε/8) (1/4)
  have dp : 0 < δ := lt_min (by positivity) (by norm_num)
  have ds : δ < 1/2 := (min_le_right ..).trans_lt (by norm_num)
  obtain ⟨K,miss⟩ := eventually_atTop.mp (zero_shells_miss_interior hb hp cop c cap dp ds)
  have eta : 0 < ε/4 := by positivity
  filter_upwards [nonzero_shells_uniform hb hp cop c cap eta,
    (tendsto_const_div_atTop_nhds_zero_nat (K:ℝ)).eventually_lt_const eta,
    eventually_gt_atTop 0] with N unif tiny hN
  let G := regularPositions p c N
  let Z := range N \ G
  have sub : G ⊆ range N := filter_subset ..
  have size : (Z.card : ℝ) + (G.card : ℝ) = N := by
    exact_mod_cast (card_sdiff_add_card_eq_card sub).trans (card_range N)
  have np : (0:ℝ) < N := by exact_mod_cast hN
  have dens : zeroDensity p c N = Z.card/(N:ℝ) := by
    unfold zeroDensity; change (_ - (G.card:ℝ)) / _ = _; congr 1; linarith
  let pred (a d : ℝ) (n : ℕ) := a ≤ u n ∧ u n < d
  have decomp (a d : ℝ) : frequency u a d N =
      ((G.filter (pred a d)).card + ((Z.filter (pred a d)).card : ℝ)) / N := by
    unfold frequency; rw [split_count G sub, Nat.cast_add]
  have bounds (a d : ℝ) (ha : 0 ≤ a) (had : a < d) (hd : d ≤ 1) :
      |frequency u a d N-(d-a)| ≤ Z.card/N + ε/4 := by
    have v := abs_le.mp (unif a d ha had.le hd)
    change -_ ≤ ((G.filter (pred a d)).card:ℝ) - G.card*(d-a) ∧ _ at v
    have up : ((Z.filter (pred a d)).card:ℝ) ≤ Z.card := by exact_mod_cast card_filter_le Z _
    have part : (G.card:ℝ)*(d-a) + Z.card*(d-a) = N*(d-a) := by rw [← add_mul,add_comm,size]
    have wl : 0 ≤ (Z.card:ℝ)*(d-a) := mul_nonneg (by positivity) (by linarith)
    have wh : (Z.card:ℝ)*(d-a) ≤ Z.card := mul_le_of_le_one_right (by positivity) (by linarith)
    rw [decomp,div_sub' np.ne',abs_div,abs_of_pos np,div_le_iff₀ np,add_mul,div_mul_cancel₀ _ np.ne',abs_le]
    constructor <;> linarith only [v.1,v.2,up,wl,wh,part,Nat.cast_nonneg (α:=ℝ) (Z.filter (pred a d)).card]
  have upper : radixDiscrepancy b x N ≤ Z.card/N + ε/4 := by
    unfold radixDiscrepancy
    refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
    rintro _ ⟨a,d,ha,had,hd,rfl⟩
    exact bounds a d ha had hd
  have lowerTest : |frequency u δ (1-δ) N-((1-δ)-δ)| ≤ radixDiscrepancy b x N := by
    unfold radixDiscrepancy
    refine le_csSup ?_ ⟨δ,1-δ,dp.le,by linarith,by linarith,rfl⟩
    refine ⟨1,?_⟩; rintro _ ⟨a,d,ha,had,hd,rfl⟩
    have h := frequency_bounds (shift b x) a d N
    rw [abs_le]; constructor <;> linarith [h.1,h.2]
  have lost : Z.filter (pred δ (1-δ)) ⊆ range K := by
    intro n h; obtain ⟨hn,hit⟩ := mem_filter.mp h
    obtain ⟨nN,ng⟩ := mem_sdiff.mp hn
    have zero : c (Nat.log p n) = 0 := by
      by_contra! ne; exact ng (mem_filter.mpr ⟨nN,Or.inr ne⟩)
    by_contra late
    exact miss n (Nat.le_of_not_gt (fun a => late (mem_range.mpr a))) zero hit
  have lost' : ((Z.filter (pred δ (1-δ))).card:ℝ) ≤ K := by
    exact_mod_cast (card_le_card lost).trans (card_range K).le
  have v := (abs_le.mp (unif δ (1-δ) dp.le (by linarith) (by linarith))).2
  change ((G.filter (pred δ (1-δ))).card:ℝ) - G.card*((1-δ)-δ) ≤ _ at v
  have central := (neg_le_abs (frequency u δ (1-δ) N-((1-δ)-δ))).trans lowerTest
  rw [decomp] at central
  have cen : ((1-δ)-δ)*N - ((G.filter (pred δ (1-δ))).card +
      ((Z.filter (pred δ (1-δ))).card:ℝ)) ≤ radixDiscrepancy b x N*N := by
    apply (div_le_iff₀ np).mp; rw [sub_div,mul_div_cancel_right₀ _ np.ne']; linarith
  have width : 2*δ ≤ ε/4 := by linarith [min_le_left (ε/8) (1/4:ℝ)]
  have cardle : (Z.card:ℝ) ≤ N := by linarith [Nat.cast_nonneg (α:=ℝ) G.card]
  have small := (div_lt_iff₀ np).mp tiny
  have lower : Z.card/N - ε < radixDiscrepancy b x N := by
    rw [sub_lt_iff_lt_add,div_lt_iff₀ np,add_mul]
    nlinarith only [cen,v,lost',small,congrArg (fun t : ℝ => t*((1-δ)-δ)) size,
      mul_le_mul_of_nonneg_right width (Nat.cast_nonneg (α:=ℝ) Z.card),
      mul_le_mul_of_nonneg_left cardle eta.le,mul_pos hε np]
  rw [Real.dist_eq,sub_zero,dens,abs_lt]
  change -ε < radixDiscrepancy b x N - _ ∧ _ < ε
  constructor <;> linarith

private theorem density_bounds (p : ℕ) (c : ℕ → ℤ) (N : ℕ) :
    0 ≤ zeroDensity p c N ∧ zeroDensity p c N ≤ 1 := by
  have h : ((regularPositions p c N).card:ℝ) ≤ N := by
    exact_mod_cast (card_filter_le (range N) _).trans_eq (card_range _)
  unfold zeroDensity
  constructor
  · exact div_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg _)
  · by_cases hn : N = 0
    · simp [hn]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) (regularPositions p c N).card]

/-- Asymptotic interval discrepancy equals the upper density of zero-shell positions. -/
theorem limsup_discrepancy_eq_zeroDensity {b p C : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) :
    limsup (radixDiscrepancy b (value b p c)) atTop = limsup (zeroDensity p c) atTop := by
  let d := radixDiscrepancy b (value b p c)
  let z := zeroDensity p c
  let e := fun n => d n - z n
  have t : Tendsto e atTop (𝓝 0) := discrepancy_sub_zeroDensity_tendsto hb hp cop c cap
  have low := isBoundedUnder_of_eventually_ge (f:=atTop) (.of_forall fun n => (density_bounds p c n).1)
  have high := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall fun n => (density_bounds p c n).2)
  have add : z + e = d := by funext n; dsimp [e]; ring
  have h₁ := limsup_add_le (u:=z) (v:=e) low high t.isBoundedUnder_ge.isCoboundedUnder_le t.isBoundedUnder_le
  have h₂ := le_limsup_add (u:=z) (v:=e) high low.isCoboundedUnder_le t.isBoundedUnder_le t.isBoundedUnder_ge
  rw [add,t.limsup_eq,add_zero] at h₁
  rw [add,t.liminf_eq,add_zero] at h₂
  exact le_antisymm h₁ h₂

private def mass (p : ℕ) (c : ℕ → ℤ) (N : ℕ) : ℕ :=
  ∑ n∈range N, if n = 0 ∨ c (Nat.log p n) ≠ 0 then 0 else 1

private lemma density_eq (p : ℕ) (c : ℕ → ℤ) (N : ℕ) :
    zeroDensity p c N = (mass p c N : ℝ)/N := by
  have h : mass p c N + (regularPositions p c N).card = N := by
    unfold mass regularPositions; rw [card_filter,← sum_add_distrib]
    calc _ = ∑ _ ∈ range N, 1 := sum_congr rfl (fun i _ => by split_ifs <;> decide)
         _ = N := by simp
  unfold zeroDensity
  congr 1; have h' := (Nat.cast_inj (R:=ℝ)).mpr h; push_cast at h'; linarith

private lemma mass_shell {p : ℕ} (hp : 1 < p) (c : ℕ → ℤ) (j N : ℕ)
    (lo : p^j ≤ N) (hi : N ≤ p^(j+1)) :
    mass p c N = mass p c (p^j) + (if c j = 0 then N-p^j else 0) := by
  let t := N-p^j
  have cut : p^j+t = N := Nat.add_sub_of_le lo
  have same (i : ℕ) (h : i ∈ range t) : Nat.log p (p^j+i) = j := by
    apply Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right ..)
    have lt := mem_range.mp h
    omega
  unfold mass
  conv_lhs => rw [← cut,sum_range_add]
  congr 1
  have terms (i : ℕ) (h : i ∈ range t) :
      (if p^j+i=0 ∨ c (Nat.log p (p^j+i))≠0 then 0 else 1 : ℕ) =
        (if c j = 0 then 1 else 0) := by
    rw [same i h]
    by_cases z : c j = 0 <;> simp [z,show p ≠ 0 by omega]
  rw [sum_congr rfl terms]
  by_cases h : c j = 0 <;> simp [h,t]

/-- Integer numerator for the completed zero shells preceding the boundary `p^j`. -/
def boundaryMass (p : ℕ) (c : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | j+1 => boundaryMass p c j + (if c j = 0 then p^(j+1)-p^j else 0)

private theorem mass_boundary {p : ℕ} (hp : 1 < p) (c : ℕ → ℤ) (j : ℕ) :
    mass p c (p^j) = boundaryMass p c j := by
  induction j with
  | zero => simp [mass,boundaryMass]
  | succ j ih =>
    rw [mass_shell hp c j _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)) le_rfl,ih,boundaryMass]

/-- The limiting density at the boundary before shell `r`, for a word repeated
with period `L`. It uses only the first `L` phases when `r < L`. -/
def cycleScore (p L : ℕ) (c : ℕ → ℤ) (r : ℕ) : ℚ :=
  ((boundaryMass p c r:ℚ) + (boundaryMass p c L:ℚ)/((p:ℚ)^L-1)) / (p:ℚ)^r

/-- Largest of the rational boundary scores over one period. -/
def cycleMaximum (p L : ℕ) (c : ℕ → ℤ) : ℚ :=
  (insert 0 ((range L).image (cycleScore p L c))).max' (insert_nonempty ..)

private lemma score_step {p : ℕ} (hp : 1 < p) (L : ℕ) (c : ℕ → ℤ) (j : ℕ) :
    (p:ℚ)*cycleScore p L c (j+1) = cycleScore p L c j + (if c j = 0 then (p:ℚ)-1 else 0) := by
  have pn : (p:ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have le : p^j ≤ p^(j+1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ _)
  unfold cycleScore; rw [boundaryMass]
  split_ifs <;> push_cast [Nat.cast_sub le] <;> rw [pow_succ] <;> field_simp <;> ring

private lemma score_period {p L : ℕ} (hp : 1 < p) (hL : 0 < L)
    (c : ℕ → ℤ) (period : ∀ j, c (j+L) = c j) (j : ℕ) :
    cycleScore p L c (j+L) = cycleScore p L c j := by
  have pp : (1:ℚ) < p := by exact_mod_cast hp
  induction j with
  | zero =>
    simp only [zero_add,cycleScore,boundaryMass,pow_zero,Nat.cast_zero,zero_add,div_one]
    have h := one_lt_pow₀ pp hL.ne'
    field_simp [sub_ne_zero.mpr h.ne',(zero_lt_one.trans h).ne']; ring
  | succ j ih =>
    rw [Nat.succ_add]
    apply mul_left_cancel₀ (zero_lt_one.trans pp).ne'
    rw [score_step hp,score_step hp,ih,period]

private lemma score_at_mod {p L : ℕ} (hp : 1 < p) (hL : 0 < L) (c : ℕ → ℤ)
    (period : ∀ j, c (j+L) = c j) (j : ℕ) :
    cycleScore p L c j = cycleScore p L c (j%L) := by
  have rep (a k : ℕ) : cycleScore p L c (a + k*L) = cycleScore p L c a := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,← Nat.add_assoc,score_period hp hL c period,ih]
  simpa only [Nat.mul_comm (j/L) L,Nat.mod_add_div] using rep (j%L) (j/L)

/-- For a periodic phase sequence the discrepancy is the largest boundary score
of its periodic solution. The rational maximum is executable. -/
theorem periodic_discrepancy {b p L C : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (cop : b.Coprime p)
    (hL : 0 < L) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) (period : ∀ j, c (j+L) = c j) :
    limsup (radixDiscrepancy b (value b p c)) atTop = (cycleMaximum p L c : ℝ) := by
  rw [limsup_discrepancy_eq_zeroDensity hb hp cop c cap]
  let D : ℝ := cycleMaximum p L c
  let z := zeroDensity p c
  let A : ℝ := (boundaryMass p c L:ℝ)/((p:ℝ)^L-1)
  have pr : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have ap : 0 ≤ A := div_nonneg (by positivity) (sub_nonneg.mpr (one_lt_pow₀ pr hL.ne').le)
  have Dpos : 0 ≤ D := by
    dsimp only [D,cycleMaximum]
    exact_mod_cast (le_max' _ (0:ℚ) (mem_insert_self 0 ((range L).image (cycleScore p L c))))
  have identity (j : ℕ) : z (p^j) = (cycleScore p L c j:ℝ) - A/(p:ℝ)^j := by
    rw [show z (p^j) = (mass p c (p^j):ℝ)/(p:ℝ)^j by simpa [z] using density_eq p c (p^j),
      mass_boundary hp.one_lt]
    unfold cycleScore; push_cast; dsimp only [A]; ring
  have edge (j : ℕ) : z (p^j) ≤ D := by
    rw [identity,score_at_mod hp.one_lt hL c period]
    have cap' : (cycleScore p L c (j%L):ℝ) ≤ D := by
      dsimp only [D,cycleMaximum]
      exact_mod_cast le_max' (insert (0:ℚ) ((range L).image (cycleScore p L c))) _ (mem_insert_of_mem (mem_image.mpr
        ⟨j%L,mem_range.mpr (Nat.mod_lt j hL),rfl⟩))
    exact (sub_le_self _ (div_nonneg ap (by positivity))).trans cap'
  have allN (N : ℕ) : z N ≤ D := by
    by_cases hn : N = 0
    · simpa [z,hn,zeroDensity] using Dpos
    by_cases d1 : 1 ≤ D
    · exact (density_bounds p c N).2.trans d1
    let j := Nat.log p N
    have lo : p^j ≤ N := Nat.pow_log_le_self p hn
    have hi : N ≤ p^(j+1) := (Nat.lt_pow_succ_log_self hp.one_lt N).le
    have le := lo.trans hi
    have np : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hn
    change zeroDensity p c N ≤ D
    rw [density_eq,div_le_iff₀ np,mass_shell hp.one_lt c j N lo hi]
    by_cases zero : c j = 0
    · have h := edge (j+1)
      change zeroDensity p c (p^(j+1)) ≤ D at h
      rw [density_eq,div_le_iff₀ (Nat.cast_pos.mpr (pow_pos hp.pos _)),
        mass_shell hp.one_lt c j _ le le_rfl,ite_eq_left zero] at h
      simp only [zero,ite_true,Nat.cast_add,Nat.cast_sub lo,Nat.cast_sub le] at h ⊢
      have hN : (N:ℝ) ≤ (p^(j+1):ℕ) := by exact_mod_cast hi
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr (le_of_not_ge d1)) (sub_nonneg.mpr hN)]
    · have h := edge j
      change zeroDensity p c (p^j) ≤ D at h
      rw [density_eq,div_le_iff₀ (Nat.cast_pos.mpr (pow_pos hp.pos _))] at h
      simp only [zero,ite_false,add_zero]
      exact h.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast lo) Dpos)
  have low := isCoboundedUnder_le_of_le atTop (fun n => (density_bounds p c n).1)
  have high := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall fun n => (density_bounds p c n).2)
  refine le_antisymm (limsup_le_of_le low (.of_forall allN)) ?_
  have mem := max'_mem (insert (0:ℚ) ((range L).image (cycleScore p L c))) (insert_nonempty ..)
  change cycleMaximum p L c ∈ _ at mem
  rcases mem_insert.mp mem with hz | hm
  · have de : D = 0 := by dsimp only [D]; exact_mod_cast hz
    change D ≤ _; rw [de]
    exact le_limsup_of_frequently_le (Eventually.of_forall (fun n => (density_bounds p c n).1)).frequently high
  obtain ⟨r,hr,eq⟩ := mem_image.mp hm
  have score (k : ℕ) : (cycleScore p L c (r+k*L):ℝ) = D := by
    rw [score_at_mod hp.one_lt hL c period,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (mem_range.mp hr)]
    dsimp only [D]; exact_mod_cast eq
  have grow : Tendsto (fun k : ℕ => p^(r+k*L)) atTop atTop := by
    apply (tendsto_pow_atTop_atTop_of_one_lt hp.one_lt).comp
    apply tendsto_atTop_mono _ tendsto_id
    intro k; exact (Nat.le_mul_of_pos_right k hL).trans (Nat.le_add_left ..)
  have vanish := (tendsto_const_div_atTop_nhds_zero_nat A).comp grow
  apply (le_limsup_iff low high).mpr; intro a ha
  apply grow.frequently
  apply Eventually.frequently
  filter_upwards [vanish.eventually_lt_const (sub_pos.mpr ha)] with k small
  change A/((p^(r+k*L):ℕ):ℝ) < D-a at small
  rw [Nat.cast_pow] at small
  change a < z (p^(r+k*L))
  rw [identity,score]; linarith

/-- The three binary signed expansions with phase words 1110, 10 and 100. -/
theorem binary_three_periods :
    let disc (c : ℕ → ℤ) := limsup (radixDiscrepancy 2 (value 2 3 c)) atTop
    disc (fun j => if j%4 = 3 then 0 else 1) = 27/40 ∧
    disc (fun j => if j%2 = 0 then 1 else 0) = 3/4 ∧
    disc (fun j => if j%3 = 0 then 1 else 0) = 12/13 := by
  dsimp only
  have go {L : ℕ} (hL : 0 < L) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ 1)
      (per : ∀ j, c (j+L) = c j) {q : ℚ} (eq : cycleMaximum 3 L c = q) :
      limsup (radixDiscrepancy 2 (value 2 3 c)) atTop = (q:ℝ) := by
    rw [periodic_discrepancy (by decide) (by decide) (by decide) hL c cap per,eq]
  have test {L : ℕ} (hL : 0 < L) (c : ℕ → ℤ) {q : ℚ} (hq : 0 ≤ q)
      (atZero : cycleScore 3 L c 0 = q) (bound : ∀ r<L, cycleScore 3 L c r ≤ q) :
      cycleMaximum 3 L c = q := by
    unfold cycleMaximum
    apply le_antisymm
    · apply max'_le; intro v hv
      rcases mem_insert.mp hv with rfl | h
      · exact hq
      obtain ⟨r,hr,rfl⟩ := mem_image.mp h
      exact bound r (mem_range.mp hr)
    · exact le_max' _ _ (mem_insert_of_mem (mem_image.mpr ⟨0,mem_range.mpr hL,atZero⟩))
  refine ⟨?_,?_,?_⟩
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using go (L:=4) (by decide)
      (fun j => if j%4 = 3 then 0 else 1) (fun j => by split <;> decide)
      (fun j => by simp) (q:=27/40) (test (by decide) _ (by norm_num) (by norm_num [cycleScore,boundaryMass])
        (fun r hr => by interval_cases r <;> norm_num [cycleScore,boundaryMass]))
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using go (L:=2) (by decide)
      (fun j => if j%2 = 0 then 1 else 0) (fun j => by split <;> decide)
      (fun j => by simp) (q:=3/4) (test (by decide) _ (by norm_num) (by norm_num [cycleScore,boundaryMass])
        (fun r hr => by interval_cases r <;> norm_num [cycleScore,boundaryMass]))
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using go (L:=3) (by decide)
      (fun j => if j%3 = 0 then 1 else 0) (fun j => by split <;> decide)
      (fun j => by simp) (q:=12/13) (test (by decide) _ (by norm_num) (by norm_num [cycleScore,boundaryMass])
        (fun r hr => by interval_cases r <;> norm_num [cycleScore,boundaryMass]))

/-- The signed expansion is irrational exactly when infinitely many phases are
nonzero. Uniform visits on the regular shells exclude any rational orbit. -/
theorem irrational_iff_frequently_nonzero {b p C : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) :
    Irrational (value b p c) ↔ ∃ᶠ j in atTop, c j ≠ 0 := by
  classical
  constructor
  · contrapose!
    intro ev
    obtain ⟨J,hJ⟩ := eventually_atTop.mp ev
    intro irrational; apply irrational
    refine ⟨trunc b p c J,?_⟩
    unfold value
    rw [tsum_eq_sum (s:=range (J+1)) (fun i hi => ?_)]
    · simp [trunc]
    · have late : J < i := by simpa using hi
      cases i with
      | zero => omega
      | succ i =>
        have one := hJ i (by omega)
        have two := hJ (i+1) (by omega)
        simp [coeff,jump,one,two]
  · intro often
    rintro ⟨q,hq⟩
    let x := value b p c
    let a : ℝ := 1/(2*q.den)
    have dq : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
    have ap : 0 < a := by dsimp [a]; positivity
    have d : 2*a * q.den = 1 := by dsimp [a]; field_simp
    have d1 : 2*a ≤ 1 := by
      have one : (1:ℝ) ≤ q.den := by exact_mod_cast q.pos
      nlinarith [mul_le_mul_of_nonneg_left one (by positivity : 0 ≤ 2*a)]
    have miss (n : ℕ) : ¬ (a ≤ shift b x n ∧ shift b x n < 2*a) := by
      rintro ⟨lo,hi⟩
      let y := (b:ℝ)^n*(q:ℝ)
      let w : ℤ := (b:ℤ)^n*q.num - ⌊y⌋*q.den
      have grid : (w:ℝ) = shift b x n * q.den := by
        dsimp only [w,shift,x]; rw [← hq,Int.fract]
        push_cast; change _ = (y-⌊y⌋)*q.den
        rw [sub_mul]; congr 1; dsimp only [y]; rw [Rat.cast_def]; field_simp
      have low : (0:ℤ) < w := by
        exact_mod_cast (grid ▸ mul_pos (ap.trans_le lo) dq : (0:ℝ)<w)
      have high : w < (1:ℤ) := by
        exact_mod_cast grid.trans_lt ((mul_lt_mul_of_pos_right hi dq).trans_eq d)
      omega
    obtain ⟨K,uniform⟩ := eventually_atTop.mp (nonzero_shells_uniform hb hp cop c cap
      (show 0 < a/4 by positivity))
    obtain ⟨j,hj,nonzero⟩ := frequently_atTop.mp often K
    let B := p^j
    have bp : 0 < B := pow_pos hp.pos j
    have big : K ≤ 2*B := by have h := (Nat.lt_pow_self hp.two_le (n:=j)).le; dsimp only [B]; omega
    have inside : Ico B (2*B) ⊆ regularPositions p c (2*B) := by
      intro n hn; obtain ⟨lo,hi⟩ := mem_Ico.mp hn
      have endpt : n < p^(j+1) := hi.trans_le (by rw [pow_succ']; exact Nat.mul_le_mul_right B hp.two_le)
      exact mem_filter.mpr ⟨mem_range.mpr hi,Or.inr (by rwa [Nat.log_eq_of_pow_le_of_lt_pow lo endpt])⟩
    have card : B ≤ (regularPositions p c (2*B)).card := by
      simpa [Nat.card_Ico,two_mul] using card_le_card inside
    have h := uniform (2*B) big a (2*a) ap.le (by linarith) d1
    have empty : ((regularPositions p c (2*B)).filter
        (fun n => a ≤ shift b x n ∧ shift b x n < 2*a)) = ∅ :=
      filter_false_of_mem (fun n _ => miss n)
    change |(((_ : Finset ℕ).filter (fun n => a ≤ shift b x n ∧ shift b x n < 2*a)).card:ℝ) - _| ≤ _ at h
    rw [empty,card_empty,Nat.cast_zero,zero_sub,abs_neg,
      abs_of_nonneg (mul_nonneg (by positivity) (by linarith))] at h
    push_cast at h
    nlinarith only [h, mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr card) ap.le,
      mul_pos ap (Nat.cast_pos.mpr bp)]

end NormalityChecker.SignedPhases
