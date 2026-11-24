module

public import NormalityChecker.DeepCancellation
public import NormalityChecker.MaximalSupport
public import NormalityChecker.PartialUniformity

/-! Joint deep cancellation in prime-restricted logarithms. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

/-- At order one a failed full-mesh test removes the selected prime from the
reduced denominator, independently of the other primes and of insertion age. -/
theorem prime_cleared_of_deep_failure {b p n : ℕ} {A : Finset ℕ} (hp : p.Prime)
    (mem : p∈A) (cop : b.Coprime p)
    (fail : n∈failedCells b 1 p (Nat.log p n) (A.erase p)) :
    p.Coprime (shifted b A n).den := by
  let k := Nat.log p n
  have hi := Nat.lt_pow_succ_log_self hp.one_lt n
  have rep := canonical_prefix_residue (order:=1) (by decide) hp (notMem_erase p A) cop
    (ell:=k) le_rfl hi
  change n∈failedCells b 1 p k (A.erase p) at fail
  have zero := (mem_filter.mp fail).2
  simp only [Nat.sub_self,pow_zero,Nat.div_one,zero,insert_erase mem,pow_one] at rep
  obtain ⟨a,d,hd,eqn,congr⟩ := rep
  have da : p^k ∣ a := (pow_dvd_pow p (Nat.le_succ k)).trans
    ((ZMod.natCast_eq_zero_iff ..).mp (by simpa using congr.symm))
  obtain ⟨v,hv⟩ := da
  have cd := (ZMod.isUnit_iff_coprime ..).mp hd
  have dp : d≠0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at cd
    exact (ne_of_gt (one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero k))) cd
  have er : (d:ℚ)*partialSum b A n=v := by
    apply mul_left_cancel₀ (pow_ne_zero k (by exact_mod_cast hp.ne_zero) : (p:ℚ)^k≠0)
    simp only [powerPartial,powerWeight,pow_one] at eqn
    unfold partialSum weight
    rw [hv,Nat.cast_mul,Nat.cast_pow] at eqn
    linear_combination eqn
  have dvd := (reduced_info (x:=shifted b A n) (S:=b^n*v) (Nat.pos_of_ne_zero dp) (by
    dsimp [shifted]; push_cast; linear_combination -(b:ℚ)^n*er)).1
  exact (cd.symm.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero k))).of_dvd_right dvd

private abbrev offBase (b : ℕ) (A : Finset ℕ) := A.filter (fun p => ¬p∣b)

private abbrev jointDeep (b : ℕ) (A : Finset ℕ) (n : ℕ) :=
  ∀ p∈offBase b A,n∈failedCells b 1 p (Nat.log p n) (A.erase p)

private lemma support_divides_radix_product {b : ℕ} {A : Finset ℕ} {p : ℕ} (h : p∈A) :
    p∣b*(∏ q∈offBase b A,q) := by
  by_cases base : p∣b
  · exact base.trans (dvd_mul_right ..)
  · have dvd := dvd_prod_of_mem id (mem_filter.mpr ⟨h,base⟩ : p∈offBase b A)
    exact dvd.trans (dvd_mul_left ..)

private lemma deep_coprime_product {b n : ℕ} {A : Finset ℕ} (primes : ∀ p∈A,p.Prime)
    (fail : jointDeep b A n) : (shifted b A n).den.Coprime (∏ p∈offBase b A,p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  obtain ⟨h,off⟩ := mem_filter.mp hp
  exact (prime_cleared_of_deep_failure (primes p h) h
    ((primes p h).coprime_iff_not_dvd.mpr off).symm (fail p hp)).symm

/-- If every off-radix prime fails on its own full mesh, clearing the radix
factors makes the entire prefix integral. The meshes can have different depths. -/
theorem integral_of_joint_deep_failure {b n D : ℕ} {A : Finset ℕ} (hb : 0<b)
    (primes : ∀ p∈A,p.Prime) (size : n≤2^D) (clean : ∀ m∈indices A n,m+D≤n)
    (fail : ∀ p∈A, ¬p∣b → n∈failedCells b 1 p (Nat.log p n) (A.erase p)) :
    (shifted b A n).den=1 := by
  let J := A.filter (fun p => ¬p∣b)
  let c := ∏ p∈J,p
  have pos : 0<c := prod_pos fun p h => (primes p (mem_filter.mp h).1).pos
  have gcd := deep_coprime_product (b:=b) (n:=n) primes
    (fun p hp => fail p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
  exact Nat.eq_one_of_dvd_coprimes (gcd.pow_right D) dvd_rfl
    (clean_smooth_denominator hb pos (fun _ => support_divides_radix_product) size clean)

private lemma parent_cell {b s p : ℕ} {S : Finset ℕ} (hs : 0<s) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) {l k n : ℕ} (le : l≤k)
    (h : n∈failedCells b s p k S) : n/p^(k-l)∈failedCells b s p l S := by
  induction k,le using Nat.le_induction generalizing n with
  | base => simpa using h
  | succ k hk ih =>
    have par := ih (failed_cell_refines hs hp outside cop h)
    rw [Nat.div_div_eq_div_mul,← pow_succ'] at par
    simpa [show k+1-l=k-l+1 by omega] using par

private lemma quotient_fibres (V U : Finset ℕ) {w : ℕ} (hw : 0<w)
    (cover : ∀ n∈V,n/w∈U) : V.card≤U.card*w := by
  rw [← card_range w,← card_product]
  apply card_le_card_of_injOn (fun n => (n/w,n%w))
    (fun n hn => mem_product.mpr ⟨cover n hn,mem_range.mpr (Nat.mod_lt n hw)⟩)
  intro n _ m _ h
  obtain ⟨a,b⟩ := Prod.mk.inj h
  calc n = w*(n/w)+n%w := (Nat.div_add_mod ..).symm
       _ = w*(m/w)+m%w := by rw [a,b]
       _ = m := Nat.div_add_mod ..

/-- Width of the failed region in the normalized coordinate at precision `l+1`. -/
noncomputable def failedWidth (b s p l : ℕ) (S : Finset ℕ) : ℝ :=
  ((failedCells b s p l S).card:ℝ)/(p:ℝ)^l

private theorem width_antitone {b s p : ℕ} {S : Finset ℕ} (hs : 0<s) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) : Antitone (fun l => failedWidth b s p l S) := by
  apply antitone_nat_of_succ_le
  intro l
  have cnt := quotient_fibres (failedCells b s p (l+1) S) (failedCells b s p l S)
    hp.pos (fun _ => failed_cell_refines hs hp outside cop)
  have pos : (0:ℝ)<p := by exact_mod_cast hp.pos
  unfold failedWidth
  rw [pow_succ,← div_div _ _ (p:ℝ),div_le_iff₀ pos,div_mul_eq_mul_div,div_le_div_iff_of_pos_right (pow_pos pos l)]
  exact_mod_cast cnt

/-- The fixed-test failures missed by the deep test through *any* cutoff have
fraction at most twice the remaining loss of normalized width. -/
theorem fixed_deep_loss_bound {b s p : ℕ} {S : Finset ℕ} (hs : 0<s) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (l N : ℕ) :
    (((range N).filter (fun n => CellProfile.coordinate p (p^l) n∈failedCells b s p l S ∧
      n∉failedCells b s p (Nat.log p n) S)).card:ℝ) ≤
        2*N*(failedWidth b s p l S - ⨅ j, failedWidth b s p j S) := by
  let U := fun k => failedCells b s p k S
  let W := fun k => failedWidth b s p k S
  let gap := W l - ⨅ j,W j
  have pp : (0:ℝ)<p := by exact_mod_cast hp.pos
  have p2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have nonneg (j : ℕ) : 0≤W j := by dsimp [W,failedWidth]; positivity
  have lower (j : ℕ) : (⨅ i,W i)≤W j := ciInf_le ⟨0,by rintro _ ⟨i,rfl⟩; exact nonneg i⟩ j
  have pm : 0<(p:ℝ)-1 := by linarith
  have pos : 0≤gap := sub_nonneg.mpr (lower l)
  let lost (n : ℕ) := CellProfile.coordinate p (p^l) n∈U l ∧ n∉U (Nat.log p n)
  let F (N : ℕ) := ((range N).filter lost).card
  have early : F (p^l)=0 := by
    apply card_eq_zero.mpr; apply eq_empty_iff_forall_notMem.mpr
    intro n h
    obtain ⟨left,hf⟩ := mem_filter.mp h
    have low := (mem_Ico.mp (mem_filter.mp hf.1).1).1
    exact (mem_range.mp left).not_ge (low.trans (Nat.div_le_self ..))
  have scale (k : ℕ) (hk : l≤k) : (F (p^(k+1)):ℝ) ≤ F (p^k)+ (p:ℝ)^k*gap := by
    let shell := Ico (p^k) (p^(k+1))
    let coarse := shell.filter (fun n => CellProfile.coordinate p (p^l) n∈U l)
    have logeq {n : ℕ} (h : n∈shell) : Nat.log p n=k :=
      Nat.log_eq_of_pow_le_of_lt_pow (mem_Ico.mp h).1 (mem_Ico.mp h).2
    have coord {n : ℕ} (h : n∈shell) : CellProfile.coordinate p (p^l) n=n/p^(k-l) := by
      simp [CellProfile.coordinate,Nat.log_div_base_pow,logeq h]
    have sub : U k⊆coarse := by
      intro n hn
      have sh : n∈shell := by simpa [shell,pow_succ'] using (mem_filter.mp hn).1
      exact mem_filter.mpr ⟨sh,coord sh ▸ parent_cell hs hp outside cop hk hn⟩
    have cover : (range (p^(k+1))).filter lost ⊆ (range (p^k)).filter lost ∪ (coarse \ U k) := by
      intro n h
      obtain ⟨hi,bad⟩ := mem_filter.mp h
      by_cases low : n<p^k
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr low,bad⟩)
      · have sh : n∈shell := mem_Ico.mpr ⟨by omega,mem_range.mp hi⟩
        exact mem_union_right _ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨sh,bad.1⟩,logeq sh ▸ bad.2⟩)
    have count := (card_le_card cover).trans (card_union_le ..)
    rw [card_sdiff_of_subset sub] at count
    have upper := quotient_fibres coarse (U l) (pow_pos hp.pos (k-l)) (fun n hn => by
      obtain ⟨sh,inside⟩ := mem_filter.mp hn
      rwa [← coord sh])
    have c : (F (p^(k+1)):ℝ) ≤ F (p^k)+((coarse.card:ℝ)-(U k).card) := by
      exact_mod_cast (by simpa [Nat.cast_sub (card_le_card sub)] using (Nat.cast_le (α:=ℝ)).mpr count :
        (((range (p^(k+1))).filter lost).card:ℝ) ≤ ((range (p^k)).filter lost).card+((coarse.card:ℝ)-(U k).card))
    have width (j : ℕ) : (U j).card=(p:ℝ)^j*W j := by
      dsimp [W,U,failedWidth]; field_simp
    have prod : (p:ℝ)^l * (p:ℝ)^(k-l) = (p:ℝ)^k := by rw [← pow_add]; congr 1; omega
    have up : (coarse.card:ℝ)≤(p:ℝ)^k*W l := by
      calc (coarse.card:ℝ) ≤ (U l).card*(p:ℝ)^(k-l) := by exact_mod_cast upper
           _ = _ := by rw [width,← prod]; ring
    have low := mul_le_mul_of_nonneg_left (lower k) (pow_pos pp k).le
    rw [width] at c; dsimp [gap]; linarith
  have bound (k : ℕ) (hk : l≤k) : (F (p^k):ℝ) ≤ (p:ℝ)^k/((p:ℝ)-1)*gap := by
    induction k,hk using Nat.le_induction with
    | base => rw [early,Nat.cast_zero]; positivity
    | succ k hk ih =>
      refine (scale k hk).trans ?_
      calc _ ≤ (p:ℝ)^k/(p-1)*gap + (p:ℝ)^k*gap := by linarith
           _ = _ := by rw [pow_succ]; field_simp [pm.ne']; ring
  have mono {u v : ℕ} (h : u≤v) : F u≤F v := card_le_card (filter_subset_filter _ (range_mono h))
  change (F N:ℝ) ≤ 2*N*gap
  by_cases small : N≤p^l
  · have z := mono small
    rw [early] at z
    rw [show F N=0 by omega,Nat.cast_zero]; positivity
  · let k := Nat.log p N
    have hk : l≤k := Nat.le_log_of_pow_le hp.one_lt (by omega)
    have hi := mono (Nat.lt_pow_succ_log_self hp.one_lt N).le
    have lo : (p:ℝ)^k≤N := by exact_mod_cast Nat.pow_log_le_self p (by omega : N≠0)
    have factor : (p:ℝ)/(p-1)≤2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    apply ((Nat.cast_le (α:=ℝ)).mpr hi).trans ((bound (k+1) (by omega)).trans ?_)
    rw [pow_succ,mul_div_assoc]; apply mul_le_mul_of_nonneg_right _ pos
    linarith only [mul_le_mul_of_nonneg_left factor (pow_pos pp k).le,lo]

private theorem deep_count_eventually {b : ℕ} (A : Finset ℕ) (hb : 2≤b) (primes : ∀ p∈A,p.Prime)
    {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, (((range N).filter (jointDeep b A)).card:ℝ) ≤
      (limsup (radixDiscrepancy b (value b A)) atTop+ε)*N := by
  classical
  let J := offBase b A
  let c := ∏ p∈J,p
  have cp : 0<c := prod_pos fun p h => (primes p (mem_filter.mp h).1).pos
  let δ := min (ε/3) (1/2)
  have dp : 0<δ := lt_min (by positivity) (by norm_num)
  have small : δ≤1 := (min_le_right ..).trans (by norm_num)
  obtain ⟨K,tail⟩ := eventually_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const dp)
  let x := value b A
  let hit (n : ℕ) := 0≤shift b x n ∧ shift b x n<δ
  let f (_ : Unit) (n : ℕ) : ℂ := if jointDeep b A n then 1 else 0
  let w (n : ℕ) : ℝ := if hit n then 1 else 0
  have transfer := transfer_clean_blocks (c:=c) (s:=1) A hb cp
    (fun _ => support_divides_radix_product) f
    (fun _ _ => by dsimp [f]; split <;> simp) w (fun _ => by dsimp [w]; split <;> norm_num) (by
      intro η hη; refine ⟨K,fun B n hn _ div _ orbit _ => ?_⟩
      obtain ⟨t,ht⟩ := div
      suffices each : ∀ i∈range B, ‖f () (n+i)‖≤w (n+i) by
        exact (norm_sum_le ..).trans ((sum_le_sum each).trans (le_add_of_nonneg_left (by positivity)))
      intro i hi
      by_cases bad : jointDeep b A (n+i)
      · have gcd := deep_coprime_product primes bad
        have dvd := Rat.mul_den_dvd ((b:ℚ)^i) (powerShifted b 1 A n)
        have intden : ((b:ℚ)^i).den=1 := by rw [← Nat.cast_pow]; simp
        rw [← orbit i (mem_range.mp hi),intden,one_mul] at dvd
        have ds : (shifted b A (n+i)).den∣c^t := by
          simpa only [powerShifted,powerPartial,powerWeight,pow_one,shifted,partialSum,weight] using dvd.trans ht
        have integral := Nat.eq_one_of_dvd_coprimes (gcd.pow_right t) dvd_rfl ds
        let z := (shifted b A (n+i)).num
        have eqn : (shifted b A (n+i):ℝ)=(z:ℝ) := by
          have rat := (shifted b A (n+i)).num_div_den.symm
          simp only [integral,Nat.cast_one,div_one] at rat
          exact_mod_cast rat
        obtain ⟨low,up⟩ := shift_error b A hb (n+i)
        rw [eqn] at low up
        have cap := up.trans_lt (tail (n+i) (hn.trans (Nat.le_add_right ..)))
        have inside : hit (n+i) := by
          dsimp [hit,x,shift]; rw [← Int.fract_sub_intCast _ z,Int.fract_eq_self.mpr ⟨low,cap.trans_le small⟩]
          exact ⟨low,cap⟩
        simp only [f,w,ite_eq_left bad,ite_eq_left inside,norm_one,le_refl]
      · simp only [f,w,bad,ite_false,norm_zero]; split <;> norm_num)
  let D := limsup (radixDiscrepancy b x) atTop
  have large := eventually_lt_of_limsup_lt (show D<D+δ by linarith)
    (isBoundedUnder_of_eventually_le (.of_forall fun N => (radix_discrepancy_bounds b x N).2))
  filter_upwards [transfer δ dp,large,eventually_gt_atTop 0] with N hT hD hN
  have h := hT ()
  simp only [f,w,sum_boole,Complex.norm_natCast] at h
  have freq : frequency (shift b x) 0 δ N≤δ+radixDiscrepancy b x N := by
    have le := le_csSup (s:={d | ∃ a c : ℝ, 0≤a ∧ a<c ∧ c≤1 ∧ d=|frequency (shift b x) a c N-(c-a)|})
      (a:=|frequency (shift b x) 0 δ N-(δ-0)|) (show BddAbove _ from ⟨1,by
        rintro _ ⟨a,e,ha,lt,he,rfl⟩; have := frequency_bounds (shift b x) a e N
        rw [abs_le]; constructor <;> linarith [this.1,this.2]⟩) ⟨0,δ,le_rfl,dp,small,rfl⟩
    change _≤radixDiscrepancy b x N at le
    linarith only [(abs_le.mp le).2]
  change (((range N).filter hit).card:ℝ)/N ≤ _ at freq
  have np : (0:ℝ)<N := by exact_mod_cast hN
  have cap := (div_le_iff₀ np).mp freq
  have tiny : δ≤ε/3 := min_le_left ..
  change _ ≤ (D+ε)*N
  nlinarith only [h,cap,mul_le_mul_of_nonneg_right hD.le np.le,mul_le_mul_of_nonneg_right tiny np.le]

/-- Upper ordinary density of simultaneous failures at the common precision `l+1`.
All support primes coprime to the radix participate. -/
noncomputable def jointFailureDensity (b s l : ℕ) (A : Finset ℕ) : ℝ :=
  limsup (fun N : ℕ => (((range N).filter (fun n => ∀ p∈A.filter (fun q => ¬q∣b),
    CellProfile.coordinate p (p^l) n∈failedCells b s p l (A.erase p))).card:ℝ)/N) atTop

/-- For every finite prime support at logarithmic order, the joint certificate
densities converge to the true asymptotic interval discrepancy. -/
theorem joint_density_tendsTo_discrepancy {b : ℕ} (A : Finset ℕ) (hb : 2≤b)
    (primes : ∀ p∈A,p.Prime) :
    Tendsto (fun l => jointFailureDensity b 1 l A) atTop
      (𝓝 (limsup (radixDiscrepancy b (value b A)) atTop)) := by
  classical
  let J := offBase b A
  let D := limsup (radixDiscrepancy b (value b A)) atTop
  let fixed (p l n : ℕ) := CellProfile.coordinate p (p^l) n∈failedCells b 1 p l (A.erase p)
  let F (l N : ℕ) := (range N).filter (fun n => ∀ p∈J,fixed p l n)
  let frac (l N : ℕ) := ((F l N).card:ℝ)/N
  have nonneg (l N : ℕ) : 0≤frac l N := by dsimp [frac]; positivity
  have upper (l N : ℕ) : frac l N≤1 := by
    by_cases z : N=0
    · simp [frac,z]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero z))).mpr
      exact_mod_cast (card_filter_le ..).trans (card_range N).le
  have cop (p : ℕ) (h : p∈J) : b.Coprime p :=
    ((primes p (mem_filter.mp h).1).coprime_iff_not_dvd.mpr (mem_filter.mp h).2).symm
  have lower (l : ℕ) : D≤jointFailureDensity b 1 l A := by
    rcases J.eq_empty_or_nonempty with empty|nonempty
    · have base (p : ℕ) (h : p∈A) : p∣b := by
        by_contra hn
        have mem : p∈J := mem_filter.mpr ⟨h,hn⟩
        simp [empty] at mem
      have eqn : ∀ᶠ N : ℕ in atTop, frac l N=1 := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        simp [frac,F,empty,hN.ne']
      have lim := (tendsto_congr' eqn).mpr (tendsto_const_nhds (x:=(1:ℝ)))
      change D≤limsup (frac l) atTop
      rw [lim.limsup_eq]
      simpa [D,value_one] using (maximal_of_base_primes (s:=1) A hb (by decide) base).le
    · have hd := discrepancy_of_joint_failures (b:=b) (s:=1) A J (fun _ => l) hb
        (by decide) primes nonempty (filter_subset ..) cop (D:=jointFailureDensity b 1 l A)
      rw [value_one] at hd
      apply hd
      intro ε ep
      have ev := eventually_lt_of_limsup_lt (show limsup (frac l) atTop <
        jointFailureDensity b 1 l A+ε from lt_add_of_pos_right _ ep)
        (isBoundedUnder_of_eventually_le (.of_forall (upper l)))
      filter_upwards [ev,eventually_gt_atTop 0] with N h hN
      simpa only [sum_boole,F,fixed] using (div_lt_iff₀ (Nat.cast_pos.mpr hN)).mp h |>.le
  let W (p l : ℕ) := failedWidth b 1 p l (A.erase p)
  let gap (p l : ℕ) := W p l - ⨅ j,W p j
  have shrinking (p : ℕ) (hp : p∈J) : Tendsto (gap p) atTop (𝓝 0) := by
    have decreasing := width_antitone (b:=b) (by decide : 0<1) (primes p (mem_filter.mp hp).1)
      (notMem_erase p A) (cop p hp)
    have bound : BddBelow (Set.range (W p)) := by
      refine ⟨0,?_⟩; rintro _ ⟨j,rfl⟩; dsimp [W,failedWidth]; positivity
    simpa [gap,W] using (tendsto_atTop_ciInf decreasing bound).sub_const (⨅ j,W p j)
  have lim : Tendsto (fun l => ∑ p∈J, gap p l) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum J shrinking
  rw [Metric.tendsto_nhds]
  intro ε ep
  filter_upwards [lim.eventually_lt_const (show 0<ε/4 by positivity)] with l little
  have cap : jointFailureDensity b 1 l A ≤ (D+ε/4)+2*∑ p∈J,gap p l := by
    change limsup (frac l) atTop ≤ _
    apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (nonneg l))
    filter_upwards [deep_count_eventually A hb primes (show 0<ε/4 by positivity),eventually_gt_atTop 0] with N deep hN
    let lost (p : ℕ) := (range N).filter (fun n => fixed p l n ∧ n∉failedCells b 1 p (Nat.log p n) (A.erase p))
    have cover : F l N ⊆ (range N).filter (jointDeep b A) ∪ J.biUnion lost := by
      intro n hn
      obtain ⟨inside,allFixed⟩ := mem_filter.mp hn
      by_cases h : jointDeep b A n
      · exact mem_union_left _ (mem_filter.mpr ⟨inside,h⟩)
      · simp only [jointDeep,not_forall] at h
        obtain ⟨p,hp,fail⟩ := h
        exact mem_union_right _ (mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨inside,allFixed p hp,fail⟩⟩)
    have count := (card_le_card cover).trans ((card_union_le ..).trans
      (Nat.add_le_add_left (card_biUnion_le ..) _))
    have misses : (∑ p∈J, ((lost p).card:ℝ)) ≤ ∑ p∈J,2*N*gap p l := by
      apply sum_le_sum
      intro p hp
      exact fixed_deep_loss_bound (by decide) (primes p (mem_filter.mp hp).1)
        (notMem_erase p A) (cop p hp) l N
    rw [← mul_sum] at misses
    have ct := (Nat.cast_le (α:=ℝ)).mpr count
    push_cast at ct
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    change _ ≤ (D+ε/4)*N at deep
    linarith only [ct,misses,deep]
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (lower l))]
  change _-D<ε; linarith

/-- Digit normality at order one is equivalent to vanishing limiting joint
failure density, including when there are several off-radix primes. -/
theorem normal_iff_joint_density_zero {b : ℕ} (A : Finset ℕ) (hb : 2≤b)
    (primes : ∀ p∈A,p.Prime) : NormalIn b (value b A) ↔
    Tendsto (fun l => jointFailureDensity b 1 l A) atTop (𝓝 0) := by
  have limit := joint_density_tendsTo_discrepancy A hb primes
  refine ⟨fun normal => ?_,fun hz => normal_of_radix_limsup_zero hb (tendsto_nhds_unique limit hz).le⟩
  let D := limsup (radixDiscrepancy b (value b A)) atTop
  have low : 0≤D := le_limsup_of_le
    (isBoundedUnder_of_eventually_le (.of_forall fun N => (radix_discrepancy_bounds b (value b A) N).2))
    (fun z h => by obtain ⟨N,hN⟩ := h.exists; exact (radix_discrepancy_bounds b (value b A) N).1.trans hN)
  suffices high : D≤0 by
    have eqn : limsup (radixDiscrepancy b (value b A)) atTop=0 := le_antisymm high low
    rwa [eqn] at limit
  apply le_of_forall_pos_le_add; intro ε ep
  have grow := tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1<b by omega) : (1:ℝ)<b)
  obtain ⟨k,hk,large⟩ := ((eventually_gt_atTop 0).and (grow.eventually_ge_atTop (2/ε))).exists
  have size : 0<(b:ℝ)^k := by positivity
  have cells := discrepancy_of_fixed_cells (q:=b^k) (b:=b) (x:=value b A) (pow_pos (by omega) k)
    (fun j hj => by simpa only [Nat.cast_pow] using normal.2 k j hk hj)
  rw [Nat.cast_pow] at cells
  exact cells.trans (by rw [zero_add,div_le_iff₀ size]; linarith only [(div_le_iff₀ ep).mp large])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Order two need not clear the selected prime on a deeply failed position,
even when all other support primes divide the base and every insertion is old. -/
theorem order_two_deep_counterexample :
    Nat.log 7 186=2 ∧ 186∈failedCells 36 2 7 2 {2,3} ∧
    (∀ m∈indices {2,3,7} 186,m+16≤186) ∧
    (powerShifted 36 2 {2,3,7} 186).den=7 := by decide +kernel

end NormalityChecker.LocalizedSupport
