module

public import NormalityChecker.ProductThreeFiveResidues
public import NormalityChecker.ProductThreeFiveCount
public import NormalityChecker.ProductThreeFiveStatements

/-! Binary discrepancy from all surviving quinary-column intervals. -/
@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker.ProductThreeFive

private lemma good_den {n M : ℕ} (hn : 5^(M+1) ≤ n) (good : columnCost n = 0) :
    M ≤ (pre n).den := by
  have le := Nat.le_log_of_pow_le (by decide : 1<5) hn
  obtain ⟨l,hl⟩ : ∃ l, l+1=Nat.log 5 n := ⟨Nat.log 5 n-1,by omega⟩
  have dv := (quinary_survival_iff hl).mpr (by
    dsimp only [columnCost] at good
    rw [hl]; split_ifs at good
    simp_all)
  exact (by omega : M≤l+1).trans
    ((Nat.lt_pow_self (by decide : 1<5)).le.trans (Nat.le_of_dvd (pre n).pos dv))

private def exceptions (N B : ℕ) := insert 0 ((active N).image (fun v => location v/B))

private lemma exception_count {N k B : ℕ} (hk : 1 ≤ k) (hi : N<4^(k+1)) (hn : N≠0) :
    (exceptions N B).card+1 ≤ 18*k^2 := by
  have h₂ := Nat.log_lt_of_lt_pow hn (by simpa only [pow_mul,show (2:ℕ)^2=4 by decide] using hi : N<2^(2*(k+1)))
  have h₃ := (Nat.log_anti_left (n:=N) (by decide : 1<2) (by decide : 2≤3)).trans h₂.le
  have h₅ := (Nat.log_anti_left (n:=N) (by decide : 1<2) (by decide : 2≤5)).trans h₂.le
  have h := card_insert_le 0 ((active N).image (fun v => location v/B))
  have cap := (card_image_le (s:=active N) (f:=fun v => location v/B)).trans
    (card_filter_le _ _)
  simp only [card_product,card_range] at cap
  have lim := Nat.mul_le_mul h₃ h₅
  have big := Nat.mul_le_mul (by omega : 2*(k+1)≤4*k) (by omega : 2*(k+1)≤4*k)
  dsimp only [exceptions]
  nlinarith [Nat.one_le_pow 2 k hk]

private lemma clean {N B l : ℕ} (bp : 0<B) (hl : l<N/B) (free : l∉exceptions N B) :
    ∀ i<B, pre (l*B+i) = (2:ℚ)^i*pre (l*B) := by
  intro i hi
  apply follows
  intro v newer
  by_contra! le
  have stop := (Nat.le_div_iff_mul_le bp).mp hl
  have lt : location v < (l+1)*B := by rw [Nat.add_mul,one_mul]; omega
  have ev : v∈active N := mem_active.mpr (lt.le.trans stop)
  have eqn : location v/B=l := Nat.div_eq_of_lt_le (by simpa [mul_comm] using newer.le)
    (by simpa [mul_comm] using lt)
  exact free (mem_insert_of_mem (mem_image.mpr ⟨v,ev,eqn⟩))

private lemma local_bound {ε : ℝ} {M K N B l : ℕ} (ep : 0<ε)
    (block : ∀ T n : ℕ, K≤n → M≤(pre n).den → (∃ t : ℕ, (pre n).den∣15^t) →
        (pre n).den≤T^6 → (∀ i<T,pre (n+i)=(2:ℚ)^i*pre n) →
        ∀ a c : ℝ, 0≤a → a≤c → c≤1 →
        ‖∑ i∈range T,Localized.centered (shift 2 (alpha 3*alpha 5)) a c (n+i)‖ ≤ ε*T)
    (large : max (max K (5^(M+1))) 4 ≤ B) (upper : N ≤ 4*(B*B))
    (hl : l<N/B) (free : l∉exceptions N B) {a c : ℝ} (ha : 0≤a) (ac : a≤c) (hc : c≤1) :
    ‖∑ i∈range B, Localized.centered (shift 2 (alpha 3*alpha 5)) a c (l*B+i)‖ ≤
      ε*B + ∑ i∈range B,(columnCost (l*B+i):ℝ) := by
  have bp : 0<B := by omega
  have ne : l≠0 := fun h => free (h ▸ mem_insert_self ..)
  have lo := Nat.le_mul_of_pos_left B (Nat.pos_of_ne_zero ne)
  have endpt := (Nat.le_div_iff_mul_le bp).mp hl
  have den := prefix_denominator (n:=l*B) (bp.trans_le lo)
  have orb := clean bp hl free
  by_cases some : ∃ i<B, columnCost (l*B+i)=0
  · obtain ⟨i,hi,ok⟩ := some
    have survives := good_den (M:=M) (by omega) ok
    have dv := Rat.mul_den_dvd ((2:ℚ)^i) (pre (l*B))
    have integral : ((2:ℚ)^i).den = 1 := by exact_mod_cast Rat.den_natCast (2^i)
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
      den.1 high orb a c ha ac hc).trans
    exact le_add_of_nonneg_right (sum_nonneg fun _ _ => Nat.cast_nonneg _)
  · have allOne (i : ℕ) (hi : i∈range B) : (columnCost (l*B+i):ℝ)=1 := by
      have H : columnCost (l*B+i) ≠ 0 := fun h => some ⟨i,mem_range.mp hi,h⟩
      unfold columnCost at *
      split_ifs at * <;> simp_all
    rw [sum_congr rfl allOne]
    have h := (norm_sum_le ..).trans (sum_le_sum (s:=range B) (fun i _ =>
      Localized.centered_norm (shift 2 (alpha 3*alpha 5)) ha ac hc (l*B+i)))
    simpa using h.trans (by simpa using (le_add_of_nonneg_left (mul_nonneg ep.le (Nat.cast_nonneg (α:=ℝ) B)) :
      (B:ℝ)≤ε*B+B))

/-- Counting every surviving top column gives binary discrepancy at most 27/40.
The chosen intervals vary with both exponents and the final cutoff. -/
theorem column_discrepancy : asymptoticDiscrepancy (alpha 3 * alpha 5) ≤ 27/40 := by
  apply le_of_forall_pos_le_add
  intro ε ep
  obtain ⟨M,K,block⟩ := smooth_interval_block (b:=2) (c:=15) (d:=6)
    (fixed_support_orbit_estimate (by decide) (by decide) (by decide))
    (alpha 3*alpha 5) pre (by simpa only [Nat.cast_ofNat] using shifted_tail)
    (show 0<ε/2 by positivity)
  have err := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)).const_mul 24
  simp only [mul_zero] at err
  obtain ⟨k₀,threshold⟩ := eventually_atTop.mp ((eventually_ge_atTop 1).and
    (((tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<2)).eventually_ge_atTop
      (max (max K (5^(M+1))) 4)).and (err.eventually_le_const (show 0<ε/2 by positivity))))
  apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds 2 _ N).1))
  filter_upwards [eventually_ge_atTop (4^k₀)] with N hN
  let k := Nat.log 4 N
  let B := 2^k
  have pos : 0<N := (pow_pos (by decide : 0<4) _).trans_le hN
  obtain ⟨hk,large,small⟩ := threshold k (Nat.le_log_of_pow_le (by decide) hN)
  have sq : 4^k=B*B := by dsimp [B]; rw [← mul_pow]; rfl
  have bot : B*B≤N := sq ▸ Nat.pow_log_le_self 4 pos.ne'
  have top : N<4^(k+1) := Nat.lt_pow_succ_log_self (by decide) _
  have upper : N ≤ 4*(B*B) := by simpa only [pow_succ',sq] using top.le
  have exc := exception_count (B:=B) hk top pos.ne'
  have logle : Nat.log 5 N ≤ k := Nat.log_anti_left (by decide) (by decide : 4≤5)
  have rem : 39*Nat.log 5 N+52 ≤ 120*k^2 := by nlinarith [Nat.one_le_pow 2 k hk]
  have bp : 0<B := pow_pos (by decide) _
  have bk : (1:ℝ)≤B := by exact_mod_cast bp
  have spend : ((exceptions N B).card+1:ℝ)*B + (39*(Nat.log 5 N:ℝ)+52)/40 ≤ ε/2*N := by
    have er : ((exceptions N B).card+1:ℝ) ≤ 18*(k:ℝ)^2 := by exact_mod_cast exc
    have rr : 39*(Nat.log 5 N:ℝ)+52 ≤ 120*(k:ℝ)^2 := by exact_mod_cast rem
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at small
    have ss : 24*(k:ℝ)^2 ≤ ε/2*(B:ℝ) := by simpa [B] using small
    have nn : (B:ℝ)*B ≤ N := by exact_mod_cast bot
    nlinarith only [mul_le_mul_of_nonneg_right er (Nat.cast_nonneg B),
      rr,mul_le_mul_of_nonneg_right ss (by positivity : (0:ℝ)≤B),
      mul_le_mul_of_nonneg_left nn (by positivity : 0≤ε/2),
      mul_le_mul_of_nonneg_left bk (sq_nonneg (k:ℝ))]
  unfold radixDiscrepancy
  refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
  rintro _ ⟨a,c,ha,ac,hc,rfl⟩
  have H := charged_prefix_bound (Localized.centered (shift 2 (alpha 3*alpha 5)) a c)
    (Localized.centered_norm _ ha ac.le hc) (fun n => (columnCost n:ℝ)) (fun _ => Nat.cast_nonneg _)
    bp (exceptions N B) (show 0≤ε/2 by positivity)
    (fun l hl free => local_bound (by positivity) block large upper hl free ha ac.le hc)
  have count : 40*(∑ n ∈ range N,(columnCost n:ℝ)) ≤ 27*N+39*(Nat.log 5 N:ℝ)+52 := by
    exact_mod_cast column_cost_bound N
  have centered := Localized.centered_sum (shift 2 (alpha 3*alpha 5)) a c 0 N
  simp only [Nat.zero_add] at centered
  rw [centered] at H
  change |(IntervalFourier.count _ _ _ N:ℝ)/N-(c-a)| ≤ _
  have nr : (0:ℝ)<N := by exact_mod_cast pos
  rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_iff₀ nr]
  change |(IntervalFourier.count _ _ _ N:ℝ)-N*(c-a)| ≤ _ at H
  linarith only [H,spend,count]

/-- The strengthened bound stated solely in terms of the two defining series. -/
theorem independent_product_discrepancy : StonehamStatements.IndependentProductDiscrepancy :=
  column_discrepancy

end NormalityChecker.ProductThreeFive
