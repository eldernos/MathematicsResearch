module

public import NormalityChecker.ShadowCancellations

/-! The prime weight lost by the diagonal logarithmic models, averaged over their index. -/
@[expose] public section
open Finset Real Filter
open scoped Topology
namespace NormalityChecker.ShadowCancellations

/-- Primes in the diagonal test range that cancel at a single index. -/
def missing (n : ℕ) := (2*n).primesLE.filter (fun p => n<p ∧ ¬p∣(logShadow n n).den)
noncomputable def lostWeight (n : ℕ) := ∑ p∈missing n,Real.log p

private lemma mem_missing {p n : ℕ} : p∈missing n ↔ p.Prime ∧ n<p ∧ p≤2*n ∧ ¬p∣(logShadow n n).den := by
  simp only [missing,mem_filter,Nat.mem_primesLE]; tauto
lemma nonneg_weight (n : ℕ) : 0≤lostWeight n := sum_nonneg (fun p h => Real.log_nonneg (by exact_mod_cast (mem_missing.mp h).1.one_le))

/-- Double counting prime failures on an arbitrary interval uses its length in the spacing bound. -/
theorem window_lost_weight (A T H : ℕ) :
    ∑ n∈Ico A (A+T),lostWeight n ≤ Chebyshev.theta (2*(A+T):ℕ) * ((T:ℝ)/(H+1)+1+H^2+2*H+4) := by
  classical
  let P := (2*(A+T)).primesLE
  let M := fun p => (Ico A (A+T)).filter (fun n => p∈missing n)
  have sub (n : ℕ) (hn : n∈Ico A (A+T)) : missing n⊆P := by intro p h; obtain ⟨pr,_,hi,_⟩ := mem_missing.mp h; exact Nat.mem_primesLE.mpr ⟨hi.trans (by have := (mem_Ico.mp hn).2; omega),pr⟩
  have swap : ∑ n∈Ico A (A+T),lostWeight n = ∑ p∈P,((M p).card:ℝ)*Real.log p := by
    have row (n : ℕ) (hn : n∈Ico A (A+T)) : lostWeight n=∑ p∈P,if p∈missing n then Real.log p else 0 := by unfold lostWeight; rw [← sum_filter]; congr 1; ext p; exact ⟨fun h => mem_filter.mpr ⟨sub n hn h,h⟩,fun h => (mem_filter.mp h).2⟩
    rw [sum_congr rfl row,sum_comm]; apply sum_congr rfl; intro p _; rw [← sum_filter,sum_const,nsmul_eq_mul]
  have count (p : ℕ) (h : p∈P) : ((M p).card:ℝ) ≤ (T:ℝ)/(H+1)+1+H^2+2*H+4 := by
    obtain ⟨hi,pr⟩ := Nat.mem_primesLE.mp h
    have inc : M p ⊆ cancellations p := by intro n hn; obtain ⟨_,mem⟩ := mem_filter.mp hn; obtain ⟨_,lo,up,nz⟩ := mem_missing.mp mem; exact mem_filter.mpr ⟨mem_range.mpr lo,up,nz⟩
    by_cases ok : 3<p ∧ 2*H<p
    · have c := window_cancellations pr ok.1 ok.2 (M p) inc (filter_subset ..)
      have q := Nat.div_mul_le_self T (H+1)
      have qq : (↑(T/(H+1)):ℝ) ≤ T/(H+1) := (le_div_iff₀ (by positivity)).mpr (by exact_mod_cast q)
      have cr : ((M p).card:ℝ) ≤ (T/(H+1):ℕ)+1+(H:ℝ)^2 := by exact_mod_cast c
      linarith [Nat.cast_nonneg (α:=ℝ) H]
    · have c := (card_le_card inc).trans ((card_le_card (filter_subset _ (range p))).trans_eq (card_range p))
      have sm : p≤2*H+3 := by omega
      have cc : ((M p).card:ℝ)≤2*H+3 := by exact_mod_cast c.trans sm
      linarith [show 0≤(T:ℝ)/(H+1) by positivity,sq_nonneg (H:ℝ)]
  rw [swap,Chebyshev.theta_eq_sum_primesLE_log,sum_mul]; apply sum_le_sum; intro p hp
  have lp : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  simpa [mul_comm] using mul_le_mul_of_nonneg_right (count p hp) lp

/-- Specialization to an initial segment (with the coarser common scale `2*N`). -/
theorem total_lost_weight (N H : ℕ) :
    ∑ n∈range N,lostWeight n ≤ Chebyshev.theta (2*N:ℕ) * ((2*N:ℝ)/(H+1)+1+H^2+2*H+4) := by
  have h := window_lost_weight 0 N H
  simp only [zero_add,Nat.Ico_zero_eq_range] at h
  apply h.trans; gcongr; linarith [Nat.cast_nonneg (α:=ℝ) N]

/-- All surviving primes in `(n,2n]` divide the reduced denominator. -/
theorem diagonal_weight_lower (n : ℕ) : Chebyshev.theta (2*n:ℕ)-Chebyshev.theta n ≤
    Real.log (logShadow n n).den+lostWeight n := by
  let P := (2*n).primesLE \ n.primesLE
  let Z := missing n
  have inP {p : ℕ} (h : p∈P) : p.Prime ∧ n<p ∧ p≤2*n := by
    obtain ⟨hp,out⟩ := mem_sdiff.mp h; obtain ⟨hi,pr⟩ := Nat.mem_primesLE.mp hp
    exact ⟨pr,lt_of_not_ge (fun l => out (Nat.mem_primesLE.mpr ⟨l,pr⟩)),hi⟩
  have sub : Z⊆P := by
    intro p h; obtain ⟨pr,lo,hi,_⟩ := mem_missing.mp h
    exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hi,pr⟩,fun mem => lo.not_ge (Nat.mem_primesLE.mp mem).1⟩
  have pr {p : ℕ} (h : p∈P\Z) := (inP (mem_sdiff.mp h).1).1
  have dvd : (∏ p∈P\Z,p)∣(logShadow n n).den := prod_primes_dvd _ (fun p h => (pr h).prime) (by
    intro p h; obtain ⟨a,b⟩ := mem_sdiff.mp h; obtain ⟨prime,lo,hi⟩ := inP a; exact Classical.byContradiction (fun no => b (mem_missing.mpr ⟨prime,lo,hi,no⟩)))
  have pos := prod_pos (fun p h => (pr h).pos)
  have bound := Real.log_le_log (show (0:ℝ)<(∏ p∈P\Z,p:ℕ) by exact_mod_cast pos) ((Nat.cast_le (α:=ℝ)).mpr (Nat.le_of_dvd (logShadow n n).pos dvd))
  rw [Nat.cast_prod,Real.log_prod (fun p h => by exact_mod_cast (pr h).ne_zero)] at bound
  have split := sum_sdiff sub (f:=fun p : ℕ => Real.log p)
  have whole := sum_sdiff (Nat.primesLE_mono (show n≤2*n by omega)) (f:=fun p : ℕ => Real.log p)
  rw [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log]; change _≤_+∑ p∈Z,Real.log p
  change (∑ p∈P,Real.log p)+_= _ at whole; linarith only [bound,split,whole]

/-- The aggregate log weight lost by all diagonal models is `o(N²)`. -/
theorem mean_lost_weight : Tendsto (fun N : ℕ => (∑ n∈range N,lostWeight n)/(N:ℝ)^2) atTop (𝓝 0) := by
  have top := tendsto_natCast_atTop_atTop (R:=ℝ)
  have theta := (Chebyshev.tendsto_theta_div_atTop.comp (top.const_mul_atTop (by norm_num : (0:ℝ)<2))).eventually_lt_const (by norm_num : (1:ℝ)<2)
  rw [Metric.tendsto_atTop]; intro ε pos
  obtain ⟨H,hH⟩ := exists_nat_gt (16/ε)
  let B := 1+(H:ℝ)^2+2*H+4
  have ep := (div_lt_iff₀ pos).mp hH
  have frac : 8/((H:ℝ)+1)<ε/2 := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((theta.and (top.eventually_gt_atTop (8*B/ε))).and (eventually_gt_atTop 0))
  refine ⟨K,fun N hN => ?_⟩; obtain ⟨⟨th,nn⟩,np⟩ := hK N hN
  have nr : (0:ℝ)<N := by exact_mod_cast np
  change Chebyshev.theta (2*N)/(2*N)<2 at th; rw [div_lt_iff₀ (by positivity)] at th
  have big := (div_lt_iff₀ pos).mp nn
  have bound := total_lost_weight N H; push_cast at bound
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (sum_nonneg (fun i _ => nonneg_weight i)) (sq_nonneg _)),div_lt_iff₀ (sq_pos_of_pos nr)]
  have pr := mul_le_mul_of_nonneg_right th.le (show 0≤2*(N:ℝ)/(H+1)+B by dsimp [B]; positivity)
  have cut : 4*(2*(N:ℝ)/(H+1)+B)<ε*N := by
    have ineq := mul_lt_mul_of_pos_right frac nr
    rw [div_mul_eq_mul_div] at ineq; ring_nf at ineq ⊢; linarith only [ineq,big]
  calc _ ≤ Chebyshev.theta (2*N)*(2*N/(H+1)+B) := by dsimp [B]; linarith only [bound]
       _ ≤ 4*N*(2*N/(H+1)+B) := by linarith only [pr]
       _ < _ := by nlinarith only [mul_lt_mul_of_pos_right cut nr]

private lemma card_square_le (E : Finset ℕ) : (E.card:ℝ)^2 ≤ 2*(∑ n∈E,(n:ℝ))+E.card := by
  induction E using Finset.induction_on_max with
  | empty => simp
  | insert a E h ih =>
    have sub : E⊆range a := fun i hi => mem_range.mpr (h i hi)
    have c : (E.card:ℝ)≤a := by exact_mod_cast (card_le_card sub).trans_eq (card_range a)
    have fresh : a∉E := fun mem => (h a mem).false
    rw [card_insert_of_notMem fresh,sum_insert fresh]; push_cast; nlinarith

/-- If every late exceptional observation costs at least `δ n`, total cost `o(N²)`
forces the exceptions to have natural density zero. -/
private theorem density_of_weight (B : ℕ → Prop) [DecidablePred B] {δ : ℝ} (pos : 0<δ)
    (price : ∀ᶠ n : ℕ in atTop,B n → δ*n≤lostWeight n) :
    Tendsto (fun N : ℕ => (((range N).filter B).card:ℝ)/N) atTop (𝓝 0) := by
  obtain ⟨K,late⟩ := eventually_atTop.mp price
  have pay (n : ℕ) (h : B n) : δ*n≤lostWeight n+δ*K := by
    rcases le_total K n with l|l
    · exact (late n l h).trans (le_add_of_nonneg_right (by positivity))
    · linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr l) pos.le,nonneg_weight n]
  rw [Metric.tendsto_atTop]; intro ε he
  have cost := mean_lost_weight.eventually_lt_const (show 0<δ*ε^2/4 by positivity)
  have rem := (tendsto_const_div_atTop_nhds_zero_nat (2*δ*K+δ)).eventually_lt_const (show 0<δ*ε^2/2 by positivity)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp ((cost.and rem).and (eventually_gt_atTop 0))
  refine ⟨J,fun N hN => ?_⟩; obtain ⟨⟨c,r⟩,np⟩ := hJ N hN
  let E := (range N).filter B
  have le : (E.card:ℝ)≤N := by exact_mod_cast (card_le_card (filter_subset B (range N))).trans_eq (card_range N)
  have nr : (0:ℝ)<N := by exact_mod_cast np
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ nr]
  have obs := sum_le_sum (s:=E) (fun n h => pay n (mem_filter.mp h).2)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum] at obs
  have sumBound := sum_le_sum_of_subset_of_nonneg (s:=E) (t:=range N) (filter_subset ..) (fun i _ _ => nonneg_weight i)
  change (∑ n∈range N,lostWeight n)/_<_ at c
  rw [div_lt_iff₀ (sq_pos_of_pos nr)] at c; rw [div_lt_iff₀ nr] at r
  change (E.card:ℝ)<ε*N
  by_contra! large
  have largeSq := pow_le_pow_left₀ (mul_nonneg he.le nr.le) large 2
  have comb := mul_le_mul_of_nonneg_left (card_square_le E) pos.le
  nlinarith only [comb,obs,sumBound,c,mul_lt_mul_of_pos_right r nr,mul_le_mul_of_nonneg_left largeSq pos.le,mul_le_mul_of_nonneg_right le (show 0≤2*δ*K+δ by positivity)]

/-- For every positive fractional tolerance the diagonal models whose logarithmic
prime loss exceeds that fraction of `n` have natural density zero. -/
theorem lost_primes_density_zero {ε : ℝ} (pos : 0<ε) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n => ε*n≤lostWeight n)).card:ℝ)/N) atTop (𝓝 0) :=
  density_of_weight _ pos (.of_forall fun _ => id)

theorem small_denominator_price {ε : ℝ} (pos : 0<ε) : ∀ᶠ n : ℕ in atTop,
    Real.log (logShadow n n).den≤(1-ε)*n → (ε/2)*n≤lostWeight n := by
  have top := tendsto_natCast_atTop_atTop (R:=ℝ)
  have f := (Chebyshev.tendsto_theta_div_atTop.comp (top.const_mul_atTop (by norm_num : (0:ℝ)<2))).eventually_const_lt (by linarith : 1-ε/8<1)
  have g := (Chebyshev.tendsto_theta_div_atTop.comp top).eventually_lt_const (by linarith : 1<1+ε/4)
  filter_upwards [f,g,eventually_gt_atTop 0] with n low high hn bad
  have nr : (0:ℝ)<n := by exact_mod_cast hn
  change _<Chebyshev.theta (2*n)/(2*n) at low; rw [lt_div_iff₀ (by positivity)] at low
  change Chebyshev.theta n/(n:ℝ)<_ at high; rw [div_lt_iff₀ nr] at high
  have h := diagonal_weight_lower n; push_cast at h; linarith

/-- For each `ε>0`, the fully corrected denominators exceed `exp((1-ε)n)`
outside a set of indices of natural density zero. -/
theorem diagonal_small_denominators_density_zero {ε : ℝ} (pos : 0<ε) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n => Real.log (logShadow n n).den≤(1-ε)*n)).card:ℝ)/N) atTop (𝓝 0) :=
  density_of_weight _ (half_pos pos) (small_denominator_price pos)

theorem missing_fraction_price {ε : ℝ} (pos : 0<ε) : ∀ᶠ n : ℕ in atTop,
    ε*((2*n).primesLE \ n.primesLE).card≤(missing n).card → (ε/4)*n≤lostWeight n := by
  have top := tendsto_natCast_atTop_atTop (R:=ℝ)
  have f := (Chebyshev.tendsto_theta_div_atTop.comp (top.const_mul_atTop (by norm_num : (0:ℝ)<2))).eventually_const_lt (by norm_num : (7:ℝ)/8<1)
  have g := (Chebyshev.tendsto_theta_div_atTop.comp top).eventually_lt_const (by norm_num : (1:ℝ)<5/4)
  filter_upwards [f,g,eventually_ge_atTop 2] with n low high hn bad
  let P := (2*n).primesLE \ n.primesLE
  have nr : (2:ℝ)≤n := by exact_mod_cast hn
  change _<Chebyshev.theta (2*n)/(2*n) at low; rw [lt_div_iff₀ (by linarith)] at low
  change Chebyshev.theta n/(n:ℝ)<_ at high; rw [div_lt_iff₀ (by linarith)] at high
  have logPos := Real.log_nonneg (show (1:ℝ)≤n by linarith)
  have logBound : Real.log (2*n:ℝ)≤2*Real.log n := by rw [Real.log_mul (by norm_num) (by linarith)]; linarith only [Real.log_le_log (by norm_num : (0:ℝ)<2) nr]
  have full := sum_sdiff (Nat.primesLE_mono (show n≤2*n by omega)) (f:=fun p : ℕ => Real.log p)
  change (∑ p∈P,Real.log p)+_= _ at full
  have th : (n:ℝ)/2 ≤ ∑ p∈P,Real.log p := by
    rw [show (2:ℝ)*n=(2*n:ℕ) by push_cast; rfl,Chebyshev.theta_eq_sum_primesLE_log] at low
    rw [Chebyshev.theta_eq_sum_primesLE_log] at high; push_cast at low; linarith
  have up := sum_le_sum (s:=P) (f:=fun p : ℕ => Real.log p) (g:=fun _ => 2*Real.log n) (fun p h => (Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp (mem_sdiff.mp h).1).2.pos) (by exact_mod_cast (Nat.mem_primesLE.mp (mem_sdiff.mp h).1).1)).trans logBound)
  have down := sum_le_sum (s:=missing n) (f:=fun _ => Real.log n) (g:=fun p : ℕ => Real.log p) (fun p h => Real.log_le_log (by linarith) (by exact_mod_cast (mem_missing.mp h).2.1.le))
  rw [sum_const,nsmul_eq_mul] at up down
  change ε*P.card≤(missing n).card at bad; unfold lostWeight
  nlinarith only [down,mul_le_mul_of_nonneg_left (th.trans up) pos.le,mul_le_mul_of_nonneg_right bad logPos]

/-- For each fixed positive fraction, the indices losing that fraction of the
primes in `(n,2n]` have natural density zero. -/
theorem missing_prime_fraction_density_zero {ε : ℝ} (pos : 0<ε) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n => ε*((2*n).primesLE \ n.primesLE).card≤(missing n).card)).card:ℝ)/N) atTop (𝓝 0) :=
  density_of_weight _ (by positivity : 0<ε/4) (missing_fraction_price pos)

end NormalityChecker.ShadowCancellations
