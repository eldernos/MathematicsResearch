module

public import NormalityChecker.StrideDenominatorRate

/-! Exact reduced denominator rates from finitely many vanishing partial sums. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LogarithmBands

private def band (n v : ℕ) := (n/v).primesLE \ (n/(v+1)).primesLE
private def holes (n : ℕ) (Z : Finset ℕ) := Z.biUnion (band n)
private noncomputable def mass (s : Finset ℕ) : ℝ := ∑ p∈s,Real.log p

private lemma band_mem {p n v : ℕ} (hv : 0<v) :
    p∈band n v ↔ p.Prime ∧ n/p=v := by
  constructor
  · intro h; obtain ⟨a,b⟩ := mem_sdiff.mp h; obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp a
    have hi : n/(v+1)<p := lt_of_not_ge (fun z => b (Nat.mem_primesLE.mpr ⟨z,pr⟩))
    have l := (Nat.le_div_iff_mul_le hv).mp le
    have r := (Nat.div_lt_iff_lt_mul (Nat.succ_pos v)).mp hi
    exact ⟨pr,le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul pr.pos).mpr (by simpa [mul_comm] using r)))
      ((Nat.le_div_iff_mul_le pr.pos).mpr (by simpa [mul_comm] using l))⟩
  · rintro ⟨pr,eqn⟩
    have l := (Nat.le_div_iff_mul_le pr.pos).mp eqn.ge
    have r := (Nat.div_lt_iff_lt_mul pr.pos).mp (eqn.trans_lt (Nat.lt_succ_self _))
    exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_div_iff_mul_le hv).mpr (by simpa [mul_comm] using l),pr⟩,
      fun h => (Nat.not_le_of_gt ((Nat.div_lt_iff_lt_mul (Nat.succ_pos v)).mpr (by simpa [mul_comm] using r))) (Nat.mem_primesLE.mp h).1⟩

private lemma holes_mem {n p : ℕ} {Z : Finset ℕ} (nz : 0∉Z) :
    p∈holes n Z ↔ p.Prime ∧ n/p∈Z := by
  constructor
  · intro h; obtain ⟨v,hv,u⟩ := mem_biUnion.mp h
    have b := (band_mem (Nat.pos_of_ne_zero (fun z => nz (z ▸ hv)))).mp u
    exact ⟨b.1,b.2 ▸ hv⟩
  · rintro ⟨pr,mem⟩
    exact mem_biUnion.mpr ⟨_,mem,(band_mem (Nat.pos_of_ne_zero (fun z => nz (z ▸ mem)))).mpr ⟨pr,rfl⟩⟩

private lemma hole_rate (Z : Finset ℕ) (nz : 0∉Z) :
    Tendsto (fun n : ℕ => mass (holes n Z)/n) atTop (𝓝 (∑ v∈Z,(1/(v:ℝ)-1/((v:ℝ)+1)))) := by
  have vp {v : ℕ} (hv : v∈Z) : 0<v := Nat.pos_of_ne_zero (fun z => nz (z ▸ hv))
  have h := tendsto_finsetSum Z (fun v hv => (StrideDenominatorRate.theta_ratio v (vp hv)).sub
    (StrideDenominatorRate.theta_ratio (v+1) (Nat.succ_pos v)))
  push_cast at h; apply h.congr; intro n
  have dis : (Z:Set ℕ).PairwiseDisjoint (band n) := by
    intro i hi j hj ne; apply Finset.disjoint_left.mpr; intro p a b
    exact ne (((band_mem (vp hi)).mp a).2.symm.trans ((band_mem (vp hj)).mp b).2)
  rw [mass,holes,sum_biUnion dis,sum_div]; apply sum_congr rfl; intro v hv
  rw [←sub_div]; congr 1
  rw [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log]
  have sub := Nat.primesLE_mono (Nat.div_le_div_left (Nat.le_succ v) (vp hv) : n/(v+1)≤n/v)
  exact sub_eq_of_eq_add (sum_sdiff sub).symm

private lemma ebands (Y : ℕ → ℚ) (W : ℕ → ℤ) (base : Y 0=0)
    (step : ∀ n,Y (n+1)=2*Y n+(W (n+1):ℚ)/(n+1))
    (invar : ∀ᶠ p : ℕ in atTop,p.Prime → ∀ j,W (p*j)=W j)
    (K : ℕ) (hk : 0<K) : ∀ᶠ n : ℕ in atTop,∀ p : ℕ,p.Prime → n/K<p → p≤n →
       (p∣(Y n).den ↔ Y (n/p)≠0) := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp invar
  let b := B+3+K+∑ j∈range K,(Y j).num.natAbs
  filter_upwards [eventually_ge_atTop (b*K)] with n late p pr lo _
  have bp := ((Nat.le_div_iff_mul_le hk).mpr late).trans_lt lo
  have len := (Nat.div_lt_iff_lt_mul hk).mp lo
  have small : n/p<K := (Nat.div_lt_iff_lt_mul pr.pos).mpr (by simpa [mul_comm] using len)
  have big : 3<p := by dsimp [b] at bp; omega
  have diff := StrideDenominatorRate.weighted_short_regular Y W base step pr big
    (hB p (by dsimp [b] at bp; omega) pr) n (len.trans_le (Nat.mul_le_mul_left p (by dsimp [b] at bp; omega)))
  constructor
  · intro bad zero; simp [zero,bad] at diff
  · intro ne
    have pos := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr ne)
    have bnd := single_le_sum (f:=fun j => (Y j).num.natAbs) (fun _ _ => Nat.zero_le _) (mem_range.mpr small)
    exact StrideDenominatorRate.weighted_prime_survives Y pr big diff (Nat.not_dvd_of_pos_of_lt pos (by dsimp [b] at bp; omega))

private lemma den_dvd (Y : ℕ → ℚ) (W : ℕ → ℤ) (base : Y 0=0)
    (step : ∀ n,Y (n+1)=2*Y n+(W (n+1):ℚ)/(n+1)) (n : ℕ) : (Y n).den∣Nat.lcmUpto n := by
  induction n with
  | zero => simp [base]
  | succ n ih =>
    rw [step]; apply (Rat.add_den_dvd_lcm ..).trans (Nat.lcm_dvd ?_ ?_)
    · apply (Rat.mul_den_dvd ..).trans
      simpa using ih.trans (Finset.lcm_dvd (fun i hi => index_dvd_lcm (mem_Icc.mp hi).1 ((mem_Icc.mp hi).2.trans (Nat.le_succ n))))
    · have dvd := Rat.den_dvd (W (n+1)) ((n+1:ℕ):ℤ)
      rw [Rat.divInt_eq_div,Int.cast_natCast,Nat.cast_add,Nat.cast_one] at dvd
      exact (by exact_mod_cast dvd : ((W (n+1):ℚ)/(n+1)).den∣n+1).trans (index_dvd_lcm (Nat.succ_pos n) le_rfl)

/-- A finite zero list suffices: convergence of nonzero unshifted logarithm
series ensures that all their positive-index zero partial sums form such a list. -/
theorem denominator_rate (Y : ℕ → ℚ) (W : ℕ → ℤ) (base : Y 0=0)
    (step : ∀ n,Y (n+1)=2*Y n+(W (n+1):ℚ)/(n+1))
    (invar : ∀ᶠ p : ℕ in atTop,p.Prime → ∀ j,W (p*j)=W j)
    (Z : Finset ℕ) (zeros : ∀ v,v∈Z ↔ 0<v ∧ Y v=0) :
    Tendsto (fun n : ℕ => Real.log (Y n).den/n) atTop
      (𝓝 (1-∑ v∈Z,(1/(v:ℝ)-1/((v:ℝ)+1)))) := by
  classical
  have nz : 0∉Z := fun h => (zeros 0 |>.mp h).1.false
  let loss := ∑ v∈Z,(1/(v:ℝ)-1/((v:ℝ)+1))
  have rate := hole_rate Z nz
  have prodlog (n : ℕ) (S : Finset ℕ) (surv : ∀ p∈S,p.Prime ∧ p∣(Y n).den) :
      mass S≤Real.log (Y n).den := by
    have dvd := prod_primes_dvd (s:=S) (Y n).den (fun p h => (surv p h).1.prime) (fun p h => (surv p h).2)
    have l := Real.log_le_log (show (0:ℝ)<(∏ p∈S,p:ℕ) by exact_mod_cast prod_pos (fun p h => (surv p h).1.pos))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Y n).pos dvd))
    rw [Nat.cast_prod,Real.log_prod (fun p h => by exact_mod_cast (surv p h).1.ne_zero)] at l
    exact l
  apply tendsto_order.mpr; constructor
  · intro a gap
    obtain ⟨K,hK⟩ := exists_nat_gt (max 2 (1/(1-loss-a)))
    have kp : (0:ℝ)<K := lt_trans (by norm_num : (0:ℝ)<2) ((le_max_left ..).trans_lt hK)
    have eps := (div_lt_iff₀ (show 0<1-loss-a by dsimp [loss] at *; linarith)).mp ((le_max_right ..).trans_lt hK)
    have hsmall : 1/(K:ℝ)<1-loss-a := (div_lt_iff₀ kp).mpr (by linarith [mul_comm (K:ℝ) (1-loss-a)])
    have hk : 0<K := by exact_mod_cast kp
    have lim := ((Chebyshev.tendsto_theta_div_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).sub
      (StrideDenominatorRate.theta_ratio K hk)).sub rate
    filter_upwards [ebands Y W base step invar K hk,lim.eventually_const_lt (show a<1-1/(K:ℝ)-loss by linarith)] with n tests lo
    let P := n.primesLE \ (n/K).primesLE
    let H := holes n Z
    have upper (p : ℕ) (h : p∈P) : p.Prime ∧ n/K<p ∧ p≤n := by
      obtain ⟨m,u⟩ := mem_sdiff.mp h; have g := Nat.mem_primesLE.mp m
      exact ⟨g.2,lt_of_not_ge (fun le => u (Nat.mem_primesLE.mpr ⟨le,g.2⟩)),g.1⟩
    have d := prodlog n (P \ H) (fun p h => by
      obtain ⟨m,no⟩ := mem_sdiff.mp h; obtain ⟨pr,l,u⟩ := upper p m
      refine ⟨pr,(tests p pr l u).mpr (fun z => no ((holes_mem nz).mpr ⟨pr,(zeros _).mpr ⟨(Nat.le_div_iff_mul_le pr.pos).mpr (by simpa using u),z⟩⟩))⟩)
    have hcost : mass P ≤ mass (P \ H)+mass H := by
      have eqn : P \ (P ∩ H)=P \ H := by ext; simp
      unfold mass
      rw [←sum_sdiff (Finset.inter_subset_left (s₁:=P) (s₂:=H)),eqn]
      exact add_le_add_right (sum_le_sum_of_subset_of_nonneg (f:=fun p : ℕ => Real.log p) (Finset.inter_subset_right (s₁:=P) (s₂:=H))
        (fun p hp _ => Real.log_nonneg (by exact_mod_cast ((holes_mem nz).mp hp).1.one_le))) _
    have full : Chebyshev.theta n-Chebyshev.theta (n/K:ℕ)=mass P := by
      rw [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log]
      exact sub_eq_of_eq_add (sum_sdiff (Nat.primesLE_mono (Nat.div_le_self n K))).symm
    change a<Chebyshev.theta n/n-Chebyshev.theta (n/K:ℕ)/n-mass H/n at lo
    rw [←sub_div,←sub_div,full] at lo
    exact lo.trans_le (div_le_div_of_nonneg_right (by linarith) (by positivity))
  · intro a gap
    let K := Z.sup id + 1
    have hk : 0<K := Nat.succ_pos _
    have lim := Nat.tendsto_log_lcmUpto_div_atTop.sub rate
    filter_upwards [ebands Y W base step invar K hk,lim.eventually_lt_const gap] with n tests lo
    let H := holes n Z
    have info (p : ℕ) (h : p∈H) : p.Prime ∧ p≤n ∧ ¬p∣(Y n).den := by
      obtain ⟨pr,mem⟩ := (holes_mem nz).mp h
      obtain ⟨pos,zero⟩ := (zeros _).mp mem
      have pn : p≤n := by simpa using (Nat.le_div_iff_mul_le pr.pos).mp pos
      have short : n/p<K := Nat.lt_succ_of_le (Finset.le_sup (f:=id) mem)
      have l := (Nat.div_lt_iff_lt_mul pr.pos).mp short
      exact ⟨pr,pn,fun d => (tests p pr ((Nat.div_lt_iff_lt_mul hk).mpr (by simpa [mul_comm] using l)) pn).mp d zero⟩
    have dvd : (∏ p∈H,p)∣Nat.lcmUpto n := prod_primes_dvd (s:=H) (Nat.lcmUpto n) (fun p h => (info p h).1.prime)
      (fun p h => index_dvd_lcm (info p h).1.pos (info p h).2.1)
    have cop : Nat.Coprime (∏ p∈H,p) (Y n).den := Nat.coprime_prod_left_iff.mpr
      (fun p h => (info p h).1.coprime_iff_not_dvd.mpr (info p h).2.2)
    have joint := cop.mul_dvd_of_dvd_of_dvd dvd (den_dvd Y W base step n)
    have pp : 0<∏ p∈H,p := prod_pos fun p h => (info p h).1.pos
    have l := Real.log_le_log (show (0:ℝ)<((∏ p∈H,p)*(Y n).den:ℕ) by exact_mod_cast Nat.mul_pos pp (Y n).pos)
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.lcmUpto_pos n) joint))
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast pp.ne') (by exact_mod_cast (Y n).pos.ne'),
        Nat.cast_prod,Real.log_prod (fun p h => by exact_mod_cast (info p h).1.ne_zero)] at l
    change Real.log (Nat.lcmUpto n)/n-mass H/n<a at lo; rw [←sub_div] at lo
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (by dsimp [H,mass] at *; linarith) (by positivity)) lo

end NormalityChecker.LogarithmBands
