module

public import NormalityChecker.StridedLogarithm
public import NormalityChecker.ShadowGrowth

/-! Actual large-prime survival and the half-length denominator exponent. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StrideDenominatorRate

/-- The integer coefficient in the binary-exponent representation. -/
def weight (j : ℕ) : ℤ := (if 2∣j then 4 else 0)+(if 3∣j then 3 else 0)-(if 6∣j then 6 else 0)

theorem step (N : ℕ) :
    twoStridePrefix (N+1)=2*twoStridePrefix N+(weight (N+1):ℚ)/(N+1) := by
  simp only [twoStridePrefix,stride_step,weight,Int.cast_ofNat,Int.cast_neg,Int.cast_pow,Int.cast_one,
    Int.cast_add,Int.cast_sub,apply_ite (fun n:ℤ => (n:ℚ))]
  have q {k : ℕ} (hk : 0<k) (hd : k∣N+1) : (((N+1)/k:ℕ):ℚ)=((N:ℚ)+1)/k := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hk.ne')).mpr
    exact_mod_cast Nat.div_mul_cancel hd
  have ns : (N:ℚ)+1≠0 := by positivity
  by_cases h₂ : 2∣N+1 <;> by_cases h₃ : 3∣N+1
  · have even : Even ((N+1)/3) := ⟨(N+1)/6,by omega⟩
    simp [h₂,h₃,show 6∣N+1 by omega,even.neg_one_pow,q (by decide) h₂,q (by decide) h₃]
    field_simp; ring
  · simp [h₂,h₃,show ¬6∣N+1 by omega,q (by decide) h₂]
    field_simp; ring
  · have odd : Odd ((N+1)/3) := ⟨(N+1)/6,by omega⟩
    simp [h₂,h₃,show ¬6∣N+1 by omega,odd.neg_one_pow,q (by decide) h₃]
    field_simp; ring
  · simp [h₂,h₃,show ¬6∣N+1 by omega]; ring

private theorem weight_mul {p : ℕ} (pr : p.Prime) (big : 3<p) (j : ℕ) : weight (p*j)=weight j := by
  have a : p.Coprime 2 := pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have b : p.Coprime 3 := pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) big)
  have c : p.Coprime 6 := a.mul_right b
  simp [weight,a.symm.dvd_mul_left,b.symm.dvd_mul_left,c.symm.dvd_mul_left]

private def regular (p : ℕ) (z : ℚ) := ¬p∣z.den

private lemma regular_add {p : ℕ} {a b : ℚ} (pr : p.Prime) (ha : regular p a) (hb : regular p b) :
    regular p (a+b) := fun h => (pr.dvd_mul.mp (h.trans (Rat.add_den_dvd ..))).elim ha hb

private lemma regular_sub {p : ℕ} {a b : ℚ} (pr : p.Prime) (ha : regular p a) (hb : regular p b) :
    regular p (a-b) := fun h => (pr.dvd_mul.mp (h.trans (Rat.sub_den_dvd ..))).elim ha hb

private lemma regular_twice {p : ℕ} {z : ℚ} (pr : p.Prime) (h : regular p z) : regular p (2*z) := by
  rw [two_mul]; exact regular_add pr h h

private lemma regular_frac {p j : ℕ} (a : ℤ) (h : ¬p∣j) : regular p ((a:ℚ)/j) := by
  have d := Rat.den_dvd a (j:ℤ)
  rw [Rat.divInt_eq_div,Int.cast_natCast] at d
  exact fun v => h (v.trans (by exact_mod_cast d))

/-- Removing the p-indexed short prefix leaves a rational which is integral at p. -/
theorem short_prefix_regular {p : ℕ} (pr : p.Prime) (big : 3<p) (N : ℕ) (small : N<p*p) :
    ¬p∣(twoStridePrefix N-(2:ℚ)^(N-N/p)*twoStridePrefix (N/p)/p).den := by
  let : Fact p.Prime := ⟨pr⟩
  have pp : (p:ℚ)≠0 := by exact_mod_cast pr.ne_zero
  change regular p _
  induction N with
  | zero => simpa [regular,twoStridePrefix,stridedPrefix] using pr.not_dvd_one
  | succ n ih =>
    have old := regular_twice pr (ih (by omega))
    have le := Nat.div_le_self n p
    by_cases dvd : p∣n+1
    · let j := n/p+1
      have eqj : (n+1)/p=j := Nat.succ_div_of_dvd dvd
      have prod : p*j=n+1 := eqj ▸ Nat.mul_div_cancel' dvd
      have jr : (0:ℚ)<j := by dsimp [j]; positivity
      have jl : j<p := (Nat.mul_lt_mul_left pr.pos).mp (prod ▸ small)
      let e := n-n/p
      have id : e=(p-1)*j := by
        have h : (p-1)*j+j=p*j := by rw [← Nat.succ_mul,show (p-1).succ=p by omega]
        dsimp [e,j] at *; omega
      have fermat : (p:ℤ)∣1-(2:ℤ)^e := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
        have un : (2:ZMod p)≠0 := by
          exact_mod_cast ((ZMod.natCast_eq_zero_iff 2 p).not.mpr
            (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
        rw [id,pow_mul]; push_cast; rw [ZMod.pow_card_sub_one_eq_one un]; simp
      obtain ⟨v,hv⟩ := fermat
      have hvq := congrArg (fun z : ℤ => (z:ℚ)) hv; push_cast at hvq
      have prodq := congrArg (fun z : ℕ => (z:ℚ)) prod; push_cast at prodq
      have w : weight (n+1)=weight j := prod ▸ weight_mul pr big j
      have eqn : twoStridePrefix (n+1)-(2:ℚ)^(n+1-(n+1)/p)*twoStridePrefix ((n+1)/p)/p =
          2*(twoStridePrefix n-(2:ℚ)^e*twoStridePrefix (n/p)/p)+((weight j*v:ℤ):ℚ)/j := by
        rw [step,eqj,show n+1-j=e by dsimp [j,e]; omega,w,show twoStridePrefix j=2*twoStridePrefix (n/p)+(weight j:ℚ)/j by simpa [j] using step (n/p)]
        push_cast; rw [← prodq]; field_simp
        linear_combination (norm:=ring_nf) (weight j:ℚ)*hvq
      rw [eqn]; exact regular_add pr old (regular_frac _ (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos (n/p)) jl))
    · have eqj := Nat.succ_div_of_not_dvd dvd
      have eqn : twoStridePrefix (n+1)-(2:ℚ)^(n+1-(n+1)/p)*twoStridePrefix ((n+1)/p)/p =
          2*(twoStridePrefix n-(2:ℚ)^(n-n/p)*twoStridePrefix (n/p)/p)+(weight (n+1):ℚ)/(n+1) := by
        rw [step,eqj,show n+1-n/p=n-n/p+1 by omega,pow_succ]; ring
      rw [eqn]; exact regular_add pr old (by simpa using regular_frac (weight (n+1)) dvd)

/-- Test on the actual short numerator, valid on every large-prime band. -/
theorem prime_survives {N p : ℕ} (pr : p.Prime) (big : 3<p) (small : N<p*p)
    (unit : ¬p∣(twoStridePrefix (N/p)).num.natAbs) : p∣(twoStridePrefix N).den := by
  by_contra absent
  let z := twoStridePrefix (N/p)
  let h := N-N/p
  let q := (2:ℚ)^h*z/p
  have free := regular_sub pr (a:=twoStridePrefix N) (b:=twoStridePrefix N-q) absent
    (short_prefix_regular pr big N small)
  rw [sub_sub_cancel] at free
  have eqn : (p:ℚ)*q=2^h*z := by dsimp [q]; field_simp
  have cross : (2:ℤ)^h*z.num*q.den = p*(q.num*z.den) := by
    apply Int.cast_injective (α:=ℚ); push_cast
    rw [←Rat.den_mul_eq_num,←Rat.den_mul_eq_num]; linear_combination -(q.den:ℚ)*z.den*eqn
  have dvd : (p:ℤ)∣(2:ℤ)^h*z.num*q.den := ⟨_,cross⟩
  have natural := Int.natCast_dvd.mp dvd
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,show (2:ℤ).natAbs=2 by decide] at natural
  exact (pr.dvd_mul.mp ((pr.dvd_mul.mp natural).resolve_right free)).elim
    (fun hd => Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p) (pr.dvd_of_dvd_pow hd)) unit


private lemma weight_nonneg (j : ℕ) : 0≤weight j := by
  unfold weight; split_ifs <;> omega

private lemma prefix_pos {j : ℕ} (hj : 2≤j) : 0<twoStridePrefix j := by
  induction j,hj using Nat.le_induction with
  | base => decide +kernel
  | succ n _ ih =>
    rw [step]; exact add_pos_of_pos_of_nonneg (by positivity)
      (div_nonneg (by exact_mod_cast weight_nonneg (n+1)) (by positivity))

/-- All primes in (N/K,N/2] survive for every sufficiently late N at fixed K. -/
theorem band_survival (K : ℕ) (hk : 0<K) : ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
    p.Prime → N/K<p → p≤N/2 → p∣(twoStridePrefix N).den := by
  let bound := 3+K+∑ j∈range K,(twoStridePrefix j).num.natAbs
  filter_upwards [eventually_ge_atTop (bound*K)] with N large p pr lo hi
  have bp : bound<p := (Nat.le_div_iff_mul_le hk).mpr large |>.trans_lt lo
  have len : N<p*K := (Nat.div_lt_iff_lt_mul hk).mp lo
  have kp : K≤p := by dsimp [bound] at bp; omega
  have small : N/p<K := (Nat.div_lt_iff_lt_mul pr.pos).mpr (by simpa [mul_comm] using len)
  have two : 2≤N/p := (Nat.le_div_iff_mul_le pr.pos).mpr (by have := (Nat.le_div_iff_mul_le (by decide : 0<2)).mp hi; omega)
  have pos : 0<(twoStridePrefix (N/p)).num.natAbs :=
    Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (prefix_pos two).ne')
  have sum := single_le_sum (f:=fun j => (twoStridePrefix j).num.natAbs) (fun _ _ => Nat.zero_le _) (mem_range.mpr small)
  exact prime_survives pr (by dsimp [bound] at bp; omega) (len.trans_le (Nat.mul_le_mul_left p kp))
    (Nat.not_dvd_of_pos_of_lt pos (by dsimp [bound] at bp; omega))

/-- The floor in the digit cutoff contributes a vanishing normalized error. -/
theorem floor_ratio (k : ℕ) (hk : 0<k) :
    Tendsto (fun n : ℕ => ((n/k:ℕ):ℝ)/n) atTop (𝓝 (1/(k:ℝ))) := by
  have kr : (0:ℝ)<k := by exact_mod_cast hk
  have rem : Tendsto (fun n : ℕ => ((n%k:ℕ):ℝ)/n) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity) (fun n => div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (Nat.mod_lt n hk).le) (by positivity)) (tendsto_const_div_atTop_nhds_zero_nat (k:ℝ))
  have h := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop (α:=ℕ))).sub rem
  have hh := h.div_const (k:ℝ)
  simp only [sub_zero] at hh
  apply hh.congr'; filter_upwards [eventually_gt_atTop 0] with n hn
  have e := congrArg (fun t : ℕ => (t:ℝ)) (Nat.div_add_mod n k)
  push_cast at e
  field_simp; linarith

private lemma theta_ratio (k : ℕ) (hk : 0<k) :
    Tendsto (fun n : ℕ => Chebyshev.theta (n/k:ℕ)/n) atTop (𝓝 (1/(k:ℝ))) := by
  have grow := Nat.tendsto_div_const_atTop hk.ne'
  have h := (Chebyshev.tendsto_theta_div_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)).mul (floor_ratio k hk)
  rw [one_mul] at h
  apply h.congr'; filter_upwards [grow.eventually_gt_atTop 0] with n hn
  change Chebyshev.theta (n/k:ℕ)/(n/k:ℕ)*(((n/k:ℕ):ℝ)/n)=_
  have nz : ((n/k:ℕ):ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

private lemma band_log (K : ℕ) (hk : 2≤K) : ∀ᶠ n : ℕ in atTop,
    Chebyshev.theta (n/2:ℕ)-Chebyshev.theta (n/K:ℕ) ≤ Real.log (twoStridePrefix n).den := by
  filter_upwards [band_survival K (by omega)] with n all
  let S := (n/2).primesLE \ (n/K).primesLE
  have sub := Nat.primesLE_mono (Nat.div_le_div_left hk (by omega : 0<2) : n/K≤n/2)
  have get {p : ℕ} (h : p∈S) : p.Prime ∧ n/K<p ∧ p≤n/2 := by
    obtain ⟨a,b⟩ := mem_sdiff.mp h; obtain ⟨hi,pr⟩ := Nat.mem_primesLE.mp a
    exact ⟨pr,lt_of_not_ge (fun lo => b (Nat.mem_primesLE.mpr ⟨lo,pr⟩)),hi⟩
  have dv : (∏ p∈S,p)∣(twoStridePrefix n).den :=
    prod_primes_dvd _ (fun p h => (get h).1.prime) (fun p h => all p (get h).1 (get h).2.1 (get h).2.2)
  have bound := Real.log_le_log (show (0:ℝ)<(∏ p∈S,p:ℕ) by exact_mod_cast prod_pos (fun p h => (get h).1.pos))
    (Nat.cast_le.mpr (Nat.le_of_dvd (twoStridePrefix n).pos dv))
  rw [Nat.cast_prod,Real.log_prod (fun p h => by exact_mod_cast (get h).1.ne_zero)] at bound
  rwa [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log,← sum_sdiff sub,add_sub_cancel_right]

/-- The actual reduced denominator of the half-length model has logarithmic rate 1/2. -/
theorem log_denominator_rate :
    Tendsto (fun N : ℕ => Real.log (twoStridePrefix N).den/N) atTop (𝓝 (1/2:ℝ)) := by
  apply tendsto_order.mpr; constructor
  · intro a ha
    obtain ⟨K,hK⟩ := exists_nat_gt (max 2 (1/(1/2-a)))
    have kp : (0:ℝ)<K := lt_trans (by norm_num : (0:ℝ)<2) ((le_max_left ..).trans_lt hK)
    have eps : 1/(K:ℝ)<1/2-a := by
      have d := (div_lt_iff₀ (by linarith : 0<1/2-a)).mp ((le_max_right ..).trans_lt hK)
      exact (div_lt_iff₀ kp).mpr (by linarith [mul_comm (K:ℝ) (1/2-a)])
    have two : 2≤K := by exact_mod_cast ((le_max_left ..).trans_lt hK).le
    have t := (theta_ratio 2 (by decide)).sub (theta_ratio K (by omega))
    filter_upwards [band_log K two,t.eventually_const_lt (show a<1/(2:ℕ)-1/(K:ℝ) by norm_num at *; linarith)] with n b lo
    change a<Chebyshev.theta (n/2:ℕ)/n-Chebyshev.theta (n/K:ℕ)/n at lo
    rw [←sub_div] at lo; exact lo.trans_le (div_le_div_of_nonneg_right b (by positivity))
  · intro a ha
    have g := Nat.tendsto_div_const_atTop (by decide : 2≠0)
    have t := (Nat.tendsto_log_lcmUpto_div_atTop.comp g).mul (floor_ratio 2 (by decide))
    rw [one_mul] at t; norm_num only [Nat.cast_ofNat] at t
    filter_upwards [t.eventually_lt_const ha,g.eventually_gt_atTop 0] with n bound hn
    have pos : (0:ℝ)<(n/2:ℕ) := by exact_mod_cast hn
    have h := Real.log_le_log (show (0:ℝ)<(twoStridePrefix n).den by exact_mod_cast (twoStridePrefix n).pos)
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.lcmUpto_pos _) (twoStridePrefix_den n)))
    change Real.log (Nat.lcmUpto (n/2))/(n/2:ℕ)*(((n/2:ℕ):ℝ)/n)<a at bound
    rw [div_mul_div_cancel₀ pos.ne'] at bound
    exact (div_le_div_of_nonneg_right h (by positivity)).trans_lt bound

end NormalityChecker.StrideDenominatorRate
