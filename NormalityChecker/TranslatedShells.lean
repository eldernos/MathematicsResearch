module

public import NormalityChecker.CircleDiscrepancy
public import NormalityChecker.RationalOrbitCycle
public import NormalityChecker.SharpDiscrepancy
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Signed Stoneham phases under integer dilation and rational translation. -/
@[expose] public section
open Finset Filter NormalityChecker.CircleDiscrepancy
open scoped Topology
namespace NormalityChecker.SignedPhases

private def affinePre (b p : ℕ) (c : ℕ → ℤ) (m : ℤ) (r : ℚ) (n : ℕ) : ℚ :=
  m*pre b p c n + (b:ℚ)^n*r

private lemma affine_den (x t : ℚ) {m : ℤ} (hm : m≠0) :
    (m*x+t).den ∣ x.den*t.den ∧ x.den ≤ m.natAbs*t.den*(m*x+t).den := by
  let y : ℚ := m*x+t
  have dd : ((m:ℚ)*x).den ∣ x.den := by simpa using Rat.mul_den_dvd (m:ℚ) x
  have eqn : (m:ℚ)⁻¹*(y-t) = x := by dsimp [y]; rw [add_sub_cancel_right,inv_mul_cancel_left₀ (by exact_mod_cast hm)]
  have dv := Rat.mul_den_dvd (m:ℚ)⁻¹ (y-t)
  rw [eqn,Rat.inv_intCast_den,ite_eq_right hm] at dv
  refine ⟨(Rat.add_den_dvd ..).trans (mul_dvd_mul dd dvd_rfl),?_⟩
  have h := dv.trans (mul_dvd_mul (dvd_refl _) (Rat.sub_den_dvd y t))
  simpa [mul_assoc,mul_left_comm,mul_comm,y] using Nat.le_of_dvd
    (Nat.mul_pos (Int.natAbs_pos.mpr hm) (Nat.mul_pos y.pos t.pos)) h

private noncomputable def shadow (b p : ℕ) (c : ℕ → ℤ) (m : ℤ) (r : ℚ) (n : ℕ) : ℝ :=
  if n=0 ∨ c (Nat.log p n)≠0 then (b:ℝ)^n*((m:ℝ)*value b p c+r)
  else affinePre b p c m r n

private lemma affine_tail {b p C : ℕ} (hb : 2≤b) (hp : p.Prime) (c : ℕ → ℤ)
    (cap : ∀ j, (c j).natAbs ≤ C) (m : ℤ) (r : ℚ) :
    Tendsto (fun n => (b:ℝ)^n*((m:ℝ)*value b p c+r)-(affinePre b p c m r n:ℝ))
      atTop (𝓝 0) := by
  simpa only [affinePre,Rat.cast_add,Rat.cast_mul,Rat.cast_intCast,Rat.cast_pow,
    Rat.cast_natCast,mul_add,add_sub_add_right_eq_sub,mul_zero,mul_sub,mul_left_comm]
    using (shifted_tail_tendsto_zero hb hp c cap).const_mul (m:ℝ)

private lemma shadow_tail {b p C : ℕ} (hb : 2≤b) (hp : p.Prime) (c : ℕ → ℤ)
    (cap : ∀ j, (c j).natAbs ≤ C) (m : ℤ) (r : ℚ) :
    Tendsto (fun n => (b:ℝ)^n*((m:ℝ)*value b p c+r)-shadow b p c m r n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro ε he
  filter_upwards [(Metric.tendsto_nhds.mp (affine_tail hb hp c cap m r)) ε he] with n small
  unfold shadow; split_ifs <;> simp_all

private lemma shadow_uniform {b p C s q L : ℕ} (hb : 2≤b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C)
    (m : ℤ) (hm : m ≠ 0) (r : ℚ) (qp : 0<q) (cq : b.Coprime q) (lp : 0<L)
    (qden : ∀ n, s≤n → ((b:ℚ)^n*r).den ∣ q)
    (per : ∀ n, s≤n → shift b (r:ℝ) (n+L) = shift b r n)
    {ε : ℝ} (pos : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a d : ℝ, 0≤a → a<d → d≤1 →
      |(frequency (fun n => Int.fract (shadow b p c m r n)) a d N - (d-a)) -
        zeroDensity p c N*(frequency (fun n => shift b r (s+n)) a d L - (d-a))| ≤ ε := by
  classical
  let x : ℝ := m*value b p c+r
  let P := affinePre b p c m r
  let supp := p*q
  have sp : 1 < supp := hp.one_lt.trans_le (Nat.le_mul_of_pos_right _ qp)
  obtain ⟨M,K,block⟩ := smooth_interval_block (d:=4)
    (fixed_support_orbit_estimate hb sp (cop.mul_right cq)) x P (affine_tail hb hp c cap m r) (half_pos pos)
  obtain ⟨T,hT⟩ := exists_nat_gt ((4+2*L)/ε)
  let k₀ := 2+T+K+s+q+C*(m.natAbs*q*M)
  have pk : 1 < p^2 := one_lt_pow₀ hp.one_lt (by decide)
  filter_upwards [eventually_ge_atTop ((p^2)^k₀)] with N hN a d ha had hd
  let k := Nat.log (p^2) N
  let B := p^k
  have hk : k₀ ≤ k := Nat.le_log_of_pow_le pk hN
  have kb : k ≤ B := (Nat.lt_pow_self hp.two_le).le
  have bp : 0 < B := pow_pos hp.pos k
  have np : 0 < N := (pow_pos (pow_pos hp.pos _) _).trans_le hN
  have sq : B*B ≤ N := by
    calc B*B = (p^2)^k := by dsimp only [B]; rw [← sq,pow_right_comm]
         _ ≤ N := Nat.pow_log_le_self _ np.ne'
  have cube : N ≤ B^3 := by
    have k2 : 2 ≤ k := by dsimp [k₀] at hk; omega
    calc N ≤ (p^2)^(k+1) := (Nat.lt_pow_succ_log_self pk N).le
         _ ≤ B^3 := by dsimp only [B]; rw [← pow_mul,← pow_mul]; exact Nat.pow_le_pow_right hp.pos (by omega)
  have tb : T≤B := by dsimp [k₀] at hk; omega
  have huge := (div_lt_iff₀ pos).mp (hT.trans_le (Nat.cast_le (α:=ℝ).mpr tb))
  let w := frequency (fun n => shift b r (s+n)) a d L
  let u (i : ℕ) := Int.fract (shadow b p c m r i)
  let active (n : ℕ) := n=0 ∨ c (Nat.log p n)≠0
  let weight (n : ℕ) := if active n then d-a else w
  let f (n : ℕ) := (if a≤u n ∧ u n<d then (1:ℝ) else 0) - weight n
  have wbd : 0≤w ∧ w≤1 := frequency_bounds _ _ _ _
  have unit (n : ℕ) : ‖(f n:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_le]; dsimp [f,weight]
    split_ifs <;> constructor <;> linarith [wbd.1,wbd.2]
  have est := charged_prefix_bound (fun n => (f n:ℂ)) unit (fun _ => 0) (fun _ => le_rfl)
    (N:=N) bp {0} (half_pos pos).le (by
      intro l hl good
      simp only [sum_const_zero,add_zero]
      have hpL : 0<l := Nat.pos_of_ne_zero (by simpa using good)
      let n := l*B
      let j := Nat.log p n
      have bn : B≤n := Nat.le_mul_of_pos_left B hpL
      have npos := bp.trans_le bn
      have lo : p^j≤n := Nat.pow_log_le_self _ npos.ne'
      have hi : n<p^(j+1) := Nat.lt_pow_succ_log_self hp.one_lt n
      have kj : k≤j := Nat.le_log_of_pow_le hp.one_lt bn
      have dj : B≤p^j := Nat.pow_le_pow_right hp.pos kj
      obtain ⟨t,ht⟩ : B ∣ p^(j+1) := pow_dvd_pow p (by omega)
      have same (i : ℕ) (bi : i<B) : Nat.log p (n+i)=j := by
        apply Nat.log_eq_of_pow_le_of_lt_pow (lo.trans (Nat.le_add_right ..))
        rw [ht,mul_comm B] at hi ⊢
        have lt : l<t := Nat.lt_of_mul_lt_mul_right hi
        calc n+i < (l+1)*B := by dsimp only [n]; rw [Nat.succ_mul]; omega
             _ ≤ t*B := Nat.mul_le_mul_right B lt
      have sn : s≤n := by dsimp [k₀] at hk; omega
      by_cases zero : c j=0
      · have proj (i : ℕ) (bi : i<B) : u (n+i) = shift b r (n+i) := by
          obtain ⟨z,eqn⟩ := phase_within_shell hb hp cop c (k:=Nat.log p (n+i)) (n:=n+i)
            (Nat.pow_log_le_self _ (by omega)) (Nat.lt_pow_succ_log_self hp.one_lt _)
          simp only [same i bi,zero,Int.cast_zero,mul_zero,zero_div,add_zero] at eqn
          simp only [u,shadow,same i bi,zero,ne_eq,not_true_eq_false,or_false,
            ite_eq_right (by omega : n+i≠0),affinePre,eqn,Rat.cast_add,Rat.cast_mul,Rat.cast_intCast,
            Rat.cast_pow,Rat.cast_natCast,shift,← Int.cast_mul,Int.fract_intCast_add]
        have E := cycle_block_error (shift b r) lp per a d n B sn
        have eqn (i : ℕ) (hi : i∈range B) : f (n+i) =
            (if a≤shift b r (n+i) ∧ shift b r (n+i)<d then (1:ℝ) else 0)-w := by
          simp [f,weight,active,proj i (mem_range.mp hi),same i (mem_range.mp hi),zero,npos.ne']
        rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,sum_congr rfl eqn]
        apply E.trans; linarith [Nat.cast_nonneg (α:=ℝ) L]
      · have eqn (i : ℕ) (hi : i∈range B) :
            (f (n+i):ℂ) = Localized.centered (shift b x) a d (n+i) := by
          have act : active (n+i) := Or.inr (by rwa [same i (mem_range.mp hi)])
          have proj : u (n+i) = shift b x (n+i) := by
            change Int.fract (if active (n+i) then _ else _) = _
            rw [ite_eq_left act]; rfl
          simp only [f,Localized.centered,weight,ite_eq_left act,proj]
        rw [sum_congr rfl eqn]
        have minDen : C*(m.natAbs*q*M) ≤ p^j := by dsimp [k₀] at hk; omega
        obtain ⟨low,dv⟩ := denominator_within_nonzero_shell hb hp cop c cap lo hi zero minDen
        have ⟨d1,d2⟩ := affine_den (pre b p c n) ((b:ℚ)^n*r) hm
        have rid := qden n sn
        have small := Nat.le_of_dvd qp rid
        have support : (P n).den ∣ p^j*q := d1.trans (mul_dvd_mul dv rid)
        have minP : M≤(P n).den := by
          have cmp := (low.trans d2).trans (Nat.mul_le_mul_right (P n).den (Nat.mul_le_mul_left m.natAbs small))
          exact Nat.le_of_mul_le_mul_left cmp (Nat.mul_pos (Int.natAbs_pos.mpr hm) qp)
        have nN := (Nat.mul_le_mul_right B hl.le).trans (Nat.div_mul_le_self N B)
        have qb : q≤B := by dsimp [k₀] at hk; omega
        apply block B n (by dsimp [k₀] at hk; omega) minP
          ⟨j+1,support.trans (by rw [mul_pow]; exact mul_dvd_mul (pow_dvd_pow p (by omega)) (dvd_pow_self q (by omega)))⟩
          ((Nat.le_of_dvd (Nat.mul_pos (pow_pos hp.pos _) qp) support).trans (by
            calc p^j*q ≤ B^3*B := Nat.mul_le_mul (lo.trans (nN.trans cube)) qb
                 _ = B^4 := by ring)) _ _ _ ha had.le hd
        intro i bi
        simp only [P,affinePre,pre,ite_eq_right npos.ne',ite_eq_right (show n+i≠0 by omega),same i bi,j,pow_add]
        ring)
  simp only [sum_const_zero,add_zero,card_singleton,Nat.cast_one,← Complex.ofReal_sum,
    Complex.norm_real,Real.norm_eq_abs] at est
  have budget : 2*(B:ℝ) ≤ ε/2*N := by
    have sqr : (B:ℝ)*B≤N := by exact_mod_cast sq
    nlinarith only [mul_le_mul_of_nonneg_left sqr (half_pos pos).le,
      mul_le_mul_of_nonneg_right (show 4≤ε*(B:ℝ) by linarith [Nat.cast_nonneg (α:=ℝ) L]) (Nat.cast_nonneg (α:=ℝ) B)]
  have total : |∑ i∈range N, f i| ≤ ε*N := by linarith
  let G := regularPositions p c N
  have weights : ∑ i∈range N, weight i = G.card*(d-a) + ((N:ℝ)-G.card)*w := by
    have each (i : ℕ) : weight i = (if active i then (d-a)-w else 0)+w := by
      dsimp [weight]; split_ifs <;> ring
    simp only [each,sum_add_distrib,← sum_filter,sum_const,nsmul_eq_mul,card_range]
    change (G.card:ℝ)*_+_=_
    ring
  simp only [f,sum_sub_distrib,weights,← sum_filter,sum_const,nsmul_eq_mul,mul_one] at total
  have nr : (0:ℝ)<N := by exact_mod_cast np
  let count : ℝ := ((range N).filter (fun i => a≤u i ∧ u i<d)).card
  change |(count / N - (d-a)) - (((N:ℝ) - G.card) / N)* (w-(d-a))| ≤ ε
  rw [show (count / N - (d-a)) - (((N:ℝ) - G.card) / N)* (w-(d-a)) =
    (count - (G.card*(d-a) + ((N:ℝ)-G.card)*w))/N by field_simp; ring,
    abs_div,abs_of_pos nr,div_le_iff₀ nr]
  exact total

/-- All prefix discrepancies of a rational converge to the discrepancy of one
complete period of its eventual orbit. -/
theorem rational_discrepancy_limit (b : ℕ) (r : ℚ) {s L : ℕ} (lp : 0<L)
    (per : ∀ n, s≤n → shift b (r:ℝ) (n+L) = shift b r n) :
    Tendsto (radixDiscrepancy b r) atTop (𝓝 (disc (fun i => (b:ℝ)^(s+i)*r) L)) := by
  classical
  rw [Metric.tendsto_nhds]; intro ε he
  filter_upwards [eventually_ge_atTop s,eventually_gt_atTop 0,
    (tendsto_const_div_atTop_nhds_zero_nat ((s:ℝ)+L)).eventually_lt_const he] with N sn hn small
  rw [Real.dist_eq]
  apply lt_of_le_of_lt _ small
  have H := disc_mixture_bound (fun i => (b:ℝ)^i*r) (fun i => (b:ℝ)^(s+i)*r) N L (z:=1)
    zero_le_one (η:=((s:ℝ)+L)/N) (by
      intro a d ha had hd
      rw [one_mul,sub_sub_sub_cancel_right]
      exact cycle_frequency_error (shift b r) lp per sn hn a d)
  change |disc (fun i => (b:ℝ)^i*r) N - _| ≤ _
  simpa only [one_mul] using H

/-- With either sign of nonzero integer dilation and every rational translation,
the error in the weighted rational orbit discrepancy tends to zero over all cutoffs. -/
theorem translated_discrepancy {b p C : ℕ} (hb : 2≤b) (hp : p.Prime) (cop : b.Coprime p)
    (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) (m : ℤ) (hm : m≠0) (r : ℚ) :
    Tendsto (fun N => radixDiscrepancy b ((m:ℝ)*value b p c+r) N -
      zeroDensity p c N * limsup (radixDiscrepancy b r) atTop) atTop (𝓝 0) := by
  obtain ⟨s,q,L,qp,cq,lp,qden,per⟩ := rational_cycle b r
  let v (i : ℕ) := (b:ℝ)^(s+i)*r
  let u := shadow b p c m r
  have D : limsup (radixDiscrepancy b r) atTop = disc v L := (rational_discrepancy_limit b r lp per).limsup_eq
  have model : Tendsto (fun N => disc u N - zeroDensity p c N * disc v L) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]; intro ε he
    filter_upwards [shadow_uniform hb hp cop c cap m hm r qp cq lp qden per (half_pos he)] with N allI
    have hz : 0≤zeroDensity p c N := by
      have h : ((regularPositions p c N).card:ℝ) ≤ N := by
        exact_mod_cast (card_filter_le (range N) _).trans_eq (card_range _)
      exact div_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg _)
    rw [Real.dist_eq,sub_zero]
    exact (disc_mixture_bound u v N L hz allI).trans_lt (half_lt_self he)
  rw [D]
  change Tendsto (fun N => disc (fun i => (b:ℝ)^i*((m:ℝ)*value b p c+r)) N - _) _ _
  simpa only [u,zero_add,sub_add_sub_cancel] using (disc_sub_tendsto (shadow_tail hb hp c cap m r)).add model

/-- Multiplication of the two upper discrepancies, for every bounded signed
phase sequence and every rational translation. -/
theorem translated_limsup {b p C : ℕ} (hb : 2≤b) (hp : p.Prime) (cop : b.Coprime p)
    (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) (m : ℤ) (hm : m≠0) (r : ℚ) :
    limsup (radixDiscrepancy b ((m:ℝ)*value b p c+r)) atTop =
    limsup (radixDiscrepancy b (value b p c)) atTop * limsup (radixDiscrepancy b r) atTop := by
  let R := limsup (radixDiscrepancy b r) atTop
  let x := radixDiscrepancy b (value b p c)
  let y := radixDiscrepancy b ((m:ℝ)*value b p c+r)
  let z := fun N => x N * R
  have nonneg : 0≤R := le_limsup_of_frequently_le
    (Eventually.frequently (.of_forall fun N => (radix_discrepancy_bounds b r N).1))
    (isBoundedUnder_of_eventually_le (.of_forall fun N => (radix_discrepancy_bounds b r N).2))
  have low := isBoundedUnder_of_eventually_ge (f:=atTop) (.of_forall fun N =>
    (radix_discrepancy_bounds b (value b p c) N).1)
  have high := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall fun N =>
    (radix_discrepancy_bounds b (value b p c) N).2)
  have mono : Monotone (fun t : ℝ => t*R) := fun _ _ h => mul_le_mul_of_nonneg_right h nonneg
  have mult : limsup x atTop * R = limsup z atTop :=
    mono.map_limsup_of_continuousAt x (by fun_prop) high low.isCoboundedUnder_le
  change limsup y atTop = limsup x atTop * R
  rw [mult]
  let e := fun N => y N - z N
  have t : Tendsto e atTop (𝓝 0) := by
    have h := (translated_discrepancy hb hp cop c cap m hm r).sub
      ((discrepancy_sub_zeroDensity_tendsto hb hp cop c cap).mul_const R)
    simp only [zero_mul,sub_zero] at h
    apply h.congr; intro N; dsimp [e,z,y,x,R]; ring
  have lo := isBoundedUnder_of_eventually_ge (f:=atTop) (.of_forall fun N =>
    mul_nonneg (radix_discrepancy_bounds b (value b p c) N).1 nonneg)
  have hi := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall fun N =>
    mul_le_mul_of_nonneg_right (radix_discrepancy_bounds b (value b p c) N).2 nonneg)
  have add : z + e = y := by funext n; dsimp [e]; ring
  have h₁ := limsup_add_le (u:=z) (v:=e) lo hi t.isBoundedUnder_ge.isCoboundedUnder_le t.isBoundedUnder_le
  have h₂ := le_limsup_add (u:=z) (v:=e) hi lo.isCoboundedUnder_le t.isBoundedUnder_le t.isBoundedUnder_ge
  rw [add,t.limsup_eq,add_zero] at h₁
  rw [add,t.liminf_eq,add_zero] at h₂
  exact le_antisymm h₁ h₂

/-- Translation by one third of the three binary periodic phase examples. -/
theorem translated_third_examples (m : ℤ) (hm : m≠0) :
    let D (c : ℕ → ℤ) := limsup (radixDiscrepancy 2 ((m:ℝ)*value 2 3 c+1/3)) atTop
    D (fun j => if j%4=3 then 0 else 1) = 9/20 ∧
    D (fun j => if j%2=0 then 1 else 0) = 1/2 ∧
    D (fun j => if j%3=0 then 1 else 0) = 8/13 := by
  dsimp only
  have H (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ 1) :
      limsup (radixDiscrepancy 2 ((m:ℝ)*value 2 3 c+1/3)) atTop =
      limsup (radixDiscrepancy 2 (value 2 3 c)) atTop * (2/3) := by
    have h := translated_limsup (b:=2) (p:=3) (by decide) (by decide) (by decide) c cap m hm (1/3)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,show limsup (radixDiscrepancy 2 (1/3)) atTop = 2/3 from third_discrepancy_sharp.2] using h
  obtain ⟨A,B,C⟩ := binary_three_periods
  dsimp only at A B C
  constructor
  · rw [H _ (fun j => by split <;> decide),A]; norm_num
  constructor
  · rw [H _ (fun j => by split <;> decide),B]; norm_num
  · rw [H _ (fun j => by split <;> decide),C]; norm_num

end NormalityChecker.SignedPhases
