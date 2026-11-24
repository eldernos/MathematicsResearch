module

public import NormalityChecker.OrbitDifferencing
public import NormalityChecker.CertificateBlocks
public import NormalityChecker.StonehamOrbit

/-! Qualitative short-orbit cancellation for moduli supported on fixed primes. -/
@[expose] public section
open Finset Filter
open scoped Topology ComplexConjugate
namespace NormalityChecker

/-- Qualitative fixed-support consequence of Vandehey, Corollary 1.2. The modulus
may be any divisor of a power of `c`. The normalized estimate is uniform in the
reduced numerator and in all lengths `T` with `Q ≤ T^d`. -/
def SmoothOrbitEstimate (b c : ℕ) : Prop := ∀ d : ℕ, ∀ η : ℝ, 0<η → ∃ M : ℕ,
  ∀ (y : ℚ) (T : ℕ), M≤y.den → (∃ j : ℕ, y.den ∣ c^j) → y.den≤T^d →
    ‖∑ i ∈ range T, phase ((b:ℝ)^i*y)‖ ≤ η*T

private lemma factor_near {c K Q j : ℕ} (hc : 0<c) (hK : 0<K) (div : Q∣c^j) (low : K≤Q) :
    ∃ D, D∣Q ∧ K≤D ∧ D≤c*K := by
  induction Q using Nat.strong_induction_on with
  | ind Q ih =>
    by_cases small : Q≤c*K
    · exact ⟨Q,dvd_rfl,low,small⟩
    let r := Q.minFac
    have prime : r.Prime := Nat.minFac_prime (by intro eqn; rw [eqn] at small; exact small (Nat.mul_pos hc hK))
    have rd : r∣Q := Nat.minFac_dvd _
    have le := Nat.le_of_dvd hc (prime.dvd_of_dvd_pow (rd.trans div))
    have qpos := hK.trans_le low
    have eqn := Nat.div_mul_cancel rd
    have lower : K≤Q/r := by by_contra! h; exact small (by nlinarith [Nat.mul_le_mul h.le le])
    obtain ⟨D,hD,hlo,hhi⟩ := ih (Q/r) (Nat.div_lt_self qpos prime.one_lt) ((Nat.div_dvd_of_dvd rd).trans div) lower
    exact ⟨D,hD.trans (Nat.div_dvd_of_dvd rd),hlo,hhi⟩

private lemma scalar_den (x : ℚ) (n : ℕ) :
    x.den = ((n:ℚ)*x).den * n.gcd x.den := by
  have eqn := Rat.den_mul_den_eq_den_mul_gcd (n:ℚ) x
  simpa [Int.natAbs_mul,Nat.Coprime.gcd_mul_right_cancel _ x.reduced] using eqn

private lemma smooth_period {b c Q j : ℕ} (hb : 1<b) (hc : 1<c)
    (cop : b.Coprime c) (div : Q∣c^j) :
    0<orderOf (b:ZMod Q) ∧ orderOf (b:ZMod Q) ≤ Q := by
  have qpos := Nat.pos_of_dvd_of_pos div (pow_pos (by omega : 0<c) _)
  let : NeZero Q := ⟨qpos.ne'⟩
  have bound := fixed_support_order_bound hb hc cop div
  exact ⟨Nat.pos_of_ne_zero (by intro zero; rw [zero,mul_zero] at bound; omega),by simpa [ZMod.card] using orderOf_le_card_univ (x:=(b:ZMod Q))⟩

/-- The denominator removed by a stride difference is between the chosen divisor
and a constant times the stride. Both bounds hold for every pair of translates. -/
private lemma difference_den {b c j D a t : ℕ} (hb : 1<b) (hc : 1<c)
    (cop : b.Coprime c) (y : ℚ) (div : y.den∣c^j) (dD : D∣y.den) (at' : a<t) :
    let v := orderOf (b:ZMod D)
    let m := b^(t*v) - b^(a*v)
    ∃ g : ℕ, D≤g ∧ g≤(b^(c^2).totient-1)*(t*v) ∧ y.den=((m:ℚ)*y).den*g := by
  let v := orderOf (b:ZMod D)
  let r := (t-a)*v
  have vp := (smooth_period hb hc cop (dD.trans div)).1
  have split : t*v=r+a*v := by dsimp [r]; rw [← Nat.add_mul,Nat.sub_add_cancel at'.le]
  have one : 1≤b^r := Nat.one_le_pow _ _ (by omega)
  have diff : b^(t*v)-b^(a*v)=(b^r-1)*b^(a*v) := by rw [split,pow_add,Nat.sub_mul,one_mul]
  let g := (b^r-1).gcd y.den
  have gd : g∣y.den := Nat.gcd_dvd_right ..
  have gd' : g∣b^r-1 := Nat.gcd_dvd_left ..
  have powD : (b:ZMod D)^r=1 := by dsimp [r,v]; rw [Nat.mul_comm,pow_mul,pow_orderOf_eq_one,one_pow]
  have divD : D∣b^r-1 := (ZMod.natCast_eq_zero_iff ..).mp (by rw [Nat.cast_sub one,Nat.cast_pow,powD,Nat.cast_one,sub_self])
  have gp := Nat.pos_of_dvd_of_pos gd y.pos
  have powG : (b:ZMod g)^r=1 := by
    have z := (ZMod.natCast_eq_zero_iff ..).mpr gd'
    rw [Nat.cast_sub one,Nat.cast_pow,Nat.cast_one,sub_eq_zero] at z; exact z
  have ordle := Nat.le_of_dvd (Nat.mul_pos (Nat.sub_pos_of_lt at') vp) (orderOf_dvd_of_pow_eq_one powG)
  have co := (Nat.Coprime.of_dvd_right div (cop.pow_right j)).pow_left (a*v)
  refine ⟨g,Nat.le_of_dvd gp (Nat.dvd_gcd divD dD), (fixed_support_order_bound hb hc cop (gd.trans div)).trans ?_,?_⟩
  · exact Nat.mul_le_mul_left _ (ordle.trans (Nat.mul_le_mul_right _ (Nat.sub_le ..)))
  · have eqn := scalar_den y (b^(t*v)-b^(a*v))
    change y.den = ((↑(b^(t*v)-b^(a*v)):ℚ)*y).den*g
    simpa only [diff,co.gcd_mul_right_cancel,g] using eqn

private lemma orbit_repr (b : ℕ) (y : ℚ) [NeZero y.den] (i : ℕ) :
    phase ((b:ℝ)^i*y) = ZMod.stdAddChar ((b:ZMod y.den)^i*(y.num:ZMod y.den)) := by
  have eqn := ZMod.stdAddChar_coe (N:=y.den) ((b:ℤ)^i*y.num)
  push_cast at eqn
  rw [eqn,phase,Rat.cast_def]; congr 1; push_cast; ring

private lemma long_orbit {b c : ℕ} (hb : 1<b) (hc : 1<c) (cop : b.Coprime c)
    {η : ℝ} (pos : 0<η) : ∃ M : ℕ, ∀ (y : ℚ) (j T : ℕ), M≤y.den → y.den∣c^j →
    ‖∑ i∈range T,phase ((b:ℝ)^i*y)‖ ≤ η*T + (η+1)*y.den := by
  let C := b^(c^2).totient-1
  have cpos : 0<C := Nat.sub_pos_of_lt (one_lt_pow₀ hb (Nat.totient_pos.mpr (pow_pos (by omega : 0<c) 2)).ne')
  let δ := η/(2*C)
  have dp : 0<δ := by dsimp [δ]; positivity
  obtain ⟨H,large⟩ := exists_nat_gt (1/δ^2)
  have hp : 0<H := by exact_mod_cast (lt_trans (by positivity : (0:ℝ)<1/δ^2) large)
  obtain ⟨m,hm⟩ := exists_nat_gt (2*H/δ)
  refine ⟨max (C*H) m,?_⟩
  intro y j T low div
  let Q := y.den
  let : NeZero y.den := ⟨y.den_ne_zero⟩
  let : NeZero Q := ⟨y.den_ne_zero⟩
  let P := orderOf (b:ZMod Q)
  obtain ⟨pp,pq⟩ := smooth_period hb hc cop div
  have per := fixed_support_order_bound hb hc cop div
  have fit : H≤P := Nat.le_of_mul_le_mul_left (((le_max_left ..).trans low).trans per) cpos
  let f (i : ℕ) := phase ((b:ℝ)^i*y)
  have unit : IsUnit (y.num:ZMod Q) := (ZMod.isUnit_intCast_iff_isCoprime ..).mpr
    (Int.isCoprime_iff_nat_coprime.mpr y.reduced.symm)
  have sum := unit_orbit_bound b y.num unit (T:=P) le_rfl pq hp fit dp (by linarith only [(div_lt_iff₀ (sq_pos_of_pos dp)).mp large])
  have bound : ‖∑ i∈range P,f i‖ ≤ η*P := by
    have eqn (i : ℕ) : f i=phase ((y.num:ℝ)*b^i/Q) := by dsimp [f,Q]; rw [Rat.cast_def]; congr 1; ring
    simp_rw [eqn]; apply sum.trans
    have ml : (m:ℝ)≤Q := by exact_mod_cast (le_max_right _ _).trans low
    have hr : (Q:ℝ)≤C*P := by exact_mod_cast per
    have large' := (lt_of_lt_of_le hm ml)
    rw [div_lt_iff₀ dp] at large'
    have id : 2*δ*C=η := by dsimp [δ]; field_simp
    nlinarith only [large',mul_le_mul_of_nonneg_left hr dp.le,congrArg (fun z : ℝ => z*P) id]
  have periodic (l i : ℕ) : f (l*P+i)=f i := by
    dsimp only [f]; rw [orbit_repr,orbit_repr,pow_add,Nat.mul_comm l P,pow_mul,pow_orderOf_eq_one,one_pow,one_mul]
  have hT : T≤(T/P+1)*P := by simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ T pp).le
  have H := prefix_block_bound f (fun i => (norm_phase _).le) (s:=0) (B:=P) pp hT ∅ pos.le (fun l _ _ => by simpa only [zero_add,periodic] using bound)
  simp only [zero_add,card_empty,Nat.cast_zero,zero_add,one_mul] at H
  apply H.trans; push_cast
  have le : ((T/P:ℕ):ℝ)*P ≤ T := by exact_mod_cast Nat.div_mul_le_self T P
  have pq' : (P:ℝ)≤y.den := by exact_mod_cast pq
  nlinarith only [mul_le_mul_of_nonneg_left le pos.le,mul_le_mul_of_nonneg_left pq' pos.le,pq']

private lemma scale_orbit {b c : ℕ} (hb : 1<b) (hc : 1<c) (cop : b.Coprime c)
    (d : ℕ) : ∀ η : ℝ, 0<η → ∃ M : ℕ, ∀ (K T j : ℕ) (y : ℚ), M≤K → M≤y.den →
      y.den∣c^j → y.den≤K^(d+2) → K^3≤T → ‖∑ i∈range T, phase ((b:ℝ)^i*y)‖ ≤ η*T := by
  induction d with
  | zero =>
    intro η pos
    let δ := min 1 (η/2)
    have dp : 0<δ := lt_min zero_lt_one (half_pos pos)
    obtain ⟨m,long⟩ := long_orbit hb hc cop dp
    obtain ⟨n,hn⟩ := exists_nat_gt (4/η)
    refine ⟨max m n,?_⟩; intro K T j y kbig qbig div top length
    apply (long y j T ((le_max_left ..).trans qbig) div).trans
    have scale : (4:ℝ)≤η*K := by
      have H : (n:ℝ)≤K := by exact_mod_cast (le_max_right _ _).trans kbig
      linarith only [(div_lt_iff₀ pos).mp (hn.trans_le H)]
    have qr : (y.den:ℝ)≤(K:ℝ)^2 := by exact_mod_cast top
    have tr : (K:ℝ)^3≤T := by exact_mod_cast length
    have e := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (η/2)) (Nat.cast_nonneg T)
    have e' := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (η/2)) (Nat.cast_nonneg y.den)
    dsimp [δ]; nlinarith only [e,e',qr,mul_le_mul_of_nonneg_right scale (sq_nonneg (K:ℝ)),mul_le_mul_of_nonneg_left tr pos.le]
  | succ d ih =>
    -- Choose the number of translates before the scale. Every nontrivial
    -- pair correlation will have denominator in the previous induction range.
    intro η pos
    let δ := η/3
    have dp : 0<δ := by dsimp [δ]; positivity
    obtain ⟨m,prev⟩ := ih (min η (δ^2)) (lt_min pos (sq_pos_of_pos dp))
    obtain ⟨H,large⟩ := exists_nat_gt (1/δ^2)
    have hH : 0<H := by exact_mod_cast (lt_trans (by positivity : (0:ℝ)<1/δ^2) large)
    obtain ⟨z,hz⟩ := exists_nat_gt (2*H*c/δ)
    let C := b^(c^2).totient-1
    refine ⟨max (max (m+1) z) (m*(C*(H*c))),?_⟩
    intro K T j y kbig qbig div top length
    have mk : m+1≤K := ((le_max_left ..).trans (le_max_left ..)).trans kbig
    have mq : m≤y.den := (Nat.le_succ m).trans (((le_max_left ..).trans (le_max_left ..)).trans qbig)
    have kp : 0<K := by omega
    by_cases small : y.den≤K^(d+2)
    · exact (prev K T j y (by omega) mq div small length).trans (mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity))
    have high : K^2<y.den := (Nat.pow_le_pow_right kp (by omega : 2≤d+2)).trans_lt (lt_of_not_ge small)
    obtain ⟨D,dD,dlo,dhi⟩ := factor_near (by omega : 0<c) kp div ((show K≤K^2 by simpa using Nat.pow_le_pow_right kp (by decide : 1≤2)).trans high.le)
    let v := orderOf (b:ZMod D)
    have vcap : v≤c*K := (smooth_period hb hc cop (dD.trans div)).2.trans dhi
    have edge : 2*(H:ℝ)*v ≤ δ*T := by
      have zK : (z:ℝ)≤K := by exact_mod_cast ((le_max_right _ _).trans (le_max_left ..)).trans kbig
      have vr : (v:ℝ)≤c*K := by exact_mod_cast vcap
      have ksq : (K:ℝ)^2≤T := by exact_mod_cast (Nat.pow_le_pow_right kp (by decide : 2≤3)).trans length
      nlinarith only [mul_le_mul_of_nonneg_left vr (show (0:ℝ)≤2*H by positivity),
        mul_le_mul_of_nonneg_right ((div_lt_iff₀ dp).mp (hz.trans_le zK)).le (Nat.cast_nonneg K),mul_le_mul_of_nonneg_left ksq dp.le]
    apply (stride_cancellation (fun i => phase ((b:ℝ)^i*y)) (fun _ => norm_phase _) hH dp
      (by linarith only [(div_lt_iff₀ (sq_pos_of_pos dp)).mp large]) edge ?_).trans_eq
    · dsimp [δ]; ring
    intro a t at' th
    let n := b^(t*v)-b^(a*v)
    let w := (n:ℚ)*y
    obtain ⟨g,dg,cap,id⟩ := difference_den hb hc cop y div dD at'
    change y.den=w.den*g at id
    have kg := dlo.trans dg
    have top' : w.den≤K^(d+2) := by
      apply Nat.le_of_mul_le_mul_right _ kp
      calc w.den*K ≤ w.den*g := Nat.mul_le_mul_left _ kg
           _ = y.den := id.symm
           _ ≤ K^(d+2)*K := by simpa [show d+1+2=d+2+1 by omega,pow_succ] using top
    have low' : m≤w.den := by
      by_contra! h
      have gcap : g≤(C*(H*c))*K := cap.trans (by dsimp [C]; calc
        _ ≤ (b^(c^2).totient-1)*(H*(c*K)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul th.le vcap)
        _ = _ := by ring)
      have hK : m*(C*(H*c))≤K := (le_max_right ..).trans kbig
      have H' := (Nat.mul_le_mul h.le gcap).trans_eq (show m*((C*(H*c))*K)=(m*(C*(H*c)))*K by ring)
      rw [id,sq] at high; exact high.not_ge (H'.trans (Nat.mul_le_mul_right K hK))
    have wdiv : w.den∣c^j := (dvd_of_mul_right_dvd (id ▸ dvd_rfl : w.den*g ∣ y.den)).trans div
    have result := prev K T j w (by omega) low' wdiv top' length
    have cover : (b:ℕ)^(a*v)≤b^(t*v) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ at'.le)
    have row (i : ℕ) : phase ((b:ℝ)^(i+t*v)*y)*conj (phase ((b:ℝ)^(i+a*v)*y)) = phase ((b:ℝ)^i*w) := by
      rw [phase_conj,← phase_add]; congr 1; dsimp [w,n]; push_cast [Nat.cast_sub cover]; rw [pow_add,pow_add]; ring
    simp_rw [row]; exact result.trans (mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity))

/-- For a fixed prime support and fixed polynomial exponent, the normalized sum tends
to zero uniformly. This qualitative consequence has an elementary differencing
proof here. It does not give Vandehey's quantitative savings. -/
theorem fixed_support_orbit_estimate {b c : ℕ} (hb : 1<b) (hc : 1<c)
    (cop : b.Coprime c) : SmoothOrbitEstimate b c := by
  intro d η pos
  obtain ⟨M,scale⟩ := scale_orbit hb hc cop (6*d) η pos
  let m := max 1 M
  refine ⟨max (8^(m*d+1)) M,?_⟩
  intro y T low ⟨j,div⟩ top
  have lt : 8^(m*d)<y.den := (Nat.pow_lt_pow_right (by decide : 1<8) (Nat.lt_succ_self _)).trans_le ((le_max_left ..).trans low)
  have tlo : 8^m≤T := by
    by_contra! h; rw [pow_mul] at lt
    exact lt.not_ge (top.trans (Nat.pow_le_pow_left h.le _))
  let k := Nat.log 8 T
  let K := 2^k
  have mk : m≤k := Nat.le_log_of_pow_le (by decide) tlo
  have mk' : M≤K := ((le_max_right 1 M).trans mk).trans (Nat.lt_two_pow_self.le)
  have kp : 2≤K := by simpa [K] using Nat.pow_le_pow_right (by decide : 0<2) ((le_max_left 1 M).trans mk)
  have eqn : K^3=8^k := by dsimp [K]; rw [← pow_mul,Nat.mul_comm,pow_mul]; rfl
  have hp : 8≤K^3 := Nat.pow_le_pow_left kp 3
  have tr := Nat.lt_pow_succ_log_self (by decide : 1<8) T
  change T<8^(k+1) at tr; rw [pow_succ,← eqn] at tr
  have hi : T≤K^6 := tr.le.trans ((Nat.mul_le_mul_left _ hp).trans_eq (by ring))
  apply scale K T j y mk' ((le_max_right ..).trans low) div _
    (eqn ▸ Nat.pow_log_le_self 8 (by have := (pow_pos (by decide : 0<8) m).trans_le tlo; omega))
  exact (top.trans ((Nat.pow_le_pow_left hi d).trans_eq (pow_mul K 6 d).symm)).trans (Nat.pow_le_pow_right (by omega) (by omega))

end NormalityChecker
