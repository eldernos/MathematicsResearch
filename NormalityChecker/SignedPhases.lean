module

public import NormalityChecker.PeriodicWeights
public import NormalityChecker.Concentration
public import NormalityChecker.IndexedExpansion

/-! Power-boundary expansions with signed, bounded integer phase coefficients. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.SignedPhases

/-- The signed insertion that changes the phase from `c j` to `c (j+1)`. -/
def jump (p : ℕ) (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => c 0
  | j+1 => c (j+1)-p*c j

def coeff (p : ℕ) (c : ℕ → ℤ) (j : ℕ) : ℚ := (jump p c j:ℚ)/(p:ℚ)^j
noncomputable def value (b p : ℕ) (c : ℕ → ℤ) := ∑' j, (coeff p c j:ℝ)/(b:ℝ)^(p^j)

def trunc (b p : ℕ) (c : ℕ → ℤ) (j : ℕ) := ∑ i∈range (j+1),coeff p c i/(b:ℚ)^(p^i)
def pre (b p : ℕ) (c : ℕ → ℤ) (n : ℕ) := if n=0 then 0 else (b:ℚ)^n*trunc b p c (Nat.log p n)

private lemma euler_gap {b p : ℕ} (hb : 2≤b) (hp : p.Prime) (cop : b.Coprime p) (k : ℕ) :
    ∃ z : ℤ, (b:ℚ)^(p^(k+1)-p^k)=1+(p:ℚ)^k*z := by
  have diff : p^(k+1)-p^k=p^k*(p-1) := by rw [pow_succ,Nat.mul_sub,Nat.mul_one]
  have m := Nat.ModEq.pow_totient (cop.pow_right (k+1))
  rw [Nat.totient_prime_pow_succ hp] at m
  have d := (pow_dvd_pow p (Nat.le_succ k)).trans ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp m.symm)
  obtain ⟨v,hv⟩ := d
  refine ⟨v,?_⟩; rw [diff]; exact_mod_cast (show b^(p^k*(p-1))=1+p^k*v by have := Nat.one_le_pow (p^k*(p-1)) b (by omega); omega)

/-- After clearing completed pairs, the current coefficient alone controls the denominator. -/
theorem phase_at_boundary {b p : ℕ} (hb : 2≤b) (hp : p.Prime) (cop : b.Coprime p)
    (c : ℕ → ℤ) (k : ℕ) : ∃ z : ℤ,
    (b:ℚ)^(p^k)*trunc b p c k=z+(c k:ℚ)/(p:ℚ)^k := by
  induction k with
  | zero => refine ⟨0,?_⟩; simp [trunc,coeff,jump]; field_simp [show (b:ℚ)≠0 by exact_mod_cast (by omega : b≠0)]
  | succ k ih =>
    obtain ⟨z,old⟩ := ih; obtain ⟨w,lift⟩ := euler_gap hb hp cop k
    let gap := p^(k+1)-p^k
    have add : gap+p^k=p^(k+1) := Nat.sub_add_cancel (Nat.pow_le_pow_right hp.pos (Nat.le_succ _))
    have scale : (b:ℚ)^(p^(k+1))=(b:ℚ)^gap*(b:ℚ)^(p^k) := by rw [← pow_add,add]
    have next : trunc b p c (k+1)=trunc b p c k+coeff p c (k+1)/(b:ℚ)^(p^(k+1)) := sum_range_succ ..
    refine ⟨(b:ℤ)^gap*z+w*c k,?_⟩
    have bn : (b:ℚ)≠0 := by exact_mod_cast (by omega : b≠0)
    have pn : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
    rw [next,mul_add,show (b:ℚ)^(p^(k+1))*(coeff p c (k+1)/(b:ℚ)^(p^(k+1)))=coeff p c (k+1) by field_simp,scale,mul_assoc,old,mul_add]; push_cast
    dsimp only [coeff,jump]; push_cast; rw [pow_succ]; change (b:ℚ)^gap*z+(b:ℚ)^gap*_+_=_
    rw [show (b:ℚ)^gap*(c k/(p:ℚ)^k)=(1+(p:ℚ)^k*w)*(c k/(p:ℚ)^k) by rw [← lift]]
    field_simp; ring

private lemma tail {b p : ℕ} (hb : 2≤b) (hp : p.Prime) (c : ℕ → ℤ) {C : ℕ}
    (cap : ∀ j,(c j).natAbs≤C) : Tendsto (fun n => (b:ℝ)^n*value b p c-(pre b p c n:ℝ)) atTop (𝓝 0) := by
  have pp : 0<(p:ℝ) := by exact_mod_cast hp.pos
  let I (n : ℕ) := if n=0 then ∅ else range (Nat.log p n+1)
  have mem (n i : ℕ) : i∈I n ↔ p^i≤n := by
    by_cases z : n=0
    · simp [I,z,hp.ne_zero]
    · simp [I,z,Nat.le_log_iff_pow_le hp.one_lt z]
  have small (ε : ℝ) (pos : 0<ε) : ∃ N : ℕ, ∀ i, N≤p^i → |(coeff p c i:ℝ)|≤ε := by
    obtain ⟨N,hN⟩ := exists_nat_gt (((p:ℝ)+1)*C/ε)
    have ac (j : ℕ) : |(c j:ℝ)|≤C := by rw [← Int.cast_abs,← Int.natCast_natAbs]; exact_mod_cast cap j
    refine ⟨N,fun i hi => ?_⟩; simp only [coeff,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_natCast,abs_div,abs_of_pos (by positivity : 0<(p:ℝ)^i)]
    rw [div_le_iff₀ (by positivity)]; have bd := (div_lt_iff₀ pos).mp (hN.trans_le (by exact_mod_cast hi : (N:ℝ)≤(p:ℝ)^i))
    have top : |(jump p c i:ℝ)|≤((p:ℝ)+1)*C := by
      cases i with
      | zero => change |(c 0:ℝ)|≤_; nlinarith [ac 0,mul_nonneg pp.le (Nat.cast_nonneg (α:=ℝ) C)]
      | succ i => simp only [jump,Int.cast_sub,Int.cast_mul,Int.cast_natCast]; apply (abs_sub ..).trans
                  rw [abs_mul,abs_of_pos pp]; nlinarith [ac (i+1),mul_le_mul_of_nonneg_left (ac i) (Nat.cast_nonneg (α:=ℝ) p)]
    linarith
  have H := indexed_shift_error_signed hb (fun i => p^i) (Nat.pow_right_injective hp.two_le) (coeff p c) small I mem
  apply H.congr'; filter_upwards [eventually_ne_atTop 0] with n hn
  simp [value,pre,I,hn,trunc]

private lemma within {b p : ℕ} (hb : 2≤b) (hp : p.Prime) (cop : b.Coprime p)
    (c : ℕ → ℤ) {k n : ℕ} (lo : p^k≤n) (hi : n<p^(k+1)) : ∃ z : ℤ,
    pre b p c n=z+(b:ℚ)^(n-p^k)*c k/(p:ℚ)^k := by
  obtain ⟨z,bd⟩ := phase_at_boundary hb hp cop c k
  refine ⟨(b:ℤ)^(n-p^k)*z,?_⟩; rw [pre,ite_eq_right (Nat.ne_of_gt ((pow_pos hp.pos k).trans_le lo)),Nat.log_eq_of_pow_le_of_lt_pow lo hi]
  conv_lhs => rw [← Nat.sub_add_cancel lo,pow_add,mul_assoc,bd]
  push_cast; ring

private lemma phase_den {b p : ℕ} (hp : p.Prime) (cop : b.Coprime p) (j a : ℕ) (v : ℤ) :
    let y := (b:ℚ)^a*v/(p:ℚ)^j
    y.den∣p^j ∧ p^j∣v.natAbs*y.den := by
  let U : ℤ := (b:ℤ)^a*v
  let Q := p^j
  have qp : 0<Q := pow_pos hp.pos j
  let y := Rat.divInt U Q
  have eqn : y=(b:ℚ)^a*v/(p:ℚ)^j := by simp [y,U,Q,Rat.divInt_eq_div]
  rw [← eqn]; constructor
  · exact_mod_cast Rat.den_dvd U (Q:ℤ)
  · have H := (y.num_div_den); rw [eqn] at H
    have cross : (y.num:ℚ)*(Q:ℚ)=U*(y.den:ℚ) := by
      rw [← eqn] at H
      have H' : (y.num:ℚ)/y.den=(U:ℚ)/(Q:ℚ) := by simpa [U,Q] using H.trans eqn
      exact (div_eq_div_iff (by exact_mod_cast y.den_ne_zero) (by exact_mod_cast qp.ne')).mp H'
    have crossZ : y.num*(Q:ℤ)=U*y.den := by exact_mod_cast cross
    have dvd : Q∣U.natAbs*y.den := by refine ⟨y.num.natAbs,?_⟩; simpa only [Int.natAbs_mul,Int.natAbs_natCast,mul_comm] using (congrArg Int.natAbs crossZ).symm
    dsimp [U] at dvd; simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,mul_assoc] at dvd
    exact ((cop.symm.pow_left j).pow_right a).dvd_of_dvd_mul_left dvd

/-- A bounded signed phase sequence gives a normal value exactly when only finitely
many phases vanish. Each zero phase occupies a whole interval of proportional length. -/
theorem normal_iff_eventually_nonzero {b p C : ℕ} (hb : 2≤b) (hp : p.Prime)
    (cop : b.Coprime p) (c : ℕ → ℤ) (cap : ∀ j,(c j).natAbs≤C) :
    NormalIn b (value b p c) ↔ ∀ᶠ j in atTop, c j≠0 := by
  classical
  have htail := tail hb hp c cap
  constructor
  · contrapose!; intro often
    apply not_normal_of_prefix_hits (P:=fun n => (pre b p c n:ℝ)) (C:={0}) (η:=(1:ℝ)/p)
      (by have := hp.pos; positivity) htail
    rw [frequently_atTop] at often ⊢; intro N
    obtain ⟨k,hk,zero⟩ := often N
    let q := p^k
    have qp : 0<q := pow_pos hp.pos k
    have hq : k≤q := (Nat.lt_pow_self hp.two_le).le
    refine ⟨2*q,by omega,?_⟩
    have sub : Ico q (2*q) ⊆ (range (2*q)).filter (fun i => ∃ t∈({0}:Finset ℝ), ∃ z : ℤ, (pre b p c i:ℝ)=t+z) := by
      intro i hi; obtain ⟨lo,hi⟩ := mem_Ico.mp hi
      have top : i<p^(k+1) := hi.trans_le (by rw [pow_succ']; exact Nat.mul_le_mul_right _ hp.two_le)
      obtain ⟨z,id⟩ := within hb hp cop c lo top
      refine mem_filter.mpr ⟨mem_range.mpr hi,0,by simp,z,?_⟩
      simp only [zero,Int.cast_zero,mul_zero,zero_div,add_zero] at id; simp [id]
    have count := card_le_card sub; rw [Nat.card_Ico,show 2*q-q=q by omega] at count
    have realCount := (Nat.cast_le (α:=ℝ)).mpr count
    rw [div_le_div_iff₀ (by exact_mod_cast hp.pos) (by exact_mod_cast (show 0<2*q by omega))]
    push_cast; nlinarith [mul_le_mul_of_nonneg_right (show (2:ℝ)≤p by exact_mod_cast hp.two_le) (Nat.cast_nonneg (α:=ℝ) q),
      mul_le_mul_of_nonneg_right realCount (Nat.cast_nonneg (α:=ℝ) p)]
  · intro ev
    obtain ⟨J,good⟩ := eventually_atTop.mp ev
    apply normal_of_arithmetic_certificate (c:=p) (L:=p) (B:=p) hb hp.pos hp.one_lt _ _ htail
      (fixed_support_orbit_estimate hb hp.one_lt cop) 3
    intro u hu M η ηp
    obtain ⟨ul,ur⟩ := mem_Ico.mp hu
    filter_upwards [eventually_ge_atTop (max (C*M) (max J 2))] with k hk
    refine ⟨∅,by simp; positivity,?_⟩; intro l hl _
    let B := p^k
    let m := u*B+l
    let n := m*B
    let j := Nat.log p n
    have Bp : 0<B := pow_pos hp.pos k
    have mpos : 0<m := Nat.add_pos_left (Nat.mul_pos ul Bp) _
    have np : 0<n := Nat.mul_pos mpos Bp
    have lo : p^j≤n := Nat.pow_log_le_self _ np.ne'
    have hi : n<p^(j+1) := Nat.lt_pow_succ_log_self hp.one_lt _
    have k_le : k≤j := Nat.le_log_of_pow_le hp.one_lt (Nat.le_mul_of_pos_left B mpos)
    have km : max (C*M) (max J 2)≤k := hk
    have jnz : c j≠0 := good j (by omega)
    obtain ⟨z,id⟩ := within hb hp cop c lo hi
    let y := (b:ℚ)^(n-p^j)*c j/(p:ℚ)^j
    have e : (pre b p c n).den=y.den := by rw [id,Rat.intCast_add_den]
    obtain ⟨dv,recover⟩ := phase_den hp cop j (n-p^j) (c j)
    change M≤(pre b p c n).den ∧ _; rw [e]
    have cp : 0<(c j).natAbs := Int.natAbs_pos.mpr jnz
    have prod : C*M≤p^j := (show C*M≤j by omega).trans (Nat.lt_pow_self hp.two_le).le
    have low := (prod.trans (Nat.le_of_dvd (Nat.mul_pos cp y.pos) recover)).trans (Nat.mul_le_mul_right y.den (cap j))
    have tight : n≤B^3 := by
      have k2 : 2≤k := by omega
      have direct : m<(p*p)*B := by
        dsimp only [m]; calc u*B+l < (u+1)*B := by rw [Nat.succ_mul]; change l<B at hl; omega
                             _ ≤ _ := Nat.mul_le_mul_right B ur
      have pp : p*p≤B := by simpa [B,sq] using Nat.pow_le_pow_right hp.pos k2
      calc n ≤ ((p*p)*B)*B := Nat.mul_le_mul_right B direct.le
           _ ≤ (B*B)*B := by gcongr
           _ = B^3 := by ring
    refine ⟨Nat.le_of_mul_le_mul_left low (cp.trans_le (cap j)),⟨j,dv⟩,(Nat.le_of_dvd (pow_pos hp.pos j) dv).trans (lo.trans tight),?_⟩
    intro i hbi
    have dm : B∣p^(j+1) := pow_dvd_pow p (by omega)
    obtain ⟨a,ha⟩ := dm
    have endLt : n+i<p^(j+1) := by
      rw [ha,mul_comm B] at hi ⊢; change m*B<a*B at hi; have lt := Nat.lt_of_mul_lt_mul_right hi
      calc n+i < (m+1)*B := by rw [Nat.succ_mul]; dsimp only [n,B] at *; omega
           _ ≤ a*B := Nat.mul_le_mul_right B lt
    have same := Nat.log_eq_of_pow_le_of_lt_pow (lo.trans (Nat.le_add_right n i)) endLt
    change pre b p c (n+i)=(b:ℚ)^i*pre b p c n
    simp only [pre,ite_eq_right (by omega : n+i≠0),ite_eq_right np.ne',same,j,pow_add]; ring

end NormalityChecker.SignedPhases
