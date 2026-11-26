module

public import NormalityChecker.AlternateBaseWindows
public import NormalityChecker.StonehamPolynomial

/-! Alternate mixed radices for polynomial images of the standard Stoneham series. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.AlternateBase
open StonehamPolynomial

/-- All insertion locations in every relevant degree avoid the open gap. -/
def PowerGap (c d U V : ℕ) : Prop :=
  ∀ k r : ℕ, r ≤ d → ∀ j : Fin r → ℕ,
    (∑ i, c^(j i+1)) ≤ U*c^k ∨ V*c^k ≤ ∑ i, c^(j i+1)

private theorem gap_below_multiple {ι : Type*} [DecidableEq ι] {c : ℕ} (hc : 1<c)
    (j : ι → ℕ) (s : Finset ι) :
    ∀ k M : ℕ, c^(k+s.card) ∣ M → (∑ i ∈ s, c^(j i)) < M →
      (∑ i ∈ s, c^(j i)) + c^k ≤ M := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro k M divides below
    by_cases all : ∀ i∈s, k ≤ j i
    · have dv := Finset.dvd_sum (s:=s) (fun i hi => pow_dvd_pow c (all i hi))
      have dm := (pow_dvd_pow c (Nat.le_add_right k s.card)).trans divides
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt below) (Nat.dvd_sub dm dv)
      omega
    · push Not at all
      obtain ⟨i,mem,small⟩ := all
      have card := card_erase_add_one mem
      have sum := sum_erase_add (s:=s) (fun i => c^(j i)) mem
      have dv : c^(k+1+(s.erase i).card) ∣ M := by
        rwa [show k+1+(s.erase i).card = k+s.card by omega]
      have bound := ih (s.erase i) (erase_ssubset mem) (k+1) M dv (by omega)
      have less := Nat.pow_lt_pow_right hc small
      rw [pow_succ] at bound
      have := Nat.mul_le_mul_left (c^k) (show 2≤c by omega)
      omega

/-- A normalized gap valid in every degree at most d, including composite c. -/
theorem universal_gap {c : ℕ} (hc : 1<c) (d : ℕ) : PowerGap c d (c^d-1) (c^d) := by
  intro k r rd j
  by_cases h : c^d*c^k ≤ ∑ i, c^(j i+1)
  · exact Or.inr h
  apply Or.inl
  have dvd : c^(k+(univ : Finset (Fin r)).card) ∣ c^d*c^k := by
    rw [card_univ,Fintype.card_fin,← pow_add,add_comm d k]
    exact pow_dvd_pow c (Nat.add_le_add_left rd _)
  have bound := gap_below_multiple hc (fun i => j i+1) univ k _ dvd (lt_of_not_ge h)
  rw [Nat.sub_mul,one_mul]; omega

/-- When the degree is smaller than c, each coordinate is either at most c^k
or already at least the next power. -/
theorem coordinate_gap (c d : ℕ) (hc : 1<c) : PowerGap c d d c := by
  intro k r rd j
  by_cases all : ∀ i, j i+1 ≤ k
  · left
    calc _ ≤ ∑ _ : Fin r, c^k := sum_le_sum fun i _ => Nat.pow_le_pow_right (by omega) (all i)
         _ ≤ _ := by simpa using Nat.mul_le_mul_right (c^k) rd
  · push Not at all
    obtain ⟨i,hi⟩ := all
    right
    calc c*c^k = c^(k+1) := (pow_succ' ..).symm
         _ ≤ c^(j i+1) := Nat.pow_le_pow_right (by omega) hi
         _ ≤ _ := single_le_sum (f:=fun i => c^(j i+1)) (fun _ _ => Nat.zero_le _) (mem_univ i)

private lemma axis_standard {b c : ℕ} (hc : 0<c) : axis b c c = (c:ℝ)*alpha b c := by
  rw [axis,alpha,← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [pow_succ' c,pow_succ' (c:ℝ),inv_pow]
  field_simp

private abbrev ones (r : ℕ) : Strides r := fun _ => 1
private abbrev params (r c : ℕ) : StonehamPolynomial.Vector r := fun _ => c

private lemma location {c r : ℕ} (j : Fin r → ℕ) :
    position c (ones r) (params r c) j = ∑ i, c^(j i+1) := by
  simp [position,stretch,ones,params,pow_succ']

private lemma clearance {c U r : ℕ} (hc : 1<c) {l : ℝ} (hl : 0<l) :
    ∀ᶠ k : ℕ in atTop, (r*(Nat.log c (U*c^k)+1):ℕ) ≤ l*(c:ℝ)^k := by
  have Ule : U ≤ c^U := (Nat.lt_pow_self hc).le
  have logs (k : ℕ) : Nat.log c (U*c^k) ≤ U+k := by
    rw [← Nat.log_pow hc (U+k),pow_add]
    exact Nat.log_monotone (Nat.mul_le_mul_right _ Ule)
  have tiny := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by exact_mod_cast hc : (1:ℝ)<c)).const_mul
    ((r:ℝ)*(U+2))
  simp only [pow_one,mul_zero] at tiny
  filter_upwards [eventually_ge_atTop 1,tiny.eventually_le_const hl] with k hk bound
  rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at bound
  apply le_trans _ bound
  have le : r*(Nat.log c (U*c^k)+1) ≤ r*(U+2)*k := by
    rw [mul_assoc]; apply Nat.mul_le_mul_left
    nlinarith [logs k,Nat.mul_le_mul_left U hk]
  exact_mod_cast le

private lemma prefix_below {b c r : ℕ} (hb : 1<b) (hc : 1<c) (E : ℕ) {y : ℝ}
    (tail : Tendsto (fun n => (b:ℝ)^n*y-(productPrefix b c (ones r) (params r c) n:ℝ))
      atTop (𝓝 0)) :
    0 ≤ (b:ℝ)^E*y-(productPrefix b c (ones r) (params r c) E:ℝ) := by
  let pref := productPrefix b c (ones r) (params r c)
  let S := active c (ones r) (params r c)
  have positive (i : Fin r) : 0 < params r c i := (by omega : 0<c)
  by_contra! neg
  obtain ⟨n,better,le⟩ := (((tendsto_order.mp tail).1 _ neg).and (eventually_ge_atTop E)).exists
  have sub : S E ⊆ S n := fun j hj => (mem_active hc positive).mpr (((mem_active hc positive).mp hj).trans le)
  have grow : (b:ℚ)^(n-E)*pref E ≤ pref n := by
    unfold pref productPrefix
    rw [mul_sum]
    calc _ = ∑ j ∈ S E, (b:ℚ)^(n-position c (ones r) (params r c) j) /
            (c:ℚ)^weight (stretch (ones r) j) := by
              apply sum_congr rfl; intro j hj
              have before := (mem_active hc positive).mp hj
              rw [← mul_div_assoc,← pow_add]
              congr 2; omega
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  have cast : (b:ℝ)^(n-E)*(pref E:ℝ) ≤ (pref n:ℝ) := by exact_mod_cast grow
  have eqn : (b:ℝ)^n*y = (b:ℝ)^(n-E)*((b:ℝ)^E*y) := by
    rw [← mul_assoc,← pow_add,Nat.sub_add_cancel le]
  have one := one_le_pow₀ (show (1:ℝ)≤b by exact_mod_cast hb.le) (n:=n-E)
  change (b:ℝ)^E*y-(pref E:ℝ) < (b:ℝ)^n*y-(pref n:ℝ) at better
  rw [eqn] at better
  linarith only [better,cast,mul_le_mul_of_nonpos_right one neg.le]

/-- The denominator c^r accounts for the standard starting index j=1.
The remaining denominator is that of the shifted, truncated product. -/
theorem power_zero_windows {b c a d U V r : ℕ} (hb : 1<b) (hc : 1<c)
    (rd : r≤d) (gap : PowerGap c d U V) (uv : U<V) {l h : ℝ} (hl : 0<l)
    (clear : (U:ℝ) ≤ a*l)
    (valid : h*Real.log (b^a*c : ℕ) ≤ V*Real.log b) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, l*(c:ℝ)^k≤n → (n:ℝ)<h*c^k →
      shift (b^a*c) (alpha b c ^ r) n < ε := by
  have bp : (0:ℝ)<b := by exact_mod_cast (by omega : 0<b)
  have cp : (0:ℝ)<c := by exact_mod_cast (by omega : 0<c)
  let B := b^a*c
  have Bp : (0:ℝ)<B := by dsimp [B]; positivity
  have B1 : 1 < B := by
    dsimp [B]; exact hc.trans_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _))
  have logB := Real.log_pos (show (1:ℝ)<B by exact_mod_cast B1)
  let A (k : ℕ) := U*c^k
  let E (k : ℕ) := V*c^k-1
  let pref := productPrefix b c (ones r) (params r c)
  let y := (axis b c c)^r
  have yval : y = (c:ℝ)^r*(alpha b c)^r := by simp [y,axis_standard (by omega : 0<c),mul_pow]
  have tail : Tendsto (fun e => (b:ℝ)^e*y-(pref e:ℝ)) atTop (𝓝 0) := by
    simpa [y,pref,ones,params] using product_tail hb hc (e:=ones r) (m:=params r c) (fun _ => (by omega : 0<c))
  have grow : Tendsto E atTop atTop := by
    apply tendsto_atTop.mpr
    intro t
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hc).eventually_ge_atTop (t+1)] with k hk
    have := Nat.le_mul_of_pos_left (c^k) (show 0<V by omega)
    dsimp [E]; omega
  intro ε pos
  have small := (Metric.tendsto_atTop.mp (tail.comp grow)) (ε/(b:ℝ)) (div_pos pos bp)
  obtain ⟨K,hK⟩ := small
  filter_upwards [eventually_ge_atTop K,clearance (U:=U) (r:=r) hc hl] with k hk enough n lower upper
  have qpos : 0<c^k := pow_pos (by omega) _
  have ae : A k ≤ E k := by
    have := Nat.mul_lt_mul_of_pos_right uv qpos
    dsimp [A,E]; omega
  have e1 : E k+1=V*c^k := Nat.sub_add_cancel (Nat.mul_pos (by omega) qpos)
  have first : A k ≤ a*n := by
    have t := (mul_le_mul_of_nonneg_right clear (pow_nonneg cp.le k)).trans
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left lower (Nat.cast_nonneg a))
    exact_mod_cast t
  have last : (B:ℝ)^n ≤ (b:ℝ)^(E k+1) := by
    apply (Real.log_le_log_iff (pow_pos Bp _) (pow_pos bp _)).mp
    rw [Real.log_pow,Real.log_pow,e1]; push_cast
    calc (n:ℝ)*Real.log B ≤ h*c^k*Real.log B := mul_le_mul_of_nonneg_right upper.le logB.le
         _ = (h*Real.log B)*c^k := by ring
         _ ≤ _ := by simpa [B,mul_right_comm] using mul_le_mul_of_nonneg_right valid (pow_nonneg cp.le k)
  let R := pref (A k)
  have follow : pref (E k) = (b:ℚ)^(E k-A k)*R := by
    have f := prefix_follows (b:=b) hc (e:=ones r) (m:=params r c) (fun _ => (by omega : 0<c))
      (n:=A k) (i:=E k-A k) (by
        intro j after
        rw [location] at *
        rcases gap k r rd j with before|later
        · exact False.elim (after.not_ge before)
        · dsimp [E]; omega)
    simpa [Nat.add_sub_of_le ae,pref,R] using f
  obtain ⟨q,hq⟩ : R.den ∣ c^(r*Nat.log c (A k)) := denominator_dvd (by omega) _ _
  let D := r*Nat.log c (A k)
  have budget : D+r ≤ n := by
    dsimp [D,A]
    rw [← Nat.mul_succ]
    exact_mod_cast enough.trans lower
  let z : ℤ := (b:ℤ)^(a*n-A k)*(c:ℤ)^(n-(D+r))*q*R.num
  have de : (c:ℝ)^D = (R.den:ℝ)*q := by exact_mod_cast hq
  have cross : (R.den:ℝ)*(R:ℝ)=R.num := by exact_mod_cast Rat.den_mul_eq_num R
  have qp : (q:ℝ) ≠ 0 := fun eqn => (pow_pos cp D).ne' (by simpa [eqn] using de)
  have model : (B:ℝ)^n*(pref (E k):ℝ) / ((b:ℝ)^(E k)*(c:ℝ)^r) = z := by
    rw [follow]; push_cast
    simp only [B,Nat.cast_mul,Nat.cast_pow,mul_pow,← pow_mul,z,Int.cast_mul,Int.cast_pow,
      Int.cast_natCast,pow_sub₀ _ bp.ne' ae,pow_sub₀ _ bp.ne' first,
      pow_sub₀ _ cp.ne' budget,pow_add,de]
    field_simp [qp]
    linear_combination cross
  let scale := (B:ℝ)^n / ((b:ℝ)^(E k)*(c:ℝ)^r)
  have sp : 0≤scale := by dsimp [scale]; positivity
  have su : scale ≤ b := by
    rw [div_le_iff₀ (by positivity : 0<(b:ℝ)^(E k)*(c:ℝ)^r)]
    rw [pow_succ'] at last
    calc _ ≤ _ := last
         _ ≤ _ := by
            have := one_le_pow₀ (show (1:ℝ)≤c by exact_mod_cast hc.le) (n:=r)
            nlinarith only [mul_le_mul_of_nonneg_left this (mul_nonneg bp.le (pow_nonneg bp.le (E k)))]
  have eqn : (B:ℝ)^n*alpha b c^r-z = scale*((b:ℝ)^(E k)*y-(pref (E k):ℝ)) := by
    rw [← model,yval]; dsimp [scale]; field_simp
  have nn : 0 ≤ (B:ℝ)^n*alpha b c^r-z := eqn ▸ mul_nonneg sp (prefix_below hb hc _ tail)
  change Int.fract ((B:ℝ)^n*alpha b c^r) < ε
  rw [← Int.fract_sub_intCast _ z]
  apply lt_of_le_of_lt (b:=(B:ℝ)^n*alpha b c^r-z)
  · rw [Int.fract]; linarith [show (0:ℝ)≤⌊(B:ℝ)^n*alpha b c^r-z⌋ by exact_mod_cast Int.floor_nonneg.mpr nn]
  rw [← abs_of_nonneg nn,eqn,abs_mul,abs_of_nonneg sp]
  have t := hK k hk
  simp only [Function.comp_apply,Real.dist_eq,sub_zero] at t
  exact (mul_le_mul_of_nonneg_right su (abs_nonneg _)).trans_lt (by
    linarith only [(lt_div_iff₀ bp).mp t, mul_comm (b:ℝ) |(b:ℝ)^(E k)*y-(pref (E k):ℝ)|])

private theorem integerWindows_of_zero {B c : ℕ} {x l h : ℝ}
    (w : ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, l*(c:ℝ)^k≤n → (n:ℝ)<h*c^k →
      shift B x n < ε) : IntegerWindows B c x l h := by
  intro ε pos
  filter_upwards [w ε pos] with k hk n lo up
  exact ⟨⌊(B:ℝ)^n*x⌋, (abs_of_nonneg (Int.fract_nonneg _)).trans_lt (hk n lo up)⟩

private theorem add_windows {B c : ℕ} {x y l h : ℝ}
    (wx : IntegerWindows B c x l h) (wy : IntegerWindows B c y l h) :
    IntegerWindows B c (x+y) l h := by
  intro ε pos
  filter_upwards [wx (ε/2) (half_pos pos), wy (ε/2) (half_pos pos)] with k hx hy n lo up
  obtain ⟨z,hz⟩ := hx n lo up
  obtain ⟨v,hv⟩ := hy n lo up
  refine ⟨z+v,?_⟩
  rw [Int.cast_add,mul_add,show (B:ℝ)^n*x+(B:ℝ)^n*y-(z+v) =
    ((B:ℝ)^n*x-z)+((B:ℝ)^n*y-v) by ring]
  exact (abs_add_le ..).trans_lt (by linarith)

private theorem mul_windows {B c : ℕ} {x l h : ℝ} (z : ℤ)
    (w : IntegerWindows B c x l h) : IntegerWindows B c (z*x) l h := by
  intro ε pos
  have den : 0 < |(z:ℝ)|+1 := by positivity
  filter_upwards [w (ε/(|(z:ℝ)|+1)) (div_pos pos den)] with k hk n lo up
  obtain ⟨v,hv⟩ := hk n lo up
  refine ⟨z*v,?_⟩
  rw [Int.cast_mul,show (B:ℝ)^n*(z*x)-z*v = z*((B:ℝ)^n*x-v) by ring,abs_mul]
  have le := (lt_div_iff₀ den).mp hv
  nlinarith only [le,abs_nonneg ((B:ℝ)^n*x-v)]

private theorem sum_windows {ι : Type*} {B c : ℕ} {l h : ℝ} (s : Finset ι) (f : ι → ℝ)
    (w : ∀ i∈s, IntegerWindows B c (f i) l h) : IntegerWindows B c (∑ i∈s,f i) l h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact fun ε pos => .of_forall fun k n _ _ => ⟨0,by simpa using pos⟩
  | insert i s out ih =>
    rw [sum_insert out]; exact add_windows (w i (mem_insert_self ..))
      (ih fun j hj => w j (mem_insert_of_mem hj))

/-- Any common denominator D for the coefficients gives integer windows for
D times the polynomial. This includes constant terms of either sign. -/
theorem polynomial_windows {b c a d U V D : ℕ} (hb : 1<b) (hc : 1<c) (P : ℚ[X])
    (degree : P.natDegree≤d) (den : ∀ r≤P.natDegree, (P.coeff r).den ∣ D)
    (gap : PowerGap c d U V) (uv : U<V) {l h : ℝ} (hl : 0<l)
    (clear : (U:ℝ) ≤ a*l) (valid : h*Real.log (b^a*c : ℕ) ≤ V*Real.log b) :
    IntegerWindows (b^a*c) c (D * P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) l h := by
  rw [Polynomial.eval₂_eq_sum_range,mul_sum]
  apply sum_windows
  intro r mem
  have le := mem_range_succ_iff.mp mem
  obtain ⟨q,hq⟩ := den r le
  have eqn : (D:ℝ)*((P.coeff r):ℝ) = ((q:ℤ)*(P.coeff r).num:ℤ) := by
    have e := Rat.den_mul_eq_num (P.coeff r)
    have t : ((P.coeff r).den:ℝ)*(P.coeff r:ℝ)=(P.coeff r).num := by exact_mod_cast e
    rw [hq]; push_cast; linear_combination (q:ℝ)*t
  rw [← mul_assoc]; change IntegerWindows _ _ (((D:ℝ)*(P.coeff r:ℝ))*_) _ _
  rw [eqn]
  exact mul_windows _ (integerWindows_of_zero (power_zero_windows hb hc (le.trans degree) gap uv hl clear valid))

/-- Explicit extreme discrepancy for the original rational polynomial.
Both bounds are divided by a common positive coefficient denominator. -/
theorem polynomial_discrepancy_of_gap {b c a d U V D : ℕ} (hb : 1<b) (hc : 1<c)
    (P : ℚ[X]) (degree : P.natDegree≤d) (hd : 0<D) (den : ∀ r≤P.natDegree, (P.coeff r).den ∣ D)
    (gap : PowerGap c d U V) (uv : U<V) {l h : ℝ} (hl : 0<l) (lh : l<h) (sep : h≤c*l)
    (clear : (U:ℝ) ≤ a*l) (valid : h*Real.log (b^a*c : ℕ) ≤ V*Real.log b) :
    let x := P.eval₂ (algebraMap ℚ ℝ) (alpha b c)
    (h-l)/(((c:ℝ)-1)*l)/D ≤ liminf (radixDiscrepancy (b^a*c) x) atTop ∧
    ((c:ℝ)*(h-l)/(((c:ℝ)-1)*h))/D ≤ limsup (radixDiscrepancy (b^a*c) x) atTop :=
  discrepancy_of_grid_windows hc hd hl lh sep (polynomial_windows hb hc P degree den gap uv hl clear valid)

/-- A normalized gap with positive window length suffices for rational coefficients. -/
theorem polynomial_nonnormal_of_gap {b c a d U V : ℕ} (hb : 1<b) (hc : 1<c) (P : ℚ[X])
    (degree : P.natDegree≤d) (gap : PowerGap c d U V) (uv : U<V) {l h : ℝ}
    (hl : 0<l) (width : l<h) (clear : (U:ℝ) ≤ a*l)
    (valid : h*Real.log (b^a*c : ℕ) ≤ V*Real.log b) :
    ¬NormalIn (b^a*c) (P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) := by
  let D := ∏ r ∈ range (P.natDegree+1), (P.coeff r).den
  have positive : 0<D := prod_pos fun r _ => (P.coeff r).pos
  have windows := polynomial_windows (D:=D) hb hc P degree
    (fun r le => dvd_prod_of_mem _ (mem_range_succ_iff.mpr le)) gap uv hl clear valid
  have base : 2≤b^a*c := hc.trans_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _))
  exact fun hn => not_normal_of_integerWindows hc hl width windows ((normal_mul_nat_iff base positive _).mpr hn)

/-- The exact criterion for a window of positive length with endpoints U/a and
V log b / log B. It depends only on the gap and the three radix parameters. -/
theorem polynomial_nonnormal_of_log_gap {b c a d U V : ℕ} (hb : 1<b) (hc : 1<c)
    (gap : PowerGap c d U V) (up : 0<U) (uv : U<V)
    (large : (U:ℝ)*Real.log c < a*((V:ℝ)-U)*Real.log b)
    (P : ℚ[X]) (degree : P.natDegree≤d) :
    ¬NormalIn (b^a*c) (P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) := by
  have bp := Real.log_pos (show (1:ℝ)<b by exact_mod_cast hb)
  have cp := Real.log_pos (show (1:ℝ)<c by exact_mod_cast hc)
  have ap : (0:ℝ)<a := by
    apply Nat.cast_pos.mpr
    by_contra! bad
    have eqn : a=0 := by omega
    simp only [eqn,Nat.cast_zero,zero_mul] at large
    exact (mul_nonneg (Nat.cast_nonneg U) cp.le).not_gt large
  let B := b^a*c
  have logB : Real.log B = a*Real.log b+Real.log c := by
    dsimp [B]; rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul (by positivity) (by positivity),Real.log_pow]
  have Bp : 0<Real.log B := by rw [logB]; positivity
  apply polynomial_nonnormal_of_gap hb hc P degree gap uv
    (l:=(U:ℝ)/a) (h:=(V:ℝ)*Real.log b/Real.log B) (div_pos (by exact_mod_cast up) ap)
  · rw [div_lt_div_iff₀ ap Bp,logB]
    nlinarith only [large]
  · rw [mul_comm,div_mul_cancel₀ _ ap.ne']
  · exact (div_mul_cancel₀ _ Bp.ne').le

/-- For a fixed degree bound, every a satisfying the displayed explicit condition works.
No primality or coprimality hypothesis on b and c occurs in the alternate-base argument. -/
theorem polynomial_nonnormal {b c a d : ℕ} (hb : 1<b) (hc : 1<c) (hd : 0<d)
    (large : ((c^d-1:ℕ):ℝ)*Real.log c < a*Real.log b)
    (P : ℚ[X]) (degree : P.natDegree≤d) :
    ¬NormalIn (b^a*c) (P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) := by
  have v : 1<c^d := one_lt_pow₀ hc hd.ne'
  apply polynomial_nonnormal_of_log_gap hb hc (universal_gap hc d) (by omega) (by omega) _ P degree
  have diff : ((c^d:ℕ):ℝ) - (c^d-1:ℕ) = 1 := by rw [Nat.cast_sub v.le]; push_cast; ring
  simpa only [diff,mul_one] using large

/-- A better sufficient bound when the degree is smaller than c. -/
theorem small_degree_polynomial_nonnormal {b c a d : ℕ} (hb : 1<b) (hc : 1<c) (hd : 0<d)
    (dc : d<c) (large : (d:ℝ)*Real.log c < a*((c:ℝ)-d)*Real.log b)
    (P : ℚ[X]) (degree : P.natDegree≤d) :
    ¬NormalIn (b^a*c) (P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) :=
  polynomial_nonnormal_of_log_gap hb hc (coordinate_gap c d hc) hd dc large P degree

/-- Every sufficiently large a works simultaneously for all polynomials up to a fixed degree. -/
theorem eventually_polynomial_nonnormal {b c : ℕ} (hb : 1<b) (hc : 1<c) {d : ℕ} (hd : 0<d) :
    ∀ᶠ a : ℕ in atTop, ∀ P : ℚ[X], P.natDegree≤d →
      ¬NormalIn (b^a*c) (P.eval₂ (algebraMap ℚ ℝ) (alpha b c)) := by
  have bp := Real.log_pos (show (1:ℝ)<b by exact_mod_cast hb)
  obtain ⟨A,bound⟩ := exists_nat_gt (((c^d-1:ℕ):ℝ)*Real.log c/Real.log b)
  filter_upwards [eventually_ge_atTop A] with a ha
  exact polynomial_nonnormal hb hc hd ((div_lt_iff₀ bp).mp (bound.trans_le (by exact_mod_cast ha)))

/-- Exact open observation window for the square, with the standard starting index one. -/
theorem square_zero_windows : ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
    (1/2:ℝ)*(3:ℝ)^k ≤ n → (n:ℝ)<(3*Real.log 2/Real.log 48)*3^k →
      shift 48 (alpha 2 3 ^ 2) n < ε := by
  have p : 0<Real.log 48 := Real.log_pos (by norm_num)
  apply power_zero_windows (b:=2) (c:=3) (a:=4) (d:=2) (by decide) (by decide) le_rfl
    (coordinate_gap 3 2 (by decide)) (by decide) (by norm_num) (by norm_num)
  norm_num [div_mul_cancel₀ _ p.ne']

private theorem square_width : (1:ℝ)/2 < 3*Real.log 2/Real.log 48 := by
  rw [lt_div_iff₀ (Real.log_pos (by norm_num))]
  have h := Real.log_lt_log (by norm_num : (0:ℝ)<48) (by norm_num : (48:ℝ)<2^6)
  rw [Real.log_pow] at h; norm_num at h; linarith

private theorem square_disjoint : 3*Real.log 2/Real.log 48 ≤ (3:ℝ)*(1/2) := by
  rw [div_le_iff₀ (Real.log_pos (by norm_num))]
  have t := Real.log_le_log (by norm_num : (0:ℝ)<2^2) (by norm_num : (2:ℝ)^2≤48)
  rw [Real.log_pow] at t; norm_num at t; linarith

theorem quadratic_nonnormal_48 (P : ℚ[X]) (degree : P.natDegree≤2) :
    ¬NormalIn 48 (P.eval₂ (algebraMap ℚ ℝ) (alpha 2 3)) := by
  apply polynomial_nonnormal_of_gap (b:=2) (c:=3) (a:=4) (by decide) (by decide) P degree
    (coordinate_gap 3 2 (by decide)) (by decide) (by norm_num) square_width (by norm_num)
  norm_num [div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ)<48)).ne']

theorem square_nonnormal_48 : ¬NormalIn 48 (alpha 2 3 ^ 2) :=
  not_normal_of_integerWindows (by decide) (by norm_num) square_width (integerWindows_of_zero square_zero_windows)

/-- The lower bound at arbitrary cutoffs and the larger bound at window endpoints. -/
theorem square_discrepancy_48 :
    let h := 3*Real.log 2/Real.log 48
    h-1/2 ≤ liminf (radixDiscrepancy 48 (alpha 2 3 ^ 2)) atTop ∧
    3*(h-1/2)/(2*h) ≤ limsup (radixDiscrepancy 48 (alpha 2 3 ^ 2)) atTop := by
  have windows : IntegerWindows 48 3 ((1:ℕ)*(alpha 2 3^2)) (1/2) (3*Real.log 2/Real.log 48) := by
    simpa using integerWindows_of_zero square_zero_windows
  have H := discrepancy_of_grid_windows (D:=1) (by decide) (by decide) (by norm_num) square_width square_disjoint windows
  norm_num at H ⊢
  exact H

/-- Every fixed all-zero word has at least the same lower limiting frequency.
For one digit this already exceeds the simple-normal frequency. -/
theorem square_zero_word_liminf (m : ℕ) :
    3*Real.log 2/Real.log 48-1/2 ≤
      liminf (frequency (shift 48 (alpha 2 3^2)) 0 (1/(48:ℝ)^m)) atTop := by
  let h := 3*Real.log 2/Real.log 48
  let t := 1/(48:ℝ)^m
  let x := alpha 2 3^2
  let p (n : ℕ) := 0≤shift 48 x n ∧ shift 48 x n<t
  have cert : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, (1/2:ℝ)*(3:ℝ)^k ≤ n → (n:ℝ)<h*3^k → p n := by
    filter_upwards [square_zero_windows t (by dsimp [t]; positivity)] with k hk n lo up
    exact ⟨Int.fract_nonneg _,hk n lo up⟩
  have share := (geometric_window_shares (c:=3) (by decide) (by norm_num) square_width square_disjoint p cert).1
  apply le_of_forall_pos_le_add
  intro ε pos
  have counts : ∀ᶠ N : ℕ in atTop, h-1/2-ε ≤ frequency (shift 48 x) 0 t N := by
    filter_upwards [share ε pos] with N hN
    change (h-1/2)/(((3:ℝ)-1)*(1/2))-ε ≤ _ at hN
    rwa [show ((3:ℝ)-1)*(1/2)=1 by norm_num,div_one] at hN
  have lim := le_liminf_of_le (isCoboundedUnder_ge_of_le _ fun N => (frequency_bounds (shift 48 x) 0 t N).2) counts
  linarith

theorem square_zero_digit_excess :
    1/48 < liminf (frequency (shift 48 (alpha 2 3^2)) 0 (1/48)) atTop := by
  refine lt_of_lt_of_le (b:=3*Real.log 2/Real.log 48-1/2) ?_ (by simpa only [pow_one] using square_zero_word_liminf 1)
  have t := Real.log_lt_log (by norm_num : (0:ℝ)<48^25) (by norm_num : (48:ℝ)^25<2^144)
  rw [Real.log_pow,Real.log_pow] at t
  rw [lt_sub_iff_add_lt,lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<48))]
  norm_num at t ⊢
  linarith

end NormalityChecker.AlternateBase
