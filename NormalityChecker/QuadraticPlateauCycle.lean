module

public import NormalityChecker.QuadraticOrbitTransfer
public import NormalityChecker.ParameterTwoQuadraticHeight
public import NormalityChecker.TranslatedShells
public import NormalityChecker.MaskedDiscrepancy

/-! Periodic interval counts for the actual rational prefix on the upper half
of a quadratic shell. The coefficient denominator may share primes with the radix. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.QuadraticOrbit
open SignedPhases CircleDiscrepancy

/-- The actual rational prefix at the midpoint, including the integer part
of the numerator polynomial before division by the coefficient denominator. -/
def plateauSeed (b D : ℕ) (A B C : ℤ) (r : ℕ) : ℚ :=
  model b A B C (3*2^r) / D

/-- Discrepancy of the uniform measure on the eventual rational orbit. -/
noncomputable def orbitFactor (b : ℕ) (y : ℚ) : ℝ :=
  limsup (radixDiscrepancy b y) atTop

theorem orbitFactor_eq_period (b : ℕ) (y : ℚ) {s L : ℕ} (hL : 0 < L)
    (per : ∀ n, s ≤ n → shift b (y:ℝ) (n+L) = shift b y n) :
    orbitFactor b y = disc (fun i => (b:ℝ)^(s+i)*y) L :=
  (rational_discrepancy_limit b y hL per).limsup_eq

theorem orbitFactor_bounds (b : ℕ) (y : ℚ) : 0 ≤ orbitFactor b y ∧ orbitFactor b y ≤ 1 := by
  have bd := radix_discrepancy_bounds b y
  exact ⟨le_limsup_of_frequently_le (Eventually.frequently (.of_forall fun N => (bd N).1))
    (isBoundedUnder_of_eventually_le (.of_forall fun N => (bd N).2)),
    limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (bd N).1)) (.of_forall fun N => (bd N).2)⟩

theorem exists_clear (b D : ℕ) : ∃ s : ℕ, b.Coprime (((b:ℚ)^s / D).den) := by
  obtain ⟨s,q,_,_,cop,_,dvd,_⟩ := rational_cycle b (D:ℚ)⁻¹
  exact ⟨s,cop.of_dvd_right (by simpa [div_eq_mul_inv] using dvd s le_rfl)⟩

/-- A shift depending only on the radix and the coefficient denominator. -/
noncomputable def clearingShift (b D : ℕ) := Nat.find (exists_clear b D)

/-- The reduced rational point on the eventual cycle, obtained by a fixed
number of radix shifts from the actual plateau seed. -/
noncomputable def plateauPoint (b D : ℕ) (A B C : ℤ) (r : ℕ) : ℚ :=
  Int.fract ((b:ℚ)^(clearingShift b D)*plateauSeed b D A B C r)

private theorem clear_coprime (b D : ℕ) :
    b.Coprime (((b:ℚ)^(clearingShift b D) / D).den) := Nat.find_spec (exists_clear b D)

def periodLength (b s : ℕ) (y : ℚ) := (((b:ℚ)^s*y).den).totient

private theorem periodic_after {b s : ℕ} (y : ℚ)
    (cop : b.Coprime (((b:ℚ)^s*y).den)) :
    ∀ n, s ≤ n → shift b (y:ℝ) (n + periodLength b s y) = shift b y n := by
  let u := (b:ℚ)^s*y
  let L := u.den.totient
  obtain ⟨z,hz⟩ : (u.den:ℤ) ∣ (b:ℤ)^L-1 := by
    simpa [L] using Nat.modEq_iff_dvd.mp (Nat.ModEq.pow_totient cop).symm
  have eqn : (b:ℚ)^L-1 = u.den*z := by exact_mod_cast hz
  have full : (b:ℚ)^L*u = u + (z*u.num:ℤ) := by
    push_cast
    linear_combination u*eqn + (z:ℚ)*u.den_mul_eq_num
  rintro n ns
  let k := n-s
  have e : (b:ℚ)^(n+L)*y = (b:ℚ)^n*y + ((b:ℤ)^k*(z*u.num):ℤ) := by
    rw [show n = k+s by dsimp [k]; omega, pow_add (b:ℚ) k s, Nat.add_assoc, pow_add, pow_add]
    push_cast at full ⊢; dsimp only [u] at full ⊢
    linear_combination (b:ℚ)^k*full
  have h := congrArg (fun v : ℚ => (v:ℝ)) e
  simp only [Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_intCast,Rat.cast_pow] at h
  change Int.fract ((b:ℝ)^(n+L)*y) = _
  rw [h,Int.fract_add_intCast]; rfl

/-- Mean of one full eventual period on the half-open test interval. -/
noncomputable def cycleMass (b s : ℕ) (y : ℚ) (a d : ℝ) : ℝ :=
  frequency (fun i => shift b y (s+i)) a d (periodLength b s y)

private theorem shell_support {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D) (A B C : ℤ) (nz : A ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) :
    let s := clearingShift b D
    let z := (b:ℚ)^s/D
    let y := plateauSeed b D A B C r
    let v := (b:ℚ)^s*y
    b.Coprime v.den ∧ v.den ∣ z.den*2^(2*r) ∧
      upperDen b A B C r ≤ z⁻¹.den*v.den := by
  dsimp only
  let s := clearingShift b D
  let z := (b:ℚ)^s/D
  let P := model b A B C (3*2^r)
  have eqn : (b:ℚ)^s*plateauSeed b D A B C r = z*P := by dsimp [plateauSeed,P,z]; ring
  rw [eqn]
  have dv : P.den ∣ 2^(2*r) := (shell_den hb odd hr (by rw [pow_succ']; omega)
    (by rw [pow_add]; have := pow_pos (by decide : 0<2) r; omega) A B C nz).1
  have div := (Rat.mul_den_dvd z P).trans (Nat.mul_dvd_mul_left _ dv)
  refine ⟨((clear_coprime b D).mul_right (odd.coprime_two_right.pow_right _)).of_dvd_right div,div,?_⟩
  have zn : z ≠ 0 := div_ne_zero (pow_ne_zero _ (by exact_mod_cast (show b ≠ 0 by omega))) (by exact_mod_cast hd.ne')
  exact Nat.le_of_dvd (Nat.mul_pos z⁻¹.pos (Rat.pos _)) (by
    simpa only [inv_mul_cancel_left₀ zn] using Rat.mul_den_dvd z⁻¹ (z*P))

private theorem seed_period {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) {r : ℕ} (hr : 1 ≤ r) :
    let y := plateauSeed b D A B C r
    let s := clearingShift b D
    ∀ n, s ≤ n → shift b (y:ℝ) (n+periodLength b s y) = shift b y n :=
  periodic_after _ (shell_support hb odd hd A B C nz hr).1

theorem plateau_orbitFactor {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) {r : ℕ} (hr : 1 ≤ r) :
    let y := plateauSeed b D A B C r
    let s := clearingShift b D
    orbitFactor b y = disc (fun i => (b:ℝ)^(s+i)*y) (periodLength b s y) :=
  orbitFactor_eq_period _ _ (Nat.totient_pos.mpr (Rat.pos _)) (seed_period hb odd hd A B C nz hr)

private theorem large_support {b c : ℕ} (hb : 1 < b) (hc : 1 < c) (cop : b.Coprime c)
    {η : ℝ} (he : 0 < η) : ∃ M : ℕ, ∀ v : ℚ, M ≤ v.den → (∃ t : ℕ, v.den ∣ c^t) →
    ∀ T : ℕ, v.den ≤ T^3 → ∀ a d : ℝ, 0 ≤ a → a ≤ d → d ≤ 1 →
      |(IntervalFourier.count (shift b v) a d T : ℝ) - T*(d-a)| ≤ η*T := by
  obtain ⟨M,δ,pos,est⟩ := PolynomialMasks.interval_block (d:=3)
    (fixed_support_orbit_estimate hb hc cop) he
  refine ⟨M,fun v hv dv T hT a d ha had hd => ?_⟩
  have H := est (v:ℝ) v T 0 hv dv hT (fun _ _ => by simpa using pos) a d ha had hd
  rw [Localized.centered_sum] at H
  simpa only [zero_add] using H

/-- A function counting membership in an interval. -/
private noncomputable def hit (u : ℕ → ℝ) (a d : ℝ) (i : ℕ) : ℝ :=
  if a ≤ u i ∧ u i < d then 1 else 0

private theorem hit_sum (u : ℕ → ℝ) (a d : ℝ) (T : ℕ) :
    ∑ i ∈ range T, hit u a d i = (IntervalFourier.count u a d T : ℝ) := by
  classical simp [hit,IntervalFourier.count]

private theorem hit_shift (u : ℕ → ℝ) (a d : ℝ) (s T : ℕ) :
    |∑ i ∈ range T, hit u a d i - ∑ i ∈ range T, hit u a d (s+i)| ≤ s := by
  let f := hit u a d
  have same := congrArg (fun n => ∑ i ∈ range n, f i) (Nat.add_comm T s)
  simp only [sum_range_add] at same
  have bd (n : ℕ) : 0 ≤ ∑ i ∈ range s, f (n+i) ∧ ∑ i ∈ range s, f (n+i) ≤ s := by
    constructor
    · apply sum_nonneg; intro i _; dsimp [f,hit]; split <;> norm_num
    · exact (sum_le_sum (g:=fun _ => (1:ℝ)) (fun _ _ => by dsimp [f,hit]; split <;> norm_num)).trans_eq (by simp)
  have start := bd 0
  simp only [zero_add] at start
  change |∑ i ∈ range T, f i - ∑ i ∈ range T, f (s+i)| ≤ s
  rw [abs_le]; constructor <;> linarith [(bd T).1,(bd T).2]

private theorem advanced {b s : ℕ} (y : ℚ) (i : ℕ) :
    shift b y (s+i) = shift b (((b:ℚ)^s*y):ℚ) i := by
  simp only [shift,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow,pow_add]
  congr 1; ring

/-- An integer part or a finite preperiod does not change the cycle measure's
discrepancy. This identifies the unadvanced seed with the cleared point used
in the arithmetic description. -/
theorem orbitFactor_advance (b s : ℕ) (y : ℚ) :
    orbitFactor b (Int.fract ((b:ℚ)^s*y)) = orbitFactor b y := by
  let v := (b:ℚ)^s*y
  let z := Int.fract v
  have step (i : ℕ) : shift b z i = shift b y (s+i) := by
    rw [advanced y]
    change Int.fract ((b:ℝ)^i*(z:ℝ)) = Int.fract ((b:ℝ)^i*(v:ℝ))
    have e : (z:ℝ) = (v:ℝ) - (⌊v⌋:ℤ) := by simp only [z,Int.fract,Rat.cast_sub,Rat.cast_intCast]
    have intPart : (b:ℝ)^i*(⌊v⌋:ℤ) = (((b:ℤ)^i*⌊v⌋:ℤ):ℝ) := by push_cast; rfl
    rw [e,mul_sub,intPart,Int.fract_sub_intCast]
  have limit (p : ℚ) : Tendsto (radixDiscrepancy b p) atTop (𝓝 (orbitFactor b p)) := by
    obtain ⟨t,_,L,_,_,lp,_,per⟩ := rational_cycle b p
    rw [orbitFactor_eq_period b p lp per]
    exact rational_discrepancy_limit b p lp per
  have approx : Tendsto (fun N => radixDiscrepancy b y N - radixDiscrepancy b z N) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]; intro ε ep
    filter_upwards [eventually_gt_atTop 0,(tendsto_const_div_atTop_nhds_zero_nat (s:ℝ)).eventually_lt_const ep]
      with N np cost
    have nr : (0:ℝ)<N := by exact_mod_cast np
    rw [Real.dist_eq,sub_zero]
    apply lt_of_le_of_lt _ cost
    have H := disc_mixture_bound (fun i => (b:ℝ)^i*y) (fun i => (b:ℝ)^i*z) N N
      (z:=1) zero_le_one (η:=(s:ℝ)/N) (by
        intro a d _ _ _
        rw [one_mul,sub_sub_sub_cancel_right]
        change |(IntervalFourier.count (shift b y) a d N:ℝ)/N - (IntervalFourier.count (shift b z) a d N:ℝ)/N| ≤ _
        rw [← sub_div,abs_div,abs_of_pos nr,div_le_div_iff_of_pos_right nr,← hit_sum,← hit_sum]
        simpa only [hit,step] using hit_shift (shift b y) a d s N)
    change |disc (fun i => (b:ℝ)^i*y) N - disc (fun i => (b:ℝ)^i*z) N| ≤ _
    simpa only [one_mul] using H
  exact (sub_eq_zero.mp (tendsto_nhds_unique ((limit y).sub (limit z)) approx)).symm

private theorem large_cycle {b s : ℕ} (y : ℚ)
    (per : ∀ n, s ≤ n → shift b (y:ℝ) (n+periodLength b s y) = shift b y n)
    {η : ℝ}
    (bound : ∀ T : ℕ, ((b:ℚ)^s*y).den ≤ T^3 → ∀ a d : ℝ, 0 ≤ a → a ≤ d → d ≤ 1 →
      |(IntervalFourier.count (shift b (((b:ℚ)^s*y):ℚ)) a d T : ℝ) - T*(d-a)| ≤ η*T) :
    orbitFactor b y ≤ η := by
  let v := (b:ℚ)^s*y
  let L := periodLength b s y
  have lp : 0 < L := Nat.totient_pos.mpr (Rat.pos _)
  have eqn (i : ℕ) : (b:ℝ)^(s+i)*y = (b:ℝ)^i*(v:ℝ) := by
    simp only [v,pow_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]; ring
  have per' (n : ℕ) (_ : 0 ≤ n) : shift b v (n+L) = shift b v n := by
    rw [← advanced y,← advanced y,← Nat.add_assoc,per _ (Nat.le_add_right ..)]
  have limit := rational_discrepancy_limit b v lp per'
  simp only [zero_add] at limit
  rw [orbitFactor_eq_period b y lp per]
  simp only [eqn]
  apply le_of_tendsto limit
  filter_upwards [eventually_ge_atTop v.den,eventually_gt_atTop 0] with T ht hp
  have tr : (0:ℝ)<T := by exact_mod_cast hp
  apply disc_le
  intro a d ha had hd
  have H := bound T (ht.trans (by simpa using (Nat.pow_le_pow_right hp (show 1≤3 by decide)))) a d ha had.le hd
  change |(IntervalFourier.count (shift b v) a d T:ℝ)/T - (d-a)| ≤ η
  rw [div_sub' tr.ne', abs_div, abs_of_pos tr, div_le_iff₀ tr]
  simpa only [mul_comm (d-a)] using H

/-- Large midpoint denominators force small discrepancy of the full eventual cycle,
uniformly across the quadratic shells. -/
theorem plateau_factor_decay {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) {η : ℝ} (he : 0 < η) :
    ∃ M : ℕ, ∀ r ≥ 1, M ≤ upperDen b A B C r → orbitFactor b (plateauSeed b D A B C r) ≤ η := by
  let s := clearingShift b D
  let z := (b:ℚ)^s/D
  have dp := z.pos
  obtain ⟨M,est⟩ := large_support (by omega : 1 < b) (by omega : 1 < 2*z.den)
    (odd.coprime_two_right.mul_right (clear_coprime b D)) he
  refine ⟨z⁻¹.den*M,fun r hr hM => ?_⟩
  obtain ⟨_,dvd,recov⟩ := shell_support hb odd hd A B C nz hr
  apply large_cycle _ (seed_period hb odd hd A B C nz hr)
  apply est _ (Nat.le_of_mul_le_mul_left (hM.trans recov) z⁻¹.pos)
  exact ⟨2*r,dvd.trans (by rw [mul_pow,mul_comm]; exact Nat.mul_dvd_mul_left _ (dvd_pow_self _ (by omega)))⟩

theorem cycleMass_error_le {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) {r : ℕ} (hr : 1 ≤ r)
    {a d : ℝ} (ha : 0 ≤ a) (had : a < d) (hd' : d ≤ 1) :
    let y := plateauSeed b D A B C r
    |cycleMass b (clearingShift b D) y a d - (d-a)| ≤ orbitFactor b y := by
  dsimp only
  rw [plateau_orbitFactor hb odd hd A B C nz hr]
  exact test_le _ _ ha had hd'

/-- Uniformly in the interval and in the partial length, the rational plateau
counts agree with length times eventual cycle mass up to o(2^r). -/
theorem plateau_counts {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ T ≤ 2^r, ∀ a d : ℝ, 0 ≤ a → a < d → d ≤ 1 →
      let y := plateauSeed b D A B C r
      |(IntervalFourier.count (shift b y) a d T : ℝ) -
        T*cycleMass b (clearingShift b D) y a d| ≤ ε*(2:ℝ)^r := by
  let s := clearingShift b D
  let z := (b:ℚ)^s/D
  let η := ε/4
  have he : 0 < η := by dsimp [η]; positivity
  have dp := z.pos
  obtain ⟨M,est⟩ := large_support (by omega : 1 < b) (by omega : 1 < 2*z.den)
    (odd.coprime_two_right.mul_right (clear_coprime b D)) he
  have grow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)
  filter_upwards [eventually_ge_atTop 1, grow.eventually_ge_atTop ((s+M:ℝ)/η),
    grow.eventually_ge_atTop ((z.den:ℝ)/η^3)] with r hr price big T ht a d ha had hd'
  let y := plateauSeed b D A B C r
  let v := (b:ℚ)^s*y
  let m := cycleMass b s y a d
  let Q := (2:ℝ)^r
  have per := seed_period hb odd hd A B C nz hr
  have lp : 0 < periodLength b s y := Nat.totient_pos.mpr (Rat.pos _)
  have cost : (s:ℝ)+M ≤ η*Q := by linarith only [(div_le_iff₀ he).mp price]
  have cap := (shell_support hb odd hd A B C nz hr).2.1
  change v.den ∣ z.den*2^(2*r) at cap
  have tm : (T:ℝ) ≤ Q := by dsimp [Q]; exact_mod_cast ht
  let U := (IntervalFourier.count (shift b y) a d T : ℝ)
  let V := (IntervalFourier.count (shift b v) a d T : ℝ)
  have offset : |U-V| ≤ s := by
    have H := hit_shift (shift b y) a d s T
    dsimp only [U,V]; rw [← hit_sum,← hit_sum]
    simpa only [hit,advanced,v] using H
  have mass := frequency_bounds (fun i => shift b y (s+i)) a d (periodLength b s y)
  change 0 ≤ m ∧ m ≤ 1 at mass
  change |U - T*m| ≤ ε*Q
  by_cases small : v.den < M
  · have full := cycle_block_error (shift b y) lp per a d s T le_rfl
    change |∑ i ∈ range T, (hit (shift b y) a d (s+i) - m)| ≤ periodLength b s y at full
    rw [sum_sub_distrib] at full
    simp only [hit,advanced,sum_const,card_range,nsmul_eq_mul] at full
    change |∑ i ∈ range T, hit (shift b v) a d i - T*m| ≤ periodLength b s y at full
    rw [hit_sum] at full
    have len : periodLength b s y ≤ M := (Nat.totient_le v.den).trans small.le
    have H := (abs_sub_le U V (T*m)).trans (add_le_add offset full)
    calc _ ≤ (s:ℝ)+M := H.trans (by exact_mod_cast Nat.add_le_add_left len s)
         _ ≤ ε*Q := cost.trans (by gcongr; dsimp [η]; linarith)
  · have large := est v (by omega) ⟨2*r,cap.trans (by rw [mul_pow,mul_comm]; exact Nat.mul_dvd_mul_left _ (dvd_pow_self _ (by omega)))⟩
    by_cases long : v.den ≤ T^3
    · have reg := large T long a d ha had.le hd'
      have fac := large_cycle y per large
      have near : |m-(d-a)| ≤ η := (cycleMass_error_le hb odd hd A B C nz hr ha had hd').trans fac
      have H := (abs_sub_le U V (T*m)).trans (add_le_add offset (abs_sub_le V (T*(d-a)) (T*m)))
      rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg T : (0:ℝ) ≤ T),abs_sub_comm (d-a)] at H
      have u := mul_le_mul_of_nonneg_left near (Nat.cast_nonneg T)
      dsimp only [V] at H
      have g := mul_le_mul_of_nonneg_left tm he.le
      dsimp only [η] at *; linarith [Nat.cast_nonneg (α:=ℝ) M]
    · have denbd : (v.den:ℝ) ≤ z.den*Q^2 := by
        have h := Nat.le_of_dvd (Nat.mul_pos dp (by positivity)) cap
        rw [mul_comm 2 r,pow_mul] at h; dsimp [Q]; exact_mod_cast h
      have cubic : (T:ℝ)^3 ≤ (η*Q)^3 := calc
        _ ≤ (v.den:ℝ) := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge long))
        _ ≤ z.den*Q^2 := denbd
        _ ≤ (η^3*Q)*Q^2 := by
          gcongr; linarith only [(div_le_iff₀ (pow_pos he 3)).mp big]
        _ = _ := by ring
      have short : (T:ℝ) ≤ η*Q := by
        by_contra! h; exact (pow_lt_pow_left₀ h (by positivity : 0 ≤ η*Q) (by decide : 3≠0)).not_ge cubic
      have cnt : U ≤ T := by dsimp [U,IntervalFourier.count]; exact_mod_cast (card_filter_le (range T) _).trans_eq (card_range T)
      have un : 0 ≤ U := Nat.cast_nonneg _
      have cheap : |U-T*m| ≤ T := by
        rw [abs_le]; constructor <;> linarith [mul_nonneg (Nat.cast_nonneg T) mass.1,
          mul_le_mul_of_nonneg_left mass.2 (Nat.cast_nonneg T)]
      exact cheap.trans (short.trans (by gcongr; dsimp [η]; linarith))

end NormalityChecker.QuadraticOrbit
