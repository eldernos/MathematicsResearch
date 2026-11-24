module

public import NormalityChecker.TranslatedShells
public import NormalityChecker.PartialUniformity

/-! Positive rational orbit factors tending to zero, and finite digit cycles. -/
@[expose] public section
open Finset Filter NormalityChecker.CircleDiscrepancy
open scoped Topology
namespace NormalityChecker.SignedPhases

/-- Every rational orbit misses a fixed positive-length interval between grid nodes. -/
theorem rational_discrepancy_pos (b : ℕ) (r : ℚ) :
    0 < limsup (radixDiscrepancy b r) atTop := by
  let a : ℝ := 1/(2*r.den)
  have dq : (0:ℝ)<r.den := Nat.cast_pos.mpr r.pos
  have ap : 0<a := by dsimp [a]; positivity
  have d : 2*a*r.den = 1 := by dsimp [a]; field_simp
  have one : (1:ℝ) ≤ r.den := by exact_mod_cast r.pos
  have d1 : 2*a ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left one (by positivity : 0≤2*a)]
  have miss (n : ℕ) : ¬ (a≤shift b (r:ℝ) n ∧ shift b r n<2*a) := by
    rintro ⟨lo,hi⟩
    let y := (b:ℝ)^n*(r:ℝ)
    let w : ℤ := (b:ℤ)^n*r.num - ⌊y⌋*r.den
    have grid : (w:ℝ) = shift b (r:ℝ) n*r.den := by
      dsimp only [w,shift]; rw [Int.fract]; push_cast
      change _ = (y-⌊y⌋)*r.den
      rw [sub_mul]; congr 1; dsimp only [y]; rw [Rat.cast_def]; field_simp
    have low : (0:ℤ)<w := by exact_mod_cast (grid ▸ mul_pos (ap.trans_le lo) dq : (0:ℝ)<w)
    have high : w<(1:ℤ) := by exact_mod_cast grid.trans_lt ((mul_lt_mul_of_pos_right hi dq).trans_eq d)
    omega
  apply ap.trans_le
  apply le_limsup_of_frequently_le _ (isBoundedUnder_of_eventually_le (.of_forall fun N => (radix_discrepancy_bounds b r N).2))
  apply Eventually.frequently (.of_forall _)
  intro N
  have H := test_le (fun i => (b:ℝ)^i*r) N ap.le (show a<2*a by linarith) d1
  change |frequency (shift b r) a (2*a) N - (2*a-a)| ≤ radixDiscrepancy b r N at H
  simpa [frequency,miss,show 2*a-a=a by ring,abs_of_pos ap] using H

/-- Fraction with a repeating block of length L and base-b integer encoding A. -/
def periodicWord (b L A : ℕ) : ℚ := A / ((b:ℚ)^L-1)

/-- Number of rotations of the word lying in cell j of the L-cell grid. -/
def wordCellCount (b L A j : ℕ) : ℕ :=
  ((range L).filter fun i => let y := Int.fract ((b:ℚ)^i * periodicWord b L A)
    (j:ℚ)/L ≤ y ∧ y < ((j:ℚ)+1)/L).card

/-- A length-L cyclic word with exactly one visit to each L-cell has positive
discrepancy at most 2/L. Order-k de Bruijn words satisfy the count for L=b^k. -/
theorem de_bruijn_discrepancy_bounds {b L : ℕ} (hb : 2≤b) (lp : 0<L) (A : ℕ)
    (counts : ∀ j<L, wordCellCount b L A j = 1) :
    let r := periodicWord b L A
    0 < limsup (radixDiscrepancy b r) atTop ∧ limsup (radixDiscrepancy b r) atTop ≤ 2/(L:ℝ) := by
  classical
  let r := periodicWord b L A
  refine ⟨rational_discrepancy_pos _ _,discrepancy_of_fixed_cells lp ?_⟩
  have br : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have per (n : ℕ) (_ : 0≤n) : shift b (r:ℝ) (n+L)=shift b r n := by
    have e : (b:ℝ)^(n+L)*r = (b:ℝ)^n*r + ((b:ℤ)^n*A:ℤ) := by
      simp only [r,periodicWord,Rat.cast_div,Rat.cast_natCast,Rat.cast_sub,Rat.cast_pow,Rat.cast_one,
        pow_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
      field_simp [sub_ne_zero.mpr (one_lt_pow₀ br lp.ne').ne']; ring
    rw [shift,e,Int.fract_add_intCast,shift]
  intro j hj
  have F : frequency (fun i => shift b (r:ℝ) (0+i)) (j/(L:ℝ)) (((j:ℝ)+1)/L) L = 1/(L:ℝ) := by
    simp only [Nat.zero_add,frequency]
    suffices eqn : ((range L).filter fun i => (j:ℝ)/L ≤ shift b (r:ℝ) i ∧
        shift b (r:ℝ) i < ((j:ℝ)+1)/L).card = wordCellCount b L A j by rw [eqn,counts j hj,Nat.cast_one]
    unfold wordCellCount; apply congrArg Finset.card; apply filter_congr; intro i hi
    dsimp only [shift]
    have cast : Int.fract ((b:ℝ)^i*(r:ℝ)) = ((Int.fract ((b:ℚ)^i*r):ℚ):ℝ) := by norm_cast
    rw [cast,show (j:ℝ)/L = ((j/(L:ℚ):ℚ):ℝ) by push_cast; rfl,
      show ((j:ℝ)+1)/L = ((((j:ℚ)+1)/L):ℚ) by push_cast; rfl]
    exact and_congr Rat.cast_le Rat.cast_lt
  rw [← F,Metric.tendsto_nhds]
  intro ε he
  filter_upwards [eventually_gt_atTop 0,(tendsto_const_div_atTop_nhds_zero_nat ((0:ℝ)+L)).eventually_lt_const he]
    with N hn small
  rw [Real.dist_eq]; exact (cycle_frequency_error _ lp per (Nat.zero_le _) hn _ _).trans_lt (by simpa only [Nat.cast_zero] using small)

/-- The binary word 00010111 has one cyclic occurrence of every three-bit word. -/
theorem de_bruijn_eight_cells : ∀ j : Fin 8, wordCellCount 2 8 23 j = 1 := by decide +kernel

/-- Rational translations by inverse powers of any fixed integer coprime to the
base have discrepancy tending to zero as their denominator grows. -/
theorem inverse_power_discrepancy_tendsto {b t : ℕ} (hb : 2≤b) (ht : 1<t) (cop : b.Coprime t) :
    Tendsto (fun k : ℕ => limsup (radixDiscrepancy b (1/(t:ℝ)^k)) atTop) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro ε he
  let w := ε/64
  have wp : 0<w := by dsimp [w]; positivity
  obtain ⟨H,hH⟩ := exists_nat_gt ((3+(1/w)^2)/w)
  have hp : (0:ℝ)<H := (by positivity : 0<(3+(1/w)^2)/w).trans hH
  let : NeZero H := ⟨by exact_mod_cast hp.ne'⟩
  let η := w/(H:ℝ)
  have ep : 0<η := div_pos wp hp
  obtain ⟨M,estimate⟩ := fixed_support_orbit_estimate hb ht cop 1 η ep
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt ht).eventually_ge_atTop (H*M)] with k hk
  let y : ℚ := 1/(↑(t^k):ℚ)
  have den : y.den=t^k := by dsimp [y]; rw [one_div,Rat.inv_natCast_den_of_pos (by positivity)]
  have cast : (y:ℝ) = 1/(t:ℝ)^k := by simp [y]
  rw [← cast,Real.dist_eq,sub_zero,abs_of_pos (rational_discrepancy_pos b y)]
  apply lt_of_le_of_lt (b:=ε/2) _ (half_lt_self he)
  apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds b y N).1))
  filter_upwards [eventually_ge_atTop (t^k)] with N hn
  change disc (fun i => (b:ℝ)^i*y) N ≤ _
  apply disc_le; intro a d ha had hd
  let u := shift b (y:ℝ)
  have fourier (h : ℤ) (nz : h≠0) (hs : h.natAbs<H) :
      ‖∑ i∈range N,phase (h*u i)‖ ≤ η*N := by
    simp only [u,shift,phase_fract]
    apply model_orbit_bound h nz y estimate
    · rw [den]; exact (Nat.mul_le_mul_right M hs.le).trans hk
    · exact den.dvd
    · simpa [den] using hn
  have est := IntervalFourier.interval_count_bound (H:=H) (T:=N) u
    (fun i => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩) ha had.le hd wp (by positivity) fourier
  have tiny : 3/(H:ℝ)+(1/w)^2/H≤w := by rw [← add_div,div_le_iff₀ hp]; linarith only [(div_lt_iff₀ wp).mp hH]
  have id : (H:ℝ)*η=w := by dsimp [η]; field_simp
  have nr : (0:ℝ)<N := Nat.cast_pos.mpr ((pow_pos (by omega : 0<t) k).trans_le hn)
  change |(IntervalFourier.count u a d N:ℝ)/N - (d-a)| ≤ _
  rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_iff₀ nr]
  change |(IntervalFourier.count u a d N:ℝ)-N*(d-a)| ≤ _
  nlinarith only [est,mul_le_mul_of_nonneg_left tiny nr.le,
    congrArg (fun z : ℝ => z*N) id,
    mul_le_mul_of_nonneg_right (show 12*w ≤ ε/2 by dsimp [w]; linarith) nr.le]

/-- One fixed signed expansion with positive discrepancy yields arbitrarily small
strictly positive discrepancies by explicitly adding inverse powers of `t`. -/
theorem arbitrarily_small_translations {b p C t : ℕ} (hb : 2≤b) (hp : p.Prime) (cop : b.Coprime p)
    (c : ℕ → ℤ) (cap : ∀ j, (c j).natAbs ≤ C) (ht : 1<t) (ct : b.Coprime t)
    (hx : 0 < limsup (radixDiscrepancy b (value b p c)) atTop) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ k : ℕ in atTop, let D := limsup (radixDiscrepancy b (value b p c + 1/(t:ℝ)^k)) atTop
      0 < D ∧ D < ε := by
  have h := (inverse_power_discrepancy_tendsto hb ht ct).const_mul (limsup (radixDiscrepancy b (value b p c)) atTop)
  rw [mul_zero] at h
  filter_upwards [h.eventually_lt_const he] with k bound
  let r : ℚ := 1/(t:ℚ)^k
  have cast : (r:ℝ) = 1/(t:ℝ)^k := by simp [r]
  dsimp only
  have eqn := translated_limsup hb hp cop c cap 1 one_ne_zero r
  simp only [Int.cast_one,one_mul,cast] at eqn
  rw [eqn]
  exact ⟨mul_pos hx (cast ▸ rational_discrepancy_pos b r),bound⟩

private lemma rational_shift_factor (b k : ℕ) (r : ℚ) :
    limsup (radixDiscrepancy b r) atTop = limsup (radixDiscrepancy b ((b:ℝ)^k*r)) atTop := by
  let t := (b:ℚ)^k*r
  obtain ⟨s,_,L,_,_,lp,_,per⟩ := rational_cycle b t
  have cast : (t:ℝ) = (b:ℝ)^k*r := by simp [t]
  have step (n : ℕ) : shift b (r:ℝ) (k+n) = shift b t n := by
    simp only [shift,cast,pow_add]; congr 1; ring
  have per' (n : ℕ) (hn : k+s≤n) : shift b (r:ℝ) (n+L) = shift b r n := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (by omega : k≤n)
    rw [Nat.add_assoc,step,step,per i (by omega)]
  rw [← cast,(rational_discrepancy_limit b r lp per').limsup_eq,
    (rational_discrepancy_limit b t lp per).limsup_eq]
  unfold disc; congr 1; ext v
  have eqn (i : ℕ) : (b:ℝ)^(k+s+i)*r = (b:ℝ)^(s+i)*t := by
    simp only [cast,pow_add]; ring
  simp only [eqn]

private lemma integer_factor (b : ℕ) (z : ℤ) : limsup (radixDiscrepancy b (z:ℝ)) atTop = 1 := by
  apply Tendsto.limsup_eq
  apply tendsto_const_nhds.congr'
  filter_upwards with N
  apply le_antisymm _ (radix_discrepancy_bounds b z N).2
  by_contra! low
  let D := radixDiscrepancy b z N
  let a := (1-D)/2
  have dp := (radix_discrepancy_bounds b z N).1
  have ap : 0<a := by dsimp [a,D]; linarith
  have al : a<1 := by dsimp [a,D]; linarith
  have allzero (n : ℕ) : shift b (z:ℝ) n=0 := by
    simpa only [shift,Int.cast_mul,Int.cast_pow,Int.cast_natCast] using Int.fract_intCast (R:=ℝ) ((b:ℤ)^n*z)
  have H := test_le (fun i => (b:ℝ)^i*(z:ℝ)) N ap.le al le_rfl
  change |frequency (shift b z) a 1 N-(1-a)| ≤ D at H
  simp [frequency,allzero,not_le.mpr ap] at H
  change D<1 at low; dsimp [a] at H; linarith [(abs_le.mp H).1]

/-- Numerical discrepancy can change after division by nine, even for the
explicit nonnormal transcendental example with alternating phases. -/
theorem division_by_nine_example :
    let c (j : ℕ) : ℤ := if j%2=0 then 1 else 0
    let x := 9*value 2 3 c+3/8
    limsup (radixDiscrepancy 2 x) atTop = 3/4 ∧
      limsup (radixDiscrepancy 2 (x/9)) atTop = 1/2 := by
  dsimp only
  let c (j : ℕ) : ℤ := if j%2=0 then 1 else 0
  have cap (j : ℕ) : (c j).natAbs ≤ 1 := by dsimp [c]; split <;> decide
  have original : limsup (radixDiscrepancy 2 (value 2 3 c)) atTop = 3/4 := binary_three_periods.2.1
  have dyadic := rational_shift_factor 2 3 (3/8)
  have third := rational_shift_factor 2 3 (1/24)
  norm_num at dyadic third
  have A := translated_limsup (b:=2) (p:=3) (by decide) (by decide) (by decide) c cap 9 (by decide) (3/8)
  have B := translated_limsup (b:=2) (p:=3) (by decide) (by decide) (by decide) c cap 1 one_ne_zero (1/24)
  have dy : limsup (radixDiscrepancy 2 (3/8)) atTop = 1 := by
    exact dyadic.trans (integer_factor 2 3)
  have th : limsup (radixDiscrepancy 2 (1/24)) atTop = 2/3 := by
    exact third.trans (by convert third_discrepancy_sharp.2 using 2; norm_num [asymptoticDiscrepancy])
  simp only [Int.cast_ofNat,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Int.cast_one,one_mul,original,dy,th,mul_one] at A B
  refine ⟨A,?_⟩
  change limsup (radixDiscrepancy 2 ((9*value 2 3 c+3/8)/9)) atTop = 1/2
  rw [show (9*value 2 3 c+3/8)/9 = value 2 3 c+1/24 by ring,B]; norm_num

end NormalityChecker.SignedPhases
