module

public import NormalityChecker.MaskWindows

/-! Concentration on finite rational grids and the integer-polynomial classification. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

/-- A condition absent from every sufficiently large clean block has density zero. -/
theorem exceptional_frequency (S : Finset ℕ) (bad : ℕ → Prop) [DecidablePred bad]
    (clean : ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n → ∀ i<2^k, ¬bad (n+i)) :
    Tendsto (fun N => (((range N).filter bad).card:ℝ)/N) atTop (𝓝 0) := by
  let f (_ : Unit) (n : ℕ) : ℂ := if bad n then 1 else 0
  have H := transfer S f (fun _ _ => by dsimp [f]; split <;> simp)
    (fun _ => 0) (fun _ => le_rfl) (by
      intro η pos; filter_upwards [clean] with k free n hn _
      rw [sum_eq_zero (fun i hi => ite_eq_right (free n hn i (mem_range.mp hi)))]
      simp; positivity)
  rw [Metric.tendsto_atTop]; intro ε pos
  obtain ⟨K,hK⟩ := eventually_atTop.mp (H (ε/2) (by positivity))
  refine ⟨K+1,fun N hn => ?_⟩
  have upper := hK N (by omega) ()
  simp only [f,sum_boole,Complex.norm_natCast,sum_const_zero,add_zero] at upper
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ (by exact_mod_cast (show 0<N by omega))]
  exact upper.trans_lt (mul_lt_mul_of_pos_right (by linarith) (by exact_mod_cast (show 0<N by omega)))

theorem interval_le_radix {b N : ℕ} (x : ℝ) {a c : ℝ} (ha : 0≤a) (hlt : a<c) (hc : c≤1) :
    |frequency (shift b x) a c N-(c-a)| ≤ radixDiscrepancy b x N := by
  apply le_csSup (s:={d | ∃ a c : ℝ, 0≤a ∧ a<c ∧ c≤1 ∧ d=|frequency (shift b x) a c N-(c-a)|})
  · refine ⟨1,?_⟩; rintro _ ⟨u,v,hu,lt,hv,rfl⟩; have f := frequency_bounds (shift b x) u v N
    rw [abs_le]; constructor <;> linarith [f.1,f.2]
  · exact ⟨a,c,ha,hlt,hc,rfl⟩

/-- The reduced prefix on every sufficiently large clean block lies on the
grid of spacing 1/L. -/
def GridPrefixes (b L : ℕ) (S : Finset ℕ) (a : ℕ → ℚ) : Prop :=
  ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n → (pre b a n).den ∣ L

theorem grid_avoids {b L : ℕ} (hb : 2≤b) (hL : 0<L) {S : Finset ℕ} {a : ℕ → ℚ}
    (growth : PolyGrowth a) (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (grid : GridPrefixes b L S a) {δ : ℝ} (pos : 0<δ) :
    Tendsto (frequency (shift b (series b a)) (δ/L) ((1-δ)/L)) atTop (𝓝 0) := by
  classical
  let x := series b a
  have lp : (0:ℝ)<L := by exact_mod_cast hL
  apply exceptional_frequency S
  filter_upwards [grid,clean_approx hb growth supp (div_pos pos lp)] with k denom near n h i hi
  obtain ⟨q,hq⟩ := denom n h
  let z : ℤ := (b:ℤ)^i*q*(pre b a n).num
  have model : (L:ℝ)*((b:ℝ)^i*(pre b a n:ℝ)) = z := by
    have hq' : (L:ℝ) = (pre b a n).den*q := by exact_mod_cast hq
    have eqn := Rat.den_mul_eq_num (pre b a n)
    have hr : ((pre b a n).den:ℝ)*(pre b a n:ℝ)=(pre b a n).num := by exact_mod_cast eqn
    dsimp [z]; push_cast; rw [hq']; linear_combination (b:ℝ)^i*q*hr
  let y := (b:ℝ)^(n+i)*x
  have err := near n h i hi
  have close : |(L:ℝ)*y-z|<δ := by
    rw [← model,← mul_sub,abs_mul,abs_of_pos lp,mul_comm,← lt_div_iff₀ lp]; exact err
  rintro ⟨lo,up⟩
  change δ/L ≤ Int.fract y at lo
  change Int.fract y < (1-δ)/L at up
  rw [div_le_iff₀ lp] at lo; rw [lt_div_iff₀ lp] at up
  rw [Int.fract] at lo up
  have bounds := abs_lt.mp close
  have small : (0:ℝ)<(z:ℝ)-(L:ℝ)*⌊y⌋ ∧ (z:ℝ)-(L:ℝ)*⌊y⌋<1 := by
    constructor <;> nlinarith only [lo,up,bounds.1,bounds.2]
  have hz : 0<z-(L:ℤ)*⌊y⌋ ∧ z-(L:ℤ)*⌊y⌋<1 := by exact_mod_cast small
  omega

/-- Concentration on the 1/L grid leaves a gap of length 1/L and precludes normality. -/
theorem grid_discrepancy {b L : ℕ} (hb : 2≤b) (hL : 0<L) {S : Finset ℕ} {a : ℕ → ℚ}
    (growth : PolyGrowth a) (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (grid : GridPrefixes b L S a) :
    1/(L:ℝ) ≤ liminf (radixDiscrepancy b (series b a)) atTop ∧ ¬ NormalIn b (series b a) := by
  let x := series b a
  have lp : (0:ℝ)<L := by exact_mod_cast hL
  have one : (1:ℝ)≤L := by exact_mod_cast hL
  have zero := fun {δ : ℝ} (pos : 0<δ) => grid_avoids hb hL growth supp grid pos
  constructor
  · apply le_of_forall_pos_le_add; intro ε pos
    let δ := min (1/4:ℝ) (ε/4)
    have dp : 0<δ := lt_min (by norm_num) (by positivity)
    have tiny : δ≤ε/4 := min_le_right ..
    have small : δ≤1/4 := min_le_left ..
    have H := le_liminf_of_le (f:=atTop)
      (isCoboundedUnder_ge_of_le _ (fun N => (radix_discrepancy_bounds b x N).2))
      (a:=1/(L:ℝ)-ε) (by
        filter_upwards [(zero dp).eventually_lt_const dp] with N few
        have I := interval_le_radix (b:=b) (N:=N) x (div_nonneg dp.le lp.le)
          ((div_lt_div_iff_of_pos_right lp).mpr (by linarith : δ<1-δ))
          ((div_le_one lp).mpr (by linarith))
        have low := (abs_le.mp I).1
        change frequency (shift b x) _ _ N<δ at few
        have cost := div_le_self dp.le one
        rw [sub_div] at low few
        linarith)
    linarith
  · intro normal
    let δ := (1/4:ℝ)
    let l := δ/L
    let u := (1-δ)/L
    have hl : 0≤l := by dsimp [l,δ]; positivity
    have lt : l<u := (div_lt_div_iff_of_pos_right lp).mpr (by norm_num [δ])
    have hu : u≤1 := (div_le_one lp).mpr (by dsimp [δ]; linarith)
    have HF := (anchored_frequency_of_normal normal (hl.trans lt.le) hu).sub (anchored_frequency_of_normal normal hl (lt.le.trans hu))
    have H : Tendsto (frequency (shift b x) l u) atTop (𝓝 (u-l)) :=
      HF.congr (fun N => (anchored_difference _ hl lt.le N).symm)
    have eqn := tendsto_nhds_unique H (zero (by norm_num : 0<δ))
    linarith

theorem maximal_of_grid_one {b : ℕ} (hb : 2≤b) {S : Finset ℕ} {a : ℕ → ℚ}
    (growth : PolyGrowth a) (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (grid : GridPrefixes b 1 S a) :
    Tendsto (radixDiscrepancy b (series b a)) atTop (𝓝 1) := by
  have lower := (grid_discrepancy hb (by decide) growth supp grid).1
  norm_num at lower
  rw [tendsto_order]; constructor
  · intro z hz; exact eventually_lt_of_lt_liminf (hz.trans_le lower)
      (isBoundedUnder_of_eventually_ge (.of_forall fun N => (radix_discrepancy_bounds b _ N).1))
  · intro z hz; exact .of_forall fun N => (radix_discrepancy_bounds b _ N).2.trans_lt hz

/-- A common rational coefficient denominator with its radix part absorbed in bˡ.
If t=0 the smooth primes may be arbitrary. -/
theorem grid_of_denominator {b t L l : ℕ} (hb : 2≤b) (hL : 0<L) {S : Finset ℕ} {a : ℕ → ℚ}
    (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (den : ∀ m∈Nat.factoredNumbers S, (a m).den ∣ (L*b^l)*m^t)
    (base : t=0 ∨ ∀ p∈S, p∣b) : GridPrefixes b L S a := by
  have clear := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul (4*(t:ℝ)+l)
  simp only [pow_one,mul_zero] at clear
  filter_upwards [eventually_ge_atTop 1,clear.eventually_le_const zero_lt_one] with k hk budget n hn
  let J := 2*(k+1)
  have bound : n ≤ 2^J := by
    apply (Nat.le_add_right n (2^k)).trans (hn.bound.trans_eq _)
    dsimp [J]; rw [Nat.mul_add,Nat.mul_one,pow_add,Nat.mul_comm 2 k,pow_mul]; ring
  rw [← mul_div_assoc,div_le_iff₀ (by positivity),one_mul] at budget
  have enough : (4*t+l)*k ≤ 2^k := by exact_mod_cast budget
  have delay : l+J*t ≤ 2^k := by
    dsimp [J]; nlinarith [Nat.mul_le_mul_left l hk,Nat.mul_le_mul_left t hk]
  apply (Rat.den_sum_dvd_lcm_den ..).trans; apply Finset.lcm_dvd
  intro m hm; have mn := mem_range_succ_iff.mp hm
  by_cases sm : m∈Nat.factoredNumbers S
  · have d : m^t ∣ b^(J*t) := by
      rcases base with rfl|support
      · simp
      · rw [pow_mul]; exact pow_dvd_pow_of_dvd (LocalizedSupport.cofactor_dvd (by omega : 0<b) support sm (mn.trans bound)) _
    have past := hn.old m sm (by have : 0<2^k := pow_pos (by decide) _; omega)
    rw [← Nat.cast_pow]; apply cleared_term _ hL.ne'
    apply (den m sm).trans
    calc L*b^l*m^t ∣ L*b^l*b^(J*t) := Nat.mul_dvd_mul_left _ d
         _ = L*b^(l+J*t) := by rw [pow_add,mul_assoc]
         _ ∣ L*b^(n-m) := Nat.mul_dvd_mul_left _ (pow_dvd_pow _ (by omega))
  · simp [supp m sm]

/-- Cancellation of the factor at zero holds term by term, for rational coefficients
and every mask, including all instances of a removable monomial denominator. -/
theorem masked_cancel (b r t : ℕ) (S : Finset ℕ) (keep : ℕ → Bool) (P : ℚ[X]) :
    maskedValue b S keep (X^r*P) (r+t) = maskedValue b S keep P t := by
  unfold maskedValue; congr 1; funext m
  by_cases sm : m∈Nat.factoredNumbers S <;> by_cases km : keep m=true <;> simp [weights,sm,km,pow_add]
  field_simp [sm.1]

theorem integer_grid {b t : ℕ} (hb : 2≤b) (S : Finset ℕ) (keep : ℕ → Bool) (G : ℤ[X])
    (base : t=0 ∨ ∀ p∈S, p∣b) :
    Tendsto (radixDiscrepancy b (maskedValue b S keep (G.map (algebraMap ℤ ℚ)) t)) atTop (𝓝 1) := by
  let P := G.map (algebraMap ℤ ℚ)
  have eval (m : ℕ) : (sample G m : ℚ)=(1:ℤ)*P.eval (m:ℚ) := by
    simp only [Int.cast_one,one_mul,P]; exact (eval_map_apply (p:=G) (algebraMap ℤ ℚ) (m:ℤ)).symm
  apply maximal_of_grid_one hb (weights_growth ..) (weights_supported S keep P t)
  apply grid_of_denominator (l:=0) hb (by decide) (weights_supported S keep P t) _ base
  intro m hm; simpa using coefficient_den (by decide : (1:ℤ)≠0) eval S keep t m hm

theorem integer_mask_maximal {b s r : ℕ} (hb : 2≤b) (S : Finset ℕ) (keep : ℕ → Bool) (G : ℤ[X])
    (cases : s≤r ∨ ∀ p∈S, p∣b) :
    Tendsto (radixDiscrepancy b (maskedValue b S keep ((X^r*G).map (algebraMap ℤ ℚ)) s)) atTop (𝓝 1) := by
  rcases cases with le|base
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le le
    rw [pow_add,mul_assoc,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
    have he := masked_cancel b s 0 S keep ((X^j*G).map (algebraMap ℤ ℚ))
    simp only [Nat.add_zero] at he
    rw [he]
    exact integer_grid hb S keep _ (Or.inl rfl)
  · exact integer_grid hb S keep _ (Or.inr base)

/-- Full classification for integral polynomials. The root multiplicity is the
order of vanishing at zero and places no restriction on the total degree. -/
theorem integer_full_classification {b s : ℕ} (hb : 2≤b) (S : Finset ℕ)
    (primes : ∀ p∈S,p.Prime) (P : ℤ[X]) (nz : P≠0) :
    limsup (radixDiscrepancy b (maskedValue b S (fun _ => true) (P.map (algebraMap ℤ ℚ)) s)) atTop = 1 ↔
      s ≤ P.rootMultiplicity 0 ∨ ∀ p∈S,p∣b := by
  let r := P.rootMultiplicity 0
  obtain ⟨G,fac,unit⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd nz 0
  simp only [map_zero,sub_zero] at fac unit
  change P=X^r*G at fac
  change _ ↔ s≤r ∨ _
  constructor
  · intro maximal; by_contra! bad
    obtain ⟨lt,p,mem,off⟩ := bad
    let Q := G.map (algebraMap ℤ ℚ)
    have g0 : G.eval 0≠0 := by simpa [X_dvd_iff,coeff_zero_eq_eval_zero] using unit
    have q0 : Q.eval 0≠0 := by
      have cast := eval_map_apply (p:=G) (algebraMap ℤ ℚ) (0:ℤ)
      simpa [Q] using (show (G.map (algebraMap ℤ ℚ)).eval ((algebraMap ℤ ℚ) 0)≠0 by rw [cast]; change ((G.eval 0 : ℤ):ℚ)≠0; exact_mod_cast g0)
    have H := late_powers_discrepancy hb (primes p mem) off (Nat.sub_pos_of_lt lt) q0 S primes mem
      (fun _ => true) (.of_forall fun _ => rfl)
    conv at maximal => lhs; rw [fac,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
      show s=r+(s-r) by omega,masked_cancel]
    rw [maximal] at H
    have hp : (1:ℝ)<p := by exact_mod_cast (primes p mem).one_lt
    linarith [one_div_pos.mpr (sub_pos.mpr hp)]
  · intro h
    rw [fac]
    exact (integer_mask_maximal hb S (fun _ => true) G h).limsup_eq

end NormalityChecker.PolynomialMasks
