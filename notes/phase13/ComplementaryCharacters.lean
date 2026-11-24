import NormalityChecker.StrideDenominatorRate
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Standalone checks for the Gaussian prefix and the modular character estimate. -/

namespace Phase13.ComplementaryCharacters

open Finset

/-- Multiplication by 2+2i on the Gaussian integers in the basis (1,i).
Its j-th power has trace twice the real part of (2+2i)^j. -/
def G : Matrix (Fin 2) (Fin 2) ℤ := !![2, -2; 2, 2]

/-- Common numerator of the j-th Taylor terms, before division by j * 16^j. -/
def coeff (k : ℤ) (N j : ℕ) : ℤ :=
  (if 2*j ≤ N then 2*4^j else 0) -
  (if 3*j ≤ N then (1+k)*(-2)^j else 0) +
  (if 4*j ≤ N then 2*k else 0) -
  (if 5*j ≤ 2*N then k*(G^j).trace else 0)

def gaussianPrefix (k : ℤ) (N : ℕ) : ℚ :=
  2^N * ∑ i ∈ range (N/2), (coeff k N (i+1) : ℚ) / ((i+1 : ℕ) * 16^(i+1) : ℚ)

theorem gaussian_log_identity (k : ℝ) :
    -2*Real.log (3/4) + (1+k)*Real.log (9/8) - 2*k*Real.log (15/16) +
      k*Real.log (25/32) = Real.log 2 := by
  have h : Real.log ((9/8:ℝ) / (3/4)^2) = Real.log 2 := congrArg Real.log (by norm_num)
  have z : Real.log ((9/8:ℝ) * (25/32)) = Real.log ((15/16)^2) :=
    congrArg Real.log (by norm_num)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at z
  linear_combination h + k*z

noncomputable def z : ℂ := ⟨1/8, 1/8⟩

/-- All four Taylor series, with the Gaussian term taken in its real part. -/
theorem gaussian_series (k : ℝ) :
    HasSum (fun i : ℕ => 2*((1/4:ℝ)^(i+1)/(i+1)) -
      (1+k)*((-1/8:ℝ)^(i+1)/(i+1)) + 2*k*((1/16:ℝ)^(i+1)/(i+1)) -
      2*k*(z^(i+1)/(i+1)).re) (Real.log 2) := by
  have hn : ‖z‖^2 = 1/32 := by norm_num [Complex.sq_norm, Complex.normSq_apply,z]
  have hd : ‖1-z‖^2 = 25/32 := by norm_num [Complex.sq_norm, Complex.normSq_apply,z]
  have hl := congrArg Real.log hd
  rw [Real.log_pow] at hl
  have A := Real.hasSum_pow_div_log_of_abs_lt_one (x:=1/4) (by norm_num)
  have B := Real.hasSum_pow_div_log_of_abs_lt_one (x:=-1/8) (by norm_num)
  have C := Real.hasSum_pow_div_log_of_abs_lt_one (x:=1/16) (by norm_num)
  have D := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' (z:=z) (by nlinarith))
  have tot := ((((A.mul_left 2).sub (B.mul_left (1+k))).add (C.mul_left (2*k))).sub
    (D.mul_left (2*k)))
  norm_num only [show (1-1/4:ℝ)=3/4 by norm_num, show (1-(-1/8):ℝ)=9/8 by norm_num,
    show (1-1/16:ℝ)=15/16 by norm_num, Complex.neg_re, Complex.log_re] at tot
  convert tot using 1
  · simp only [neg_div]
  · linarith [gaussian_log_identity k, congrArg (k * ·) hl]

/-- In every characteristic p the trace gives the same first digit at j and pj. -/
theorem trace_frobenius (p j : ℕ) [Fact p.Prime] :
    (((G^(p*j)).trace : ℤ) : ZMod p) = (((G^j).trace : ℤ) : ZMod p) := by
  let f := Int.castRingHom (ZMod p)
  change f _ = f _
  rw [Nat.mul_comm p j, pow_mul, AddMonoidHom.map_trace f, Matrix.map_pow,
    ZMod.trace_pow_card, ZMod.pow_card, ← AddMonoidHom.map_trace]

private theorem pole_cancels {N p : ℕ} (hp : p.Prime) :
    (5*p ≤ 2*N → N < 3*p → (p : ℤ) ∣ coeff 2 N p) ∧
      (3*p ≤ N → N < 4*p → (p : ℤ) ∣ coeff 5 N p) := by
  let : Fact p.Prime := ⟨hp⟩
  have ht := trace_frobenius p 1
  simp only [mul_one, pow_one] at ht
  have hG : G.trace = 4 := by decide
  rw [hG] at ht
  constructor <;> intro lo hi <;> apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
  · simp [coeff, show 2*p ≤ N by omega, show ¬3*p ≤ N by omega,
      show ¬4*p ≤ N by omega, lo, ht, ZMod.pow_card]
  · simp [coeff, show 2*p ≤ N by omega, lo, show ¬4*p ≤ N by omega,
      show 5*p ≤ 2*N by omega, ht, ZMod.pow_card]
    ring

private theorem regular_frac {p j : ℕ} (a : ℤ) (h : ¬p ∣ j) : ¬p ∣ ((a : ℚ)/j).den := by
  have d := Rat.den_dvd a (j:ℤ)
  rw [Rat.divInt_eq_div, Int.cast_natCast] at d
  exact fun v => h (v.trans (by exact_mod_cast d))

private theorem regular_of_cancel {N p : ℕ} {k : ℤ} (hp : p.Prime) (odd : 2 < p)
    (hi : N < 4*p) (cancel : (p : ℤ) ∣ coeff k N p) : ¬p ∣ (gaussianPrefix k N).den := by
  have unit : ¬ p ∣ 16 := fun h => by
    have pow : p ∣ 2^4 := by simpa using h
    exact (Nat.not_dvd_of_pos_of_lt (by decide) odd) (hp.dvd_of_dvd_pow pow)
  have reg (j : ℕ) (pos : 0 < j) (le : j ≤ N/2) :
      ¬p ∣ ((coeff k N j : ℚ) / ((j : ℚ) * 16^j)).den := by
    have hu : ¬ p ∣ 16^j := fun h => unit (hp.dvd_of_dvd_pow h)
    by_cases hj : p ∣ j
    · have jeq : j = p := by
        obtain ⟨k, hk⟩ := hj
        rcases k with _ | _ | k
        · simp at hk; omega
        · simpa using hk
        · have big := Nat.mul_le_mul_left p (show 2 ≤ k+1+1 by omega)
          omega
      subst j
      obtain ⟨b, hb⟩ := cancel
      have eqn : (coeff k N p : ℚ) / ((p : ℚ)*16^p) = (b : ℚ)/(16^p : ℕ) := by
        rw [hb]; push_cast
        field_simp [show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne_zero]
      rw [eqn]
      exact regular_frac _ hu
    · have h := regular_frac (coeff k N j) (show ¬ p ∣ j*16^j from
          fun h => (hp.dvd_mul.mp h).elim hj hu)
      simpa using h
  have partialSum (m : ℕ) (hm : m ≤ N/2) :
      ¬ p ∣ (∑ i ∈ range m, (coeff k N (i+1) : ℚ) / ((i+1 : ℕ)*16^(i+1) : ℚ)).den := by
    induction m with
    | zero => simp [hp.not_dvd_one]
    | succ m ih =>
      rw [sum_range_succ]
      exact fun h => (hp.dvd_mul.mp (h.trans (Rat.add_den_dvd ..))).elim
        (ih (by omega)) (reg (m+1) (by omega) hm)
  intro h
  obtain left | right := hp.dvd_mul.mp (h.trans (Rat.mul_den_dvd ..))
  · have d : ((2:ℚ)^N).den = 1 := by simp
    exact hp.not_dvd_one (d ▸ left)
  · exact partialSum _ le_rfl right

/-- The two choices of the zero identity remove different bands from the actual denominators. -/
theorem lost_bands {N p : ℕ} (hp : p.Prime) (odd : 2 < p) :
    (5*p ≤ 2*N → N < 3*p → ¬p ∣ (gaussianPrefix 2 N).den) ∧
      (3*p ≤ N → N < 4*p → ¬p ∣ (gaussianPrefix 5 N).den) :=
  ⟨fun a b => regular_of_cancel hp odd (by omega) ((pole_cancels hp).1 a b),
   fun a b => regular_of_cancel hp odd b ((pole_cancels hp).2 a b)⟩

private theorem integral_trace (j : ℕ) :
    ∃ a : ℤ, 2^((5*j+1)/2)*(G^j).trace = 16^j*a := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases h : j < 4
    · interval_cases j
      · exact ⟨2, by decide⟩
      · exact ⟨2, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨-2, by decide⟩
    · let m := j-4
      obtain ⟨a, ha⟩ := ih m (by dsimp [m]; omega)
      have hj : j = m+4 := by dsimp [m]; omega
      have ht : (G^(m+4)).trace = -64*(G^m).trace := by
        rw [pow_add, show G^4 = (-64:ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) by decide,
          Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul]
      use -a
      rw [hj, ht, show (5*(m+4)+1)/2 = (5*m+1)/2+10 by omega, pow_add, pow_add]
      linear_combination -65536*ha

private theorem integral_coeff (k : ℤ) (N j : ℕ) : (16:ℤ)^j ∣ 2^N * coeff k N j := by
  have extend (a b : ℤ) {e : ℕ} (cut : e ≤ N) (id : 2^e*a = 16^j*b) :
      (16:ℤ)^j ∣ 2^N*a := by
    use 2^(N-e)*b
    calc 2^N*a = 2^(N-e)*(2^e*a) := by rw [←mul_assoc, ←pow_add, Nat.sub_add_cancel cut]
         _ = _ := by rw [id]; ring
  simp only [coeff, mul_sub, mul_add]
  apply dvd_sub
  · apply dvd_add
    · apply dvd_sub
      · split_ifs with h
        · apply extend _ 2 h
          rw [pow_mul, mul_left_comm, ←mul_pow]; norm_num; ring
        · simp
      · split_ifs with h
        · apply extend _ ((1+k)*(-1)^j) h
          rw [pow_mul, mul_left_comm, ←mul_pow]
          rw [show (2:ℤ)^3*(-2) = 16*(-1) by norm_num, mul_pow]; ring
        · simp
    · split_ifs with h
      · apply extend _ (2*k) h
        rw [pow_mul]; norm_num
      · simp
  · split_ifs with h
    · obtain ⟨a, ha⟩ := integral_trace j
      apply extend _ (k*a) (show (5*j+1)/2 ≤ N by omega)
      linear_combination k*ha
    · simp

theorem common_denominator (k : ℤ) (N : ℕ) :
    (gaussianPrefix k N).den ∣ Nat.lcmUpto (N/2) := by
  let term (i : ℕ) : ℚ := 2^N*((coeff k N (i+1):ℚ)/((i+1:ℕ)*16^(i+1):ℚ))
  have dt (i : ℕ) : (term i).den ∣ i+1 := by
    obtain ⟨a, ha⟩ := integral_coeff k N (i+1)
    have hq := congrArg (fun z : ℤ => (z:ℚ)) ha
    push_cast at hq
    have eqn : term i = (a:ℚ)/(i+1:ℕ) := by
      dsimp [term]; push_cast
      field_simp
      linear_combination hq
    have h := Rat.den_dvd a ((i+1:ℕ):ℤ)
    rw [Rat.divInt_eq_div, Int.cast_natCast] at h
    rw [eqn]; exact_mod_cast h
  have go (m : ℕ) (hm : m ≤ N/2) : (∑ i ∈ range m, term i).den ∣ Nat.lcmUpto (N/2) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      exact (Rat.add_den_dvd_lcm ..).trans (Nat.lcm_dvd (ih (by omega))
        ((dt m).trans (NormalityChecker.index_dvd_lcm (by omega) hm)))
  simpa only [gaussianPrefix, mul_sum, term] using go (N/2) le_rfl

open Filter NormalityChecker.StrideDenominatorRate

/-- The exponent of the actual Gaussian denominator is eventually below
every number strictly larger than 5/12. -/
theorem eventually_below {a : ℝ} (ha : 5/12 < a) :
    ∀ᶠ n : ℕ in atTop, Real.log (gaussianPrefix 5 n).den / n < a := by
  have finite_bound (n : ℕ) (hn : 8 ≤ n) :
      Real.log (gaussianPrefix 5 n).den ≤ Real.log (Nat.lcmUpto (n/2)) -
        (Chebyshev.theta (n/3:ℕ) - Chebyshev.theta (n/4:ℕ)) := by
    let S := (n/3).primesLE \ (n/4).primesLE
    have sub := Nat.primesLE_mono (show n/4 ≤ n/3 by omega)
    have get {p : ℕ} (h : p∈S) : p.Prime ∧ 2<p ∧ 3*p≤n ∧ n<4*p := by
      obtain ⟨x,y⟩ := mem_sdiff.mp h
      obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp x
      have l := lt_of_not_ge (fun z => y (Nat.mem_primesLE.mpr ⟨z,pr⟩))
      exact ⟨pr, by omega, by omega, by omega⟩
    have dvd : (∏ p∈S,p) ∣ Nat.lcmUpto (n/2) :=
      prod_primes_dvd _ (fun p h => (get h).1.prime)
        (fun p h => NormalityChecker.index_dvd_lcm (get h).1.pos (by have := (get h).2.2.1; omega))
    have cop : Nat.Coprime (∏ p∈S,p) (gaussianPrefix 5 n).den :=
      Nat.coprime_prod_left_iff.mpr fun p h => (get h).1.coprime_iff_not_dvd.mpr
        ((lost_bands (get h).1 (get h).2.1).2 (get h).2.2.1 (get h).2.2.2)
    have joint := cop.mul_dvd_of_dvd_of_dvd dvd (common_denominator 5 n)
    have pos := prod_pos (s:=S) (f:=id) (fun p h => (get h).1.pos)
    have bound := Real.log_le_log (show (0:ℝ)<((∏ p∈S,p)*(gaussianPrefix 5 n).den:ℕ) by
        exact_mod_cast Nat.mul_pos pos (gaussianPrefix 5 n).pos)
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.lcmUpto_pos _) joint))
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast pos.ne') (by exact_mod_cast (gaussianPrefix 5 n).pos.ne'),
        Nat.cast_prod, Real.log_prod (fun p h => by exact_mod_cast (get h).1.ne_zero)] at bound
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
      ←sum_sdiff sub, add_sub_cancel_right]
    dsimp [S] at bound; linarith
  have grow := Nat.tendsto_div_const_atTop (by decide : 2≠0)
  have lcm := (Nat.tendsto_log_lcmUpto_div_atTop.comp grow).mul (floor_ratio 2 (by decide))
  have lim := lcm.sub ((theta_ratio 3 (by decide)).sub (theta_ratio 4 (by decide)))
  filter_upwards [eventually_ge_atTop 8, grow.eventually_gt_atTop 0,
    lim.eventually_lt_const (by norm_num at *; linarith : _ < a)] with n hn hp bound
  change Real.log (Nat.lcmUpto (n/2))/(n/2:ℕ)*(((n/2:ℕ):ℝ)/n) -
    (Chebyshev.theta (n/3:ℕ)/n-Chebyshev.theta (n/4:ℕ)/n) < a at bound
  rw [div_mul_div_cancel₀ (by exact_mod_cast hp.ne'), ←sub_div, ←sub_div] at bound
  exact (div_le_div_of_nonneg_right (finite_bound n hn) (by positivity)).trans_lt bound

/-- The one-step forcing costs at most nine times the mean squared distance
from a common phase, after summing and shifting the endpoint. -/
theorem forcing_distance (u v c : ℂ) (hu : ‖u‖ = 1) (hc : ‖c‖ = 1) :
    ‖v*c-u^2‖^2 ≤ 3*‖v-c‖^2 + 6*‖u-c‖^2 := by
  have id : v*c-u^2 = (v-c)*c + (c-u)*(c+u) := by ring
  have add : ‖c+u‖ ≤ 2 := by linarith [norm_add_le c u]
  have b : ‖v*c-u^2‖ ≤ ‖v-c‖ + 2*‖u-c‖ := by
    rw [id]
    apply (norm_add_le ..).trans
    rw [norm_mul, norm_mul, hc, mul_one, norm_sub_rev c u]
    linarith [mul_le_mul_of_nonneg_left add (norm_nonneg (u-c))]
  have sq := pow_le_pow_left₀ (norm_nonneg _) b 2
  nlinarith [sq_nonneg (‖v-c‖-‖u-c‖)]


/-- Finite interval transfer, including the endpoint cost, for an arbitrary
sequence on the unit circle. -/
theorem forcing_sum (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (T : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    ∑ i ∈ range T, ‖z (i+1)*c-(z i)^2‖^2 ≤
      9*(∑ i ∈ range T, ‖z i-c‖^2) + 12 := by
  let d (i : ℕ) := ‖z i-c‖^2
  have step := sum_le_sum (s:=range T) (fun i _ => forcing_distance (z i) (z (i+1)) c (hz i) hc)
  change _ ≤ ∑ i ∈ range T, (3*d (i+1)+6*d i) at step
  rw [sum_add_distrib, ←mul_sum, ←mul_sum] at step
  have telescope := sum_range_sub d T
  rw [sum_sub_distrib] at telescope
  have e : ‖z T-c‖ ≤ 2 := by linarith [norm_sub_le (z T) c, hz T]
  have bound : d T ≤ 4 := by
    dsimp [d]; nlinarith [pow_le_pow_left₀ (norm_nonneg _) e 2]
  change _ ≤ 9*(∑ i ∈ range T, d i)+12
  linarith [show 0 ≤ d 0 from sq_nonneg _]

end Phase13.ComplementaryCharacters
