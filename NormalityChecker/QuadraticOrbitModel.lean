module

public import NormalityChecker.ParameterTwoQuadratic
public import NormalityChecker.IndexedExpansion

/-! The actual rational model of an integer quadratic on the positive-index
parameter-two axis. Shell `r` below is [2·2^r, 4·2^r), so its usual index is r+1. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.QuadraticOrbit
open ParameterTwoSquare

abbrev linear := ParameterTwoQuadratic.linearPrefix

abbrev model (b : ℕ) (A B C : ℤ) (n : ℕ) : ℚ :=
  ParameterTwoQuadratic.«prefix» b n A B C

noncomputable def value (b : ℕ) (A B C : ℤ) : ℝ :=
  A * (StonehamStatements.stoneham b 2)^2 + B * StonehamStatements.stoneham b 2 + C

abbrev upperDen (b : ℕ) (A B C : ℤ) (r : ℕ) :=
  (model b A B C (3*2^r)).den

theorem shifted_tail {b : ℕ} (hb : 2 ≤ b) (A B C : ℤ) :
    Tendsto (fun n => (b : ℝ)^n * value b A B C - (model b A B C n : ℝ)) atTop (𝓝 0) := by
  let g (i : ℕ) : ℕ := 2^(i+1)
  let w (i : ℕ) := (1 / (2 : ℚ)^(i+1))
  have inj : Function.Injective g := fun i j h => by
    have := (Nat.pow_right_injective (by decide : 2 ≤ 2)) h
    omega
  have small : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i, N ≤ g i → |(w i : ℝ)| ≤ ε := by
    intro ε ep
    obtain ⟨N,large⟩ := exists_nat_gt (1/ε)
    refine ⟨N,fun i hi => ?_⟩
    have h : 1/ε ≤ (2:ℝ)^(i+1) := large.le.trans (by exact_mod_cast hi)
    simp only [w,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^(i+1))]
    rw [div_le_iff₀ (by positivity)]
    linarith only [(div_le_iff₀ ep).mp h, mul_comm ε ((2:ℝ)^(i+1))]
  have mem (n i : ℕ) : i ∈ range (Nat.log 2 n) ↔ g i ≤ n := by
    rw [mem_range]; change i+1 ≤ Nat.log 2 n ↔ 2^(i+1) ≤ n
    cases n with
    | zero => simp
    | succ n => exact Nat.le_log_iff_pow_le (by decide) (by omega)
  have ht := indexed_shift_error_signed hb g inj w small _ mem
  have lin : Tendsto (fun n => (b : ℝ)^n * StonehamStatements.stoneham b 2 - (linear b n : ℝ))
      atTop (𝓝 0) := by
    simpa only [g,w,StonehamStatements.stoneham,linear,ParameterTwoQuadratic.linearPrefix,term,Rat.cast_div,Rat.cast_one,
      Rat.cast_pow,Rat.cast_ofNat,Nat.cast_ofNat,div_div] using ht
  have S := ((ParameterTwoSquare.shifted_tail hb).const_mul (A:ℝ)).add (lin.const_mul (B:ℝ))
  simp only [mul_zero,add_zero] at S
  apply S.congr
  intro n; dsimp [model,ParameterTwoQuadratic.«prefix»,value]; push_cast; ring

private theorem linear_den {b n : ℕ} (hb : 0 < b) (hn : 0 < n) :
    (linear b n).den ∣ 2^(Nat.log 2 n) := by
  let k := Nat.log 2 n
  have cut : 2^k ≤ n := Nat.pow_log_le_self 2 hn.ne'
  let z := (b : ℤ)^(n-2^k) * axisNumerator b k
  have eqn : linear b n = (z : ℚ) / (2^k : ℕ) := by
    rw [eq_div_iff (by positivity)]
    dsimp only [z,linear,ParameterTwoQuadratic.linearPrefix]; push_cast
    rw [← clear_axis hb, weighted_eq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel cut]
    ring
  rw [eqn,div_eq_mul_inv]
  simpa [Rat.inv_natCast_den_of_pos (pow_pos (by decide : 0 < 2) k)] using
    Rat.mul_den_dvd (z : ℚ) (((2^k : ℕ):ℚ)⁻¹)

private theorem lower_terms_den {b n : ℕ} (hb : 0 < b) (hn : 0 < n) (B C : ℤ) :
    ((B:ℚ)*linear b n + C*(b:ℚ)^n).den ∣ 2^(Nat.log 2 n) := by
  rw [show (C:ℚ)*(b:ℚ)^n = ((C*(b:ℤ)^n : ℤ):ℚ) by push_cast; rfl,Rat.add_intCast_den]
  exact (by simpa using Rat.mul_den_dvd (B:ℚ) (linear b n) :
    ((B:ℚ)*linear b n).den ∣ (linear b n).den).trans (linear_den hb hn)

/-- Common denominator and a lower bound on its surviving part before the midpoint. -/
theorem shell_den {b r n : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hr : 1 ≤ r)
    (lo : 2^(r+1) ≤ n) (hi : n < 2^(r+2)) (A B C : ℤ) (nz : A ≠ 0) :
    (model b A B C n).den ∣ 2^(2*r) ∧
    (n < 3*2^r → 2^(2*r) ≤ A.natAbs * (model b A B C n).den * 2^(r+1)) := by
  have logn := Nat.log_eq_of_pow_le_of_lt_pow lo hi
  have pos := (pow_pos (by decide : 0<2) _).trans_le lo
  let R := (B:ℚ)*linear b n + C*(b:ℚ)^n
  have rd : R.den ∣ 2^(r+1) := logn ▸ lower_terms_den (by omega) pos B C
  have eqn : model b A B C n = (A:ℚ)*pre b n + R := by dsimp [model,ParameterTwoQuadratic.«prefix»,R]; ring
  have early (h : n < 3*2^r) : (pre b n).den = 2^(2*r) := by
    simpa only [two_mul] using (first_half_reduction (by omega) odd hr lo hi h).2
  constructor
  · rw [eqn]; apply (Rat.add_den_dvd_lcm ..).trans; apply Nat.lcm_dvd
    · apply (by simpa using Rat.mul_den_dvd (A:ℚ) (pre b n) :
        ((A:ℚ)*pre b n).den ∣ (pre b n).den).trans
      by_cases h : n < 3*2^r
      · rw [early h]
      · rw [(second_half_reduction (by omega) odd hr lo hi (by omega)).2]
        exact pow_dvd_pow _ (by omega)
    · exact rd.trans (pow_dvd_pow _ (by omega))
  · intro h
    let P := model b A B C n
    have recov : (A:ℚ)⁻¹*(P-R) = pre b n := by
      dsimp only [P]; rw [eqn,add_sub_cancel_right,inv_mul_cancel_left₀ (by exact_mod_cast nz)]
    have div := Rat.mul_den_dvd (A:ℚ)⁻¹ (P-R)
    rw [recov,Rat.inv_intCast_den,ite_eq_right nz,early h] at div
    have both := div.trans (Nat.mul_dvd_mul_left _ ((Rat.sub_den_dvd ..).trans (Nat.mul_dvd_mul_left P.den rd)))
    exact Nat.le_of_dvd (by have := Int.natAbs_pos.mpr nz; have := P.pos; positivity)
      (by simpa [Nat.mul_assoc,P] using both)

theorem follows {b n i : ℕ} (hb : 0 < b) (A B C : ℤ)
    (same : Nat.log 2 (n+i) = Nat.log 2 n)
    (free : ∀ a c, n < location a c → n+i < location a c) :
    model b A B C (n+i) = (b:ℚ)^i * model b A B C n := by
  simp only [model, ParameterTwoQuadratic.«prefix», ParameterTwoSquare.follows hb free]
  simp only [ParameterTwoQuadratic.linearPrefix,same,pow_add]; ring

/-- There are no quadratic insertions in the open upper half. -/
theorem upper_follows {b r i : ℕ} (hb : 0 < b) (A B C : ℤ) (hi : i < 2^r) :
    model b A B C (3*2^r+i) = (b:ℚ)^i * model b A B C (3*2^r) := by
  have start : 2^(r+1) = 2*2^r := pow_succ' ..
  have stop : 2^(r+2) = 4*2^r := by rw [pow_add]; ring
  have klog (t : ℕ) (ht : t < 2^r) : Nat.log 2 (3*2^r+t) = r+1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by rw [start]; omega) (by rw [stop]; omega)
  apply follows hb A B C ((klog i hi).trans (by simpa using (klog 0 (by positivity)).symm))
  intro a c entered
  by_contra! inc
  change 3*2^r < 2^(a+1)+2^(c+1) at entered
  change 2^(a+1)+2^(c+1) ≤ 3*2^r+i at inc
  have small {j : ℕ} (h : 2^j ≤ 3*2^r+i) : 2^j ≤ 2^r ∨ 2^j = 2*2^r := by
    have hj := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (show 2^j < 2^(r+2) by rw [stop]; omega)
    rcases le_or_gt j r with le | gt
    · exact Or.inl (Nat.pow_le_pow_right (by decide) le)
    · exact Or.inr (by rw [show j=r+1 by omega,start])
  rcases small (j:=a+1) ((Nat.le_add_right ..).trans inc) with h|h <;>
    rcases small (j:=c+1) ((Nat.le_add_left ..).trans inc) with h'|h' <;> omega

theorem upper_den_constant {b r i : ℕ} (odd : Odd b) (hb : 3 ≤ b) (hr : 1 ≤ r)
    (A B C : ℤ) (nz : A ≠ 0) (hi : i < 2^r) :
    (model b A B C (3*2^r+i)).den = upperDen b A B C r := by
  have top : 2^(r+2) = 4*2^r := by rw [pow_add]; ring
  have d := (shell_den hb odd hr (n:=3*2^r) (by rw [pow_succ']; omega)
    (by rw [top]; have := pow_pos (by decide : 0<2) r; omega) A B C nz).1
  let y := model b A B C (3*2^r)
  have cop : (b^i).Coprime y.den :=
    (Nat.Coprime.of_dvd_right d (odd.coprime_two_right.pow_right _)).pow_left i
  rw [upper_follows (by omega) A B C hi, ← Nat.cast_pow]
  change (((b^i:ℕ):ℚ)*y).den = y.den
  simp only [Rat.mul_den,Rat.den_natCast,Rat.num_natCast,one_mul,Int.natAbs_mul,
    Int.natAbs_natCast,(cop.mul_left y.reduced).gcd_eq_one,Nat.div_one]

/-- Normal prefixes force cancellation on the difference between the midpoint
and the right endpoint. A fixed factorial character detects every denominator
bounded by the same integer along any unbounded sequence of upper halves. -/
theorem upper_den_tendsto_of_normal {b : ℕ} (hb : 3 ≤ b) (odd : Odd b)
    (A B C : ℤ) (nz : A ≠ 0) (normal : NormalIn b (value b A B C)) :
    Tendsto (upperDen b A B C) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  let h : ℤ := M.factorial
  have ne : h ≠ 0 := by dsimp [h]; exact_mod_cast M.factorial_ne_zero
  let P := model b A B C
  let f (n : ℕ) := phase ((h:ℝ)*(P n:ℝ))
  have cancel : Tendsto (mean f) atTop (𝓝 0) := by
    simpa only [f,mean_phase] using
      (normalIn_iff_prefix_fourier (by omega) _ _ (shifted_tail (by omega : 2 ≤ b) A B C)).mp normal h ne
  obtain ⟨K, bound⟩ := eventually_atTop.mp ((mean_zero_iff_dyadic_cells f).mp cancel (1/8) (by norm_num))
  filter_upwards [eventually_ge_atTop (max K 1)] with r hr
  by_contra! small
  let t := 2^r
  have twice : 2^(r+1) = t+t := by dsimp [t]; rw [pow_succ]; omega
  have H (T : ℕ) (le : T ≤ t+t) : ‖∑ i ∈ range T, f (t+t+i)‖ ≤ (t:ℝ)/4 := by
    have H := bound (r+1) (by omega) T (twice ▸ le)
    rw [one_mul,twice] at H
    simpa only [t,Nat.cast_pow,Nat.cast_ofNat,pow_succ] using (H.trans_eq (by dsimp [t]; ring))
  have block : (∑ i ∈ range t, f (t+t+(t+i))) = (t:ℂ) := by
    calc _ = ∑ _i ∈ range t, (1:ℂ) := by
           apply sum_congr rfl; intro i hi
           let y := P (3*t+i)
           have den : y.den = upperDen b A B C r :=
             upper_den_constant odd hb (by omega) A B C nz (mem_range.mp hi)
           obtain ⟨v,hv⟩ := Nat.dvd_factorial y.pos (den ▸ small.le)
           have integer : (h:ℝ)*(y:ℝ) = ((v*y.num:ℤ):ℝ) := by
             have clear := congrArg (fun z : ℚ => (z:ℝ)) (Rat.den_mul_eq_num y)
             push_cast at clear
             dsimp [h]; push_cast; rw [hv]; push_cast; linear_combination (v:ℝ)*clear
           rw [show t+t+(t+i) = 3*t+i by omega]; change phase ((h:ℝ)*(y:ℝ)) = 1
           rw [integer]; simpa [phase,mul_comm] using Complex.exp_int_mul_two_pi_mul_I (v*y.num)
         _ = _ := by simp
  have decomp := sum_range_add (fun i => f (t+t+i)) t t
  simp only [block] at decomp
  have eqn : (t:ℂ) = (∑ i ∈ range (t+t), f (t+t+i)) - ∑ i ∈ range t, f (t+t+i) := by
    rw [decomp]; abel
  have impossible := (norm_sub_le _ _).trans (add_le_add (H _ le_rfl) (H t (Nat.le_add_right ..)))
  rw [← eqn,Complex.norm_natCast] at impossible
  have pos : 0 < (t:ℝ) := by dsimp [t]; positivity
  linarith

end NormalityChecker.QuadraticOrbit
