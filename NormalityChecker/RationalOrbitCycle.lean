module

public import NormalityChecker.SignedShellDiscrepancy

/-! Periodic interval counts for a rational radix orbit after its preperiod. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.SignedPhases

/-- The eventual reduced denominator is coprime to the base, including when the
original denominator has base-prime factors. The period need not be minimal. -/
theorem rational_cycle (b : ℕ) (r : ℚ) : ∃ s q L : ℕ, 0 < q ∧
    b.Coprime q ∧ 0 < L ∧ (∀ n, s≤n → ((b:ℚ)^n*r).den ∣ q) ∧
    ∀ n, s≤n → shift b (r:ℝ) (n+L) = shift b r n := by
  classical
  let R (n : ℕ) := (b:ℚ)^n*r
  let P (k : ℕ) := ∃ n, (R n).den = k
  have existsDen : ∃ k, P k := ⟨_,0,rfl⟩
  obtain ⟨s,hs⟩ := Nat.find_spec existsDen
  let q := (R s).den
  have low (n : ℕ) : q ≤ (R n).den := by
    dsimp [q]; rw [hs]; exact Nat.find_min' existsDen ⟨n,rfl⟩
  have sc : R (s+1) = b*R s := by dsimp [R]; rw [pow_succ']; ring
  have id : q = (R (s+1)).den * b.gcd q := by
    simpa [q,sc,Int.natAbs_mul,Nat.Coprime.gcd_mul_right_cancel _ (R s).reduced] using
      Rat.den_mul_den_eq_den_mul_gcd (b:ℚ) (R s)
  have qp : 0<q := Rat.pos _
  have cop : b.Coprime q := by
    change b.gcd q = 1
    have hi : q * b.gcd q ≤ q := (Nat.mul_le_mul_right _ (low (s+1))).trans_eq id.symm
    have one := Nat.le_of_mul_le_mul_left (hi.trans_eq (Nat.mul_one q).symm) qp
    have p := Nat.gcd_pos_of_pos_right b qp
    omega
  have div (n : ℕ) (hn : s≤n) : (R n).den ∣ q := by
    have eqn : R n = (↑(b^(n-s)):ℚ)*R s := by
      dsimp [R]; push_cast; rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hn]
    rw [eqn]; simpa [q] using Rat.mul_den_dvd (↑(b^(n-s)):ℚ) (R s)
  let L := q.totient
  have poweq := Nat.ModEq.pow_totient cop
  have diff : (q:ℤ) ∣ (b:ℤ)^L-1 := by
    simpa [L] using (Nat.modEq_iff_dvd.mp poweq.symm)
  refine ⟨s,q,L,qp,cop,Nat.totient_pos.mpr qp,div,?_⟩
  intro n hn
  obtain ⟨z,hz⟩ : ((R n).den:ℤ) ∣ (b:ℤ)^L-1 :=
    (Int.natCast_dvd_natCast.mpr (div n hn)).trans diff
  have H : (b:ℚ)^(n+L)*r = R n + (z*(R n).num:ℤ) := by
    have e : (b:ℚ)^L-1 = ((R n).den:ℚ)*z := by exact_mod_cast hz
    calc _ = R n + ((b:ℚ)^L-1)*R n := by dsimp [R]; rw [pow_add]; ring
         _ = _ := by
           have hnum := (div_eq_iff (by exact_mod_cast (R n).den_ne_zero : ((R n).den:ℚ)≠0)).mp (R n).num_div_den
           rw [e]; push_cast; linear_combination - (z:ℚ) * hnum
  unfold shift; have h := congrArg (fun t : ℚ => (t:ℝ)) H
  simp only [Rat.cast_mul,Rat.cast_pow,Rat.cast_add,Rat.cast_natCast,Rat.cast_intCast] at h
  rw [h,Int.fract_add_intCast]; simp [R]

/-- In a block starting anywhere after the preperiod, the error against one full
period is bounded by the period length for every interval. -/
theorem cycle_block_error (u : ℕ → ℝ) {s L : ℕ} (pos : 0<L)
    (per : ∀ n, s≤n → u (n+L)=u n) (a d : ℝ) (n B : ℕ) (hn : s≤n) :
    let w := frequency (fun i => u (s+i)) a d L
    |∑ i ∈ range B, ((if a≤u (n+i) ∧ u (n+i)<d then (1:ℝ) else 0) - w)| ≤ L := by
  classical
  let f (n : ℕ) : ℝ := if a≤u n ∧ u n<d then 1 else 0
  let w := frequency (fun i => u (s+i)) a d L
  let g (n : ℕ) := f n - w
  have wbd := frequency_bounds (fun i => u (s+i)) a d L
  have unit (j : ℕ) : |g j| ≤ 1 := by
    change |_ - frequency _ a d L| ≤ 1
    dsimp only [f]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith [wbd.1,wbd.2]
  have step (j : ℕ) (hj : s≤j) : g (j+L) = g j := by simp [g,f,per j hj]
  have full (j : ℕ) (hj : s≤j) : ∑ i ∈ range L, g (j+i) = 0 := by
    induction j,hj using Nat.le_induction with
    | base =>
      simp only [g,f,w,frequency,sum_sub_distrib,← sum_filter,sum_const,nsmul_eq_mul,card_range,mul_one]
      field_simp; ring
    | succ j h ih =>
      have A := sum_range_succ (fun i => g (j+i)) L
      have D := sum_range_succ' (fun i => g (j+i)) L
      simp only [step _ h,ih,zero_add] at A
      simp only [Nat.add_zero] at D
      simpa only [Nat.add_right_comm j 1, Nat.add_assoc, Nat.add_comm 1] using
        (show ∑ i ∈ range L, g (j+(i+1))=0 by linarith)
  have mult (k : ℕ) : ∑ i ∈ range (k*L), g (n+i) = 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,sum_range_add,ih,zero_add]; simpa [Nat.add_assoc] using full (n+k*L) (by omega)
  have cut : B/L*L + B%L = B := by simpa [Nat.mul_comm] using Nat.div_add_mod B L
  change |∑ i ∈ range B, g (n+i)| ≤ L
  conv_lhs => rw [← cut,sum_range_add,mult,zero_add]
  exact (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _ => unit _)).trans (by
    simp only [sum_const,card_range,nsmul_eq_mul,mul_one]; exact_mod_cast (Nat.mod_lt B pos).le))

/-- Every interval in any prefix differs from its limiting period frequency
by at most the combined length of the preperiod and one period, divided by N. -/
theorem cycle_frequency_error (u : ℕ → ℝ) {s L N : ℕ} (lp : 0<L)
    (per : ∀ n, s≤n → u (n+L)=u n) (sn : s≤N) (hn : 0<N) (a d : ℝ) :
    |frequency u a d N - frequency (fun i => u (s+i)) a d L| ≤ ((s:ℝ)+L)/N := by
  classical
  let w := frequency (fun i => u (s+i)) a d L
  let f (i : ℕ) := (if a≤u i ∧ u i<d then (1:ℝ) else 0) - w
  have ew := frequency_bounds (fun i => u (s+i)) a d L
  have unit (i : ℕ) : |f i| ≤ 1 := by dsimp [f,w]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith [ew.1,ew.2]
  have pre : |∑ i∈range s,f i| ≤ s :=
    (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _ => unit i)).trans_eq (by simp))
  have post : |∑ i∈range (N-s),f (s+i)| ≤ L := cycle_block_error u lp per a d s (N-s) le_rfl
  have total : |∑ i∈range N,f i| ≤ (s:ℝ)+L := by
    conv_lhs => rw [← Nat.add_sub_of_le sn,sum_range_add]
    exact (abs_add_le ..).trans (add_le_add pre post)
  simp only [f,sum_sub_distrib,← sum_filter,sum_const,nsmul_eq_mul,card_range,mul_one] at total
  have nr : (0:ℝ)<N := by exact_mod_cast hn
  change |(_/(N:ℝ)) - w| ≤ _
  rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_div_iff_of_pos_right nr]
  exact total

end NormalityChecker.SignedPhases
