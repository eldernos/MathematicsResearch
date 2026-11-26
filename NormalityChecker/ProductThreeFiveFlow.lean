module

public import NormalityChecker.ProductThreeFiveResidues
public import NormalityChecker.LocalizedMesh

/-! Simultaneous cancellations on long intervals from the two logarithmic axes. -/
@[expose] public section
namespace NormalityChecker.ProductThreeFive

/-- Arbitrarily late powers have ratio between 1 and 5/4 even when both
exponents must be divisible by a prescribed positive integer. -/
theorem aligned_powers (H A : ℕ) (hH : 0<H) :
    ∃ K L : ℕ, A≤K ∧ H∣K ∧ H∣L ∧ 3^K<5^L ∧ 4*5^L<5*3^K := by
  let d : Localized.Parameters := ⟨5,5,3,by decide,by decide,Nat.prime_three,dvd_rfl,by decide⟩
  let δ := (5/4:ℝ)^((H:ℝ)⁻¹)
  have bigger : 1<δ := Real.one_lt_rpow (by norm_num) (by positivity)
  have pos : 0<(3:ℝ)^A := by positivity
  obtain ⟨a,i,lo,hi⟩ := Localized.threshold_between d
    (x:=(3:ℝ)^A) (y:=3^A*δ) (one_le_pow₀ (by norm_num))
    (by simpa only [mul_one] using mul_lt_mul_of_pos_left bigger pos)
  change (3:ℝ)^A < 5^a/3^i at lo
  change (5:ℝ)^a/3^i < 3^A*δ at hi
  have den : 0<(3:ℝ)^i := by positivity
  have low : (3:ℝ)^(A+i) < 5^a := by rw [pow_add]; exact (lt_div_iff₀ den).mp lo
  have high : (5:ℝ)^a < 3^(A+i)*δ := by
    rw [pow_add]; convert (div_lt_iff₀ den).mp hi using 1; ring
  refine ⟨(A+i)*H,a*H,(Nat.le_add_right A i).trans (Nat.le_mul_of_pos_right _ hH),
    dvd_mul_left ..,dvd_mul_left ..,?_,?_⟩
  · exact_mod_cast (by simpa only [pow_mul] using pow_lt_pow_left₀ low (by positivity) hH.ne' :
      (3:ℝ)^((A+i)*H) < 5^(a*H))
  · have bound := pow_lt_pow_left₀ high (by positivity) hH.ne'
    rw [mul_pow,Real.rpow_inv_natCast_pow (by norm_num : (0:ℝ)≤5/4) hH.ne'] at bound
    have h : (4:ℝ)*5^(a*H)<5*3^((A+i)*H) := by rw [pow_mul,pow_mul]; linarith
    exact_mod_cast h

/-- Both full prime powers disappear throughout a whole interval of length
comparable to its start, on arbitrarily large ternary shells. -/
theorem simultaneous_top_loss (A : ℕ) :
    ∃ K L : ℕ, A ≤ K ∧ 3^K<5^L ∧ 4*5^L<5*3^K ∧
      ∀ n, 3^K+5^L ≤ n → n<3*3^K →
        ¬3^K ∣ (pre n).den ∧ ¬5^L ∣ (pre n).den := by
  obtain ⟨K,L,hK,mK,mL,ratio,cap⟩ := aligned_powers 4 (A+1) (by decide)
  have kp : 0<K := by omega
  have lp : 0<L := by
    by_contra! h
    have := Nat.one_le_pow K 3 (by decide)
    simp [Nat.eq_zero_of_le_zero h] at ratio
  refine ⟨K,L,by omega,ratio,cap,fun n lo hi => ?_⟩
  have Klog := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 3^K≤n)
    (by rwa [pow_succ'] : n<3^(K+1))
  have Llog := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 5^L≤n)
    (by rw [pow_succ']; omega : n<5^(L+1))
  have J := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 5^L≤n-3^K)
    (by rw [pow_succ']; omega : n-3^K<5^(L+1))
  have I := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 3^K≤n-5^L)
    (by rw [pow_succ']; omega : n-5^L<3^(K+1))
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero kp.ne'
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero lp.ne'
  rw [ternary_survival_iff Klog.symm,quinary_survival_iff Llog.symm,J,I]
  simp only [not_not]
  exact ⟨Nat.mod_eq_zero_of_dvd ((by decide : 2∣4).trans mL),Nat.mod_eq_zero_of_dvd mK⟩

end NormalityChecker.ProductThreeFive
