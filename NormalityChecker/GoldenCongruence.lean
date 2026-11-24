module

public import NormalityChecker.GoldenOrbit

/-! A congruence obstruction for certifying small Zeckendorf indices. -/
@[expose] public section
open Real Filter
open scoped goldenRatio Topology
namespace NormalityChecker

private def fibStep (m : ℕ) : Equiv.Perm (ZMod m × ZMod m) where
  toFun x := (x.2,x.1+x.2)
  invFun x := (x.2-x.1,x.1)
  left_inv := by rintro ⟨x,y⟩; simp
  right_inv := by rintro ⟨x,y⟩; simp

private theorem fib_state (m j : ℕ) : (fibStep m ^ j) (0,1) =
    ((Nat.fib j : ZMod m),(Nat.fib (j+1) : ZMod m)) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ',Equiv.Perm.mul_apply,ih,Nat.fib_add_two]; simp [fibStep]

private theorem large_fib_one (m J : ℕ) [NeZero m] :
    ∃ j≥J, (Nat.fib j : ZMod m)=1 := by
  let h := orderOf (fibStep m)
  have pos : 0<h := orderOf_pos _
  let k := h*J
  have id : fibStep m ^ k=1 := by rw [show k=h*J from rfl,pow_mul,pow_orderOf_eq_one,one_pow]
  have pair := fib_state m k
  rw [id] at pair
  exact ⟨k+1,by dsimp [k]; nlinarith, (congrArg Prod.snd pair).symm⟩

/-- Every residue class contains starts with arbitrarily long doubling blocks
on which every least occupied index exceeds any prescribed cutoff. In particular
a condition on the residues of the input integers alone cannot certify a hit. -/
theorem golden_high_indices_in_every_class (m : ℕ) [NeZero m] (r K T : ℕ) :
    ∃ M : ℕ, 0<M ∧ (M:ZMod m)=r ∧ ∀ i≤T, K<leastFibIndex (2^i*M) := by
  let a := r+m
  have ap : 0<a := Nat.add_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne m))
  let q := φ⁻¹
  have qp : 0<q := inv_pos.mpr goldenRatio_pos
  have ql : q<1 := inv_lt_one_of_one_lt₀ one_lt_goldenRatio
  have cap : 0<(2:ℝ)^T*a := by positivity
  obtain ⟨J,small⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos qp (K+1)) cap) ql
  obtain ⟨j,late,cong⟩ := large_fib_one m (J+1)
  have fp : 0<Nat.fib j := Nat.fib_pos.mpr (by omega)
  refine ⟨a*Nat.fib j,Nat.mul_pos ap fp,by simp [a,cong],?_⟩
  intro i hi
  let v := 2^i*a
  have vp : 0<v := Nat.mul_pos (by positivity) ap
  have upper : turnDistance ((v*Nat.fib j:ℕ)*φ) ≤ (v:ℝ)*q^j := by
    apply (round_le _ ((v*Nat.fib (j+1):ℕ):ℤ)).trans
    have h := fib_succ_sub_goldenRatio_mul_fib j
    push_cast
    rw [show (v:ℝ)*Nat.fib j*φ-v*Nat.fib (j+1)= -((v:ℝ)*(Nat.fib (j+1)-φ*Nat.fib j)) by ring,h,
      abs_neg,abs_mul,abs_pow,abs_of_neg goldenConj_neg,← inv_goldenRatio,abs_of_nonneg (Nat.cast_nonneg v)]
  have vbound : (v:ℝ) ≤ (2:ℝ)^T*a := by dsimp [v]; push_cast; gcongr; norm_num
  have tiny := (mul_le_mul vbound (pow_le_pow_of_le_one qp.le ql.le (by omega : J≤j))
    (pow_nonneg qp.le j) cap.le).trans_lt (by simpa [mul_comm] using (lt_div_iff₀ cap).mp small)
  have lower := (golden_zeckendorf_bounds (Nat.mul_pos vp fp)).1
  by_contra! low
  rw [← Nat.mul_assoc] at low
  have order : q^(K+1)≤q^(leastFibIndex (v*Nat.fib j)+1) :=
    pow_le_pow_of_le_one qp.le ql.le (Nat.succ_le_succ low)
  exact (not_lt_of_ge (order.trans lower)) (upper.trans_lt tiny)

end NormalityChecker
