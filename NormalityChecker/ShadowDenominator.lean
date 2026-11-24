module

public import NormalityChecker.LogShadow
public import NormalityChecker.PrimeCancellation

/-! Denominator obstructions for the corrected logarithmic prefixes. -/
@[expose] public section
namespace NormalityChecker

private lemma upper_prime_difference {n r p : ℕ} (hp : p.Prime) (lo : p≤n) (hi : n+r+1<2*p) :
    ¬p∣(logDifference r n).den := by
  have noMultiple (j : ℕ) (hj : j≤r) : ¬p∣n+1+j := by
    rintro ⟨v,hv⟩; rcases v with _|_|v
    · simp at hv
    · simp at hv; omega
    · have H := Nat.mul_le_mul_left p (show 2≤v+1+1 by omega); omega
  have good : ∀ j≤r+1, ¬p∣(n+1).ascFactorial j := by
    intro j; induction j with
    | zero => simp [hp.not_dvd_one]
    | succ j ih => intro hj; rw [Nat.ascFactorial_succ,hp.dvd_mul]; exact not_or.mpr ⟨noMultiple j (by omega),ih (by omega)⟩
  have cle : (r.factorial:ℚ)=(n+1).ascFactorial (r+1)*logDifference r n := by
    unfold logDifference; rw [show n+r+1=n+(r+1) by omega,← Nat.factorial_mul_ascFactorial]; push_cast; field_simp [Nat.factorial_ne_zero]
  have pos : 0<(n+1).ascFactorial (r+1) := Nat.pos_of_ne_zero (fun z => (good _ le_rfl) (z ▸ dvd_zero _))
  exact fun d => good _ le_rfl (d.trans (reduced_info pos cle).1)

/-- Each odd prime in `((n+r)/2,n]` survives all `r` correction terms. -/
theorem logShadow_upper_prime {n r p : ℕ} (hp : p.Prime) (odd : p≠2) (lo : p≤n) (hi : n+r<2*p) :
    p∣(logShadow r n).den := by
  induction r with
  | zero =>
    have high : n<p^(1+1) := by simpa [sq] using (show n<2*p by omega).trans_le (Nat.mul_le_mul_right p hp.two_le)
    have one : n/p=1 := (Nat.div_eq_iff hp.pos).mpr ⟨by simpa using lo,by omega⟩
    have H := prime_cancellation (a:=1) hp odd (by decide) (by simpa using lo) high
    simp only [pow_one,one] at H
    apply H.mpr
    have e : partialLogTwo 1=1/2 := by norm_num [partialLogTwo]
    rw [e]; have num : ((1/2:ℚ).num.natAbs)=1 := by decide +kernel
    rw [num]; exact hp.not_dvd_one
  | succ r ih =>
    have old := ih (by omega)
    let z : ℚ := (-1)^r*logDifference r n
    have unit : ¬p∣z.den := by
      have dvd := Rat.mul_den_dvd ((-1:ℚ)^r) (logDifference r n)
      have sd : ((-1:ℚ)^r).den=1 := by exact_mod_cast Rat.den_intCast ((-1:ℤ)^r)
      rw [sd,one_mul] at dvd
      exact fun h => upper_prime_difference hp lo (by omega : n+r+1<2*p) (h.trans dvd)
    have e : logShadow r n=logShadow (r+1) n-z := by simp [logShadow,z]
    rw [e] at old
    exact (hp.dvd_mul.mp (old.trans (Rat.sub_den_dvd ..))).resolve_right unit

end NormalityChecker
