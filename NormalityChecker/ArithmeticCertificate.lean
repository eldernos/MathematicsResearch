module

public import NormalityChecker.SmoothOrbit

/-! Normality certificates for general rational prefixes with sparse insertions. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Sufficient conditions on rational prefixes. At every fixed denominator cutoff
`M`, the exceptional starts may include insertions, clearing delays and severe
cancellations. The polynomial exponent is fixed across all cutoffs and scales. -/
theorem normal_of_arithmetic_certificate {b c B L : ℕ} (hb : 2≤b) (hB : 0<B) (hL : 1<L)
    (x : ℝ) (P : ℕ → ℚ) (tail : Tendsto (fun n => (b:ℝ)^n*x-(P n:ℝ)) atTop (𝓝 0))
    (estimate : SmoothOrbitEstimate b c) (d : ℕ)
    (cert : ∀ u ∈ Ico 1 (L*B), ∀ M : ℕ, ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop,
      ∃ E : Finset ℕ, (E.card:ℝ) ≤ η*(L:ℝ)^k ∧ ∀ l<L^k, l∉E →
        let n := (u*L^k+l)*B^k
        M≤(P n).den ∧ (∃ j : ℕ, (P n).den ∣ c^j) ∧ (P n).den≤(B^k)^d ∧
          ∀ i<B^k, P (n+i)=(b:ℚ)^i*P n) : NormalIn b x := by
  apply normal_of_sparse_blocks hb hB hL x P tail
  intro h hh u hu η pos
  obtain ⟨M,bound⟩ := estimate d η pos
  filter_upwards [cert u hu (h.natAbs*M) η pos] with k hk
  obtain ⟨E,card,good⟩ := hk; refine ⟨E,card,?_⟩
  intro l hl he; obtain ⟨lo,⟨j,div⟩,hi,orb⟩ := good l hl he
  let n := (u*L^k+l)*B^k
  let y := (h:ℚ)*P n
  have dd : y.den ∣ (P n).den := by simpa [y] using Rat.mul_den_dvd (h:ℚ) (P n)
  have recover : (P n).den ∣ h.natAbs*y.den := by
    have e : (h:ℚ)⁻¹*y=P n := inv_mul_cancel_left₀ (by exact_mod_cast hh) _
    simpa only [e,Rat.inv_intCast_den,hh,ite_false] using Rat.mul_den_dvd (h:ℚ)⁻¹ y
  have hp := Int.natAbs_pos.mpr hh
  have low := Nat.le_of_mul_le_mul_left (lo.trans (Nat.le_of_dvd (Nat.mul_pos hp y.pos) recover)) hp
  have sm := bound y (B^k) low ⟨j,dd.trans div⟩ ((Nat.le_of_dvd (P n).pos dd).trans hi)
  change ‖∑ i ∈ range (B^k),phase ((h:ℝ)*P (n+i))‖ ≤ _
  have term (i : ℕ) (hi : i∈range (B^k)) : phase ((h:ℝ)*P (n+i))=phase ((b:ℝ)^i*y) := by
    have e : P (n+i)=(b:ℚ)^i*P n := orb i (mem_range.mp hi)
    rw [e]; dsimp [y]; push_cast; ring_nf
  rw [sum_congr rfl term]; simpa using sm

end NormalityChecker
