module

public import NormalityChecker.Basic

@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker

/-- Summing disjoint intervals from earlier scales improves the single-interval bound.
The hypothesis only has to hold from some scale onward. -/
theorem geometric_cells_limsup {c l : ℕ} (hc : 1<c) (hl : 0<l) (hlc : l<c)
    {v : ℕ → ℝ} {a d : ℝ}
    (H : ∀ᶠ k : ℕ in atTop, ∀ n, l*c^k ≤ n → n<c^(k+1) → a≤v n ∧ v n<d) :
    ((c:ℝ)-l)/(c-1) ≤ limsup (frequency v a d) atTop := by
  classical
  let visited (N : ℕ) := (range N).filter (fun n => a≤v n ∧ v n<d)
  have hC : (1:ℝ)<c := by exact_mod_cast hc
  obtain ⟨J,hJ⟩ := eventually_atTop.mp H
  have count (k : ℕ) (hk : J≤k) :
      ((c:ℝ)-l)*((c:ℝ)^k-c^J) ≤ (c-1)*(visited (c^k)).card := by
    induction k, hk using Nat.le_induction with
    | base => simp only [sub_self,mul_zero]; positivity
    | succ k hk ih =>
      let A := visited (c^k)
      let B := Ico (l*c^k) (c^(k+1))
      have hs : A ∪ B ⊆ visited (c^(k+1)) := by
        intro n hn
        rcases mem_union.mp hn with h₁ | h₂
        · obtain ⟨hn,hv⟩ := mem_filter.mp h₁
          exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hn).trans
            (Nat.pow_lt_pow_right hc (Nat.lt_succ_self _))),hv⟩
        · obtain ⟨hn,hv⟩ := mem_Ico.mp h₂
          exact mem_filter.mpr ⟨mem_range.mpr hv,hJ k hk n hn hv⟩
      have hdis : Disjoint A B := by
        apply disjoint_left.mpr
        intro n hn hn'
        have h₁ := mem_range.mp (mem_filter.mp hn).1
        have h₂ := (mem_Ico.mp hn').1
        exact h₁.not_ge ((Nat.le_mul_of_pos_left _ hl).trans h₂)
      have hcard := card_le_card hs
      rw [card_union_of_disjoint hdis,Nat.card_Ico] at hcard
      have hle : l*c^k ≤ c^(k+1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hlc.le
      have hcard' := Nat.cast_le (α:=ℝ).mpr hcard
      push_cast [Nat.cast_sub hle] at hcard'
      dsimp only [A] at hcard'
      rw [pow_succ (c:ℝ)] at hcard' ⊢
      nlinarith [mul_le_mul_of_nonneg_left hcard' (sub_nonneg.mpr hC.le)]
  have hn0 (N : ℕ) : 0≤frequency v a d N := by unfold frequency; positivity
  have hn1 (N : ℕ) : frequency v a d N ≤ 1 := by
    cases N with
    | zero => simp [frequency]
    | succ n =>
      apply (div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
      exact_mod_cast (card_filter_le (range (n+1)) _).trans_eq (card_range _)
  apply (le_limsup_iff (isCoboundedUnder_le_of_le _ hn0)
    (isBoundedUnder_of_eventually_le (Eventually.of_forall hn1))).mpr
  intro y hy
  have htop := tendsto_pow_atTop_atTop_of_one_lt hc
  apply htop.frequently
  let A := ((c:ℝ)-l)/(c-1)
  have hsmall : Tendsto (fun k : ℕ => A*(c:ℝ)^J/(c:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=A*(c:ℝ)^J)).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hC))
  apply Eventually.frequently
  filter_upwards [eventually_ge_atTop J,hsmall.eventually_lt_const (sub_pos.mpr hy)] with k hk hsmall'
  have he : A*(c-1)=(c:ℝ)-l := div_mul_cancel₀ _ (sub_pos.mpr hC).ne'
  have hq : (0:ℝ)<(c:ℝ)^k := by positivity
  have H₁ := (div_lt_iff₀ hq).mp hsmall'
  have H₂ := count k hk
  change y < ((visited (c^k)).card:ℝ)/((c^k:ℕ):ℝ)
  push_cast
  apply (lt_div_iff₀ hq).mpr
  have hcell : A*((c:ℝ)^k-c^J) ≤ (visited (c^k)).card := by
    apply (mul_le_mul_iff_left₀ (sub_pos.mpr hC)).mp
    calc
      _ = ((c:ℝ)-l)*((c:ℝ)^k-c^J) := by rw [← he]; ring
      _ ≤ _ := by simpa only [mul_comm] using H₂
  linarith

end NormalityChecker
