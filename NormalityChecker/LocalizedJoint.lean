module

public import NormalityChecker.FullPolynomialNormality
public import NormalityChecker.JointWeyl
public import NormalityChecker.LocalizedJointStatements

/-! Distinct pole orders on the same smooth support. -/
@[expose] public section
noncomputable section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.LocalizedSupport
open PolynomialMasks

/-- Collect a nonzero character over a common denominator. The largest *active*
pole is unique, even if coordinates of greater order have coefficient zero. -/
private theorem collect_character {b d : ℕ} (hb : 2 ≤ b) (S : Finset ℕ) (keep : ℕ → Bool)
    (P : Fin d → ℚ[X]) (unit : ∀ i, (P i).eval 0 ≠ 0) (s : Fin d → ℕ)
    (pos : ∀ i, 0 < s i) (inj : Function.Injective s) (h : Fin d → ℤ) (nz : h ≠ 0) :
    ∃ t : ℕ, 0 < t ∧ ∃ Q : ℚ[X], Q.eval 0 ≠ 0 ∧
      ∑ i, (h i : ℝ) * maskedValue b S keep (P i) (s i) = maskedValue b S keep Q t := by
  classical
  let A := univ.filter (fun i => h i ≠ 0)
  have active (i) : i ∈ A ↔ h i ≠ 0 := by simp [A]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp nz
  obtain ⟨j, hj, largest⟩ := A.exists_max_image s ⟨k, (active k).mpr hk⟩
  let t := s j
  let Q : ℚ[X] := ∑ i ∈ A, C (h i : ℚ) * X^(t - s i) * P i
  have eval (z : ℚ) : Q.eval z = ∑ i ∈ A, (h i : ℚ) * z^(t - s i) * (P i).eval z := by
    simp [Q, eval_finsetSum]
  refine ⟨t, pos j, Q, ?_, ?_⟩
  · rw [eval, sum_eq_single_of_mem j hj]
    · simpa [t] using mul_ne_zero (Int.cast_ne_zero.mpr ((active j).mp hj) : (h j : ℚ) ≠ 0) (unit j)
    · intro i hi ne
      have lt : s i < t := lt_of_le_of_ne (largest i hi) (fun e => ne (inj e))
      simp [zero_pow (Nat.sub_pos_of_lt lt).ne']
  let term (i : Fin d) (m : ℕ) : ℝ := (weights S keep (P i) (s i) m : ℝ) / (b : ℝ)^m
  have summable_term (i : Fin d) : Summable (term i) := summable_weight hb (weights_growth ..)
  have head : (∑ i ∈ A, (h i : ℝ) * maskedValue b S keep (P i) (s i)) =
      ∑ i, (h i : ℝ) * maskedValue b S keep (P i) (s i) := by
    apply sum_subset (subset_univ _)
    intro i _ hi
    simp [not_ne_iff.mp (mt (active i).mpr hi)]
  rw [← head]
  change (∑ i ∈ A, (h i : ℝ) * ∑' m, term i m) = _
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun i _ => (summable_term i).mul_left (h i : ℝ))]
  apply tsum_congr
  intro m
  by_cases hit : m ∈ Nat.factoredNumbers S ∧ keep m = true
  · have m0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hit.1.1
    have scale (i : Fin d) (hi : i ∈ A) :
        (h i : ℚ) * ((P i).eval (m : ℚ) / (m : ℚ)^(s i)) =
        (h i : ℚ) * (m : ℚ)^(t - s i) * (P i).eval (m : ℚ) / (m : ℚ)^t := by
      rw [pow_sub₀ _ m0 (largest i hi)]
      field_simp
      rfl
    have coeff : (∑ i ∈ A, (h i : ℚ) * weights S keep (P i) (s i) m) =
        weights S keep Q t m := by
      simp only [weights, ite_eq_left hit, eval]
      rw [sum_div]
      exact sum_congr rfl scale
    change (∑ i ∈ A, (h i : ℝ) * ((weights S keep (P i) (s i) m : ℝ) / (b : ℝ)^m)) =
      (weights S keep Q t m : ℝ) / (b : ℝ)^m
    simp only [mul_div_assoc', ← sum_div]
    congr 1
    exact_mod_cast coeff
  · simp [term, weights, hit]

/-- A scalar criterion for a shared mask lifts to a joint theorem for distinct
positive pole orders and arbitrary rational polynomial numerators nonzero at zero. -/
theorem joint_of_masked_poles {b d : ℕ} (hb : 2 ≤ b) (S : Finset ℕ) (keep : ℕ → Bool)
    (scalar : ∀ (Q : ℚ[X]) (t : ℕ), Q.eval 0 ≠ 0 → 0 < t → NormalIn b (maskedValue b S keep Q t))
    (P : Fin d → ℚ[X]) (unit : ∀ i, (P i).eval 0 ≠ 0) (s : Fin d → ℕ)
    (pos : ∀ i, 0 < s i) (inj : Function.Injective s) :
    JointUniform b (fun i => maskedValue b S keep (P i) (s i)) := by
  apply JointWeyl.rectangle_of_scalar_normal
  intro h nz
  obtain ⟨t, ht, Q, q0, eqn⟩ := collect_character hb S keep P unit s pos inj h nz
  rw [eqn]
  exact scalar Q t q0 ht

/-- Rational Laurent weights of distinct exact pole orders on a common full
finite prime support give simultaneous rectangle frequencies. -/
theorem joint_full_polynomial_orders {b d : ℕ} (hb : 2 ≤ b) (S : Finset ℕ)
    (primes : ∀ p ∈ S, p.Prime) (off : ∃ p ∈ S, ¬ p ∣ b)
    (P : Fin d → ℚ[X]) (unit : ∀ i, (P i).eval 0 ≠ 0) (s : Fin d → ℕ)
    (pos : ∀ i, 0 < s i) (inj : Function.Injective s) :
    JointUniform b (fun i => maskedValue b S (fun _ => true) (P i) (s i)) := by
  apply joint_of_masked_poles hb S _ _ P unit s pos inj
  intro Q t q0 ht
  have nz : Q ≠ 0 := by rintro rfl; simp at q0
  exact (full_rational_normal_iff hb S primes Q nz).mpr ⟨(rootMultiplicity_eq_zero q0) ▸ ht, off⟩

/-- On a single off-radix prime axis the same vector theorem holds on every
unbounded common mask. The gaps between retained exponents may be unbounded. -/
theorem joint_infinite_axis_orders {b p d : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (off : ¬ p ∣ b)
    (keep : ℕ → Bool) (often : ∀ J : ℕ, ∃ k ≥ J, keep (p^k) = true)
    (P : Fin d → ℚ[X]) (unit : ∀ i, (P i).eval 0 ≠ 0) (s : Fin d → ℕ)
    (pos : ∀ i, 0 < s i) (inj : Function.Injective s) :
    JointUniform b (fun i => maskedValue b {p} keep (P i) (s i)) :=
  joint_of_masked_poles hb {p} keep
    (fun Q _ q0 ht => infinite_axis_normal hb hp off ht Q q0 keep often) P unit s pos inj

/-- For a nonempty vector on a single off-radix prime axis, unboundedness
of the shared mask is necessary and sufficient for joint uniformity. -/
theorem joint_axis_orders_iff {b p d : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (off : ¬ p ∣ b)
    (hd : 0 < d) (keep : ℕ → Bool) (P : Fin d → ℚ[X]) (unit : ∀ i, (P i).eval 0 ≠ 0)
    (s : Fin d → ℕ) (pos : ∀ i, 0 < s i) (inj : Function.Injective s) :
    JointUniform b (fun i => maskedValue b {p} keep (P i) (s i)) ↔
      ∀ J : ℕ, ∃ k ≥ J, keep (p^k) = true := by
  refine ⟨fun joint => ?_, fun often => joint_infinite_axis_orders hb hp off keep often P unit s pos inj⟩
  let i : Fin d := ⟨0, hd⟩
  exact (axis_normal_iff hb hp off (pos i) (P i) (unit i) keep).mp (joint.normalIn hb i)

/-- In odd radix, on any finite prime support containing two, a common mask may
vary arbitrarily away from the sufficiently late powers of two. -/
theorem joint_late_twos_orders {b d : ℕ} (hb : 2 ≤ b) (odd : ¬ 2 ∣ b) (S : Finset ℕ)
    (primes : ∀ p ∈ S, p.Prime) (two : 2 ∈ S) (keep : ℕ → Bool)
    (late : ∀ᶠ k : ℕ in atTop, keep (2^k) = true)
    (P : Fin d → ℚ[X]) (unit : ∀ i, (P i).eval 0 ≠ 0) (s : Fin d → ℕ)
    (pos : ∀ i, 0 < s i) (inj : Function.Injective s) :
    JointUniform b (fun i => maskedValue b S keep (P i) (s i)) :=
  joint_of_masked_poles hb S keep
    (fun _ _ q0 ht => normal_of_late_twos hb odd ht q0 S primes two keep late) P unit s pos inj

private theorem smooth_iff (S : Finset ℕ) (m : ℕ) :
    LocalizedJointStatements.Smooth S m ↔ m ∈ Nat.factoredNumbers S :=
  ⟨fun h => Nat.mem_factoredNumbers'.mpr h.2,
    fun h => ⟨Nat.pos_of_ne_zero h.1, Nat.mem_factoredNumbers'.mp h⟩⟩

private theorem independent_value_eq (b s : ℕ) (S : Finset ℕ) :
    LocalizedJointStatements.value b s S = powerValue b s S := by
  classical
  apply tsum_congr
  intro i
  by_cases h : i+1 ∈ Nat.factoredNumbers S <;>
    simp [powerCoefficient, smooth_iff, h]

private theorem powerValue_eq_masked (b s : ℕ) (S : Finset ℕ) :
    powerValue b s S = maskedValue b S (fun _ => true) 1 s := by
  classical
  let f (m : ℕ) := (weights S (fun _ => true) 1 s m : ℝ) / (b : ℝ)^m
  have cover : Function.support f ⊆ Set.range Nat.succ := by
    rintro (_ | m) hm
    · have excluded : 0 ∉ Nat.factoredNumbers S := fun h => h.1 rfl
      exact False.elim (hm (by simp [f, weights, excluded]))
    · exact ⟨m, rfl⟩
  change powerValue b s S = ∑' m, f m
  rw [← Nat.succ_injective.tsum_eq cover]
  apply tsum_congr
  intro i
  by_cases h : i+1 ∈ Nat.factoredNumbers S <;>
    simp [f, powerCoefficient, weights, h, Nat.succ_eq_add_one]

/-- Paper II, Corollary 1.3. Joint visits of the distinct unsigned orders to
every half-open rectangle converge to the product of its side lengths. -/
theorem joint_full_orders {b d : ℕ} (hb : 2 ≤ b) (S : Finset ℕ) (primes : ∀ p ∈ S, p.Prime)
    (off : ∃ p ∈ S, ¬ p ∣ b) (s : Fin d → ℕ) (pos : ∀ i, 0 < s i) (inj : Function.Injective s)
    (a c : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (hac : ∀ i, a i ≤ c i) (hc : ∀ i, c i ≤ 1) :
    Tendsto (rectangleFrequency (fun n i => shift b (powerValue b (s i) S) n) a c)
      atTop (𝓝 (∏ i, (c i - a i))) := by
  simp_rw [powerValue_eq_masked]
  exact joint_full_polynomial_orders hb S primes off (fun _ => 1) (by simp) s pos inj a c ha hac hc

/-- The independent positive-index series and direct position count satisfy the corollary. -/
theorem distinct_orders_checked : LocalizedJointStatements.DistinctOrders := by
  intro b d hb _ S primes off s pos inj a c ha hac hc
  simp_rw [independent_value_eq]
  exact joint_full_orders hb S primes off s pos inj a c ha hac hc

end NormalityChecker.LocalizedSupport
