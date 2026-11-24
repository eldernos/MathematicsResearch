module

public import NormalityChecker.SmoothOrbit

/-! Normality certificates for general rational prefixes with sparse insertions. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Distance in turns from a phase difference to its nearest integer. -/
noncomputable def turnDistance (x : ℝ) := |x - round x|

/-- A separate integral shift can be removed at each sample. -/
theorem phase_model_sum_bound (h : ℤ) (T : ℕ) (f g : ℕ → ℝ) :
    ‖∑ i ∈ range T, phase (h*f i)‖ ≤ ‖∑ i ∈ range T, phase (h*g i)‖ +
      (2*Real.pi*|(h:ℝ)|) * ∑ i ∈ range T, turnDistance (f i-g i) := by
  let F i := phase (h*f i)
  let G i := phase (h*g i)
  have term (i : ℕ) : ‖F i-G i‖ ≤ (2*Real.pi*|(h:ℝ)|)*turnDistance (f i-g i) := by
    let z := round (f i-g i)
    have hz : phase ((h*z:ℤ):ℝ) = 1 := by simpa [phase,mul_comm] using Complex.exp_int_mul_two_pi_mul_I (h*z)
    have eqn : phase (h*((g i)+(z:ℝ))) = G i := by rw [mul_add,phase_add,← Int.cast_mul,hz,mul_one]
    change ‖phase _ - G i‖ ≤ _
    rw [← eqn]; apply (phase_sub_le ..).trans_eq
    rw [show (h:ℝ)*f i-h*(g i+z)=h*(f i-g i-z) by ring,abs_mul]; simp only [turnDistance,z,mul_assoc]
  have diff := (norm_sum_le (range T) (fun i => F i-G i)).trans (sum_le_sum (fun i _ => term i))
  rw [sum_sub_distrib,← mul_sum] at diff
  change ‖∑ i ∈ range T, F i‖ ≤ ‖∑ i ∈ range T, G i‖ + _
  exact le_trans (norm_le_norm_add_norm_sub' _ _) (by linarith only [diff])

/-- Finite-cutoff Weyl bound with separate costs for model cancellation, mean
error in turns, exceptional full blocks, and the final partial block. -/
theorem approximate_prefix_bound (h : ℤ) (f : ℕ → ℝ) (model : ℕ → ℕ → ℝ)
    {start B L T : ℕ} (hb : 0<B) (len : T≤L*B) (E : Finset ℕ) {ε δ : ℝ} (he : 0≤ε) (hd : 0≤δ)
    (orbit : ∀ l<L, l∉E → ‖∑ i ∈ range B, phase (h*model l i)‖ ≤ ε*B)
    (close : ∀ l<L, l∉E → ∑ i ∈ range B, turnDistance (f (start+l*B+i)-model l i) ≤ δ*B) :
    ‖∑ i ∈ range T, phase (h*f (start+i))‖ ≤
      (ε+2*Real.pi*|(h:ℝ)| * δ)*(L*B)+(E.card+1:ℝ)*B := by
  apply prefix_block_bound (fun n => phase (h*f n)) (fun n => (norm_phase _).le) hb len E (by positivity)
  intro l hl hg
  apply (phase_model_sum_bound h B (fun i => f (start+l*B+i)) (model l)).trans
  exact (add_le_add (orbit l hl hg) (mul_le_mul_of_nonneg_left (close l hl hg) (by positivity))).trans_eq (by ring)

private lemma model_orbit_bound {b c d M T : ℕ} {η : ℝ} (h : ℤ) (hh : h≠0) (model : ℚ)
    (bound : ∀ y : ℚ, ∀ t : ℕ, M≤y.den → (∃ j : ℕ, y.den ∣ c^j) → y.den≤t^d →
      ‖∑ i ∈ range t, phase ((b:ℝ)^i*y)‖ ≤ η*t)
    (lo : h.natAbs*M≤model.den) (div : model.den∣c^j) (hi : model.den≤T^d) :
    ‖∑ i ∈ range T, phase ((h:ℝ)*((b:ℝ)^i*model))‖ ≤ η*T := by
  let y := (h:ℚ)*model
  have dd : y.den ∣ (model).den := by simpa [y] using Rat.mul_den_dvd (h:ℚ) (model)
  have recover : (model).den ∣ h.natAbs*y.den := by
    have e : (h:ℚ)⁻¹*y=model := inv_mul_cancel_left₀ (by exact_mod_cast hh) _
    simpa only [e,Rat.inv_intCast_den,hh,ite_false] using Rat.mul_den_dvd (h:ℚ)⁻¹ y
  have hp := Int.natAbs_pos.mpr hh
  have low := Nat.le_of_mul_le_mul_left (lo.trans (Nat.le_of_dvd (Nat.mul_pos hp y.pos) recover)) hp
  have sm := bound y T low ⟨j,dd.trans div⟩ ((Nat.le_of_dvd (model).pos dd).trans hi)
  convert sm using 3; dsimp [y]; push_cast; ring_nf

/-- A good block can use any smooth rational orbit whose mean phase distance is
small. Its initial rational value may be chosen independently on each block. -/
theorem normal_of_approximate_arithmetic_certificate {b c B L : ℕ} (hb : 2≤b) (hB : 0<B) (hL : 1<L)
    (x : ℝ) (P : ℕ → ℚ) (tail : Tendsto (fun n => (b:ℝ)^n*x-(P n:ℝ)) atTop (𝓝 0))
    (estimate : SmoothOrbitEstimate b c) (d : ℕ)
    (cert : ∀ u ∈ Ico 1 (L*B), ∀ M : ℕ, ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop,
      ∃ E : Finset ℕ, (E.card:ℝ) ≤ η*(L:ℝ)^k ∧ ∀ l<L^k, l∉E →
        let n := (u*L^k+l)*B^k
        ∃ y : ℚ, M≤y.den ∧ (∃ j : ℕ, y.den ∣ c^j) ∧ y.den≤(B^k)^d ∧
          ∑ i ∈ range (B^k), turnDistance ((P (n+i):ℝ)-(b:ℝ)^i*y) ≤ η*(B:ℝ)^k) : NormalIn b x := by
  apply normal_of_sparse_blocks hb hB hL x P tail
  intro h hh u hu η pos
  let C := 2*Real.pi*|(h:ℝ)|
  have cpos : 0≤C := by dsimp [C]; positivity
  let δ := η/(1+C)
  have den : 0<1+C := by linarith
  have dp : 0<δ := div_pos pos den
  have le : δ≤η := div_le_self pos.le (by linarith)
  obtain ⟨M,bound⟩ := estimate d δ dp
  filter_upwards [cert u hu (h.natAbs*M) δ dp] with k hk
  obtain ⟨E,card,good⟩ := hk
  refine ⟨E,card.trans (by gcongr),?_⟩
  intro l hl he
  obtain ⟨y,lo,⟨j,div⟩,hi,close⟩ := good l hl he
  let n := (u*L^k+l)*B^k
  have orbit := model_orbit_bound h hh y bound lo div hi
  have H := phase_model_sum_bound h (B^k) (fun i => (P (n+i):ℝ)) (fun i => (b:ℝ)^i*y)
  apply H.trans ((add_le_add (by simpa using orbit : _ ≤ δ*(B:ℝ)^k) (mul_le_mul_of_nonneg_left close cpos)).trans_eq _)
  have hd : δ*(1+C)=η := div_mul_cancel₀ _ den.ne'
  rw [← hd]; ring

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
  apply normal_of_approximate_arithmetic_certificate hb hB hL x P tail estimate d
  intro u hu M η pos
  filter_upwards [cert u hu M η pos] with k hk
  obtain ⟨E,card,good⟩ := hk
  refine ⟨E,card,?_⟩; intro l hl he
  obtain ⟨lo,div,hi,orb⟩ := good l hl he
  refine ⟨_,lo,div,hi,?_⟩
  apply (sum_eq_zero (fun i hi => ?_)).le.trans (by positivity)
  rw [orb i (mem_range.mp hi)]; simp [turnDistance]

end NormalityChecker
