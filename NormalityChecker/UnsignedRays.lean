module

public import NormalityChecker.UnsignedPhase
public import NormalityChecker.LocalizedMesh

/-! Separation of values of a local moment supported on finitely many geometric rays. -/
@[expose] public section
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace NormalityChecker.LocalizedSupport.Unsigned

variable {p : ℕ} [hp : Fact p.Prime]

private def threshold (p m i : ℕ) : ℝ := (m : ℝ) / (p : ℝ)^i

private lemma ray_gap {r : ℕ} (hr : r.Prime) (C : Finset ℕ) (B : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {i k m n : ℕ}, k ≤ B → ¬p ∣ n →
      (∃ c ∈ C, ∃ l, m = c*r^l) → (∃ c ∈ C, ∃ l, n = c*r^l) →
      0 < m → 0 < n →
      |Real.log (threshold p m i) - Real.log (threshold p n (i+k))| < ε →
      k = 0 ∧ m = n := by
  let offsets := (((C ×ˢ C) ×ˢ range (B+1)).image fun u =>
    Real.log u.1.1 - Real.log u.1.2 + (u.2 : ℝ) * Real.log p)
  obtain ⟨ε,hε,gap⟩ := ThresholdDifferences.finite_ray_gap offsets
    (Real.log_pos (by exact_mod_cast hr.one_lt : (1:ℝ) < r))
  refine ⟨ε,hε,?_⟩
  rintro i k m n hk hn ⟨c,hc,l,rfl⟩ ⟨d,hd,j,rfl⟩ hmpos hnpos small
  have cp : c ≠ 0 := by rintro rfl; simp at hmpos
  have dp : d ≠ 0 := by rintro rfl; simp at hnpos
  have pp : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  have rp : (0:ℝ) < r := by exact_mod_cast hr.pos
  have identity : Real.log (threshold p (c*r^l) i) - Real.log (threshold p (d*r^j) (i+k)) =
      (Real.log c - Real.log d + (k:ℝ)*Real.log p) + ((l:ℤ)-j : ℤ)*Real.log r := by
    simp [threshold, Real.log_div, Real.log_mul, Real.log_pow, cp, dp, rp.ne', pp.ne']
    ring
  have mem : Real.log c - Real.log d + (k:ℝ)*Real.log p ∈ offsets :=
    mem_image.mpr ⟨((c,d),k), mem_product.mpr ⟨mem_product.mpr ⟨hc,hd⟩,mem_range.mpr (by omega)⟩,rfl⟩
  rw [identity] at small
  have eqn := sub_eq_zero.mp (identity.trans (gap _ mem _ small))
  have same := Real.log_injOn_pos (x₁ := threshold p (c*r^l) i) (x₂ := threshold p (d*r^j) (i+k))
    (div_pos (by exact_mod_cast hmpos) (pow_pos pp _))
    (div_pos (by exact_mod_cast hnpos) (pow_pos pp _)) eqn
  obtain h := (div_eq_div_iff (pow_ne_zero i pp.ne') (pow_ne_zero (i+k) pp.ne')).mp same
  rw [pow_add, mul_left_comm ((c*r^l : ℕ):ℝ), mul_comm _ ((p:ℝ)^i)] at h
  have natEq : c*r^l*p^k = d*r^j := by
    exact_mod_cast (mul_left_cancel₀ (pow_ne_zero i pp.ne') h)
  have kz : k = 0 := by
    by_contra nz
    exact hn (natEq ▸ dvd_mul_of_dvd_right (dvd_pow_self p nz) _)
  exact ⟨kz,by simpa [kz] using natEq⟩

private def jumps (S : Finset ℕ) (A : ℕ → ℤ_[p]) (x y : ℝ) (i : ℕ) : Finset ℕ := by
  classical
  exact ((indices S ⌊y*(p:ℝ)^i⌋₊) \ (indices S ⌊x*(p:ℝ)^i⌋₊)).filter (fun m => A m ≠ 0)

private lemma mem_jumps {S : Finset ℕ} {A : ℕ → ℤ_[p]} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {m i : ℕ} : m ∈ jumps S A x y i ↔
    m ∈ Nat.factoredNumbers S ∧ A m ≠ 0 ∧ x < threshold p m i ∧ threshold p m i ≤ y := by
  classical
  have pp : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  simp only [jumps, mem_filter, Finset.mem_sdiff, mem_indices, Nat.le_floor_iff (mul_nonneg hx (pow_pos pp _).le),
    Nat.le_floor_iff (mul_nonneg hy (pow_pos pp _).le), threshold, lt_div_iff₀ (pow_pos pp _),
    div_le_iff₀ (pow_pos pp _)]
  grind

private lemma row_sub_eq (S : Finset ℕ) (A : ℕ → ℤ_[p]) (s i : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    row S A s ⌊y*(p:ℝ)^i⌋₊ - row S A s ⌊x*(p:ℝ)^i⌋₊ =
    ∑ m ∈ jumps S A x y i, A m * (m:ℤ_[p]).inv^s := by
  classical
  have sub : indices S ⌊x*(p:ℝ)^i⌋₊ ⊆ indices S ⌊y*(p:ℝ)^i⌋₊ := by
    intro m hm
    exact mem_indices.mpr ⟨(mem_indices.mp hm).1.trans (Nat.floor_mono (by gcongr)),(mem_indices.mp hm).2⟩
  rw [row, row, ← sum_sdiff_eq_sub sub]
  symm
  exact sum_subset (filter_subset _ _) (fun m hm hn => by
    have : A m = 0 := by by_contra ne; exact hn (mem_filter.mpr ⟨hm,ne⟩)
    simp [this])

/-- Finite-ray moments separate any two sufficiently close log phases, uniformly
in their location. The bare ray supplies an actual jump in every open interval. -/
theorem finite_ray_separation {r s : ℕ} (hr : r.Prime) (rp : r ≠ p)
    {S : Finset ℕ} (out : p ∉ S) (rS : r ∈ S) (hs : 0 < s)
    (A : ℕ → ℤ_[p]) (C : Finset ℕ)
    (rays : ∀ m ∈ Nat.factoredNumbers S, A m ≠ 0 → ∃ c ∈ C, ∃ l, m = c*r^l)
    (bare : ∀ l, A (r^l) ≠ 0) (finite : (Set.range A).Finite) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {x y : ℝ}, 1 ≤ x → x < y → Real.log y - Real.log x < ε →
      moment S A s x ≠ moment S A s y := by
  classical
  let P := (p:ℤ_[p])^s
  have pp : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  have pnorm : ‖P‖ < 1 := by
    rw [show ‖P‖ = _ from norm_pow _ _, PadicInt.norm_p]
    exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)) hs.ne'
  have grow := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg P) pnorm
  have bound : ∀ᶠ k : ℕ in atTop, ∀ a ∈ Set.range A, a ≠ 0 → ‖P‖^k < ‖a‖ := by
    apply (finite.eventually_all).mpr
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · filter_upwards [grow.eventually_lt_const (norm_pos_iff.mpr ha)] with k hk using fun _ => hk
  obtain ⟨K,bK⟩ := eventually_atTop.mp bound
  obtain ⟨ε,ep,gap⟩ := ray_gap (p:=p) hr C K
  refine ⟨ε,ep,?_⟩
  intro x y hx hxy width same
  let d : Localized.Parameters := ⟨r,r,p,hr.two_le,hr.two_le,hp.out,dvd_rfl,
    (Nat.coprime_primes hr hp.out).mpr rp⟩
  obtain ⟨l,j,hl,hj⟩ := Localized.threshold_between d hx hxy
  let J := jumps S A x y
  have xpos : 0 < x := zero_lt_one.trans_le hx
  have ypos := xpos.trans hxy
  have some_jump : ∃ i, (J i).Nonempty := by
    refine ⟨j,r^l,(mem_jumps xpos.le ypos.le).mpr ⟨prime_power_mem hr rS l,bare l,?_,?_⟩⟩
    · simpa [threshold,d] using hl
    · simpa [threshold,d] using hj.le
  let i := Nat.find some_jump
  obtain ⟨m,hm⟩ : (J i).Nonempty := Nat.find_spec some_jump
  have info := (mem_jumps xpos.le ypos.le).mp hm
  have unique {j n : ℕ} (lim : j < i+K+1) (hn : n ∈ J j) : j = i ∧ n = m := by
    have lower : i ≤ j := Nat.find_min' some_jump ⟨n,hn⟩
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le lower
    have en := (mem_jumps xpos.le ypos.le).mp hn
    have loc {z : ℝ} (hz : x < z ∧ z ≤ y) : Real.log x < Real.log z ∧ Real.log z ≤ Real.log y :=
      ⟨Real.log_lt_log xpos hz.1,Real.log_le_log (xpos.trans hz.1) hz.2⟩
    have a := loc info.2.2
    have b := loc en.2.2
    obtain ⟨k0,mn⟩ := gap (i:=i) (k:=k) (by omega)
      ((hp.out.coprime_iff_not_dvd.mp (hp.out.factoredNumbers_coprime out en.1)))
      (rays m info.1 info.2.1) (rays n en.1 en.2.1) (Nat.pos_of_ne_zero info.1.1)
      (Nat.pos_of_ne_zero en.1.1) (abs_lt.mpr ⟨by linarith,by linarith⟩)
    exact ⟨by omega,mn.symm⟩
  let N := i+K+1
  let v (n : ℕ) := A n * (n:ℤ_[p]).inv^s
  have jumpsum :
      (∑ j ∈ range N, P^j * ∑ n ∈ J j, v n) = P^i*v m := by
    rw [sum_eq_single_of_mem i (mem_range.mpr (by dsimp [N]; omega)) (fun j hj ne => by
      rw [sum_eq_zero (fun n hn => (ne (unique (mem_range.mp hj) hn).1).elim),mul_zero])]
    rw [sum_eq_single_of_mem m hm (fun n hn ne => (ne (unique (by omega) hn).2).elim)]
  obtain ⟨e,he⟩ := moment_tail S A hs x N
  obtain ⟨f,hf⟩ := moment_tail S A hs y N
  have eqn : P^i*v m = P^N*(e-f) := by
    rw [← jumpsum]
    simp_rw [show ∀ j, ∑ n ∈ J j, v n = _ from fun j => (row_sub_eq S A s j hxy.le).symm,
      mul_sub, sum_sub_distrib]
    rw [he,hf] at same
    change _ + P^N*e = _ + P^N*f at same
    linear_combination -same
  have P0 : P ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have canceled : v m = P^(K+1)*(e-f) := by
    apply mul_left_cancel₀ (pow_ne_zero i P0)
    rw [eqn, ← mul_assoc, ← pow_add, ← Nat.add_assoc]
  have unit := PadicInt.norm_natCast_eq_one_iff.mpr (hp.out.factoredNumbers_coprime out info.1)
  have invunit := congrArg norm (PadicInt.inv_mul unit)
  simp only [norm_mul,unit,mul_one,norm_one] at invunit
  have normeq := congrArg norm canceled
  simp only [v, norm_mul, norm_pow,invunit,one_pow,mul_one] at normeq
  have cap := mul_le_of_le_one_right (pow_nonneg (norm_nonneg P) (K+1)) (PadicInt.norm_le_one (e-f))
  exact (bK (K+1) (by omega) (A m) ⟨m,rfl⟩ info.2.1).not_ge (normeq.trans_le cap)

end NormalityChecker.LocalizedSupport.Unsigned
