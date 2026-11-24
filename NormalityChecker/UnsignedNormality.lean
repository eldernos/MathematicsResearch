module

public import NormalityChecker.UnsignedRays
public import NormalityChecker.UnsignedWeights
public import NormalityChecker.UnsignedRotation
public import NormalityChecker.HigherOrderDiscrepancy

/-! Normality of every unsigned expansion on a finite prime support containing
a prime coprime to the defining radix. All positive denominator orders are allowed. -/
@[expose] public section
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace NormalityChecker.LocalizedSupport
namespace Unsigned

variable {p : ℕ} [hp : Fact p.Prime]

/-- On the fundamental interval, each fiber of a finite-ray moment is finite. -/
theorem finite_ray_fiber {r s : ℕ} (hr : r.Prime) (rp : r ≠ p)
    {S : Finset ℕ} (out : p ∉ S) (rS : r ∈ S) (hs : 0 < s)
    (A : ℕ → ℤ_[p]) (C : Finset ℕ)
    (rays : ∀ m ∈ Nat.factoredNumbers S, A m ≠ 0 → ∃ c ∈ C, ∃ l, m = c*r^l)
    (bare : ∀ l, A (r^l) ≠ 0) (finite : (Set.range A).Finite) (v : ℤ_[p]) :
    {t : ℝ | t ∈ Set.Ico 1 (p:ℝ) ∧ moment S A s t = v}.Finite := by
  obtain ⟨ε,ep,sep⟩ := finite_ray_separation hr rp out rS hs A C rays bare finite
  let cell (t : ℝ) := ⌊Real.log t / ε⌋₊
  apply Set.Finite.of_injOn (f:=cell) (t:=Set.Iic (cell p)) _ _ (Set.finite_Iic _)
  · intro t ht
    exact Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log (zero_lt_one.trans_le ht.1.1) ht.1.2.le) ep.le)
  · have near {x y : ℝ} (hx : 1 ≤ x) (eqn : cell x = cell y) : Real.log y - Real.log x < ε := by
      have lo := Nat.floor_le (div_nonneg (Real.log_nonneg hx) ep.le)
      have hi := Nat.lt_floor_add_one (Real.log y / ε)
      rw [← show ⌊Real.log x / ε⌋₊ = ⌊Real.log y / ε⌋₊ from eqn] at hi
      have h := (div_lt_iff₀ ep).mp (hi.trans_le (add_le_add_left lo 1))
      rw [add_mul,div_mul_cancel₀ _ ep.ne',one_mul] at h
      linarith
    intro x hx y hy eqn
    rcases lt_trichotomy x y with h|h|h
    · exact (sep hx.1.1 h (near hx.1.1 eqn) (hx.2.trans hy.2.symm)).elim
    · exact h
    · exact (sep hy.1.1 h (near hy.1.1 eqn.symm) (hy.2.trans hx.2.symm)).elim

private lemma no_event_of_finite {S : Finset ℕ} {A : ℕ → ℤ_[p]} {s : ℕ}
    (finite : {t : ℝ | t ∈ Set.Ico 1 (p:ℝ) ∧ moment S A s t = 0}.Finite) :
    ¬ PositiveZeros S A s := by
  rintro ⟨E,_,pos,zeros⟩
  apply pos
  apply (finite.image (fun t => (Real.log t : AddCircle (Real.log (p:ℝ))))).subset _ |>.measure_zero volume
  intro x hx
  let y := AddCircle.equivIco (Real.log (p:ℝ)) 0 x
  have ppos : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  have hi : (y:ℝ) < Real.log (p:ℝ) := by simpa using y.property.2
  have top := (Real.exp_lt_exp.mpr hi).trans_eq (Real.exp_log ppos)
  have repr : (Real.log (Real.exp y) : AddCircle (Real.log (p:ℝ))) = x := by
    rw [Real.log_exp]
    exact AddCircle.coe_equivIco
  exact ⟨Real.exp y,⟨⟨Real.one_le_exp y.property.1,top⟩,
    zeros _ (Real.exp_pos _) top (repr.symm ▸ hx)⟩,repr⟩

/-- Removing the last unprocessed cofactor leaves the retained ray and finitely
many of its dilates. The residue modulus can grow at each recurrence step. -/
private theorem no_event {r s : ℕ} (hr : r.Prime) (rp : r ≠ p) {S : Finset ℕ}
    (out : p ∉ S) (rS : r ∈ S) (hs : 0 < s) (U : Finset ℕ)
    (sub : U ⊆ S) (primes : ∀ q ∈ U, q.Prime) (other : r ∉ U)
    {A : ℕ → ℤ_[p]} {C : Finset ℕ} {D : ℕ} (pos : 0 < D) (period : ResidueWeight D A)
    (support : SupportedOn S A C (insert r U)) (bare : ∀ l, A (r^l) ≠ 0) :
    ¬ PositiveZeros S A s := by
  classical
  induction U using Finset.induction_on generalizing A C D with
  | empty =>
    apply no_event_of_finite (finite_ray_fiber hr rp out rS hs A C _ bare (finite_range_of_residue pos period) 0)
    intro m hm nz
    obtain ⟨c,hc,v,hv,eqn⟩ := support m hm nz
    let e := Nat.equivProdNatFactoredNumbers (s:=∅) hr (by simp)
    let u := e.symm ⟨v,hv⟩
    have mul : r^u.1*u.2.val = v := congrArg Subtype.val (e.apply_symm_apply ⟨v,hv⟩)
    have one : u.2.val = 1 := by simpa using u.2.property
    exact ⟨c,hc,u.1,by simpa [← mul,one] using eqn⟩
  | insert q U qout ih =>
    intro event
    have qprime := primes q (mem_insert_self ..)
    have qS := sub (mem_insert_self ..)
    have rq : r ≠ q := fun e => other (e ▸ mem_insert_self ..)
    obtain ⟨L,h,hpos,stride⟩ := cofactor_stride q pos
    obtain ⟨n,npos,next⟩ := positiveZeros_difference (h:=h) out hs qprime qS event
    have supp := difference_support qprime (show q ∉ insert r U by simp [rq.symm,qout]) period (stride n)
      (show SupportedOn S A C (insert q (insert r U)) by simpa only [Finset.insert_comm] using support)
    exact ih (fun _ hm => sub (mem_insert_of_mem hm)) (fun q hq => primes q (mem_insert_of_mem hq))
      (fun h => other (mem_insert_of_mem h)) (Nat.mul_pos (pow_pos qprime.pos _) pos)
      (difference_residue (pow_pos qprime.pos _) period) supp
      (fun l => (difference_bare (A:=A) qprime hr rq.symm (Nat.mul_pos hpos npos) l).symm ▸ bare l) next

/-- With no cofactor prime at all, the first row is a unit and the tail is
divisible by p. In particular the actual unsigned moment never vanishes here. -/
theorem phaseMoment_empty_ne_zero (w : ℤ_[p]) (unit : ‖w‖ = 1) {s : ℕ} (hs : 0 < s)
    {t : ℝ} (ht : 1 ≤ t) : phaseMoment ∅ w s t ≠ 0 := by
  intro zero
  obtain ⟨e,he⟩ := phaseMoment_tail ∅ w hs t 1
  have idx : indices ∅ ⌊t⌋₊ = {1} := by
    ext m
    have one : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht : ((1:ℕ):ℝ) ≤ t)
    simp [mem_indices, Nat.factoredNumbers_empty]
    rintro rfl
    exact one
  have inv : (1:ℤ_[p]).inv = 1 := by simpa using PadicInt.inv_mul (p:=p) (z:=1) norm_one
  simp [zero,idx,momentRow,inv] at he
  have eqn : w = -((p:ℤ_[p])^s*e) := eq_neg_of_add_eq_zero_left he.symm
  have normeq := congrArg norm eqn
  rw [unit,norm_neg,norm_mul,norm_pow,PadicInt.norm_p] at normeq
  have small : ((p:ℝ)⁻¹)^s < 1 := pow_lt_one₀ (by positivity)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)) hs.ne'
  exact small.not_ge (normeq.trans_le (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one e)))

end Unsigned

/-- For *each* off-radix support prime, the infinite intersection of the
checker's failed regions has Lebesgue measure zero, in every positive order. -/
theorem unsigned_persistent_null {b s p : ℕ} {S : Finset ℕ} (hp : p.Prime)
    (out : p ∉ S) (cop : b.Coprime p) (hs : 0 < s) (primes : ∀ q ∈ S, q.Prime) :
    volume (persistentRegion b s p S) = 0 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨w,z,fixed,unit,factor⟩ := inverse_radix_factors cop
  by_contra pos
  have event := Unsigned.positiveZeros_of_persistent out hs fixed factor cop pos
  rcases S.eq_empty_or_nonempty with rfl | ⟨r,hr⟩
  · apply Unsigned.no_event_of_finite _ event
    apply Set.finite_empty.subset
    rintro t ⟨ht,zero⟩
    exact (Unsigned.phaseMoment_empty_ne_zero w unit hs ht.1 zero).elim
  · have wn : w ≠ 0 := by rintro rfl; simp at unit
    obtain ⟨D,hD,period⟩ := Unsigned.unsigned_residue fixed unit
    have rp : r ≠ p := fun e => out (e ▸ hr)
    apply Unsigned.no_event (primes r hr) rp out hr hs (S.erase r)
      (erase_subset ..) (fun q h => primes q (mem_of_mem_erase h)) (notMem_erase r S) hD period
      (C:={1}) _ (fun l => pow_ne_zero _ wn) event
    rw [insert_erase hr]
    exact fun m hm _ => ⟨1,mem_singleton_self _,m,hm,(one_mul _).symm⟩

/-- The computable worst-prefix certificate tends to zero for every individual
off-base prime. The conclusion allows a positive certificate at every finite depth. -/
theorem unsigned_certificate_tendsTo_zero {b s p : ℕ} {S : Finset ℕ} (hp : p.Prime)
    (out : p ∉ S) (cop : b.Coprime p) (hs : 0 < s) (primes : ∀ q ∈ S, q.Prime) :
    Tendsto (fun k => (discrepancyCertificate b s p k S : ℝ)) atTop (𝓝 0) := by
  have limit := region_mass_tendsto hs hp out cop
  rw [measureReal_def, unsigned_persistent_null hp out cop hs primes, ENNReal.toReal_zero] at limit
  apply squeeze_zero (fun k => by exact_mod_cast CellProfile.bound_nonneg p (p^k) (failedCells b s p k S)) _
    (by simpa using limit.const_mul 2)
  intro k
  let Z := failedCells b s p k S
  change ((CellProfile.bound p (p^k) Z : ℚ) : ℝ) ≤ 2 * volume.real (meshRegion (p^k) Z)
  rw [mesh_mass (pow_pos hp.pos k)]
  suffices rat : CellProfile.bound p (p^k) Z ≤ 2 * ((Z.card:ℚ)/(p^k:ℕ)) by
    simpa using (Rat.cast_le (K:=ℝ)).mpr rat
  apply max'_le _ _ _
  intro u hu
  rcases mem_insert.mp hu with rfl|hu
  · positivity
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hu
  have low : ((p^k:ℕ):ℚ) ≤ v := by exact_mod_cast (mem_Icc.mp hv).1
  have pos : (0:ℚ) < (p^k:ℕ) := by exact_mod_cast pow_pos hp.pos k
  have den : (1:ℚ) ≤ p-1 := by
    have h : (2:ℚ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have a := div_le_self (Nat.cast_nonneg Z.card : (0:ℚ) ≤ Z.card) den
  have c : (CellProfile.mass Z v:ℚ) ≤ Z.card := by exact_mod_cast card_filter_le Z _
  change ((Z.card:ℚ)/(p-1) + (CellProfile.mass Z v:ℚ))/v ≤ _
  rw [← mul_div_assoc]
  exact (div_le_div_of_nonneg_right (by linarith) (pos.trans_le low).le).trans
    (div_le_div_of_nonneg_left (by positivity) pos low)

private theorem unsigned_limsup_le_zero {b s : ℕ} (S : Finset ℕ) (hb : 2 ≤ b)
    (hs : 0 < s) (primes : ∀ q ∈ S, q.Prime) (off : ∃ p ∈ S, ¬p ∣ b) :
    limsup (radixDiscrepancy b (powerValue b s S)) atTop ≤ 0 := by
  obtain ⟨p,mem,off⟩ := off
  have hp := primes p mem
  have cop := (hp.coprime_iff_not_dvd.mpr off).symm
  have tp : ∀ q ∈ S.erase p, q.Prime := fun q h => primes q (mem_of_mem_erase h)
  apply ge_of_tendsto' (unsigned_certificate_tendsTo_zero hp (notMem_erase p S) cop hs tp)
  intro k
  simpa only [insert_erase mem] using discrepancy_le_certificate hb hs hp (notMem_erase p S) cop tp k

/-- Every unsigned full finite-prime expansion with an off-base prime is normal
in its defining radix, at every positive denominator order. -/
theorem unsigned_finite_support_normal {b s : ℕ} (S : Finset ℕ) (hb : 2 ≤ b)
    (hs : 0 < s) (primes : ∀ q ∈ S, q.Prime) (off : ∃ p ∈ S, ¬p ∣ b) :
    NormalIn b (powerValue b s S) :=
  normal_of_radix_limsup_zero hb (unsigned_limsup_le_zero S hb hs primes off)

/-- Along every prefix, interval discrepancy tends to one for all-base
supports and to zero for supports containing an off-base prime. -/
theorem unsigned_discrepancy_limit {b s : ℕ} (S : Finset ℕ) (hb : 2 ≤ b)
    (hs : 0 < s) (primes : ∀ q ∈ S, q.Prime) :
    Tendsto (radixDiscrepancy b (powerValue b s S)) atTop (𝓝 (if ∀ q ∈ S, q ∣ b then 1 else 0)) := by
  split_ifs with base
  · exact prefix_discrepancy_tendsTo_one S hb hs base
  · push Not at base
    have lim := unsigned_limsup_le_zero S hb hs primes base
    have bd := radix_discrepancy_bounds b (powerValue b s S)
    rw [Metric.tendsto_nhds]
    intro ε ep
    filter_upwards [eventually_lt_of_limsup_lt (lim.trans_lt ep)
      (isBoundedUnder_of_eventually_le (.of_forall fun n => (bd n).2))] with n hn
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (bd n).1] using hn

end NormalityChecker.LocalizedSupport
