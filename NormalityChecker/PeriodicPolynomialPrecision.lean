module

public import NormalityChecker.PeriodicPolynomialMass
public import NormalityChecker.CyclotomicLift

/-! Finite precision for the reflected Teichmüller cycles of a Stoneham prefix. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

variable {p : ℕ} [Fact p.Prime]

/-- At precision `p^L` every term outside the box of side `L` vanishes. -/
private theorem reduce_box {d c L J : ℕ} (pc : p ∣ c) (le : L ≤ J)
    (u : ℕ → ℤ_[p]) (U : Set (Vector d)) :
    PadicInt.toZModPow L (boxProductSum (fun j => (c : ℤ_[p])^j * u j) U J) =
    PadicInt.toZModPow L (boxProductSum (fun j => (c : ℤ_[p])^j * u j) U L) := by
  classical
  simp only [boxProductSum, map_sum, map_prod, map_mul, map_pow, map_natCast]
  symm
  apply sum_subset_zero_on_sdiff
  · intro v hv
    simp only [mem_filter, mem_box] at hv ⊢
    exact ⟨fun i => (hv.1 i).trans_le le, hv.2⟩
  · intro v hv
    obtain ⟨hi,hn⟩ := mem_sdiff.mp hv
    obtain ⟨i,large⟩ : ∃ i, L ≤ v i := by
      by_contra! small
      exact hn (mem_filter.mpr ⟨mem_box.mpr small,(mem_filter.mp hi).2⟩)
    apply prod_eq_zero (mem_univ i)
    have zero : (c : ZMod (p^L))^(v i) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact (pow_dvd_pow_of_dvd pc L).trans (pow_dvd_pow c large)
    simp [zero]
  · simp

/-- Nonzero limits for individual upper sets give a single precision valid for
all upper sets through the anchor, at every larger box size and precision. -/
theorem uniform_padic_box_precision {d c : ℕ} (pc : p ∣ c) (anchor : Vector d)
    (u : ℕ → ℤ_[p])
    (nonzero : ∀ U : Set (Vector d), IsUpperSet U → anchor ∈ U →
      ∃ z : ℚ_[p], z ≠ 0 ∧ Tendsto
        (fun J => ((boxProductSum (fun j => (c : ℤ_[p])^j * u j) U J : ℤ_[p]) : ℚ_[p]))
        atTop (𝓝 z)) :
    ∃ L : ℕ, ∀ J ≥ L, ∀ U : Set (Vector d), IsUpperSet U → anchor ∈ U →
      PadicInt.toZModPow J (boxProductSum (fun j => (c : ℤ_[p])^j * u j) U J) ≠ 0 := by
  classical
  by_contra! h
  choose J large U upper hit vanish using h
  let f (j : ℕ) (v : Vector d) : Bool := decide (v ∈ U j)
  obtain ⟨g, φ, inc, conv⟩ := CompactSpace.tendsto_subseq f
  let V : Set (Vector d) := {v | g v = true}
  have coord (v : Vector d) : ∀ᶠ j in atTop, (v ∈ U (φ j) ↔ v ∈ V) := by
    have c := (tendsto_pi_nhds.mp conv v).eventually
      ((isOpen_discrete {g v}).mem_nhds (Set.mem_singleton _))
    filter_upwards [c] with j hj
    change decide (v ∈ U (φ j)) = g v at hj
    simp [V, ← hj]
  have hv : IsUpperSet V := by
    intro x y le hx
    obtain ⟨j,hx',hy'⟩ := ((coord x).and (coord y)).exists
    exact hy'.mp (upper _ le (hx'.mpr hx))
  have ha : anchor ∈ V := by
    obtain ⟨j,hj⟩ := (coord anchor).exists
    exact hj.mp (hit _)
  let f₀ (j : ℕ) := (c : ℤ_[p])^j * u j
  have zero (L : ℕ) : PadicInt.toZModPow L (boxProductSum f₀ V L) = 0 := by
    have matchbox := (eventually_all_finset (box d L)).mpr (fun v _ => coord v)
    obtain ⟨j,hj,hl⟩ := (matchbox.and (inc.tendsto_atTop.eventually_ge_atTop L)).exists
    have le := hl.trans (large (φ j))
    have reduce := PadicInt.cast_toZModPow L _ le (boxProductSum f₀ (U (φ j)) (J (φ j)))
    rw [show boxProductSum f₀ V L = boxProductSum f₀ (U (φ j)) L by
      unfold boxProductSum; congr 1; ext v; simp only [mem_filter]
      exact and_congr_right (fun h => (hj v h).symm), ← reduce_box pc le u, ← reduce, vanish]
    simp
  obtain ⟨z,nz,lim⟩ := nonzero V hv ha
  apply nz
  apply tendsto_nhds_unique lim
  apply Metric.tendsto_atTop.mpr
  intro ε pos
  obtain ⟨L,small⟩ := PadicInt.exists_pow_neg_lt p pos
  refine ⟨L, fun J hJ => lt_of_le_of_lt ?_ small⟩
  rw [dist_zero_right, ← PadicInt.norm_def, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, reduce_box pc hJ u, zero]

/-- The powers of one Teichmüller lift belong to a common number field in ℚₚ. -/
private theorem cycle_limit {c h d m : ℕ} (hc : 2 < c) (pc : p ∣ c) (hh : 0 < h)
    (w : ℤ_[p]) (hm : 0 < m) (root : w^m = 1) (e : ℕ → ℕ) (per : Function.Periodic e h)
    (U : Set (Vector d)) (upper : IsUpperSet U) (hit : U.Nonempty) :
    ∃ z : ℚ_[p], z ≠ 0 ∧ Tendsto (fun L =>
      ((boxProductSum (fun j => (c : ℤ_[p])^j * w^(e j)) U L : ℤ_[p]) : ℚ_[p]))
      atTop (𝓝 z) := by
  let x : ℚ_[p] := w
  have rx : x^m = 1 := by simpa [x, ← PadicInt.coe_pow] using congrArg (fun y : ℤ_[p] => (y : ℚ_[p])) root
  have ix : IsIntegral ℚ x := ⟨X^m-1, monic_X_pow_sub_C 1 hm.ne', by simp [rx]⟩
  let K := IntermediateField.adjoin ℚ ({x} : Set ℚ_[p])
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional ix
  let : NumberField K := NumberField.of_module_finite ℚ K
  let a : K := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  have ar : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨m,hm,Subtype.ext (by exact rx)⟩
  obtain ⟨z,nz,conv⟩ := periodic_upper_mass_nonzero K.val.toRingHom hc hh
    (Padic.norm_natCast_lt_one_iff.mpr pc) (fun j => a^(e j))
    (fun j => congrArg (a^·) (per j)) (fun _ => ar.pow) U upper hit
  refine ⟨z,nz,?_⟩
  have mapped (L : ℕ) : ((boxProductSum (fun j => (c : ℤ_[p])^j * w^(e j)) U L : ℤ_[p]) : ℚ_[p]) =
      boxProductSum (fun j => (c : ℚ_[p])^j * K.val.toRingHom (a^(e j))) U L := by
    change (algebraMap ℤ_[p] ℚ_[p]) _ = _
    simp only [boxProductSum, map_sum, map_prod, map_mul, map_pow, map_natCast]
    rfl
  exact conv.congr (fun L => (mapped L).symm)

private theorem power_cycle {m c : ℕ} (hm : 0 < m) :
    ∃ N h : ℕ, 0 < h ∧ ∀ t, c^(N+t+h) ≡ c^(N+t) [MOD m] := by
  let : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i,j,ne,eqn⟩ := Finite.exists_ne_map_eq_of_infinite (fun j : ℕ => (c : ZMod m)^j)
  have aux {i j : ℕ} (lt : i < j) (e : (c : ZMod m)^i = (c : ZMod m)^j) :
      ∃ N h : ℕ, 0 < h ∧ ∀ t, c^(N+t+h) ≡ c^(N+t) [MOD m] := by
    refine ⟨i,j-i,by omega,fun t => ?_⟩
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    rw [show i+t+(j-i) = j+t by omega, Nat.cast_pow, Nat.cast_pow, pow_add, pow_add, e]
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact aux lt eqn
  · exact aux gt eqn.symm

/-- The reflected inverse radix agrees at precision `p^L` with one of finitely
many periodic cycles. Each cycle has a nonzero limiting mass on every nonempty upper set. -/
theorem exists_reflected_cycles {b c : ℕ} (hc : 2 < c) (pc : p ∣ c) (cop : b.Coprime p) :
    ∃ h N : ℕ, ∃ phase : ℕ → Fin h, ∃ u : Fin h → ℕ → ℤ_[p],
      0 < h ∧ Function.Periodic (fun j => phase (N+j)) h ∧
      (∀ r v, (u r v)^(p-1) = 1) ∧
      (∀ L k v : ℕ, N + L + v ≤ k →
        (b : ZMod (p^L))^(c^(k-v)) * PadicInt.toZModPow L (u (phase k) v) = 1) ∧
      (∀ r, Function.Periodic (u r) h) ∧
      ∀ {d : ℕ} (r : Fin h) (U : Set (Vector d)), IsUpperSet U → U.Nonempty →
        ∃ z : ℚ_[p], z ≠ 0 ∧ Tendsto (fun L =>
          ((boxProductSum (fun j => (c : ℤ_[p])^j * u r j) U L : ℤ_[p]) : ℚ_[p]))
          atTop (𝓝 z) := by
  obtain ⟨w,root,red⟩ := exists_inverse_lift b cop
  let m := orderOf (b : ZMod p)
  have bn := ((ZMod.isUnit_iff_coprime b p).mpr cop).ne_zero
  have hm : 0 < m := Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one bn)
    (by have := (Fact.out : p.Prime).one_lt; omega)
  obtain ⟨N,h,hh,repeatPow⟩ := power_cycle (c:=c) hm
  let : NeZero h := ⟨hh.ne'⟩
  let exp (r : Fin h) (v : ℕ) := c^(N+((r.val : ZMod h) - v).val)
  let phase (k : ℕ) : Fin h := ⟨(k-N)%h,Nat.mod_lt _ hh⟩
  have per (r : Fin h) : Function.Periodic (exp r) h := fun v => by simp [exp]
  have shell : Function.Periodic (fun j => phase (N+j)) h := fun j => by
    apply Fin.ext
    simp [phase]
  have roots (r : Fin h) (v : ℕ) : (w^(exp r v))^(p-1) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      (root.pow_eq_one_iff_dvd _).mpr (ZMod.orderOf_dvd_card_sub_one bn), one_pow]
  refine ⟨h,N,phase,fun r v => w^(exp r v),hh,shell,roots,?_,fun r v => congrArg (w^·) (per r v),
    fun r U upper hit => cycle_limit hc pc hh w hm root.pow_eq_one _ (per r) U upper hit⟩
  intro L k v late
  let t := k-v-N
  have cyc : Function.Periodic (fun t : ℕ => w^(c^(N+t))) h :=
    fun j => pow_eq_pow_of_modEq (by simpa [Nat.add_assoc] using repeatPow j) root.pow_eq_one
  have rem := (cyc.nat_mul (t/h)) (t%h)
  have index : (phase k).val = (k-N)%h := rfl
  have modval : (((phase k).val : ZMod h) - v).val = t%h := by
    rw [index, ZMod.natCast_mod, ← Nat.cast_sub (show v ≤ k-N by omega), ZMod.val_natCast]
    congr 1; dsimp [t]; omega
  have eqn : w^(exp (phase k) v) = w^(c^(k-v)) := by
    change w^(c^(N+_)) = _
    rw [modval, ← rem]
    simp only [Nat.cast_id, Nat.mul_comm (t/h) h, Nat.mod_add_div]
    rw [show N+t=k-v by dsimp [t]; omega]
  dsimp only
  rw [eqn]
  let I : Ideal ℤ_[p] := Ideal.span {(p:ℤ_[p])}
  have initial : (b:ℤ_[p])*w ≡ 1 [SMOD I] := by
    dsimp only [I]
    rw [SModEq.sub_mem, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [red,bn]
  obtain ⟨q,hq⟩ := (pow_dvd_pow_of_dvd pc L).trans (pow_dvd_pow c (show L ≤ k-v by omega))
  have lift := (initial.pow_pow_add_one (show (p:ℤ_[p]) ∈ I from Ideal.subset_span (by simp)) L).pow q
  dsimp only [I] at lift
  rw [← pow_mul, ← hq, SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at lift
  have low := (pow_dvd_pow (p:ℤ_[p]) (Nat.le_succ L)).trans lift
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker] at low
  simpa only [map_sub, mul_pow, map_mul, map_pow, map_natCast, one_pow, map_one, sub_eq_zero] using low

end NormalityChecker.StonehamPolynomial
