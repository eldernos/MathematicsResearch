module

public import NormalityChecker.StonehamPolynomialOrthant
import all NormalityChecker.StonehamPolynomialOrthant
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

/-! Binary geometric mass on symmetric upper sets of odd prime-power dimension. -/

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

universe u

/-- Reindexing coordinates preserves membership. -/
def SymmetricSet {d : ℕ} (U : Set (Vector d)) : Prop :=
  ∀ (v : Vector d) (σ : Equiv.Perm (Fin d)), v ∘ σ ∈ U ↔ v ∈ U

/-- Modulo the rotation prime, an invariant sum on words of prime-power length
reduces to its constant words. Apply the fixed-point congruence on each fiber. -/
theorem sum_eq_diagonal_of_prime_power {q d r : ℕ} (hq : q.Prime) (hd : d = q ^ r)
    {A : Type u} [Fintype A] (f : (Fin d → A) → ZMod q)
    (symm : ∀ v (σ : Equiv.Perm (Fin d)), f (v ∘ σ) = f v) :
    ∑ v, f v = ∑ a, f (fun _ => a) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero d := ⟨hd ▸ pow_ne_zero _ hq.ne_zero⟩
  have group : IsAddPGroup q (Fin d) := IsAddPGroup.of_card ((Nat.card_fin d).trans hd)
  let diag (a : A) := f (fun _ => a)
  have fiber (z : ZMod q) :
      (#{v | f v = z} : ZMod q) = (#{a | diag a = z} : ZMod q) := by
    let X := {v : Fin d → A // f v = z}
    let action : AddAction (Fin d) X := {
      vadd g v := ⟨v.val ∘ Equiv.addRight g, (symm _ _).trans v.property⟩
      zero_vadd v := by apply Subtype.ext; funext i; change v.val (i + 0) = v.val i; rw [add_zero]
      add_vadd g h v := by apply Subtype.ext; funext i; change v.val (i + (g+h)) = v.val ((i+g)+h); rw [add_assoc] }
    let E : AddAction.fixedPoints (Fin d) X ≃ {a // diag a = z} :=
      { toFun := fun v => ⟨v.val.val 0, by
          have heq (i : Fin d) := congrArg (fun w : X => w.val 0)
            (AddAction.mem_fixedPoints.mp v.property i)
          have eqv : (fun _ : Fin d => v.val.val 0) = v.val.val := by
            funext i
            have h := heq i
            change v.val.val (0+i) = v.val.val 0 at h
            simpa using h.symm
          exact (congrArg f eqv).trans v.val.property⟩
        invFun := fun a => ⟨⟨fun _ => a.val, a.property⟩, AddAction.mem_fixedPoints.mpr fun _ => rfl⟩
        left_inv := by
          intro v
          apply Subtype.ext; apply Subtype.ext; funext i
          have h := congrArg (fun w : X => w.val 0) (AddAction.mem_fixedPoints.mp v.property i)
          change v.val.val (0+i) = v.val.val 0 at h
          simpa using h.symm
        right_inv := fun _ => rfl }
    have h := group.card_modEq_card_fixedPoints X
    rw [Nat.card_congr E] at h
    simpa [X, Nat.card_eq_fintype_card, Fintype.card_subtype] using
      (ZMod.natCast_eq_natCast_iff _ _ q).mpr h
  have byValue {B : Type u} [Fintype B] (g : B → ZMod q) :
      ∑ i, g i = ∑ z, (#{i | g i = z} : ZMod q) * z := by
    rw [← sum_fiberwise univ g g]
    apply sum_congr rfl
    intro z _
    calc
      _ = ∑ _i ∈ univ.filter (fun i => g i = z), z :=
        sum_congr rfl fun i hi => (mem_filter.mp hi).2
      _ = _ := by simp
  rw [byValue f, show (∑ a, f (fun _ => a)) = ∑ a, diag a from rfl, byValue diag]
  simp_rw [fiber]

/-- Dickson's lemma gives a common coordinate bound for the minimal generators. -/
private theorem exists_clip {d : ℕ} (U : Set (Vector d)) (upper : IsUpperSet U) (a : ℕ) :
    ∃ M ≥ a, ∀ v : Vector d, (fun i => min (v i) M) ∈ U ↔ v ∈ U := by
  classical
  let S : Set (Vector d) := {v | Minimal (· ∈ U) v}
  have anti : IsAntichain (· ≤ ·) S := fun _ hx _ hy ne le => ne (le_antisymm le (hy.2 hx.1 le))
  let F := (WellQuasiOrderedLE.finite_of_isAntichain anti).toFinset
  let M := max a (F.sup weight)
  refine ⟨M, le_max_left .., fun v => ⟨upper (fun _ => min_le_left ..), fun hv => ?_⟩⟩
  obtain ⟨u,le,hu⟩ := (Set.isPWO_of_wellQuasiOrderedLE U).exists_le_minimal hv
  have mem : u ∈ F := by simpa [F, S] using hu
  apply upper (a := u) _ hu.1
  intro i
  exact le_min (le i) ((single_le_sum (fun j _ => Nat.zero_le (u j)) (mem_univ i)).trans
    ((Finset.le_sup (f := weight) mem).trans (le_max_right ..)))

/-- Binary weights on the clipped alphabet. The last letter collects the geometric tail. -/
private def letter (M j : ℕ) : ℤ := if j < M then 2^j else -(2^M)

private noncomputable def clippedMass {d : ℕ} (U : Set (Vector d)) (M : ℕ) : ℤ := by
  classical exact ∑ v : Fin d → Fin (M+1),
    if (fun i => (v i : ℕ)) ∈ U then ∏ i, letter M (v i) else 0

private lemma mass_eq_clipped {d M L : ℕ} (hML : M ≤ L) (U : Set (Vector d))
    (clip : ∀ v : Vector d, (fun i => min (v i) M) ∈ U ↔ v ∈ U) :
    (mass 2 L U : ZMod (2^L)) = clippedMass U M := by
  classical
  let c (j : ℕ) : Fin (M+1) := ⟨min j M, Nat.lt_succ_of_le (min_le_right ..)⟩
  let w (j : ℕ) : ZMod (2^L) := 2^j
  have two : (2 : ZMod (2^L)) - 1 = 1 := by ring
  have oneLetter (a : Fin (M+1)) :
      ∑ j ∈ (range L).filter (fun j => c j = a), w j = (letter M a : ZMod (2^L)) := by
    by_cases h : a.val < M
    · have cells : (range L).filter (fun j => c j = a) = {a.val} := by
        ext j; simp only [mem_filter, mem_range, mem_singleton, Fin.ext_iff, c]
        omega
      simp [cells, w, letter, h]
    · have cells : (range L).filter (fun j => c j = a) = Ico M L := by
        ext j; simp only [mem_filter, mem_range, mem_Ico, Fin.ext_iff, c]
        have := a.isLt
        omega
      have z : (2 : ZMod (2^L))^L = 0 := by
        exact_mod_cast (ZMod.natCast_self (2^L))
      rw [cells]
      simpa [w, letter, h, z, two] using geom_sum_Ico_mul (2 : ZMod (2^L)) hML
  let C (v : Vector d) := fun i => c (v i)
  let V := (box d L).filter (· ∈ U)
  have prodWeight (v : Vector d) :
      (2 : ZMod (2^L))^weight (stretch (fun _ => 1) v) = ∏ i, w (v i) := by
    simp [weight, stretch, w, prod_pow_eq_pow_sum]
  simp only [mass, weightedMass, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, prodWeight]
  change (∑ v ∈ V, ∏ i, w (v i)) = _
  rw [← sum_fiberwise V C]
  simp only [clippedMass, Int.cast_sum, Int.cast_ite, Int.cast_prod, Int.cast_zero]
  apply sum_congr rfl
  intro u _
  have hu (v : Vector d) (eqn : C v = u) :
      (fun i => (u i : ℕ)) ∈ U ↔ v ∈ U := eqn ▸ clip v
  split_ifs with H
  · have cells : V.filter (fun v => C v = u) =
        Fintype.piFinset fun i => (range L).filter (fun j => c j = u i) := by
      ext v
      simp only [V, mem_filter, mem_box, Fintype.mem_piFinset, mem_range]
      constructor
      · rintro ⟨⟨hv,_⟩,eqn⟩
        exact fun i => ⟨hv i, congrFun eqn i⟩
      · intro hv
        have eqn : C v = u := funext fun i => (hv i).2
        exact ⟨⟨fun i => (hv i).1, (hu _ eqn).mp H⟩, eqn⟩
    rw [cells, ← prod_univ_sum _ (fun _ j => w j)]
    exact prod_congr rfl fun i _ => oneLetter (u i)
  · apply sum_eq_zero
    intro v hv
    exact False.elim (H ((hu v (mem_filter.mp hv).2).mpr (mem_filter.mp (mem_filter.mp hv).1).2))

private lemma clippedMass_mod_prime {d q r M : ℕ} (hq : q.Prime) (hd : d = q ^ r)
    (U : Set (Vector d)) (upper : IsUpperSet U) (symm : SymmetricSet U)
    {a : ℕ} (hit : (fun _ => a) ∈ U) (ha : a ≤ M) :
    ∃ m ≤ a, (clippedMass U M : ZMod q) = -(2 ^ m) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  have ex : ∃ j : ℕ, (fun _ => j) ∈ U := ⟨a, hit⟩
  let m := Nat.find ex
  have hm : m ≤ M := (Nat.find_min' ex hit).trans ha
  have threshold (j : ℕ) : (fun _ => j) ∈ U ↔ m ≤ j :=
    ⟨fun hj => Nat.find_min' ex hj, fun hj => upper (fun _ => hj) (Nat.find_spec ex)⟩
  let f (v : Fin d → Fin (M+1)) : ZMod q :=
    if (fun i => (v i : ℕ)) ∈ U then ∏ i, (letter M (v i) : ZMod q) else 0
  have inv (v) (σ : Equiv.Perm (Fin d)) : f (v ∘ σ) = f v := by
    have h := symm (fun i => (v i : ℕ)) σ
    change ((fun i => ((v ∘ σ) i : ℕ)) ∈ U ↔ _) at h
    simp only [f, h]
    split_ifs
    · exact Equiv.prod_comp σ (fun i => (letter M (v i) : ZMod q))
    · rfl
  have diag (a : Fin (M+1)) : f (fun _ => a) =
      if m ≤ a.val then (letter M a : ZMod q) else 0 := by
    simp [f, threshold, hd, ZMod.pow_card_pow]
  refine ⟨m, Nat.find_min' ex hit, ?_⟩
  simp only [clippedMass, Int.cast_sum, Int.cast_ite, Int.cast_prod, Int.cast_zero]
  change (∑ v, f v) = _
  rw [sum_eq_diagonal_of_prime_power hq hd f inv]
  simp only [diag]
  rw [Fin.sum_univ_eq_sum_range (fun j => if m ≤ j then (letter M j : ZMod q) else 0), sum_range_succ]
  have cells : (range M).filter (m ≤ ·) = Ico m M := by ext; simp; omega
  rw [← sum_filter, cells, ite_eq_left hm]
  have inner : ∑ j ∈ Ico m M, (letter M j : ZMod q) = ∑ j ∈ Ico m M, (2 : ZMod q)^j :=
    sum_congr rfl fun j hj => by simp [letter,(mem_Ico.mp hj).2]
  have geom := geom_sum_Ico_mul (2 : ZMod q) hm
  rw [inner]
  simp [letter] at geom ⊢
  linear_combination geom

/-- In prime-power dimension, binary mass stabilizes at an integer whose
residue modulo the degree prime is the negative of a power of two. -/
theorem symmetric_binary_mass {d q r : ℕ} (hq : q.Prime) (hd : d = q ^ r)
    (U : Set (Vector d)) (upper : IsUpperSet U) (symm : SymmetricSet U)
    {a : ℕ} (anchor : (fun _ => a) ∈ U) :
    ∃ K : ℤ, ∃ m ≤ a, (K : ZMod q) = -(2^m) ∧
      ∀ᶠ L : ℕ in atTop, (mass 2 L U : ZMod (2^L)) = K := by
  classical
  obtain ⟨M, le, clip⟩ := exists_clip U upper a
  obtain ⟨m, hm, eqn⟩ := clippedMass_mod_prime hq hd U upper symm anchor le
  refine ⟨clippedMass U M, m, hm, eqn, ?_⟩
  filter_upwards [eventually_ge_atTop M] with L hL
  exact mass_eq_clipped hL U clip

/-- A single binary precision works for all symmetric upper sets containing a
given constant point, when their dimension is a power of an odd prime. -/
theorem symmetric_binary_uniform_precision {d q r : ℕ} (hq : q.Prime) (odd : 2 < q)
    (hd : d = q ^ r) (a : ℕ) :
    ∃ L : ℕ, ∀ U : Set (Vector d), IsUpperSet U → SymmetricSet U → (fun _ => a) ∈ U →
      (mass 2 L U : ZMod (2^L)) ≠ 0 := by
  classical
  by_contra! h
  choose U upper symm hit vanish using h
  let f (j : ℕ) (v : Vector d) : Bool := decide (v ∈ U j)
  obtain ⟨g, φ, inc, conv⟩ := CompactSpace.tendsto_subseq f
  let V : Set (Vector d) := {v | g v = true}
  have coord (v : Vector d) : ∀ᶠ j in atTop, (v ∈ U (φ j) ↔ v ∈ V) := by
    have c := (tendsto_pi_nhds.mp conv v).eventually
      (isOpen_discrete {g v} |>.mem_nhds (Set.mem_singleton _))
    filter_upwards [c] with j hj
    change decide (v ∈ U (φ j)) = g v at hj
    simp [V, ← hj]
  have hv : IsUpperSet V := by
    intro x y le hx
    obtain ⟨j,hx',hy'⟩ := ((coord x).and (coord y)).exists
    exact hy'.mp (upper _ le (hx'.mpr hx))
  have sv : SymmetricSet V := by
    intro v σ
    obtain ⟨j,h₁,h₂⟩ := ((coord (v ∘ σ)).and (coord v)).exists
    exact h₁.symm.trans ((symm (φ j) v σ).trans h₂)
  obtain ⟨j,hj⟩ := (coord (fun _ => a)).exists
  obtain ⟨K,m,_,residue,stable⟩ := symmetric_binary_mass hq hd V hv sv (hj.mp (hit _))
  have nonzero : K ≠ 0 := by
    let : Fact q.Prime := ⟨hq⟩
    have nz : (2 : ZMod q) ≠ 0 := by
      exact_mod_cast fun h => (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) odd) ((ZMod.natCast_eq_zero_iff 2 q).mp h)
    intro zero
    simp [zero, pow_ne_zero m nz] at residue
  obtain ⟨L,eqn,large⟩ := (stable.and (eventually_ge_atTop (K.natAbs+1))).exists
  have matchbox := (eventually_all_finset (box d L)).mpr (fun v _ => coord v)
  obtain ⟨j,matchj,late⟩ := (matchbox.and (inc.tendsto_atTop.eventually_ge_atTop L)).exists
  have eqMass : mass 2 L (U (φ j)) = mass 2 L V := by
    unfold mass weightedMass
    congr 1
    ext v
    simp only [mem_filter]
    exact and_congr_right (fun hv => matchj v hv)
  have zero : (mass 2 L V : ZMod (2^L)) = 0 := by
    rw [← eqMass, ← mass_reduce (fun _ => 1) late, ZMod.natCast_eq_zero_iff]
    exact (pow_dvd_pow 2 late).trans ((ZMod.natCast_eq_zero_iff ..).mp (vanish (φ j)))
  have div := (ZMod.intCast_zmod_eq_zero_iff_dvd K (2^L)).mp (eqn.symm.trans zero)
  apply nonzero (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs div ?_)
  simpa using (show K.natAbs < 2^L from (by omega : K.natAbs < L).trans (Nat.lt_pow_self (by decide)))

end NormalityChecker.StonehamPolynomial
