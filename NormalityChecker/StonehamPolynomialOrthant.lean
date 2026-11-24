module

public import Mathlib.Order.WellFoundedSet
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.GeomSum

/-! Truncated geometric sums on upper sets of exponent vectors. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

abbrev Vector (d : ℕ) := Fin d → ℕ

def box (d L : ℕ) : Finset (Vector d) := Fintype.piFinset fun _ => range L

@[simp] theorem mem_box {d L : ℕ} {v : Vector d} : v ∈ box d L ↔ ∀ i, v i < L := by
  simp [box, Fintype.mem_piFinset]

def weight {d : ℕ} (v : Vector d) := ∑ i, v i

noncomputable def mass {d : ℕ} (p L : ℕ) (U : Set (Vector d)) : ℕ := by
  classical exact ∑ v ∈ (box d L).filter (· ∈ U), p ^ weight v

private lemma big_power {p L j : ℕ} (h : L ≤ j) : (p : ZMod (p^L)) ^ j = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow _ h

private lemma mass_orthant {d : ℕ} (p L : ℕ) (a : Vector d) :
    (mass p L (Set.Ici a) : ZMod (p^L)) * (1-p)^d = (p : ZMod (p^L))^weight a := by
  classical
  have cells : @Finset.filter _ (· ∈ Set.Ici a) (fun _ => Classical.propDecidable _) (box d L) = Fintype.piFinset fun i => Ico (a i) L := by
    ext v
    simp only [mem_filter, mem_box, Set.mem_Ici, Fintype.mem_piFinset, mem_Ico, Pi.le_def]
    grind
  have single (i : Fin d) :
      (∑ j ∈ Ico (a i) L, (p : ZMod (p^L)) ^ j) * (1-p) = p ^ (a i) := by
    by_cases h : a i ≤ L
    · simpa [big_power (le_refl L)] using geom_sum_Ico_mul_neg (p : ZMod (p^L)) h
    · simp [Ico_eq_empty_of_le (le_of_not_ge h), big_power (le_of_not_ge h)]
  unfold mass
  rw [cells]
  simp only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow, weight, ← prod_pow_eq_pow_sum]
  rw [← prod_univ_sum (fun i => Ico (a i) L) (fun _ j => (p : ZMod (p^L))^j)]
  simpa only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] using
    prod_congr (s₁ := (univ : Finset (Fin d))) rfl (fun i _ => single i)

private def orthants {d : ℕ} (s : List (Vector d)) : Set (Vector d) :=
  {v | ∃ a ∈ s, a ≤ v}

private lemma union_formula {d : ℕ} (p L : ℕ) (a : Vector d) (s : List (Vector d)) :
    (mass p L (orthants (a :: s)) : ℤ) =
      mass p L (Set.Ici a) + mass p L (orthants s) -
        mass p L (orthants (s.map (a ⊔ ·))) := by
  classical
  simp only [mass, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_pow,
    ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  have h : v ∈ orthants (s.map (a ⊔ ·)) ↔ a ≤ v ∧ v ∈ orthants s := by
    simp [orthants, sup_le_iff]; grind
  have h' : v ∈ orthants (a :: s) ↔ a ≤ v ∨ v ∈ orthants s := by simp [orthants]
  simp only [h, h', Set.mem_Ici]
  split_ifs <;> grind

private theorem list_numerator {d p : ℕ} (hp : 2 ≤ p) {n : ℕ} (s : List (Vector d))
    (length : s.length = n) :
    ∃ K : ℤ, (K : ZMod (p-1)) = (if s = [] then 0 else 1) ∧
      ∀ L : ℕ, (mass p L (orthants s) : ZMod (p^L)) * (1-p)^d = K := by
  classical
  induction n generalizing s with
  | zero =>
    have := List.length_eq_zero_iff.mp length
    subst s
    exact ⟨0, by simp, fun L => by simp [orthants, mass]⟩
  | succ n ih =>
    obtain ⟨a,s,rfl⟩ := List.exists_cons_of_ne_nil (l := s) (by intro h; simp [h] at length)
    simp only [List.length_cons, Nat.succ.injEq] at length
    obtain ⟨P,hP,eP⟩ := ih s length
    obtain ⟨Q,hQ,eQ⟩ := ih (s.map (a ⊔ ·)) (by simpa using length)
    refine ⟨(p:ℤ)^weight a + P - Q, ?_, fun L => ?_⟩
    · have cast : (p : ZMod (p-1)) = 1 := by
        have e := congrArg (fun j : ℕ => (j : ZMod (p-1))) (show p = (p-1)+1 by omega)
        simpa only [Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add] using e
      simp only [Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_natCast, cast, one_pow, hP, hQ]
      simp
    · have eqn := congrArg (fun z : ℤ => (z : ZMod (p^L))) (union_formula p L a s)
      push_cast at eqn ⊢
      rw [eqn, sub_mul, add_mul, mass_orthant, eP, eQ]

/-- A nonempty upper set has a geometric numerator congruent to one modulo
`p-1`. Multiplication by `(1-p)^d` gives this integer at every precision. -/
theorem upper_set_numerator {d p : ℕ} (hp : 2 ≤ p) (U : Set (Vector d))
    (upper : IsUpperSet U) (nonempty : U.Nonempty) :
    ∃ K : ℤ, (K : ZMod (p-1)) = 1 ∧
      ∀ L : ℕ, (mass p L U : ZMod (p^L)) * (1-p)^d = K := by
  classical
  let S : Set (Vector d) := {v | Minimal (· ∈ U) v}
  have anti : IsAntichain (· ≤ ·) S := by
    intro x hx y hy ne h
    exact ne (le_antisymm h (hy.2 hx.1 h))
  let F := (WellQuasiOrderedLE.finite_of_isAntichain anti).toFinset
  have eqn : orthants F.toList = U := by
    ext v
    constructor
    · rintro ⟨a,ha,le⟩
      have hm : a ∈ S := by simpa [F] using ha
      exact upper le hm.1
    · intro hv
      obtain ⟨a,le,ha⟩ := (Set.isPWO_of_wellQuasiOrderedLE U).exists_le_minimal hv
      exact ⟨a, by simpa [F,S] using ha, le⟩
  have ne : F.toList ≠ [] := by
    intro h
    obtain ⟨v,hv⟩ := nonempty
    rw [← eqn,h] at hv
    simp [orthants] at hv
  simpa [ne,eqn] using list_numerator hp F.toList rfl

private lemma mass_reduce {d p L J : ℕ} (le : L ≤ J) (U : Set (Vector d)) :
    (mass p J U : ZMod (p^L)) = mass p L U := by
  classical
  simp only [mass, Nat.cast_sum, Nat.cast_pow]
  symm
  apply sum_subset_zero_on_sdiff
  · intro v hv
    simp only [mem_filter, mem_box] at hv ⊢
    exact ⟨fun i => (hv.1 i).trans_le le, hv.2⟩
  · intro v hv
    obtain ⟨hi,hn⟩ := mem_sdiff.mp hv
    simp only [mem_filter, mem_box] at hi hn
    obtain ⟨i,hi⟩ : ∃ i, L ≤ v i := by by_contra! h; exact hn ⟨h,hi.2⟩
    apply big_power (hi.trans _)
    exact single_le_sum (fun j _ => Nat.zero_le (v j)) (mem_univ i)
  · simp

/-- Uniform finite precision over all upper sets containing one specified
point. Compactness of the Boolean membership functions gives a single cutoff. -/
theorem uniform_precision {d p : ℕ} (hp : 3 ≤ p) (anchor : Vector d) :
    ∃ L : ℕ, ∀ U : Set (Vector d), IsUpperSet U → anchor ∈ U →
      (mass p L U : ZMod (p^L)) ≠ 0 := by
  classical
  by_contra! h
  choose U upper hit vanish using h
  let f (j : ℕ) (v : Vector d) : Bool := decide (v ∈ U j)
  obtain ⟨g, φ, inc, conv⟩ := CompactSpace.tendsto_subseq f
  let V : Set (Vector d) := {v | g v = true}
  have coord (v : Vector d) : ∀ᶠ j in atTop, (v ∈ U (φ j) ↔ v ∈ V) := by
    have c := (tendsto_pi_nhds.mp conv v).eventually (isOpen_discrete {g v} |>.mem_nhds (Set.mem_singleton _))
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
  obtain ⟨K,cK,eqn⟩ := upper_set_numerator (by omega : 2 ≤ p) V hv ⟨_,ha⟩
  have kn : K ≠ 0 := by
    let : Fact (1 < p-1) := ⟨by omega⟩
    intro hK
    simp [hK] at cK
  let L := K.natAbs+1
  have matchbox := (eventually_all_finset (box d L)).mpr (fun v _ => coord v)
  obtain ⟨j,matchj,large⟩ := (matchbox.and (inc.tendsto_atTop.eventually_ge_atTop L)).exists
  have eqMass : mass p L (U (φ j)) = mass p L V := by
    unfold mass
    congr 1
    ext v
    simp only [mem_filter]
    exact and_congr_right (fun hv => matchj v hv)
  have zero : (mass p L V : ZMod (p^L)) = 0 := by
    rw [← eqMass, ← mass_reduce large, ZMod.natCast_eq_zero_iff]
    exact (pow_dvd_pow p large).trans ((ZMod.natCast_eq_zero_iff ..).mp (vanish (φ j)))
  have ek := eqn L
  rw [zero,zero_mul] at ek
  have div := (ZMod.intCast_zmod_eq_zero_iff_dvd K (p^L)).mp ek.symm
  have small : K.natAbs < p^L :=
    (Nat.lt_succ_self _).trans_le (Nat.lt_pow_self (n:=L) (by omega : 2 ≤ p)).le
  exact kn (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs div (by simpa using small))

end NormalityChecker.StonehamPolynomial
