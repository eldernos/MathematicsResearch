module

public import NormalityChecker.StonehamPolynomialOrthant
public import NormalityChecker.PrimeCancellation
public import NormalityChecker.LocalizedMesh
public import Mathlib.Data.Nat.Totient

/-! The shifted rational prefix of a product with one prime parameter. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

variable {d : ℕ}

def position (p : ℕ) (m j : Vector d) := ∑ i, m i * p^(j i)

def active (p : ℕ) (m : Vector d) (n : ℕ) :=
  (box d (Nat.log p n + 1)).filter (fun j => position p m j ≤ n)

theorem mem_active {p n : ℕ} (hp : 1 < p) {m j : Vector d} (hm : ∀ i, 0 < m i) :
    j ∈ active p m n ↔ position p m j ≤ n := by
  simp only [active, mem_filter, mem_box, and_iff_right_iff_imp]
  intro h i
  have le : p^(j i) ≤ position p m j :=
    (Nat.le_mul_of_pos_left _ (hm i)).trans
      (single_le_sum (f := fun i => m i * p^(j i)) (fun _ _ => Nat.zero_le _) (mem_univ i))
  exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp (le.trans h))

def productPrefix (b p : ℕ) (m : Vector d) (n : ℕ) : ℚ :=
  ∑ j ∈ active p m n, (b:ℚ)^(n-position p m j) / (p:ℚ)^weight j

private def reflect (k : ℕ) (j : Vector d) : Vector d := fun i => k - j i

private lemma reflect_box {k : ℕ} (j : Vector d) : reflect k j ∈ box d (k+1) :=
  mem_box.mpr fun _ => Nat.lt_succ_of_le (Nat.sub_le ..)

private lemma reflect_reflect {k : ℕ} {j : Vector d} (h : j ∈ box d (k+1)) :
    reflect k (reflect k j) = j := by
  funext i
  exact Nat.sub_sub_self (Nat.le_of_lt_succ (mem_box.mp h i))

private lemma weight_reflect {k : ℕ} {j : Vector d} (h : j ∈ box d (k+1)) :
    weight (reflect k j) + weight j = d*k := by
  simp only [weight, ← sum_add_distrib, reflect]
  simp [Nat.sub_add_cancel (Nat.le_of_lt_succ (mem_box.mp h _))]

private def cut (p : ℕ) (m : Vector d) (k n : ℕ) : Set (Vector d) :=
  {j | position p m (reflect k j) ≤ n}

private lemma cut_upper {p : ℕ} (hp : 0 < p) (m : Vector d) (k n : ℕ) :
    IsUpperSet (cut p m k n) := by
  intro x y h hx
  change position p m (reflect k y) ≤ n
  apply le_trans _ hx
  exact sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp (Nat.sub_le_sub_left (h i) _)))

private def numerator (b p : ℕ) (m : Vector d) (k n : ℕ) :=
  ∑ v ∈ (box d (k+1)).filter (fun v => position p m (reflect k v) ≤ n),
    p ^ weight v * b^(n-position p m (reflect k v))

private lemma scaled {b p n : ℕ} (hp : 0 < p) (m : Vector d) :
    (numerator b p m (Nat.log p n) n : ℚ) =
      (p:ℚ)^(d*Nat.log p n) * productPrefix b p m n := by
  let k := Nat.log p n
  let A := (box d (k+1)).filter (fun v => position p m (reflect k v) ≤ n)
  have fr {v} (hv : v ∈ A) : reflect k v ∈ active p m n :=
    mem_filter.mpr ⟨reflect_box _,(mem_filter.mp hv).2⟩
  have rf {v} (hv : v ∈ active p m n) : reflect k v ∈ A := by
    refine mem_filter.mpr ⟨reflect_box _, ?_⟩
    rw [reflect_reflect (mem_filter.mp hv).1]
    exact (mem_filter.mp hv).2
  simp only [productPrefix, mul_sum, numerator, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  apply sum_bij' (fun v _ => reflect k v) (fun v _ => reflect k v)
    (fun _ hv => fr hv) (fun _ hv => rf hv)
    (fun _ hv => reflect_reflect (mem_filter.mp hv).1) (fun _ hv => reflect_reflect (mem_filter.mp hv).1)
  intro v hv
  have w := weight_reflect (k:=k) (mem_filter.mp hv).1
  change (p:ℚ)^weight v * _ = (p:ℚ)^(d*k) * (_ / (p:ℚ)^weight (reflect k v))
  rw [← w,pow_add]; field_simp; rfl

theorem denominator_dvd {b p n : ℕ} (hp : 0 < p) (m : Vector d) :
    (productPrefix b p m n).den ∣ p^(d*Nat.log p n) := by
  apply (reduced_info (S:=numerator b p m (Nat.log p n) n) (pow_pos hp _) _).1
  exact_mod_cast scaled (b:=b) (n:=n) hp m

private lemma stable_power {b p L j k : ℕ} (hp : p.Prime) (cop : b.Coprime p)
    (lo : L ≤ j) (hi : j ≤ k) :
    (b : ZMod (p^L))^(p^k) = b^(p^j) := by
  induction k, hi using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    by_cases zero : L=0
    · subst L; change (_ : ZMod 1) = _; exact Subsingleton.elim ..
    have euler : (b : ZMod (p^L)) ^ (p^L).totient = 1 := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ (p^L)).mpr (Nat.ModEq.pow_totient (cop.pow_right L))
    obtain ⟨s,hs⟩ : (p^L).totient ∣ p^k*(p-1) := by
      rw [Nat.totient_prime_pow hp (by omega)]
      exact Nat.mul_dvd_mul (pow_dvd_pow p (by omega)) dvd_rfl
    rw [show p^(k+1)=p^k + p^k*(p-1) by rw [pow_succ, show p^k + p^k*(p-1) = p^k*(1+(p-1)) by ring, show 1+(p-1)=p by have := hp.pos; omega],
      pow_add,hs,pow_mul,euler,one_pow,mul_one,ih]

private lemma stable_position {b p L k : ℕ} (hp : p.Prime) (cop : b.Coprime p)
    (m v : Vector d) (small : v ∈ box d L) (late : 2*L ≤ k) :
    (b : ZMod (p^L)) ^ position p m (fun _ => k) =
      b ^ position p m (reflect k v) := by
  simp only [position, ← prod_pow_eq_pow_sum]
  apply prod_congr rfl
  intro i _
  have hi := mem_box.mp small i
  simp only [reflect, Nat.mul_comm (m i), pow_mul]
  rw [stable_power hp cop (j:=k-v i) (by omega) (Nat.sub_le ..)]

/-- The numerator has the same vanishing behavior as the unweighted upper-set
sum. The removed factors are units modulo the chosen prime power. -/
private lemma numerator_nonzero {b p L k n : ℕ} (hp : p.Prime) (cop : b.Coprime p)
    (m : Vector d) (late : 2*L ≤ k)
    (hn : (mass p L (cut p m k n) : ZMod (p^L)) ≠ 0) :
    (numerator b p m k n : ZMod (p^L)) ≠ 0 := by
  classical
  let A := (box d (k+1)).filter (fun v => position p m (reflect k v) ≤ n)
  let F := (box d L).filter (fun v => position p m (reflect k v) ≤ n)
  have sub : F ⊆ A := by
    intro v h
    obtain ⟨hx,hw⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_box.mpr (fun i => by have := mem_box.mp hx i; omega), hw⟩
  have eqMass : mass p L (cut p m k n) = ∑ v ∈ F, p ^ weight v := by
    unfold mass; congr 1
    exact @filter_congr _ _ _ (fun _ => Classical.propDecidable _) _ _ (fun _ _ => Iff.rfl)
  have eqn :
      (numerator b p m k n : ZMod (p^L)) * b^position p m (fun _ => k) =
        (mass p L (cut p m k n) : ZMod (p^L)) * b^n := by
    rw [eqMass]
    simp only [numerator,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,sum_mul]
    symm
    apply sum_subset_zero_on_sdiff sub
    · intro v hv
      obtain ⟨ha,hf⟩ := mem_sdiff.mp hv
      have hv' : v ∉ box d L := fun h => hf (mem_filter.mpr ⟨h,(mem_filter.mp ha).2⟩)
      obtain ⟨i,hi⟩ : ∃ i, L ≤ v i := by simpa using hv'
      have w : L ≤ weight v := hi.trans (single_le_sum (fun j _ => Nat.zero_le (v j)) (mem_univ i))
      have z : (p : ZMod (p^L))^weight v = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow _ w
      simp [z]
    · intro v hv
      rw [stable_position hp cop m v (mem_filter.mp hv).1 late, mul_assoc, ← pow_add,
        Nat.sub_add_cancel (mem_filter.mp hv).2]
  intro h
  rw [h,zero_mul] at eqn
  exact hn (((ZMod.isUnit_iff_coprime b (p^L)).mpr (cop.pow_right L)).pow n |>.mul_right_cancel
    (by simpa using eqn.symm : _ = 0 * (b : ZMod (p^L))^n))

/-- On every sufficiently late scale the reduced denominator retains all but
a bounded number of the `d * log_p n` powers of the denominator prime. -/
theorem retained_denominator {b p : ℕ} (hp : p.Prime) (odd : 3 ≤ p) (cop : b.Coprime p)
    (m : Vector d) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log p n → 0 < n →
      p^(d*Nat.log p n - L) ∣ (productPrefix b p m n).den := by
  let J := ∑ i, m i
  obtain ⟨L,pass⟩ := uniform_precision odd (fun _ : Fin d => J)
  refine ⟨L,max (2*L) J,fun n late pos => ?_⟩
  let k := Nat.log p n
  have jl : J ≤ k := (le_max_right ..).trans late
  have hit : (fun _ : Fin d => J) ∈ cut p m k n := by
    change (∑ i, m i * p^(k-J)) ≤ n
    rw [← sum_mul]
    apply le_trans _ (Nat.pow_log_le_self p pos.ne')
    change J*p^(k-J) ≤ p^k
    conv_rhs => rw [← Nat.add_sub_of_le jl,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.lt_pow_self (n:=J) hp.one_lt).le
  have nz := numerator_nonzero hp cop m ((le_max_left ..).trans late)
    (pass _ (cut_upper hp.pos m k n) hit)
  let A := numerator b p m k n
  have no : ¬p^L ∣ A := fun div => nz ((ZMod.natCast_eq_zero_iff ..).mpr div)
  have reduced := reduced_info (S:=A) (x:=productPrefix b p m n) (pow_pos hp.pos (d*k))
    (by exact_mod_cast scaled (b:=b) (n:=n) hp.pos m)
  have cross := reduced.2
  have nonzero : A ≠ 0 := fun h => no (h ▸ dvd_zero _)
  have vlt : A.factorization p < L := lt_of_not_ge (fun h => no ((hp.pow_dvd_iff_le_factorization nonzero).mpr h))
  apply (hp.pow_dvd_iff_le_factorization (productPrefix b p m n).pos.ne').mpr
  have div : p^(d*k) ∣ A*(productPrefix b p m n).den := cross ▸ dvd_mul_right _ _
  have le := (hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero nonzero (productPrefix b p m n).pos.ne')).mp div
  rw [Nat.factorization_mul nonzero (productPrefix b p m n).pos.ne',Finsupp.add_apply] at le
  change d*k-L ≤ _; omega

end NormalityChecker.StonehamPolynomial
