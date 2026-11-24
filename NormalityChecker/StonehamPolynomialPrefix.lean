module

public import NormalityChecker.StonehamPolynomialOrthant
public import NormalityChecker.PrimeCancellation
public import Mathlib.Data.Nat.Totient

/-! The shifted rational prefix of a product with one prime parameter. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

variable {d : ℕ}

def position (p : ℕ) (e : Strides d) (m j : Vector d) := ∑ i, m i * p^(stretch e j i)

/-- Largest admissible index in each coordinate at prime-exponent scale `k`. -/
def caps (e : Strides d) (k : ℕ) : Vector d := fun i => k / e i

/-- All tuples up to the coordinatewise scale bounds. -/
def rectangle (e : Strides d) (k : ℕ) :=
  Fintype.piFinset fun i => range (caps e k i + 1)

private lemma mem_rectangle {e : Strides d} {k : ℕ} {v : Vector d} :
    v ∈ rectangle e k ↔ ∀ i, v i ≤ caps e k i := by
  simp [rectangle,Fintype.mem_piFinset]

def active (p : ℕ) (e : Strides d) (m : Vector d) (n : ℕ) :=
  (rectangle e (Nat.log p n)).filter (fun j => position p e m j ≤ n)

theorem mem_active {p n : ℕ} (hp : 1 < p) {e : Strides d} {m j : Vector d} (hm : ∀ i, 0 < m i) :
    j ∈ active p e m n ↔ position p e m j ≤ n := by
  simp only [active, mem_filter, mem_rectangle, and_iff_right_iff_imp]
  intro h i
  have le : p^(stretch e j i) ≤ position p e m j :=
    (Nat.le_mul_of_pos_left _ (hm i)).trans
      (single_le_sum (f := fun i => m i * p^(stretch e j i)) (fun _ _ => Nat.zero_le _) (mem_univ i))
  apply (Nat.le_div_iff_mul_le (e i).pos).mpr
  simpa only [stretch,mul_comm (j i)] using Nat.le_log_of_pow_le hp (le.trans h)

def productPrefix (b p : ℕ) (e : Strides d) (m : Vector d) (n : ℕ) : ℚ :=
  ∑ j ∈ active p e m n, (b:ℚ)^(n-position p e m j) / (p:ℚ)^weight (stretch e j)

private def reflect (e : Strides d) (k : ℕ) (j : Vector d) : Vector d := fun i => caps e k i - j i

private lemma reflect_box (e : Strides d) {k : ℕ} (j : Vector d) :
    reflect e k j ∈ rectangle e k := mem_rectangle.mpr fun _ => Nat.sub_le ..

private lemma reflect_reflect {e : Strides d} {k : ℕ} {j : Vector d} (h : j ∈ rectangle e k) :
    reflect e k (reflect e k j) = j := by
  funext i
  exact Nat.sub_sub_self (mem_rectangle.mp h i)

private def scale (e : Strides d) (k : ℕ) := weight (stretch e (caps e k))

private lemma scale_upper (e : Strides d) (k : ℕ) : scale e k ≤ d*k := by
  simpa [scale,weight,stretch,caps] using
    sum_le_sum (s:=univ) (fun (i : Fin d) _ => Nat.mul_div_le k (e i : ℕ))

private lemma scale_lower (e : Strides d) (k : ℕ) :
    d*k ≤ scale e k + ∑ i, (e i : ℕ) := by
  simp only [scale,weight,← sum_add_distrib]
  have bound (i : Fin d) : k ≤ stretch e (caps e k) i + (e i : ℕ) := by
    change k ≤ (e i : ℕ)*(k/(e i : ℕ)) + (e i : ℕ)
    have := Nat.mod_add_div k (e i : ℕ)
    have := Nat.mod_lt k (e i).pos
    omega
  simpa using sum_le_sum (s:=univ) (fun i _ => bound i)

private lemma weight_reflect {k : ℕ} {e : Strides d} {j : Vector d} (h : j ∈ rectangle e k) :
    weight (stretch e (reflect e k j)) + weight (stretch e j) = scale e k := by
  simp only [weight,scale, ← sum_add_distrib, reflect,stretch, ← Nat.mul_add]
  simp [Nat.sub_add_cancel (mem_rectangle.mp h _)]

private def cut (p : ℕ) (e : Strides d) (m : Vector d) (k n : ℕ) : Set (Vector d) :=
  {j | position p e m (reflect e k j) ≤ n}

private lemma cut_upper {p : ℕ} (hp : 0 < p) (e : Strides d) (m : Vector d) (k n : ℕ) :
    IsUpperSet (cut p e m k n) := by
  intro x y h hx
  change position p e m (reflect e k y) ≤ n
  apply le_trans _ hx
  exact sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (h i) _))))

private def numerator (b p : ℕ) (e : Strides d) (m : Vector d) (k n : ℕ) :=
  ∑ v ∈ (rectangle e k).filter (fun v => position p e m (reflect e k v) ≤ n),
    p ^ weight (stretch e v) * b^(n-position p e m (reflect e k v))

private lemma scaled {b p n : ℕ} (hp : 0 < p) (e : Strides d) (m : Vector d) :
    (numerator b p e m (Nat.log p n) n : ℚ) =
      (p:ℚ)^(scale e (Nat.log p n)) * productPrefix b p e m n := by
  let k := Nat.log p n
  let A := (rectangle e k).filter (fun v => position p e m (reflect e k v) ≤ n)
  have fr {v} (hv : v ∈ A) : reflect e k v ∈ active p e m n :=
    mem_filter.mpr ⟨reflect_box _ _,(mem_filter.mp hv).2⟩
  have rf {v} (hv : v ∈ active p e m n) : reflect e k v ∈ A := by
    refine mem_filter.mpr ⟨reflect_box _ _, ?_⟩
    rw [reflect_reflect (mem_filter.mp hv).1]
    exact (mem_filter.mp hv).2
  simp only [productPrefix, mul_sum, numerator, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  apply sum_bij' (fun v _ => reflect e k v) (fun v _ => reflect e k v)
    (fun _ hv => fr hv) (fun _ hv => rf hv)
    (fun _ hv => reflect_reflect (mem_filter.mp hv).1) (fun _ hv => reflect_reflect (mem_filter.mp hv).1)
  intro v hv
  have w := weight_reflect (k:=k) (mem_filter.mp hv).1
  change (p:ℚ)^weight (stretch e v) * _ = (p:ℚ)^(scale e k) * (_ / (p:ℚ)^weight (stretch e (reflect e k v)))
  rw [← w,pow_add]; field_simp; rfl

theorem denominator_dvd {b p n : ℕ} (hp : 0 < p) (e : Strides d) (m : Vector d) :
    (productPrefix b p e m n).den ∣ p^(d*Nat.log p n) := by
  apply Dvd.dvd.trans _ (pow_dvd_pow p (scale_upper e (Nat.log p n)))
  apply (reduced_info (S:=numerator b p e m (Nat.log p n) n) (pow_pos hp _) _).1
  exact_mod_cast scaled (b:=b) (n:=n) hp e m

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
    have step : p^(k+1) = p^k + p^k*(p-1) := by
      calc p^(k+1) = p^k*(1+(p-1)) := by rw [show 1+(p-1)=p by have := hp.pos; omega, pow_succ]
           _ = _ := by ring
    rw [step,pow_add,hs,pow_mul,euler,one_pow,mul_one,ih]

private lemma stable_position {b p L k : ℕ} (hp : p.Prime) (cop : b.Coprime p)
    (e : Strides d) (m v : Vector d) (small : v ∈ box d L) (late : ∀ i, 2*L ≤ caps e k i) :
    (b : ZMod (p^L)) ^ (∑ i, m i*p^k) =
      b ^ position p e m (reflect e k v) := by
  simp only [position, ← prod_pow_eq_pow_sum]
  apply prod_congr rfl
  intro i _
  have hi := mem_box.mp small i
  simp only [Nat.mul_comm (m i), pow_mul]
  have lo := late i
  have near : L ≤ caps e k i-v i := by omega
  apply congrArg (· ^ m i)
  exact stable_power hp cop (near.trans (Nat.le_mul_of_pos_left _ (e i).pos))
    ((Nat.mul_le_mul_left (e i : ℕ) (Nat.sub_le _ _)).trans (Nat.mul_div_le k _))

/-- Removing the radix powers leaves the weighted upper-set sum modulo the chosen prime power. -/
private lemma numerator_nonzero {b p L k n : ℕ} (hp : p.Prime) (cop : b.Coprime p)
    (e : Strides d) (m : Vector d) (late : ∀ i, 2*L ≤ caps e k i)
    (hn : (weightedMass e p L (cut p e m k n) : ZMod (p^L)) ≠ 0) :
    (numerator b p e m k n : ZMod (p^L)) ≠ 0 := by
  classical
  let A := (rectangle e k).filter (fun v => position p e m (reflect e k v) ≤ n)
  let F := (box d L).filter (fun v => position p e m (reflect e k v) ≤ n)
  have sub : F ⊆ A := by
    intro v h
    obtain ⟨hx,hw⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_rectangle.mpr (fun i => by have := mem_box.mp hx i; have := late i; omega), hw⟩
  have eqMass : weightedMass e p L (cut p e m k n) = ∑ v ∈ F, p ^ weight (stretch e v) := by
    unfold weightedMass; congr 1
    exact @filter_congr _ _ _ (fun _ => Classical.propDecidable _) _ _ (fun _ _ => Iff.rfl)
  have eqn :
      (numerator b p e m k n : ZMod (p^L)) * b^(∑ i, m i*p^k) =
        (weightedMass e p L (cut p e m k n) : ZMod (p^L)) * b^n := by
    rw [eqMass]
    simp only [numerator,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,sum_mul]
    symm
    apply sum_subset_zero_on_sdiff sub
    · intro v hv
      obtain ⟨ha,hf⟩ := mem_sdiff.mp hv
      have hv' : v ∉ box d L := fun h => hf (mem_filter.mpr ⟨h,(mem_filter.mp ha).2⟩)
      obtain ⟨i,hi⟩ : ∃ i, L ≤ v i := by simpa using hv'
      have w : L ≤ weight (stretch e v) := hi.trans (le_stretched_weight e v i)
      have z : (p : ZMod (p^L))^weight (stretch e v) = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow _ w
      simp [z]
    · intro v hv
      rw [stable_position hp cop e m v (mem_filter.mp hv).1 late, mul_assoc, ← pow_add,
        Nat.sub_add_cancel (mem_filter.mp hv).2]
  intro h
  rw [h,zero_mul] at eqn
  have unit := ((ZMod.isUnit_iff_coprime b (p^L)).mpr (cop.pow_right L)).pow n
  exact hn (unit.mul_right_cancel (by simpa using eqn.symm : _ = 0 * (b : ZMod (p^L))^n))

/-- On every sufficiently late scale the reduced denominator retains all but
a bounded number of the `d * log_p n` powers of the denominator prime. -/
theorem retained_denominator {b p : ℕ} (hp : p.Prime) (odd : 3 ≤ p) (cop : b.Coprime p)
    (e : Strides d) (m : Vector d) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log p n → 0 < n →
      p^(d*Nat.log p n - L) ∣ (productPrefix b p e m n).den := by
  let J := ∑ i, m i
  obtain ⟨L,pass⟩ := weighted_uniform_precision e odd (fun _ : Fin d => J)
  let W := ∑ i, (e i : ℕ)
  let T := max (2*L) J
  refine ⟨L+W,T*(W+1),fun n late pos => ?_⟩
  let k := Nat.log p n
  have jl : J ≤ k := (le_max_right ..).trans ((Nat.le_mul_of_pos_right T (Nat.succ_pos W)).trans late)
  have near (i : Fin d) : T ≤ caps e k i := by
    apply (Nat.le_div_iff_mul_le (e i).pos).mpr
    have w : (e i : ℕ) ≤ W := single_le_sum (fun j _ => Nat.zero_le (e j : ℕ)) (mem_univ i)
    exact (Nat.mul_le_mul_left T (by omega : (e i : ℕ) ≤ W+1)).trans late
  have hit : (fun _ : Fin d => J) ∈ cut p e m k n := by
    change (∑ i, m i * p^(stretch e (reflect e k (fun _ => J)) i)) ≤ n
    refine le_trans (b:=∑ i, m i*p^(k-J)) (sum_le_sum (fun i _ => ?_)) ?_
    · apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_right hp.pos
      change (e i : ℕ)*(k/(e i : ℕ)-J) ≤ k-J
      rw [Nat.mul_sub]
      exact tsub_le_tsub (Nat.mul_div_le k _) (Nat.le_mul_of_pos_left J (e i).pos)
    rw [← sum_mul]
    apply le_trans _ (Nat.pow_log_le_self p pos.ne')
    change J*p^(k-J) ≤ p^k
    conv_rhs => rw [← Nat.add_sub_of_le jl,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.lt_pow_self (n:=J) hp.one_lt).le
  have nz := numerator_nonzero hp cop e m (fun i => (le_max_left ..).trans (near i))
    (pass _ (cut_upper hp.pos e m k n) hit)
  let A := numerator b p e m k n
  have no : ¬p^L ∣ A := fun div => nz ((ZMod.natCast_eq_zero_iff ..).mpr div)
  have reduced := reduced_info (S:=A) (x:=productPrefix b p e m n) (pow_pos hp.pos (scale e k))
    (by exact_mod_cast scaled (b:=b) (n:=n) hp.pos e m)
  have cross := reduced.2
  have nonzero : A ≠ 0 := fun h => no (h ▸ dvd_zero _)
  have vlt : A.factorization p < L := lt_of_not_ge (fun h => no ((hp.pow_dvd_iff_le_factorization nonzero).mpr h))
  apply (hp.pow_dvd_iff_le_factorization (productPrefix b p e m n).pos.ne').mpr
  have div : p^(scale e k) ∣ A*(productPrefix b p e m n).den := cross ▸ dvd_mul_right _ _
  have le := (hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero nonzero (productPrefix b p e m n).pos.ne')).mp div
  rw [Nat.factorization_mul nonzero (productPrefix b p e m n).pos.ne',Finsupp.add_apply] at le
  change d*k-(L+W) ≤ _
  have gap : d*k ≤ scale e k+W := scale_lower e k
  omega

end NormalityChecker.StonehamPolynomial
