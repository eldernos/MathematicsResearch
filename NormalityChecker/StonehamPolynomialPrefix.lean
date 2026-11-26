module

public import NormalityChecker.StonehamPolynomialOrthant
public import NormalityChecker.PrimeCancellation
public import Mathlib.Data.Nat.Totient

/-! The shifted rational prefix of a product with one common parameter. -/
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

/-- At every prime-power precision the sequence of radix powers is eventually constant. -/
def StablePowers (b c p : ℕ) : Prop :=
  ∀ L : ℕ, ∃ N : ℕ, ∀ j k : ℕ, N ≤ j → N ≤ k →
    (b : ZMod (p^L))^(c^k) = b^(c^j)

theorem stablePowers_prime {b p : ℕ} (hp : p.Prime) (cop : b.Coprime p) : StablePowers b p p := by
  intro L
  refine ⟨L, fun j k hj hk => ?_⟩
  exact (stable_power hp cop le_rfl hk).trans (stable_power hp cop le_rfl hj).symm

private lemma stable_position {b c p L N k : ℕ}
    (stable : ∀ j k : ℕ, N ≤ j → N ≤ k → (b : ZMod (p^L))^(c^k) = b^(c^j))
    (e : Strides d) (m v : Vector d) (small : v ∈ box d L) (late : ∀ i, L+N ≤ caps e k i) :
    (b : ZMod (p^L)) ^ (∑ i, m i*c^k) =
      b ^ position c e m (reflect e k v) := by
  simp only [position, ← prod_pow_eq_pow_sum]
  apply prod_congr rfl
  intro i _
  have hi := mem_box.mp small i
  simp only [Nat.mul_comm (m i), pow_mul]
  have lo := late i
  have near : N ≤ caps e k i-v i := by omega
  have left := near.trans (Nat.le_mul_of_pos_left (caps e k i-v i) (e i).pos)
  apply congrArg (· ^ m i)
  exact stable _ _ left (left.trans ((Nat.mul_le_mul_left (e i : ℕ) (Nat.sub_le _ _)).trans
    (Nat.mul_div_le k _)))

/-- Removing the radix powers leaves the weighted upper-set sum modulo the chosen prime power. -/
private lemma numerator_nonzero {b c p L N k n : ℕ} (pc : p ∣ c) (cop : b.Coprime p)
    (stable : ∀ j k : ℕ, N ≤ j → N ≤ k → (b : ZMod (p^L))^(c^k) = b^(c^j))
    (e : Strides d) (m : Vector d) (late : ∀ i, L+N ≤ caps e k i)
    (hn : (weightedMass e c L (cut c e m k n) : ZMod (p^L)) ≠ 0) :
    (numerator b c e m k n : ZMod (p^L)) ≠ 0 := by
  classical
  let A := (rectangle e k).filter (fun v => position c e m (reflect e k v) ≤ n)
  let F := (box d L).filter (fun v => position c e m (reflect e k v) ≤ n)
  have sub : F ⊆ A := by
    intro v h
    obtain ⟨hx,hw⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_rectangle.mpr (fun i => by have := mem_box.mp hx i; have := late i; omega), hw⟩
  have eqMass : weightedMass e c L (cut c e m k n) = ∑ v ∈ F, c ^ weight (stretch e v) := by
    unfold weightedMass; congr 1
    exact @filter_congr _ _ _ (fun _ => Classical.propDecidable _) _ _ (fun _ _ => Iff.rfl)
  have eqn :
      (numerator b c e m k n : ZMod (p^L)) * b^(∑ i, m i*c^k) =
        (weightedMass e c L (cut c e m k n) : ZMod (p^L)) * b^n := by
    rw [eqMass]
    simp only [numerator,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,sum_mul]
    symm
    apply sum_subset_zero_on_sdiff sub
    · intro v hv
      obtain ⟨ha,hf⟩ := mem_sdiff.mp hv
      have hv' : v ∉ box d L := fun h => hf (mem_filter.mpr ⟨h,(mem_filter.mp ha).2⟩)
      obtain ⟨i,hi⟩ : ∃ i, L ≤ v i := by simpa using hv'
      have w : L ≤ weight (stretch e v) := hi.trans (le_stretched_weight e v i)
      have z : (c : ZMod (p^L))^weight (stretch e v) = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact (pow_dvd_pow_of_dvd pc L).trans (pow_dvd_pow c w)
      simp [z]
    · intro v hv
      rw [stable_position stable e m v (mem_filter.mp hv).1 late, mul_assoc, ← pow_add,
        Nat.sub_add_cancel (mem_filter.mp hv).2]
  intro h
  rw [h,zero_mul] at eqn
  have unit := ((ZMod.isUnit_iff_coprime b (p^L)).mpr (cop.pow_right L)).pow n
  exact hn (unit.mul_right_cancel (by simpa using eqn.symm : _ = 0 * (b : ZMod (p^L))^n))

/-- A nonzero residue bounds the number of factors lost when the prefix is reduced. -/
private theorem factorization_le_of_numerator {b c p L n : ℕ} (hp : p.Prime) (hc : 0 < c)
    (e : Strides d) (m : Vector d)
    (nz : (numerator b c e m (Nat.log c n) n : ZMod (p^L)) ≠ 0) :
    c.factorization p * scale e (Nat.log c n) ≤ (productPrefix b c e m n).den.factorization p + L := by
  let k := Nat.log c n
  let A := numerator b c e m k n
  have no : ¬p^L ∣ A := fun div => nz ((ZMod.natCast_eq_zero_iff ..).mpr div)
  have reduced := reduced_info (S:=A) (x:=productPrefix b c e m n) (pow_pos hc (scale e k))
    (by exact_mod_cast scaled (b:=b) (n:=n) hc e m)
  have cross := reduced.2
  have nonzero : A ≠ 0 := fun h => no (h ▸ dvd_zero _)
  have vlt : A.factorization p < L := lt_of_not_ge (fun h => no ((hp.pow_dvd_iff_le_factorization nonzero).mpr h))
  have div : c^(scale e k) ∣ A*(productPrefix b c e m n).den := cross ▸ dvd_mul_right _ _
  have le := (Nat.factorization_prime_le_iff_dvd (pow_pos hc _).ne'
    (Nat.mul_ne_zero nonzero (productPrefix b c e m n).pos.ne')).mpr div p hp
  rw [Nat.factorization_mul nonzero (productPrefix b c e m n).pos.ne', Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, mul_comm (scale e k)] at le
  change c.factorization p * scale e k ≤ _
  omega

/-- On every sufficiently late scale the reduced denominator retains all but
a bounded number of the `v_p(c) * d * log_c n` available powers of the prime `p`. -/
theorem retained_denominator_at {b c p : ℕ} (hp : p.Prime) (hc : 3 ≤ c) (pc : p ∣ c)
    (cop : b.Coprime p) (stable : StablePowers b c p)
    (e : Strides d) (m : Vector d) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log c n → 0 < n →
      p^(c.factorization p * (d*Nat.log c n) - L) ∣ (productPrefix b c e m n).den := by
  let J := ∑ i, m i
  obtain ⟨L,pass⟩ := weighted_uniform_precision_at e hc hp.one_lt pc (fun _ : Fin d => J)
  obtain ⟨N,freeze⟩ := stable L
  let W := ∑ i, (e i : ℕ)
  let T := max (L+N) J
  refine ⟨L+c.factorization p*W,T*(W+1),fun n late pos => ?_⟩
  let k := Nat.log c n
  have jl : J ≤ k := (le_max_right ..).trans ((Nat.le_mul_of_pos_right T (Nat.succ_pos W)).trans late)
  have near (i : Fin d) : T ≤ caps e k i := by
    apply (Nat.le_div_iff_mul_le (e i).pos).mpr
    have w : (e i : ℕ) ≤ W := single_le_sum (fun j _ => Nat.zero_le (e j : ℕ)) (mem_univ i)
    exact (Nat.mul_le_mul_left T (by omega : (e i : ℕ) ≤ W+1)).trans late
  have hit : (fun _ : Fin d => J) ∈ cut c e m k n := by
    change (∑ i, m i * c^(stretch e (reflect e k (fun _ => J)) i)) ≤ n
    refine le_trans (b:=∑ i, m i*c^(k-J)) (sum_le_sum (fun i _ => ?_)) ?_
    · apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_right (by omega : 0<c)
      change (e i : ℕ)*(k/(e i : ℕ)-J) ≤ k-J
      rw [Nat.mul_sub]
      exact tsub_le_tsub (Nat.mul_div_le k _) (Nat.le_mul_of_pos_left J (e i).pos)
    rw [← sum_mul]
    apply le_trans _ (Nat.pow_log_le_self c pos.ne')
    change J*c^(k-J) ≤ c^k
    conv_rhs => rw [← Nat.add_sub_of_le jl,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.lt_pow_self (n:=J) (by omega : 1<c)).le
  have nz := numerator_nonzero pc cop freeze e m (fun i => (le_max_left ..).trans (near i))
    (pass _ (cut_upper (by omega : 0<c) e m k n) hit)
  have le : c.factorization p * scale e k ≤ _ := factorization_le_of_numerator hp (by omega : 0 < c) e m nz
  apply (hp.pow_dvd_iff_le_factorization (productPrefix b c e m n).pos.ne').mpr
  have gap := Nat.mul_le_mul_left (c.factorization p) (show d*k ≤ scale e k+W from scale_lower e k)
  rw [Nat.mul_add] at gap
  change c.factorization p*(d*k)-(L+c.factorization p*W) ≤ _
  omega

/-- The single-prime denominator estimate. -/
theorem retained_denominator {b p : ℕ} (hp : p.Prime) (odd : 3 ≤ p) (cop : b.Coprime p)
    (e : Strides d) (m : Vector d) :
    ∃ L K : ℕ, ∀ n : ℕ, K ≤ Nat.log p n → 0 < n →
      p^(d*Nat.log p n - L) ∣ (productPrefix b p e m n).den := by
  simpa [hp.factorization_self] using
    retained_denominator_at hp odd dvd_rfl cop (stablePowers_prime hp cop) e m

end NormalityChecker.StonehamPolynomial
