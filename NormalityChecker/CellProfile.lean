module

public import NormalityChecker.LocalizedCertificate

/-! Exact prefix accounting for a pattern of failing cells repeated on geometric scales. -/
@[expose] public section
open Finset
namespace NormalityChecker.CellProfile

/-- On `[u*p^k,(u+1)*p^k)` the cell coordinate is `u`, for `S ≤ u < p*S`. -/
def coordinate (p S n : ℕ) := n / p^(Nat.log p (n/S))

theorem coordinate_eq {p S n k u : ℕ} (hp : 1<p) (hs : 0<S) (hu : S≤u) (hv : u<p*S)
    (lo : u*p^k≤n) (hi : n<(u+1)*p^k) : coordinate p S n=u := by
  have q := pow_pos (by omega : 0<p) k
  have low := (Nat.le_div_iff_mul_le hs).mpr (by simpa [mul_comm] using (Nat.mul_le_mul_right (p^k) hu).trans lo)
  have high : n/S<p^(k+1) := (Nat.div_lt_iff_lt_mul hs).mpr (hi.trans_le (by
    calc (u+1)*p^k ≤ (p*S)*p^k := Nat.mul_le_mul_right _ hv
         _ = p^(k+1)*S := by rw [pow_succ]; ring))
  unfold coordinate; rw [Nat.log_eq_of_pow_le_of_lt_pow low high]
  exact le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul q).mpr hi)) ((Nat.le_div_iff_mul_le q).mpr lo)

def mass (Z : Finset ℕ) (v : ℕ) : ℕ := (Z.filter (·<v)).card

def score (p : ℕ) (Z : Finset ℕ) (v : ℕ) : ℚ := ((Z.card:ℚ)/(p-1)+(mass Z v:ℚ))/v

/-- Compute the worst prefix, including both boundaries of the scale. -/
def bound (p S : ℕ) (Z : Finset ℕ) : ℚ :=
  (insert 0 ((Icc S (p*S)).image (score p Z))).max' (insert_nonempty ..)

theorem bound_nonneg (p S : ℕ) (Z : Finset ℕ) : 0≤bound p S Z := le_max' _ _ (mem_insert_self ..)

theorem score_le_bound {p S v : ℕ} (Z : Finset ℕ) (h : v∈Icc S (p*S)) : score p Z v≤bound p S Z :=
  le_max' _ _ (mem_insert_of_mem (mem_image.mpr ⟨v,h,rfl⟩))

private lemma mass_step (Z : Finset ℕ) (u : ℕ) : mass Z (u+1)=mass Z u+(if u∈Z then 1 else 0) := by
  classical
  by_cases h : u∈Z
  · have eqn : Z.filter (·<u+1)=insert u (Z.filter (·<u)) := by ext i; simp; grind
    unfold mass; rw [eqn]; simp [h]
  · have eqn : Z.filter (·<u+1)=Z.filter (·<u) := by ext i; simp; grind
    unfold mass; rw [eqn]; simp [h]

/-- The computed fraction bounds the number of uncontrolled positions before
*every* cutoff. Cells below the first scale carry no charge. -/
theorem count_bound {p S : ℕ} (hp : 1<p) (hs : 0<S) (Z : Finset ℕ) (hz : Z⊆Ico S (p*S)) (N : ℕ) :
    (∑ n∈range N, if coordinate p S n∈Z then (1:ℚ) else 0) ≤ bound p S Z*N := by
  let F (n : ℕ) := ∑ i∈range n, if coordinate p S i∈Z then (1:ℚ) else 0
  let D := bound p S Z
  have dp : 0≤D := bound_nonneg ..
  have early (n : ℕ) (le : n≤S) : F n=0 := by
    apply sum_eq_zero; intro i hi; apply ite_eq_right_iff.mpr; intro h; exfalso
    have a := (mem_Ico.mp (hz h)).1
    have b := Nat.div_le_self i (p^Nat.log p (i/S)); change S ≤ i / _ at a; have := mem_range.mp hi; omega
  have mlo : mass Z S=0 := by
    apply card_eq_zero.mpr; apply eq_empty_iff_forall_notMem.mpr; intro u hu
    obtain ⟨h,l⟩ := mem_filter.mp hu; exact l.not_ge (mem_Ico.mp (hz h)).1
  have mhi : mass Z (p*S)=Z.card := by rw [mass,filter_true_of_mem (fun i hi => (mem_Ico.mp (hz hi)).2)]
  have chunk (k u T : ℕ) (lo : S≤u) (hi : u<p*S) (le : T≤p^k) :
      F (u*p^k+T)=F (u*p^k)+(if u∈Z then (T:ℚ) else 0) := by
    dsimp [F]; rw [sum_range_add]; congr 1
    have coord (i : ℕ) (h : i∈range T) := coordinate_eq hp hs lo hi (Nat.le_add_right (u*p^k) i)
      (by rw [Nat.succ_mul]; have := mem_range.mp h; omega : u*p^k+i<(u+1)*p^k)
    have eqn := sum_congr (s₁:=range T) (f:=fun i => if coordinate p S (u*p^k+i)∈Z then (1:ℚ) else 0) (g:=fun _ => if u∈Z then (1:ℚ) else 0) rfl (fun i h => by rw [coord i h])
    rw [eqn]; split_ifs <;> simp
  have endpoints (k u : ℕ) (lo : S≤u) (hi : u≤p*S) :
      F (u*p^k)=F (S*p^k)+(p:ℚ)^k*mass Z u := by
    induction u,lo using Nat.le_induction with
    | base => simp [mlo]
    | succ u hu ih => rw [Nat.succ_mul,chunk k u (p^k) hu (by omega) le_rfl,ih (by omega),mass_step]; split_ifs <;> push_cast <;> ring
  let A := (Z.card:ℚ)/(p-1)
  have pp : 0<(p:ℚ)-1 := by exact sub_pos.mpr (by exact_mod_cast hp)
  have budget (k : ℕ) : F (S*p^k) ≤ (p:ℚ)^k*A := by
    induction k with
    | zero => simpa [early S le_rfl,A] using (div_nonneg (Nat.cast_nonneg Z.card) pp.le)
    | succ k ih =>
      rw [show S*p^(k+1)=p*S*p^k by rw [pow_succ]; ring,endpoints k (p*S) (Nat.le_mul_of_pos_left S (by omega)) le_rfl,mhi]
      have id : (p:ℚ)^k*A+(p:ℚ)^k*Z.card=(p:ℚ)^(k+1)*A := by dsimp [A]; rw [pow_succ]; field_simp [pp.ne']; ring
      exact (add_le_add_left ih _).trans_eq id
  change F N≤D*N
  by_cases small : N<S
  · rw [early N small.le]; positivity
  let k := Nat.log p (N/S)
  let q := p^k
  let u := N/q
  let t := N%q
  have qp : 0<q := pow_pos (by omega) _
  have ns := (Nat.le_div_iff_mul_le hs).mpr (by simpa using le_of_not_gt small : 1*S≤N)
  have left := (Nat.le_div_iff_mul_le hs).mp (Nat.pow_log_le_self p (by omega : N/S≠0))
  have hu : S≤u := (Nat.le_div_iff_mul_le qp).mpr (by simpa [q,k,mul_comm] using left)
  have up := (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_pow_succ_log_self hp (N/S))
  have hv : u<p*S := (Nat.div_lt_iff_lt_mul qp).mpr (by simpa [q,k,pow_succ,mul_assoc,mul_comm,mul_left_comm] using up)
  have cut : u*q+t=N := by simpa [u,t,mul_comm] using Nat.div_add_mod N q
  have lt := Nat.mod_lt N qp
  have eqn := chunk k u t hu hv lt.le
  rw [show u*p^k+t=N from cut,endpoints k u hu hv.le] at eqn
  have edge (v : ℕ) (lo : S≤v) (hi : v≤p*S) : A+mass Z v≤D*v :=
    (div_le_iff₀ (by exact_mod_cast hs.trans_le lo : (0:ℚ)<v)).mp (score_le_bound Z (mem_Icc.mpr ⟨lo,hi⟩))
  have start := budget k
  have right : (N:ℚ)=(u:ℚ)*q+t := by exact_mod_cast cut.symm
  rw [eqn,right,← Nat.cast_pow]; change F (S*q)+(q:ℚ)*mass Z u+_≤_
  rw [← Nat.cast_pow] at start; change F (S*q)≤(q:ℚ)*A at start
  by_cases bad : u∈Z
  · rw [ite_eq_left bad]; by_cases one : D≤1
    · have h := edge (u+1) (by omega) hv; rw [mass_step,ite_eq_left bad] at h; push_cast at h
      have hq := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q : (0:ℚ)≤q)
      have ht := mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr (by exact_mod_cast lt.le : (t:ℚ)≤q))
      nlinarith only [start,hq,ht]
    · have hq := mul_le_mul_of_nonneg_left (edge u hu hv.le) (Nat.cast_nonneg q : (0:ℚ)≤q)
      nlinarith only [start,hq,mul_nonneg (sub_nonneg.mpr (le_of_not_ge one)) (Nat.cast_nonneg t : (0:ℚ)≤t)]
  · rw [ite_eq_right bad]; have hq := mul_le_mul_of_nonneg_left (edge u hu hv.le) (Nat.cast_nonneg q : (0:ℚ)≤q)
    nlinarith only [start,hq,mul_nonneg dp (Nat.cast_nonneg t : (0:ℚ)≤t)]

end NormalityChecker.CellProfile
