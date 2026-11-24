module

public import NormalityChecker.MaskDensity

/-! Exact density on geometric periods and finite certificates for periodic masks. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks
open CellProfile

def periodCount (p S : ℕ) (Z : Finset ℕ) (N : ℕ) : ℚ :=
  ∑ i∈range N, if coordinate p S i∈Z then 1 else 0

/-- Closed count at every cell boundary. Its bounded offset from the periodic
limiting score is independent of the scale k. -/
theorem period_endpoint {p S : ℕ} (hp : 1<p) (hs : 0<S) (Z : Finset ℕ) (hz : Z⊆Ico S (p*S))
    (k v : ℕ) (hv : v∈Icc S (p*S)) :
    periodCount p S Z (v*p^k) = ((p:ℚ)^k-1)*(Z.card/(p-1):ℚ)+(p:ℚ)^k*mass Z v := by
  let F := periodCount p S Z
  have stepMass (u : ℕ) : mass Z (u+1)=mass Z u+(if u∈Z then 1 else 0) := by
    classical
    by_cases h : u∈Z
    · have eqn : Z.filter (·<u+1)=insert u (Z.filter (·<u)) := by ext i; simp; grind
      unfold mass; rw [eqn]; simp [h]
    · have eqn : Z.filter (·<u+1)=Z.filter (·<u) := by ext i; simp; grind
      unfold mass; rw [eqn]; simp [h]
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
    dsimp [F,periodCount]; rw [sum_range_add]; congr 1
    have coord (i : ℕ) (h : i∈range T) := coordinate_eq hp hs lo hi (Nat.le_add_right (u*p^k) i)
      (by rw [Nat.succ_mul]; have := mem_range.mp h; omega : u*p^k+i<(u+1)*p^k)
    have eqn := sum_congr (s₁:=range T) (f:=fun i => if coordinate p S (u*p^k+i)∈Z then (1:ℚ) else 0) (g:=fun _ => if u∈Z then (1:ℚ) else 0) rfl (fun i h => by rw [coord i h])
    rw [eqn]; split_ifs <;> simp
  have endpoints (k u : ℕ) (lo : S≤u) (hi : u≤p*S) :
      F (u*p^k)=F (S*p^k)+(p:ℚ)^k*mass Z u := by
    induction u,lo using Nat.le_induction with
    | base => simp [mlo]
    | succ u hu ih => rw [Nat.succ_mul,chunk k u (p^k) hu (by omega) le_rfl,ih (by omega),stepMass]; split_ifs <;> push_cast <;> ring

  let A := (Z.card:ℚ)/(p-1)
  have pp : 0<(p:ℚ)-1 := sub_pos.mpr (by exact_mod_cast hp)
  have main (k : ℕ) : F (S*p^k) = ((p:ℚ)^k-1)*A := by
    induction k with
    | zero => simp [early S le_rfl]
    | succ k ih =>
      rw [show S*p^(k+1)=p*S*p^k by rw [pow_succ]; ring,
        endpoints k (p*S) (Nat.le_mul_of_pos_left S (by omega)) le_rfl, mhi,ih,pow_succ]
      dsimp [A]; field_simp [pp.ne']; ring
  exact (endpoints k v (mem_Icc.mp hv).1 (mem_Icc.mp hv).2).trans (by rw [main])

/-- The finite cell score is sharp for the window price, including cutoffs partway
through a geometric scale. This describes the price, independently of orbit quality. -/
theorem exact_period_price {p S : ℕ} (hp : 1<p) (hs : 0<S) (Z : Finset ℕ) (hz : Z⊆Ico S (p*S)) :
    limsup (fun N : ℕ => (periodCount p S Z N:ℝ)/N) atTop = (bound p S Z : ℝ) := by
  let F (N : ℕ) := (periodCount p S Z N:ℝ)/N
  have nn (n : ℕ) : 0≤F n := by unfold F periodCount; push_cast; positivity
  have upper (n : ℕ) : F n ≤ bound p S Z := by
    by_cases eqn : n=0
    · simpa [F,eqn] using (Rat.cast_le (K:=ℝ)).mpr (bound_nonneg p S Z)
    apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero eqn : (0:ℝ)<n)).mpr
    have h : periodCount p S Z n ≤ bound p S Z*n := count_bound hp hs Z hz n
    exact_mod_cast h
  have ub := limsup_le_of_le (f:=atTop) (isCoboundedUnder_le_of_le _ nn) (.of_forall upper)
  refine le_antisymm ub ?_
  let vals := insert 0 ((Icc S (p*S)).image (score p Z))
  have win : bound p S Z ∈ vals := max'_mem .. 
  rcases mem_insert.mp win with eqn|mem
  · rw [eqn,Rat.cast_zero]; exact le_limsup_of_le (isBoundedUnder_of_eventually_le (.of_forall upper))
      (fun z hz => by obtain ⟨n,h⟩ := hz.exists; exact (nn n).trans h)
  obtain ⟨v,hv,best⟩ := mem_image.mp mem
  have vp := hs.trans_le (mem_Icc.mp hv).1
  let A := (Z.card:ℝ)/((p:ℝ)-1)
  have pe : (1:ℝ)<p := by exact_mod_cast hp
  have vel : (0:ℝ)<v := by exact_mod_cast vp
  have grow : Tendsto (fun k : ℕ => p^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hp
  have seq : Tendsto (fun k : ℕ => v*p^k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left _ vp) grow
  have small := (tendsto_const_div_atTop_nhds_zero_nat A).comp grow
  have limit := (tendsto_const_nhds (x:=A+(mass Z v:ℝ)) |>.sub small).div_const (v:ℝ)
  simp only [sub_zero] at limit
  have exactLimit : Tendsto (F ∘ (fun k : ℕ => v*p^k)) atTop (𝓝 ((score p Z v:ℚ):ℝ)) := by
    unfold score; push_cast
    apply limit.congr; intro k
    change (_ - A/((p^k:ℕ):ℝ))/v = (periodCount p S Z (v*p^k):ℝ)/(v*p^k:ℕ)
    rw [period_endpoint hp hs Z hz k v hv]; push_cast; dsimp [A]
    field_simp [vel.ne', (zero_lt_one.trans pe).ne']; ring
  rw [← best, ← exactLimit.limsup_eq]
  exact seq.limsup_comp_le_limsup (isCoboundedUnder_le_of_le _ nn) (isBoundedUnder_of_eventually_le (.of_forall upper))

/-- Failing integer cells of a geometric period pʰ. E lists retained exponent residues. -/
def periodMiss (p h : ℕ) (E : Finset ℕ) :=
  (Ico 1 (p^h)).filter (fun v => ¬∃ j∈E, p^j≤v ∧ v<2*p^j)

theorem periodic_discrepancy {b p t h : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b) (ht : 0<t)
    (hh : 0<h) (P : ℚ[X]) (p0 : P.eval 0≠0) (S : Finset ℕ) (primes : ∀ q∈S,q.Prime) (mem : p∈S)
    (keep : ℕ → Bool) (E : Finset ℕ)
    (kept : ∀ᶠ k : ℕ in atTop, ∀ j∈E, keep (p^(h*k+j))=true) :
    limsup (radixDiscrepancy b (maskedValue b S keep P t)) atTop ≤ (bound (p^h) 1 (periodMiss p h E):ℝ) := by
  let R := p^h
  let Z := periodMiss p h E
  have rp : 1<R := one_lt_pow₀ hp.one_lt hh.ne'
  have cover : Z⊆Ico 1 (R*1) := by simp [Z,periodMiss,R]
  apply rational_window_bound hb hp off ht p0 S primes mem keep (fun n => decide (coordinate R 1 n∈Z))
  · obtain ⟨K,late⟩ := eventually_atTop.mp kept
    filter_upwards [eventually_ge_atTop (R^K)] with n high passed
    let k := Nat.log R n
    let q := R^k
    let v := n/q
    have pos := (pow_pos (by omega : 0<R) K).trans_le high
    have qp : 0<q := pow_pos (by omega) _
    have coord : coordinate R 1 n=v := by simp [coordinate,v,q,k]
    have lo : 1≤v := (Nat.le_div_iff_mul_le qp).mpr (by simpa [q,k] using Nat.pow_log_le_self R pos.ne')
    have hi : v<R := (Nat.div_lt_iff_lt_mul qp).mpr (by simpa [q,k,pow_succ'] using Nat.lt_pow_succ_log_self rp n)
    have bad : v∉Z := by simpa [coord] using passed
    have wins : ∃ j∈E, p^j≤v ∧ v<2*p^j := by simpa [Z,periodMiss,lo,show v<p^h from hi] using bad
    obtain ⟨j,hj,low,top⟩ := wins
    refine ⟨h*k+j,late k (Nat.le_log_of_pow_le rp high) j hj,?_,?_⟩
    · simpa [q,R,pow_add,pow_mul,mul_comm] using (Nat.le_div_iff_mul_le qp).mp low
    · simpa [q,R,pow_add,pow_mul,mul_left_comm,mul_assoc,mul_comm] using (Nat.div_lt_iff_lt_mul qp).mp top
  · intro ε pos; filter_upwards with N
    have H := (Rat.cast_le (K:=ℝ)).mpr (count_bound rp (by decide : 0<1) Z cover N)
    push_cast at H
    simp only [decide_eq_true_eq]
    exact (by simpa [apply_ite] using H : (∑ i∈range N, if coordinate R 1 i∈Z then (1:ℝ) else 0) ≤ (bound R 1 Z:ℝ)*N).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right pos.le) (Nat.cast_nonneg _))

/-- Retaining exponents 0 and 1 modulo 3 at p=3 certifies exact window price
11/13 and therefore a discrepancy upper bound of 11/13. -/
theorem ternary_period_price : bound (3^3) 1 (periodMiss 3 3 {0,1})=11/13 := by decide +kernel

/-- Index-periodic masks induce an eventual period on the power exponents even
when the index modulus has a common factor with p. -/
theorem index_mask_eventual_period (p d : ℕ) (hd : 0<d) (keep : Fin d → Bool) :
    ∃ K h : ℕ, 0<h ∧ ∀ k≥K, keep ⟨p^(k+h)%d,Nat.mod_lt _ hd⟩ = keep ⟨p^k%d,Nat.mod_lt _ hd⟩ := by
  let f (k : ℕ) : Fin d := ⟨p^k%d,Nat.mod_lt _ hd⟩
  obtain ⟨i,j,lt,eqn⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f:=f) (fun _ => Set.mem_univ _)
  have ij : p^i ≡ p^j [MOD d] := congrArg Fin.val eqn
  refine ⟨i,j-i,by omega,fun k hk => ?_⟩
  apply congrArg keep; apply Fin.ext
  have H := (ij.mul_right (p^(k-i))).symm
  change p^(k+(j-i)) ≡ p^k [MOD d]
  simpa only [← pow_add,show j+(k-i)=k+(j-i) by omega,show i+(k-i)=k by omega] using H

end NormalityChecker.PolynomialMasks
