module

public import NormalityChecker.MaskRational

/-! Nonmonomial polynomial denominators on masks with controlled prime support. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

/-- A finite polynomial reciprocal on any finite list of integer units at p.
The product polynomial vanishes at each sampled denominator. Its divided difference
at zero represents their reciprocals with one common denominator prime to p. -/
theorem finite_reciprocal {p : ℕ} (hp : p.Prime) (Q : ℤ[X]) (A : Finset ℕ)
    (unit : ∀ m∈A, ¬(p:ℤ)∣sample Q m) {k : ℕ} (positive : 0<k) (hit : p^k∈A) :
    ∃ (D : ℤ) (H : ℤ[X]), ¬(p:ℤ)∣D ∧ ¬(p:ℤ)∣sample H 0 ∧
      ∀ m∈A, sample H m * sample Q m = D := by
  let D := ∏ m∈A, sample Q m
  let F : ℤ[X] := ∏ m∈A, (C (sample Q m)-X)
  have pprime := Nat.prime_iff_prime_int.mp hp
  have dunit : ¬(p:ℤ)∣D := by
    intro dv; obtain ⟨m,hm,h⟩ := (pprime.dvd_finsetProd_iff _).mp dv
    exact unit m hm h
  have atZero : (C D-F).eval 0 = 0 := by simp [F,D,eval_prod]
  obtain ⟨U,defU⟩ := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero _).trans atZero)
  have val (m : ℕ) (hm : m∈A) : sample (U.comp Q) m * sample Q m = D := by
    have eqn := congrArg (eval (sample Q m)) defU
    have vanish : F.eval (sample Q m)=0 := by
      simp only [F,eval_prod,eval_sub,eval_C,eval_X]
      exact prod_eq_zero hm (sub_self _)
    simp only [eval_sub,eval_C,vanish,sub_zero,eval_mul,eval_X] at eqn
    simpa [sample,eval_comp,mul_comm] using eqn.symm
  refine ⟨D,U.comp Q,dunit,?_,val⟩
  intro divides
  have err : (p:ℤ) ∣ sample (U.comp Q) (p^k)-sample (U.comp Q) 0 :=
    (by exact_mod_cast dvd_pow_self p positive.ne' : (p:ℤ)∣(p^k:ℕ)).trans
      (by simpa [sample] using sub_dvd_eval_sub ((p^k:ℕ):ℤ) 0 (U.comp Q))
  have top := (dvd_sub_left divides).mp err
  exact dunit ((val _ hit) ▸ dvd_mul_of_dvd_left top (sample Q (p^k)))

/-- At a retained first cell, replacing the polynomial by P/Q preserves its exact
denominator exponent whenever all sampled Q values are p-adic units. -/
theorem quotient_first_cell {b p t n k : ℕ} (hp : p.Prime) (off : ¬p∣b) (ht : 0<t)
    (P Q : ℤ[X]) (p0 : sample P 0≠0) (A : Finset ℕ) (hit : p^k∈A)
    (indices : ∀ m∈A, 0<m ∧ m≤n) (cell : n<2*p^k)
    (unit : ∀ m∈A, ¬(p:ℤ)∣sample Q m) (late : (sample P 0).natAbs.factorization p < k) :
    (∑ m∈A, (b:ℚ)^(n-m)*(sample P m:ℚ)/(sample Q m:ℚ)/(m:ℚ)^t).den.factorization p =
      k*t-(sample P 0).natAbs.factorization p := by
  obtain ⟨D,H,du,hu,eval⟩ := finite_reciprocal hp Q A unit (by omega : 0<k) hit
  have dn : D≠0 := fun h => du (h ▸ dvd_zero _)
  have hn : sample H 0≠0 := fun h => hu (h ▸ dvd_zero _)
  have vH : (sample H 0).natAbs.factorization p=0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => hu (Int.natCast_dvd.mpr h))
  have vD : D.natAbs.factorization p=0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => du (Int.natCast_dvd.mpr h))
  have hval : (sample (P*H) 0).natAbs.factorization p = (sample P 0).natAbs.factorization p := by
    rw [show sample (P*H) 0=sample P 0*sample H 0 from eval_mul,Int.natAbs_mul,
      Nat.factorization_mul (Int.natAbs_ne_zero.mpr p0) (Int.natAbs_ne_zero.mpr hn),Finsupp.add_apply,vH,add_zero]
  let y := ∑ m∈A, (b:ℚ)^(n-m)*(sample P m:ℚ)/(sample Q m:ℚ)/(m:ℚ)^t
  have cross : (D:ℚ)*y=shiftedPrefix b t n (P*H) A := by
    dsimp [y,shiftedPrefix]; rw [mul_sum]; apply sum_congr rfl; intro m hm
    have ne : (sample Q m : ℚ) ≠ 0 := by
      exact_mod_cast (show sample Q m≠0 from fun h => unit m hm (h ▸ dvd_zero _))
    have he : (D:ℚ)=(sample H m:ℚ)*sample Q m := by exact_mod_cast (eval m hm).symm
    rw [he]; simp only [sample,eval_mul,Int.cast_mul] at *; field_simp
  have exactExp := first_cell_den_exponent hp off ht (P*H) (by simpa [sample] using mul_ne_zero p0 hn)
    A hit indices cell (hval ▸ late)
  rw [hval,←cross] at exactExp
  have big : 0<((D:ℚ)*y).den.factorization p := by rw [exactExp]; have := Nat.le_mul_of_pos_right k ht; omega
  rw [rational_den_exponent hp dn y big,exactExp,vD,Nat.add_zero]

def quotientWeights (S : Finset ℕ) (keep : ℕ → Bool) (P Q : ℤ[X]) (t m : ℕ) : ℚ :=
  if m∈Nat.factoredNumbers S ∧ keep m=true then (sample P m:ℚ)/(sample Q m:ℚ)/(m:ℚ)^t else 0

private theorem growth_quotient (S : Finset ℕ) (keep : ℕ → Bool) (P Q : ℤ[X]) (t : ℕ)
    (regular : ∀ m∈Nat.factoredNumbers S, keep m=true → sample Q m≠0) :
    PolyGrowth (quotientWeights S keep P Q t) := by
  let R := P.map (algebraMap ℤ ℚ)
  obtain ⟨C,hC,d,bound⟩ := weights_growth S keep R t
  refine ⟨C,hC,d,fun m => le_trans ?_ (bound m)⟩
  by_cases sm : m∈Nat.factoredNumbers S <;> by_cases km : keep m=true <;>
    simp only [quotientWeights,weights,sm,km,and_self,ite_true,false_and,ite_false] <;> try rfl
  have ev : R.eval (m:ℚ)=(sample P m:ℚ) := eval_map_apply (p:=P) (algebraMap ℤ ℚ) (m:ℤ)
  rw [ev]; push_cast; simp only [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  apply div_le_self (abs_nonneg _)
  have one := Int.natAbs_pos.mpr (regular m sm km)
  rw [← Int.cast_abs,← Int.natCast_natAbs]; exact_mod_cast one


/-- Polynomial values on the mask have bit length linear in the bit length of m. -/
private theorem eval_height (Q : ℤ[X]) (S : Finset ℕ) (keep : ℕ → Bool) :
    ∃ d : ℕ, ∀ J m : ℕ, m≤2^J → m∈Nat.factoredNumbers S → keep m=true →
      (sample Q m).natAbs ≤ 2^(d*(J+1)) := by
  let R := Q.map (algebraMap ℤ ℚ)
  obtain ⟨C,hC,d,bd⟩ := weights_growth S keep R 0
  obtain ⟨L,hL⟩ := exists_nat_ge C
  refine ⟨L+d,fun J m cap sm km => ?_⟩
  have ev : R.eval (m:ℚ) = (sample Q m:ℚ) := eval_map_apply (p:=Q) (algebraMap ℤ ℚ) (m:ℤ)
  have h := bd m
  simp only [weights,sm,km,and_self,ite_true,pow_zero,div_one,ev,Rat.cast_intCast] at h
  have l : C≤(2:ℝ)^L := hL.trans (by exact_mod_cast (Nat.lt_two_pow_self (n:=L)).le)
  have mcap : (m:ℝ)+1 ≤ 2^(J+1) := by
    exact_mod_cast (by rw [pow_succ]; have := pow_pos (by decide : 0<2) J; omega : m+1≤2^(J+1))
  have er : (sample Q m).natAbs ≤ 2^L*(2^(J+1))^d := by
    have h' := h.trans (mul_le_mul l (pow_le_pow_left₀ (by positivity) mcap d) (by positivity) (by positivity))
    rw [← Int.cast_abs,← Int.natCast_natAbs] at h'
    exact_mod_cast h'
  apply er.trans
  rw [← pow_mul,← pow_add]; apply Nat.pow_le_pow_right (by decide); nlinarith

/-- Clean moduli for arbitrary rational samples whose denominators clear with a
linear bit budget. The denominator may involve factors unrelated to the index. -/
theorem sample_modulus {b c d : ℕ} (hc : 0<c) {S : Finset ℕ} {a : ℕ → ℚ}
    (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (den : ∀ J m : ℕ, m≤2^J → m∈Nat.factoredNumbers S → (a m).den ∣ (b*c)^(d*(J+1))) :
    ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n →
      (∃ e : ℕ, (pre b a n).den ∣ c^e) ∧ (pre b a n).den ≤ (2^k)^(5*c*d) := by
  have clear := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul (5*(d:ℝ))
  simp only [pow_one,mul_zero] at clear
  filter_upwards [eventually_ge_atTop 1,clear.eventually_le_const zero_lt_one] with k hk budget n hn
  let J := 2*(k+1)
  let e := d*(J+1)
  have bound : n ≤ 2^J := by
    apply (Nat.le_add_right n (2^k)).trans (hn.bound.trans_eq _)
    dsimp [J]; rw [Nat.mul_add,Nat.mul_one,pow_add,Nat.mul_comm 2 k,pow_mul]; ring
  rw [← mul_div_assoc,div_le_iff₀ (by positivity),one_mul] at budget
  have enough : 5*d*k ≤ 2^k := by exact_mod_cast budget
  have delay : e ≤ 2^k := by
    dsimp [e,J]; nlinarith [Nat.mul_le_mul_left d hk]
  have clearDen : (pre b a n).den ∣ c^e := by
    apply (Rat.den_sum_dvd_lcm_den ..).trans; apply Finset.lcm_dvd; intro m hm
    have mn := mem_range_succ_iff.mp hm
    by_cases sm : m∈Nat.factoredNumbers S
    · have past := hn.old m sm (by have := pow_pos (by decide : 0<2) k; omega)
      have div := den J m (mn.trans bound) sm
      change _ ∣ (b*c)^e at div; rw [mul_comm b,mul_pow] at div
      rw [← Nat.cast_pow]; apply cleared_term _ (pow_pos hc _).ne'
      exact div.trans (Nat.mul_dvd_mul_left _ (pow_dvd_pow _ (by omega)))
    · simp [supp m sm]
  refine ⟨⟨e,clearDen⟩,(Nat.le_of_dvd (pow_pos hc _) clearDen).trans ?_⟩
  calc c^e ≤ (2^c)^e := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
       _ ≤ (2^k)^(5*c*d) := by
         rw [← pow_mul,← pow_mul]; apply Nat.pow_le_pow_right (by decide)
         dsimp [e,J]; nlinarith [Nat.mul_le_mul_left (c*d) hk]

/-- For nonmonomial Q, a fixed prime support for its retained values and p-adic
unit values at the selected prime suffice for the same window bound. -/
theorem quotient_window_bound {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b) (ht : 0<t)
    (P Q : ℤ[X]) (p0 : sample P 0≠0) (S T : Finset ℕ) (primes : ∀ q∈S∪T,q.Prime)
    (pmem : p∈S) (keep bad : ℕ → Bool)
    (denSupport : ∀ m∈Nat.factoredNumbers S, keep m=true → (sample Q m).natAbs ∈ Nat.factoredNumbers T)
    (unit : ∀ m∈Nat.factoredNumbers S, keep m=true → ¬(p:ℤ)∣sample Q m)
    (windows : ∀ᶠ n : ℕ in atTop, bad n=false → Window p keep n)
    {D : ℝ} (cost : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      (∑ i∈range N, if bad i then (1:ℝ) else 0) ≤ (D+ε)*N) :
    limsup (radixDiscrepancy b (series b (quotientWeights S keep P Q t))) atTop ≤ D := by
  let a := quotientWeights S keep P Q t
  obtain ⟨c,hc,cop,rad⟩ := offbase_modulus (S∪T) primes hp (mem_union_left _ pmem) off
  have supp (m : ℕ) (hm : m∉Nat.factoredNumbers S) : a m=0 := by simp [a,quotientWeights,hm]
  have reg (m : ℕ) (sm : m∈Nat.factoredNumbers S) (km : keep m=true) : sample Q m≠0 := fun h =>
    (unit m sm km) (h ▸ dvd_zero _)
  obtain ⟨d,height⟩ := eval_height Q S keep
  have positive : 0<b*c := Nat.mul_pos (by omega) (by omega)
  have den (J m : ℕ) (cap : m≤2^J) (sm : m∈Nat.factoredNumbers S) : (a m).den ∣ (b*c)^((d+t)*(J+1)) := by
    by_cases km : keep m=true
    · have divQ := LocalizedSupport.cofactor_dvd positive (fun q hq => rad q (mem_union_right _ hq))
        (denSupport m sm km) (height J m cap sm km)
      have divM := LocalizedSupport.cofactor_dvd positive (fun q hq => rad q (mem_union_left _ hq)) sm cap
      have eqn : a m=Rat.divInt (sample P m) (sample Q m*(m:ℤ)^t) := by
        simp [a,quotientWeights,sm,km,Rat.divInt_eq_div,div_div]
      have denQ := Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd (sample P m) (sample Q m*(m:ℤ)^t))
      simp only [Int.natAbs_natCast,Int.natAbs_mul,Int.natAbs_pow,← eqn] at denQ
      apply (denQ.trans (Nat.mul_dvd_mul divQ (pow_dvd_pow_of_dvd divM t))).trans
      rw [← pow_mul,← pow_add]; apply pow_dvd_pow; nlinarith
    · simp [a,quotientWeights,km]
  apply discrepancy_of_windows hb (fixed_support_orbit_estimate hb hc cop) (growth_quotient S keep P Q t reg)
    supp (sample_modulus (by omega) supp den) bad _ cost
  let v := (sample P 0).natAbs.factorization p
  intro M
  filter_upwards [windows,eventually_ge_atTop (2*p^(M+v+1))] with n win large valid
  obtain ⟨k,hit,lo,hi⟩ := win valid
  have big : M+v+1 ≤ k := by by_contra! less; have := Nat.pow_le_pow_right hp.pos less.le; omega
  let A := (LocalizedSupport.indices S n).filter (fun m => keep m=true)
  have ps : p^k∈Nat.factoredNumbers S := Nat.mem_factoredNumbers_of_primeFactors_subset (pow_pos hp.pos _).ne' (by
    intro q hq; have h := (Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq)
    rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hp).mp h])
  have eqn : pre b a n = ∑ m∈A, (b:ℚ)^(n-m)*(sample P m:ℚ)/(sample Q m:ℚ)/(m:ℚ)^t := by
    simp only [pre,A,LocalizedSupport.indices,sum_filter]
    apply sum_congr rfl; intro m _
    by_cases sm : m∈Nat.factoredNumbers S <;> by_cases km : keep m=true <;> simp [a,quotientWeights,sm,km,mul_div_assoc]
  have exp := quotient_first_cell (b:=b) hp off ht P Q p0 A (mem_filter.mpr ⟨LocalizedSupport.mem_indices.mpr ⟨lo,ps⟩,hit⟩)
    (fun m hm => by obtain ⟨le,ms⟩ := LocalizedSupport.mem_indices.mp (mem_filter.mp hm).1; exact ⟨Nat.pos_of_ne_zero ms.1,le⟩)
    hi (fun m hm => unit m (LocalizedSupport.mem_indices.mp (mem_filter.mp hm).1).2 (mem_filter.mp hm).2) (show v<k by omega)
  rw [← eqn] at exp
  have enough : M≤(pre b a n).den.factorization p := by rw [exp]; change M≤k*t-v; have := Nat.le_mul_of_pos_right k ht; omega
  exact (Nat.lt_pow_self hp.one_lt (n:=M)).le.trans ((Nat.pow_le_pow_right hp.pos enough).trans
    (Nat.le_of_dvd (Rat.pos _) (Nat.ordProj_dvd _ _)))

end NormalityChecker.PolynomialMasks
