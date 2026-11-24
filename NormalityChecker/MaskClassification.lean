module

public import NormalityChecker.MaskedDiscrepancy

/-! Off-base prime windows for arbitrary rational polynomials and smooth masks. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

theorem weights_supported (S : Finset ℕ) (keep : ℕ → Bool) (P : ℚ[X]) (t m : ℕ)
    (hm : m∉Nat.factoredNumbers S) : weights S keep P t m = 0 := by simp [weights,hm]

/-- Clearing coefficients commutes with every shifted, masked prefix. -/
theorem normalized_prefix {P : ℚ[X]} {G : ℤ[X]} {D : ℤ}
    (eval : ∀ m : ℕ, (sample G m : ℚ) = D*P.eval (m:ℚ))
    (b t n : ℕ) (S : Finset ℕ) (keep : ℕ → Bool) :
    (D:ℚ)*pre b (weights S keep P t) n = shiftedPrefix b t n G
      ((LocalizedSupport.indices S n).filter (fun m => keep m=true)) := by
  simp only [pre,mul_sum,shiftedPrefix,LocalizedSupport.indices,sum_filter]
  apply sum_congr rfl; intro m _
  by_cases sm : m ∈ Nat.factoredNumbers S <;> by_cases km : keep m=true <;>
    simp [weights, sm, km, eval, mul_div_assoc]; ring

theorem normalize (P : ℚ[X]) : ∃ (D : ℤ) (G : ℤ[X]), D≠0 ∧
    ∀ m : ℕ, (sample G m : ℚ) = D*P.eval (m:ℚ) := by
  let G := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P
  obtain ⟨D,hD,h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
  refine ⟨D,G,nonZeroDivisors.ne_zero hD,fun m => ?_⟩
  change G.map _=D • P at h
  have he := congrArg (Polynomial.eval (m:ℚ)) h
  rw [eval_smul, zsmul_eq_mul] at he
  convert he using 1
  exact (eval_map_apply (p:=G) (algebraMap ℤ ℚ) (m:ℤ)).symm

lemma cleared_term (z : ℚ) {u v : ℕ} (hv : v≠0) (div : z.den ∣ v*u) :
    ((u:ℚ)*z).den ∣ v := by
  obtain ⟨a,ha⟩ := div
  have cross : (v:ℚ)*u = z.den*a := by exact_mod_cast ha
  have eqn : (u:ℚ)*z = Rat.divInt ((a:ℤ)*z.num) v := by
    rw [Rat.divInt_eq_div]; push_cast
    rw [eq_div_iff (by exact_mod_cast hv)]
    linear_combination z*cross + (a:ℚ)*Rat.den_mul_eq_num z
  rw [eqn]; exact_mod_cast Rat.den_dvd ((a:ℤ)*z.num) v

/-- Growth of denominators polynomial in the block length for rational weights
whose reduced denominators divide a fixed multiple of mᵗ. -/
theorem clean_modulus {b c t L : ℕ} (hb : 0<b) (hc : 0<c) (hL : 0<L)
    {S : Finset ℕ} {a : ℕ → ℚ} (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (den : ∀ m ∈ Nat.factoredNumbers S, (a m).den ∣ L*m^t)
    (support : ∀ p∈S ∪ L.primeFactors, p∣b*c) :
    ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n →
      (∃ e : ℕ, (pre b a n).den ∣ c^e) ∧ (pre b a n).den ≤ (2^k)^(4*c*(t+1)) := by
  have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have clear := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul (4*((t:ℝ)+1))
  simp only [mul_zero,pow_one] at clear
  filter_upwards [eventually_ge_atTop 1,grow.eventually_ge_atTop L,clear.eventually_le_const zero_lt_one] with k hk hl enough n clean
  let J := 2*(k+1)
  have bound : n ≤ 2^J := by
    apply (Nat.le_add_right n (2^k)).trans (clean.bound.trans_eq _)
    dsimp [J]; rw [Nat.mul_add, Nat.mul_one,pow_add, Nat.mul_comm 2 k,pow_mul]; ring
  have jk : k ≤ J := by dsimp [J]; omega
  have dl := LocalizedSupport.cofactor_dvd (Nat.mul_pos hb hc) (S:=L.primeFactors)
    (fun p hp => support p (mem_union_right _ hp))
    (Nat.mem_factoredNumbers_of_primeFactors_subset hL.ne' Subset.rfl)
    (hl.trans (Nat.pow_le_pow_right (by decide) jk))
  let e := J*(t+1)
  have delay : e ≤ 2^k := by
    rw [← mul_div_assoc,div_le_iff₀ (by positivity),one_mul] at enough
    have h : 4*(t+1)*k ≤ 2^k := by exact_mod_cast enough
    dsimp [e,J]; nlinarith [Nat.mul_le_mul_right (t+1) hk]
  have div : (pre b a n).den ∣ c^e := by
    apply (Rat.den_sum_dvd_lcm_den ..).trans; apply Finset.lcm_dvd; intro m hm
    by_cases sm : m∈Nat.factoredNumbers S
    · have mn := mem_range_succ_iff.mp hm
      have dm := LocalizedSupport.cofactor_dvd (Nat.mul_pos hb hc) (fun p hp => support p (mem_union_left _ hp)) sm (mn.trans bound)
      have dx := (den m sm).trans (Nat.mul_dvd_mul dl (pow_dvd_pow_of_dvd dm t))
      have eqn : (b*c)^J*((b*c)^J)^t = c^e*b^e := by
        rw [← mul_pow, mul_comm c]; change _ = (b*c)^(J*(t+1)); rw [pow_mul (b*c) J, pow_succ' ((b*c)^J)]
      rw [eqn] at dx
      have past := clean.old m sm (by have : 0<2^k := pow_pos (by decide) _; omega)
      rw [← Nat.cast_pow]; apply cleared_term _ (pow_pos hc _).ne'
      exact dx.trans (Nat.mul_dvd_mul_left _ (pow_dvd_pow b (by omega)))
    · simp [supp m sm]
  refine ⟨⟨e,div⟩,(Nat.le_of_dvd (pow_pos hc _) div).trans ?_⟩
  calc c^e ≤ (2^c)^e := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
       _ ≤ (2^k)^(4*c*(t+1)) := by
         rw [← pow_mul,← pow_mul]; apply Nat.pow_le_pow_right (by decide)
         dsimp [e,J]; nlinarith [Nat.mul_le_mul_left (c*(t+1)) hk]

lemma coefficient_den {D : ℤ} (hd : D≠0) {P : ℚ[X]} {G : ℤ[X]}
    (eval : ∀ m : ℕ, (sample G m : ℚ) = D*P.eval (m:ℚ))
    (S : Finset ℕ) (keep : ℕ → Bool) (t m : ℕ) (hm : m∈Nat.factoredNumbers S) :
    (weights S keep P t m).den ∣ D.natAbs*m^t := by
  by_cases km : keep m=true
  · have eqn : weights S keep P t m = Rat.divInt (sample G m) (D*(m:ℤ)^t) := by
      rw [weights,ite_eq_left ⟨hm,km⟩,Rat.divInt_eq_div]; push_cast
      rw [eval m]; field_simp
    rw [eqn]
    simpa [Int.natAbs_mul,Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd (sample G m) (D*(m:ℤ)^t))
  · simp [weights,km]

/-- A finite collection of primes is absorbed by the radix and one coprime modulus. -/
theorem offbase_modulus {b p : ℕ} (A : Finset ℕ) (primes : ∀ r∈A,r.Prime)
    (hp : p.Prime) (mem : p∈A) (unit : ¬p∣b) :
    ∃ c : ℕ, 1<c ∧ b.Coprime c ∧ ∀ r∈A,r∣b*c := by
  let U := A.filter (fun r => ¬r∣b)
  let c := ∏ r∈U,r
  have dvd (r : ℕ) (hr : r∈U) : r∣c := dvd_prod_of_mem id hr
  have pos : 0<c := prod_pos (fun r hr => (primes r (mem_filter.mp hr).1).pos)
  have high := Nat.le_of_dvd pos (dvd p (mem_filter.mpr ⟨mem,unit⟩))
  refine ⟨c,hp.one_lt.trans_le high,Nat.Coprime.prod_right (fun r hr => ((primes r (mem_filter.mp hr).1).coprime_iff_not_dvd.mpr (mem_filter.mp hr).2).symm),?_⟩
  intro r hr; by_cases h : r∣b
  · exact h.trans (dvd_mul_right ..)
  · exact (dvd r (mem_filter.mpr ⟨hr,h⟩)).trans (dvd_mul_left ..)

def Window (p : ℕ) (keep : ℕ → Bool) (n : ℕ) : Prop :=
  ∃ k, keep (p^k)=true ∧ p^k ≤ n ∧ n < 2*p^k

/-- Upper discrepancy for any selected family of late first cells, for the
rationally weighted number itself. Other retained smooth indices are arbitrary. -/
theorem rational_window_bound {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (unit : ¬p∣b)
    (ht : 0<t) {P : ℚ[X]} (p0 : P.eval 0 ≠ 0) (S : Finset ℕ) (primes : ∀ r∈S,r.Prime)
    (mem : p∈S) (keep bad : ℕ → Bool)
    (window : ∀ᶠ n : ℕ in atTop, bad n=false → Window p keep n)
    {Dmax : ℝ} (cost : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      (∑ i∈range N, if bad i then (1:ℝ) else 0) ≤ (Dmax+ε)*N) :
    limsup (radixDiscrepancy b (maskedValue b S keep P t)) atTop ≤ Dmax := by
  obtain ⟨D,G,hD,eval⟩ := normalize P
  have g0 : sample G 0 ≠ 0 := by
    have h := eval 0; simp only [Nat.cast_zero] at h
    intro z; rw [z,Int.cast_zero] at h
    exact (mul_ne_zero (by exact_mod_cast hD : (D:ℚ)≠0) p0) h.symm
  obtain ⟨c,hc,cop,supp⟩ := offbase_modulus (S ∪ D.natAbs.primeFactors)
    (fun r h => (mem_union.mp h).elim (primes r) Nat.prime_of_mem_primeFactors)
    hp (mem_union_left _ mem) unit
  apply discrepancy_of_windows hb (fixed_support_orbit_estimate hb hc cop) (weights_growth ..)
    (weights_supported S keep P t) (clean_modulus (by omega) (by omega) (Int.natAbs_pos.mpr hD)
      (weights_supported S keep P t) (coefficient_den hD eval S keep t) supp) bad _ cost
  intro M
  let v := (sample G 0).natAbs.factorization p
  filter_upwards [window,eventually_ge_atTop (2*p^(M+v+1))] with n win late good
  obtain ⟨k,hit,lo,hi⟩ := win good
  have big : M+v+1 ≤ k := by
    by_contra! less
    have := Nat.pow_le_pow_right hp.pos less.le
    omega
  let A := (LocalizedSupport.indices S n).filter (fun m => keep m=true)
  have pm : p^k ∈ Nat.factoredNumbers S := Nat.mem_factoredNumbers_of_primeFactors_subset (pow_pos hp.pos _).ne' (by
    intro q hq; have h := (Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq)
    rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hp).mp h])
  have exactExp := first_cell_den_exponent (b:=b) hp unit ht G g0 A
    (mem_filter.mpr ⟨LocalizedSupport.mem_indices.mpr ⟨lo,pm⟩,hit⟩)
    (fun m hm => by obtain ⟨le,ms⟩ := LocalizedSupport.mem_indices.mp (mem_filter.mp hm).1; exact ⟨Nat.pos_of_ne_zero ms.1,le⟩)
    hi (show v<k by omega)
  let z := shiftedPrefix b t n G A
  have div := Nat.ordProj_dvd z.den p
  change p^z.den.factorization p ∣ z.den at div
  change z.den.factorization p = k*t-v at exactExp
  have lower : M≤z.den := (Nat.lt_pow_self hp.one_lt (n:=M)).le.trans
    ((Nat.pow_le_pow_right hp.pos (by rw [exactExp]; have := Nat.le_mul_of_pos_right k ht; omega)).trans (Nat.le_of_dvd z.pos div))
  have cross := Rat.mul_den_dvd (D:ℚ) (pre b (weights S keep P t) n)
  rw [normalized_prefix eval, Rat.den_intCast,one_mul] at cross
  exact lower.trans (Nat.le_of_dvd (Rat.pos _) cross)

end NormalityChecker.PolynomialMasks
