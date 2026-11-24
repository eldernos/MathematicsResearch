module

public import NormalityChecker.MaskAxis
public import NormalityChecker.DiscrepancyChecker

/-! Transfer of full-support unsigned cell certificates to arbitrary polynomial weights. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks
open LocalizedSupport

/-- The nonconstant part loses at least one full order of the pole, uniformly
over every mask at every position below p^(k+1). -/
theorem lower_order_norm {b p n k u : ℕ} (hp : p.Prime) (G : ℤ[X]) (A : Finset ℕ)
    (indices : ∀ m∈A, 0<m ∧ m<p^(k+1)) :
    padicNorm p (shiftedPrefix b (u+1) n G A - (sample G 0:ℚ)*shiftedPrefix b (u+1) n 1 A) ≤
      (p:ℚ)^(k*u) := by
  let : Fact p.Prime := ⟨hp⟩
  let f (m : ℕ) := (b:ℚ)^(n-m)*((sample G m:ℚ)-sample G 0)/(m:ℚ)^(u+1)
  have split : shiftedPrefix b (u+1) n G A - (sample G 0:ℚ)*shiftedPrefix b (u+1) n 1 A =
      ∑ m∈A,f m := by
    simp only [shiftedPrefix,mul_sum,←sum_sub_distrib]
    apply sum_congr rfl; intro m _; simp [f,sample]; ring
  rw [split]
  by_cases nonempty : A.Nonempty
  · have ultra : IsNonarchimedean (padicNorm p) := fun _ _ => padicNorm.nonarchimedean
    apply (ultra.apply_sum_le_sup nonempty).trans
    apply sup'_le
    intro m hm
    obtain ⟨pos,top⟩ := indices m hm
    obtain ⟨z,hz⟩ : (m:ℤ) ∣ sample G m-sample G 0 := by simpa [sample] using sub_dvd_eval_sub (m:ℤ) 0 G
    have eqn : f m=Rat.divInt ((b:ℤ)^(n-m)*z) ((m:ℤ)^u) := by
      have e : (sample G m:ℚ)-sample G 0=(m:ℚ)*z := by exact_mod_cast hz
      dsimp only [f]; rw [e,Rat.divInt_eq_div]; push_cast; rw [pow_succ]; field_simp [pos.ne']
    have div : (f m).den ∣ m^u := by rw [eqn]; exact_mod_cast Rat.den_dvd ((b:ℤ)^(n-m)*z) ((m:ℤ)^u)
    have exp := (Nat.factorization_le_iff_dvd (Rat.den_ne_zero _) (pow_pos pos u).ne').mpr div p
    have mk : m.factorization p ≤ k := by
      by_contra! h
      exact top.not_ge ((Nat.pow_le_pow_right hp.pos h).trans (Nat.ordProj_le p pos.ne'))
    have bound : (f m).den.factorization p ≤ k*u := by
      rw [Nat.factorization_pow, Finsupp.smul_apply,smul_eq_mul] at exp
      exact exp.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left u mk)
    exact (Localized.norm_le_prime_part hp _).trans (pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le) bound)
  · rw [not_nonempty_iff_eq_empty.mp nonempty]; simp

/-- If an unsigned prefix has e surviving factors of p and e exceeds the
lower-order budget plus vₚ(G(0)), the polynomial prefix retains at least e-vₚ(G(0)).
The conclusion is uniform over the retained subset. -/
theorem leading_denominator {b p n k u : ℕ} (hp : p.Prime) (G : ℤ[X]) (g0 : sample G 0≠0)
    (A : Finset ℕ) (indices : ∀ m∈A, 0<m ∧ m<p^(k+1))
    (large : k*u+(sample G 0).natAbs.factorization p < (shiftedPrefix b (u+1) n 1 A).den.factorization p) :
    (shiftedPrefix b (u+1) n 1 A).den.factorization p - (sample G 0).natAbs.factorization p ≤
      (shiftedPrefix b (u+1) n G A).den.factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  let x := shiftedPrefix b (u+1) n 1 A
  let y := shiftedPrefix b (u+1) n G A
  let z := (sample G 0:ℚ)*x
  let e := x.den.factorization p
  let v := (sample G 0).natAbs.factorization p
  change k*u+v<e at large
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have nz : x≠0 := by
    intro h
    have pos : 0<e := by omega
    simp [e,h] at pos
  have vg : padicValRat p z=(v:ℤ)-e := by
    dsimp [z]; rw [padicValRat.mul (by exact_mod_cast g0) nz,valuation_of_den_factor hp x (show 0<e by omega),
      padicValRat.of_int,padicValInt,←Nat.factorization_def _ hp]; rfl
  have norm : padicNorm p z=(p:ℚ)^(e-v) := by
    rw [padicNorm.eq_zpow_of_ne_zero (mul_ne_zero (by exact_mod_cast g0) nz),vg,neg_sub,
      ← Nat.cast_sub (show v≤e by omega),zpow_natCast]
  have err := lower_order_norm (b:=b) (n:=n) (u:=u) hp G A indices
  change padicNorm p (y-z) ≤ _ at err
  have smaller := err.trans_lt (pow_lt_pow_right₀ pp (show k*u<e-v by omega))
  rw [←norm] at smaller
  have full : padicNorm p y=(p:ℚ)^(e-v) := by
    calc _ = padicNorm p (z+(y-z)) := by congr 1; ring
         _ = padicNorm p z := by rw [padicNorm.add_eq_max_of_ne smaller.ne',max_eq_left smaller.le]
         _ = _ := norm
  exact (pow_right_strictMono₀ pp).le_iff_le.mp (full.symm.trans_le (Localized.norm_le_prime_part hp y))

private theorem unsigned_eq {b t n : ℕ} (hb : 0<b) (S : Finset ℕ) :
    shiftedPrefix b t n 1 (indices S n) = powerShifted b t S n := by
  unfold shiftedPrefix powerShifted powerPartial; rw [mul_sum]
  apply sum_congr rfl; intro m hm
  have le := (mem_indices.mp hm).1
  simp [sample,powerWeight,pow_sub₀ _ (by exact_mod_cast hb.ne' : (b:ℚ)≠0) le]; ring

/-- Each executable unsigned certificate at the residual pole order also bounds the
discrepancy of the full rational polynomial series at that same precision. -/
theorem polynomial_certificate_bound {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b)
    (ht : 0<t) (P : ℚ[X]) (p0 : P.eval 0≠0) (S : Finset ℕ) (primes : ∀ q∈S,q.Prime)
    (outside : p∉S) (ell : ℕ) :
    limsup (radixDiscrepancy b (maskedValue b (insert p S) (fun _ => true) P t)) atTop ≤
      (discrepancyCertificate b t p ell S:ℝ) := by
  obtain ⟨D,G,hD,eval⟩ := normalize P
  have g0 : sample G 0 ≠ 0 := by
    have h := eval 0; simp only [Nat.cast_zero] at h
    intro z; rw [z,Int.cast_zero] at h
    exact (mul_ne_zero (by exact_mod_cast hD : (D:ℚ)≠0) p0) h.symm
  let A := insert p S
  have primeA (q : ℕ) (hq : q∈A) : q.Prime := by rcases mem_insert.mp hq with rfl|h; exacts [hp,primes q h]
  obtain ⟨c,hc,cop,supp⟩ := offbase_modulus (A∪D.natAbs.primeFactors)
    (fun q h => (mem_union.mp h).elim (primeA q) Nat.prime_of_mem_primeFactors)
    hp (mem_union_left _ (mem_insert_self ..)) off
  let Z := failedCells b t p ell S
  let U := CellProfile.coordinate p (p^ell)
  let a := weights A (fun _ => true) P t
  apply discrepancy_of_windows hb (fixed_support_orbit_estimate hb hc cop) (weights_growth ..)
    (weights_supported A _ P t) (clean_modulus (by omega) (by omega) (Int.natAbs_pos.mpr hD)
      (weights_supported A _ P t) (coefficient_den hD eval A _ t) supp) (fun n => decide (U n∈Z))
  · obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    let v := (sample G 0).natAbs.factorization p
    intro M
    let K := 2*ell+v+M+1
    filter_upwards [eventually_ge_atTop (p^K)] with n late pass
    let k := Nat.log p n
    have hk : K≤k := Nat.le_log_of_pow_le hp.one_lt late
    have pos := (pow_pos hp.pos K).trans_le late
    have lo := Nat.pow_log_le_self p pos.ne'
    have hi := Nat.lt_pow_succ_log_self hp.one_lt n
    have coord : U n=n/p^(k-ell) := by simp [U,CellProfile.coordinate,Nat.log_div_base_pow,k]
    have ke : ell≤k := by dsimp [K] at hk; omega
    have split : p^ell*p^(k-ell)=p^k := by rw [← pow_add]; congr 1; omega
    have inside : U n∈Ico (p^ell) (p*p^ell) := by
      rw [coord,mem_Ico,Nat.le_div_iff_mul_le (pow_pos hp.pos _),Nat.div_lt_iff_lt_mul (pow_pos hp.pos _),mul_assoc,split,← pow_succ']; exact ⟨lo,hi⟩
    have nz : powerCellResidue (u+1) p ell S (inverseLift b p ell ell) (U n)≠0 :=
      fun h => (of_decide_eq_false pass) (mem_filter.mpr ⟨inside,h⟩)
    rw [coord] at nz
    have unit := (hp.coprime_iff_not_dvd.mpr off).symm
    have div := cell_power_denominator (Nat.succ_pos u) hp outside unit (k:=k) (by dsimp [K] at hk; omega : ell+ell≤k)
      hi (canonical_lift_fixed hp unit ell) nz
    let z := shiftedPrefix b (u+1) n 1 (indices A n)
    have ex : k*(u+1)-ell≤z.den.factorization p :=
      (hp.pow_dvd_iff_le_factorization (Rat.den_ne_zero _)).mp (by simpa [z,unsigned_eq (by omega : 0<b),A] using div)
    have hK : 2*ell+v+M+1≤k := hk
    rw [Nat.mul_succ] at ex
    have main := leading_denominator (b:=b) (k:=k) (u:=u) hp G g0 (indices A n)
      (fun m hm => ⟨Nat.pos_of_ne_zero (mem_indices.mp hm).2.1,(mem_indices.mp hm).1.trans_lt hi⟩)
      (show k*u+v<z.den.factorization p by omega)
    change z.den.factorization p-v ≤ _ at main
    have enough : M≤(shiftedPrefix b (u+1) n G (indices A n)).den.factorization p := by omega
    have eqn := normalized_prefix eval b (u+1) n A (fun _ => true)
    simp only [Finset.filter_const,ite_true] at eqn
    have dvd := Rat.mul_den_dvd (D:ℚ) (pre b a n)
    change ((D:ℚ)*pre b (weights A (fun _ => true) P (u+1)) n).den ∣ _ at dvd
    rw [eqn,Rat.den_intCast,one_mul] at dvd
    exact (Nat.lt_pow_self hp.one_lt (n:=M)).le.trans ((Nat.pow_le_pow_right hp.pos enough).trans
      (Nat.le_of_dvd (Rat.pos _) ((Nat.ordProj_dvd _ _).trans dvd)))
  · intro ε pos; filter_upwards with N
    have H := (Rat.cast_le (K:=ℝ)).mpr (CellProfile.count_bound hp.one_lt (pow_pos hp.pos ell) Z (filter_subset ..) N)
    change _ ≤ ((CellProfile.bound p (p^ell) Z:ℝ)+ε)*N
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right pos.le) (Nat.cast_nonneg N))
    simpa [U,apply_ite] using H

/-- Vanishing unsigned certificates imply normality for every rational polynomial
with the same residual pole order on the full smooth support. -/
theorem normal_of_unsigned_certificates {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b)
    (ht : 0<t) (P : ℚ[X]) (p0 : P.eval 0≠0) (S : Finset ℕ) (primes : ∀ q∈S,q.Prime)
    (outside : p∉S) (vanish : ∀ ε : ℝ, 0<ε → ∃ ell, (discrepancyCertificate b t p ell S:ℝ) ≤ ε) :
    NormalIn b (maskedValue b (insert p S) (fun _ => true) P t) := by
  apply normal_of_radix_limsup_zero hb; apply le_of_forall_pos_le_add; intro ε pos
  obtain ⟨ell,small⟩ := vanish ε pos
  simpa only [zero_add] using (polynomial_certificate_bound hb hp off ht P p0 S primes outside ell).trans small

end NormalityChecker.PolynomialMasks
