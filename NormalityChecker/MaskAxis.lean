module

public import NormalityChecker.MaskGrid

/-! Exact rational valuations and unrestricted infinite masks of a prime-power axis. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

private lemma val_eq {p : ℕ} (hp : p.Prime) (z : ℚ) :
    padicValRat p z = (z.num.natAbs.factorization p : ℤ) - z.den.factorization p := by
  simp [padicValRat_def,padicValInt,Nat.factorization_def _ hp]

lemma valuation_of_den_factor {p : ℕ} (hp : p.Prime) (z : ℚ) (h : 0 < z.den.factorization p) :
    padicValRat p z = -(z.den.factorization p : ℤ) := by
  have div := (hp.pow_dvd_iff_le_factorization z.den_ne_zero).mpr (show 1 ≤ z.den.factorization p from h)
  rw [pow_one] at div
  have cop : ¬p∣z.num.natAbs := fun h => Nat.not_coprime_of_dvd_of_dvd hp.one_lt h div z.reduced
  simp [val_eq hp,Nat.factorization_eq_zero_of_not_dvd cop]

/-- Clearing rational coefficients changes the reduced denominator exponent by
the valuation of the clearing integer. No assumption that it is prime to p is needed. -/
theorem rational_den_exponent {p : ℕ} (hp : p.Prime) {D : ℤ} (hd : D≠0) (y : ℚ)
    (hit : 0 < ((D:ℚ)*y).den.factorization p) :
    y.den.factorization p = ((D:ℚ)*y).den.factorization p + D.natAbs.factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  have yn : y≠0 := by rintro rfl; simp at hit
  have v := valuation_of_den_factor hp _ hit
  rw [padicValRat.mul (by exact_mod_cast hd) yn, padicValRat.of_int, padicValInt,
    ← Nat.factorization_def _ hp] at v
  have vy := val_eq hp y
  have pos : 0 < y.den.factorization p := by omega
  rw [valuation_of_den_factor hp y pos] at v
  omega

private lemma shift_at_last {b n m t : ℕ} (G : ℤ[X]) (A : Finset ℕ) (mn : m≤n)
    (cap : ∀ q∈A,q≤m) :
    shiftedPrefix b t n G A=(b:ℚ)^(n-m)*shiftedPrefix b t m G A := by
  simp only [shiftedPrefix,mul_sum]
  apply sum_congr rfl; intro q hq
  rw [show n-q=(n-m)+(m-q) by have := cap q hq; omega,pow_add]; ring

/-- An isolated last retained power certifies every subsequent shift until the next
insertion, even when the next retained exponent is arbitrarily far away. -/
theorem last_power_den_exponent {b p t n k : ℕ} (hp : p.Prime) (hb : 0<b) (off : ¬p∣b)
    (ht : 0<t) (G : ℤ[X]) (g0 : sample G 0≠0) (A : Finset ℕ) (hit : p^k∈A)
    (cap : ∀ m∈A, 0<m ∧ m≤p^k) (mn : p^k≤n) (late : (sample G 0).natAbs.factorization p < k) :
    (shiftedPrefix b t n G A).den.factorization p = k*t-(sample G 0).natAbs.factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  let z := shiftedPrefix b t (p^k) G A
  have ex := first_cell_den_exponent (b:=b) hp off ht G g0 A hit cap (by have := pow_pos hp.pos k; omega) late
  change z.den.factorization p = _ at ex
  have pos : 0 < z.den.factorization p := by rw [ex]; have := Nat.le_mul_of_pos_right k ht; omega
  have zn : z≠0 := by rintro h; simp [h] at pos
  let u := b^(n-p^k)
  have vn := valuation_of_den_factor hp z pos
  have prod := padicValRat.mul (p:=p) (show (u:ℚ)≠0 by exact_mod_cast (pow_pos hb _).ne') zn
  rw [padicValRat.of_nat,multiplicity_eq_zero_of_not_dvd (fun h : p∣u => off (hp.dvd_of_dvd_pow h)),
    Nat.cast_zero,zero_add,vn] at prod
  have vv := val_eq hp ((u:ℚ)*z)
  have bigger : 0 < ((u:ℚ)*z).den.factorization p := by omega
  rw [valuation_of_den_factor hp _ bigger] at prod
  rw [shift_at_last G A mn (fun q hq => (cap q hq).2),← Nat.cast_pow]
  change ((u:ℚ)*z).den.factorization p = _
  omega

/-- Every infinite mask on a single off-base prime-power axis is normal for
all rational polynomial weights with a pole at zero, of unrestricted degree. -/
theorem infinite_axis_normal {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b) (ht : 0<t)
    (P : ℚ[X]) (p0 : P.eval 0 ≠ 0) (keep : ℕ → Bool)
    (infinite : ∀ J : ℕ, ∃ j≥J, keep (p^j)=true) :
    NormalIn b (maskedValue b {p} keep P t) := by
  obtain ⟨D,G,hD,eval⟩ := normalize P
  have g0 : sample G 0 ≠ 0 := by
    have h := eval 0; simp only [Nat.cast_zero] at h
    intro z; rw [z,Int.cast_zero] at h
    exact (mul_ne_zero (by exact_mod_cast hD : (D:ℚ)≠0) p0) h.symm
  obtain ⟨c,hc,cop,supp⟩ := offbase_modulus ({p} ∪ D.natAbs.primeFactors)
    (fun r h => (mem_union.mp h).elim (fun h => (mem_singleton.mp h) ▸ hp) Nat.prime_of_mem_primeFactors)
    hp (mem_union_left _ (mem_singleton_self _)) off
  apply normal_of_radix_limsup_zero hb
  apply discrepancy_of_windows hb (fixed_support_orbit_estimate hb hc cop) (weights_growth ..)
    (weights_supported {p} keep P t) (clean_modulus (by omega) (by omega) (Int.natAbs_pos.mpr hD)
      (weights_supported {p} keep P t) (coefficient_den hD eval _ keep t) supp) (fun _ => false)
  · intro M
    let v := (sample G 0).natAbs.factorization p
    obtain ⟨j,large,kept⟩ := infinite (M+v+1)
    filter_upwards [eventually_ge_atTop (p^j)] with n late _
    let A := (LocalizedSupport.indices {p} n).filter (fun m => keep m=true)
    have pm : p^j∈Nat.factoredNumbers {p} := by simpa using Nat.pow_mul_mem_factoredNumbers (s:=∅) hp j (by simp : 1∈Nat.factoredNumbers ∅)
    have hit : p^j∈A := mem_filter.mpr ⟨LocalizedSupport.mem_indices.mpr ⟨late,pm⟩,kept⟩
    let m := A.max' ⟨_,hit⟩
    have mem : m∈A := max'_mem ..
    have ⟨le,ms⟩ := LocalizedSupport.mem_indices.mp (mem_filter.mp mem).1
    let equiv := Nat.equivProdNatFactoredNumbers (s:=∅) hp (by simp)
    obtain ⟨⟨k,w⟩,hw⟩ := equiv.surjective ⟨m,ms⟩
    have eqn := congrArg Subtype.val hw
    change p^k*(w:ℕ)=m at eqn
    have one : (w:ℕ)=1 := by simpa using w.property
    rw [one,mul_one] at eqn
    have jk : j≤k := (pow_right_strictMono₀ hp.one_lt).le_iff_le.mp (eqn ▸ le_max' A _ hit)
    have exp := last_power_den_exponent (b:=b) hp (by omega) off ht G g0 A (eqn ▸ mem)
      (fun q hq => ⟨Nat.pos_of_ne_zero (LocalizedSupport.mem_indices.mp (mem_filter.mp hq).1).2.1,
        eqn ▸ le_max' A q hq⟩) (n:=n) (eqn ▸ le) (by change v<k; omega)
    let y := pre b (weights {p} keep P t) n
    have norm := normalized_prefix eval b t n {p} keep
    change (D:ℚ)*y = shiftedPrefix b t n G A at norm
    rw [← norm] at exp
    have pos : 0<((D:ℚ)*y).den.factorization p := by rw [exp]; have := Nat.le_mul_of_pos_right k ht; change 0<k*t-v; omega
    have actual := rational_den_exponent hp hD y pos
    rw [exp] at actual
    have enough : M≤y.den.factorization p := by change _ = k*t-v+_ at actual; have := Nat.le_mul_of_pos_right k ht; omega
    exact (Nat.lt_pow_self hp.one_lt (n:=M)).le.trans
      ((Nat.pow_le_pow_right hp.pos enough).trans (Nat.le_of_dvd y.pos (Nat.ordProj_dvd y.den p)))
  · intro ε pos; filter_upwards with N; simp; positivity

/-- Any eventually zero rational weight on a smooth support leaves a fixed grid
gap, including the empty mask. -/
theorem finite_mask_nonnormal {b : ℕ} (hb : 2≤b) {S : Finset ℕ} {a : ℕ → ℚ}
    (growth : PolyGrowth a) (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (finite : ∀ᶠ m : ℕ in atTop, a m=0) : ¬NormalIn b (series b a) := by
  obtain ⟨K,zero⟩ := eventually_atTop.mp finite
  let L := ∏ m∈range K,(a m).den
  have pos : 0<L := prod_pos (fun m _ => (a m).pos)
  apply (grid_discrepancy hb pos growth supp _).2
  apply Eventually.of_forall; intro k n _
  apply (Rat.den_sum_dvd_lcm_den ..).trans; apply Finset.lcm_dvd
  intro m _
  by_cases late : K≤m
  · simp [zero m late]
  · have dvd : (a m).den∣L := dvd_prod_of_mem (fun i => (a i).den) (mem_range.mpr (lt_of_not_ge late))
    rw [← Nat.cast_pow]
    exact cleared_term _ pos.ne' (dvd.trans (dvd_mul_right ..))

/-- Complete mask classification on one off-base prime-power axis in the
presence of a residual pole. -/
theorem axis_normal_iff {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (off : ¬p∣b) (ht : 0<t)
    (P : ℚ[X]) (p0 : P.eval 0 ≠ 0) (keep : ℕ → Bool) :
    NormalIn b (maskedValue b {p} keep P t) ↔ ∀ J : ℕ, ∃ j≥J, keep (p^j)=true := by
  refine ⟨?_,infinite_axis_normal hb hp off ht P p0 keep⟩
  intro normal; by_contra! finite
  obtain ⟨K,no⟩ := finite
  apply finite_mask_nonnormal hb (weights_growth ..) (weights_supported {p} keep P t) _ normal
  filter_upwards [eventually_ge_atTop (p^K)] with m late
  by_cases sm : m∈Nat.factoredNumbers {p}
  · let equiv := Nat.equivProdNatFactoredNumbers (s:=∅) hp (by simp)
    obtain ⟨⟨j,w⟩,hw⟩ := equiv.surjective ⟨m,sm⟩
    have eqn := congrArg Subtype.val hw
    change p^j*(w:ℕ)=m at eqn
    have one : (w:ℕ)=1 := by simpa using w.property
    rw [one,mul_one] at eqn
    have jk := (pow_right_strictMono₀ hp.one_lt).le_iff_le.mp (late.trans_eq eqn.symm)
    simp [weights,← eqn,no j jk]
  · exact weights_supported _ _ _ _ _ sm

end NormalityChecker.PolynomialMasks
