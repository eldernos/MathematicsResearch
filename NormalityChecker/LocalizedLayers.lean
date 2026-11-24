module

public import NormalityChecker.PrimeCancellation
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-! Arithmetic of a localized logarithm with insertion indices `q^a * p^j`. -/
@[expose] public section
open Finset
namespace NormalityChecker.Localized

structure Parameters where
  b : ℕ
  q : ℕ
  p : ℕ
  hb : 2 ≤ b
  hq : 2 ≤ q
  hp : p.Prime
  divides : q ∣ b
  coprime : b.Coprime p

variable (d : Parameters)

def index (v : ℕ × ℕ) := d.q^v.1 * d.p^v.2

def allowed (n : ℕ) := ((range (n+1)) ×ˢ (range (n+1))).filter (fun v => index d v ≤ n)

lemma index_pos (v) : 0 < index d v := Nat.mul_pos (pow_pos (by have := d.hq; omega) _) (pow_pos d.hp.pos _)

lemma mem_allowed {n v} : v ∈ allowed d n ↔ index d v ≤ n := by
  refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,h⟩⟩
  · have H := (Nat.lt_pow_self d.hq (n:=v.1)).le.trans ((Nat.le_mul_of_pos_right _ (pow_pos d.hp.pos v.2)).trans h)
    exact mem_range.mpr (by omega)
  · have H := (Nat.lt_pow_self d.hp.two_le (n:=v.2)).le.trans ((Nat.le_mul_of_pos_left _ (pow_pos (by have := d.hq; omega : 0<d.q) v.1)).trans h)
    exact mem_range.mpr (by omega)

def weight (v : ℕ × ℕ) : ℚ := 1 / ((index d v : ℚ) * (d.b:ℚ)^(index d v))

def unshifted (n : ℕ) : ℚ := ∑ v ∈ allowed d n, weight d v

def shifted (n : ℕ) : ℚ := (d.b:ℚ)^n * unshifted d n

lemma prime_not_dvd_base : ¬d.p ∣ d.b := d.hp.coprime_iff_not_dvd.mp d.coprime.symm

lemma prime_not_dvd_cofactor : ¬d.p ∣ d.q := fun h => prime_not_dvd_base d (h.trans d.divides)

private lemma norm_pow (x : ℚ) (n : ℕ) : padicNorm d.p (x^n) = (padicNorm d.p x)^n := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ,padicNorm.mul,ih]

lemma norm_shifted (n : ℕ) : padicNorm d.p (shifted d n) = padicNorm d.p (unshifted d n) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  simp [shifted,norm_pow,(padicNorm.nat_eq_one_iff d.b).mpr (prime_not_dvd_base d)]

lemma norm_weight (v : ℕ × ℕ) : padicNorm d.p (weight d v) = (d.p:ℚ)^v.2 := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  rw [weight,padicNorm.div]
  simp only [index,Nat.cast_mul,Nat.cast_pow,padicNorm.mul,norm_pow,padicNorm.one,(padicNorm.nat_eq_one_iff d.b).mpr (prime_not_dvd_base d),
    (padicNorm.nat_eq_one_iff d.q).mpr (prime_not_dvd_cofactor d),padicNorm.padicNorm_p_of_prime,one_pow,one_mul,mul_one,inv_pow,one_div,inv_inv]

/-- Between two cutoffs of ratio at most `q`, distinct new insertions have distinct
`p`-exponents. The left endpoint is excluded and the right endpoint is included. -/
theorem layers_injective {s t : ℕ} (ht : t ≤ d.q*s) :
    Set.InjOn Prod.snd (↑(allowed d t \ allowed d s) : Set (ℕ × ℕ)) := by
  have step {a c j : ℕ} (ha : a<c) : d.q*index d (a,j) ≤ index d (c,j) := by
    have H := Nat.pow_le_pow_right (by have := d.hq; omega : 0<d.q) (show a+1≤c from ha)
    simpa [index,pow_succ',mul_assoc] using Nat.mul_le_mul_right (d.p^j) H
  rintro ⟨a,j⟩ ha ⟨c,l⟩ hc he
  change j=l at he; subst l
  simp only [coe_sdiff,Set.mem_sdiff,mem_coe,mem_allowed,not_le] at ha hc
  have excl {a c : ℕ} (hs : s < index d (a,j)) (hc : index d (c,j) ≤ t) : ¬ a<c := by
    intro h
    exact (not_lt_of_ge (step h)) (hc.trans_lt (ht.trans_lt (Nat.mul_lt_mul_of_pos_left hs (by have := d.hq; omega))))
  exact Prod.ext (le_antisymm (not_lt.mp (excl hc.2 ha.1)) (not_lt.mp (excl ha.2 hc.1))) rfl

/-- An insertion with exponent `j` forces at least one of the two endpoint prefixes
 to have `p`-adic norm at least `p^j`, regardless of all the other insertions. -/
theorem separated_prefixes {s t : ℕ} {v : ℕ × ℕ} (hs : s < index d v)
    (hv : index d v ≤ t) (ht : t ≤ d.q*s) :
    (d.p:ℚ)^v.2 ≤ max (padicNorm d.p (shifted d s)) (padicNorm d.p (shifted d t)) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let A := allowed d t \ allowed d s
  have hA : v∈A := mem_sdiff.mpr ⟨(mem_allowed d).mpr hv,mt (mem_allowed d).mp hs.not_ge⟩
  obtain ⟨w,hw,hm⟩ := A.exists_max_image Prod.snd ⟨v,hA⟩
  have hna : IsNonarchimedean (padicNorm d.p) := fun _ _ => padicNorm.nonarchimedean
  have val := hna.apply_sum_eq_of_lt (weight d) (fun x => padicNorm.neg x) hw (fun z hz hne => by
    rw [norm_weight,norm_weight]
    exact pow_lt_pow_right₀ (by exact_mod_cast d.hp.one_lt) (lt_of_le_of_ne (hm z hz) (fun e => hne (layers_injective d ht hz hw e))))
  have sub : allowed d s ⊆ allowed d t := fun z hz => (mem_allowed d).mpr (((mem_allowed d).mp hz).trans (hs.le.trans hv))
  have e : ∑ z ∈ A, weight d z = unshifted d t - unshifted d s := eq_sub_of_add_eq (sum_sdiff sub)
  rw [e,norm_weight] at val
  rw [norm_shifted,norm_shifted,max_comm]
  exact (pow_le_pow_right₀ (by exact_mod_cast d.hp.one_le) (hm v hA)).trans (val ▸ padicNorm.sub)

lemma shifted_summand {n : ℕ} {v : ℕ × ℕ} (hv : index d v ≤ n) :
    (d.b:ℚ)^n * weight d v = (d.b:ℚ)^(n-index d v)/(index d v) := by
  have hb : (d.b:ℚ) ≠ 0 := by exact_mod_cast (show d.b ≠ 0 by have := d.hb; omega)
  rw [weight,pow_sub₀ _ hb hv]; ring

/-- Away from recent insertions the cofactor dividing the base has cleared,
and the remaining denominator divides the largest available power of `p`. -/
theorem clean_denominator (n : ℕ) (clean : ∀ v ∈ allowed d n, index d v + v.1 ≤ n) :
    (shifted d n).den ∣ d.p^(Nat.log d.p n) := by
  let k := Nat.log d.p n
  have each (v : ℕ × ℕ) (hv : v∈allowed d n) : ∃ z : ℕ,
      (z:ℚ) = d.p^k * ((d.b:ℚ)^n * weight d v) := by
    have hi := (mem_allowed d).mp hv
    have ha : v.1 ≤ n-index d v := by have := clean v hv; omega
    have hj : v.2 ≤ k := Nat.le_log_of_pow_le d.hp.one_lt
      ((Nat.le_mul_of_pos_left _ (pow_pos (by have := d.hq; omega : 0<d.q) _)).trans hi)
    obtain ⟨A,hA⟩ := (pow_dvd_pow_of_dvd d.divides v.1).trans (pow_dvd_pow d.b ha)
    obtain ⟨B,hB⟩ := pow_dvd_pow d.p hj
    refine ⟨A*B,?_⟩
    rw [shifted_summand d hi,mul_div_assoc',eq_div_iff (by exact_mod_cast (index_pos d v).ne')]
    have he : A*B*index d v = d.p^k*d.b^(n-index d v) := by rw [hA,hB]; unfold index; ring
    exact_mod_cast he
  choose! z hz using each
  apply (reduced_info (S:=∑ v ∈ allowed d n, z v) (pow_pos d.hp.pos k) _).1
  simp only [shifted,unshifted,mul_sum,Nat.cast_sum,Nat.cast_pow]
  exact sum_congr rfl hz

lemma norm_le_clean_den {n : ℕ} {e : ℕ} (he : (shifted d n).den = d.p^e) :
    padicNorm d.p (shifted d n) ≤ ((shifted d n).den:ℚ) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let x := shifted d n
  have hc := congrArg (padicNorm d.p) (Rat.den_mul_eq_num x)
  change x.den = _ at he
  rw [padicNorm.mul,he,Nat.cast_pow,norm_pow,padicNorm.padicNorm_p_of_prime,inv_pow,inv_mul_eq_div] at hc
  change padicNorm d.p x ≤ (x.den:ℚ)
  rw [he,Nat.cast_pow]
  have hp : (0:ℚ)<d.p := by exact_mod_cast d.hp.pos
  have H := (div_le_iff₀ (pow_pos hp e)).mp (hc.trans_le (padicNorm.of_int x.num))
  simpa using H

/-- With two independent cofactors 2 and 5 in base 10, the insertions at
`4*3^j` and `5*3^j` share the highest new layer on `(3*3^j,5*3^j]`.
Their combined numerator after removing that layer has exactly two factors
of three for `j ≥ 1`. -/
theorem decimal_layer_collision (k : ℕ) :
    (5*10^(3^(k+1))+4).factorization 3 = 2 := by
  let m := 5*10^(3^(k+1))+4
  have he : (m:ZMod 27) = 9 := by
    simp only [m,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [pow_succ' 3 k,pow_mul,show (10:ZMod 27)^3=1 by decide,one_pow]; decide
  have red := congrArg (ZMod.castHom (by decide : 9 ∣ 27) (ZMod 9)) he
  have h9 : 3^2 ∣ m := (ZMod.natCast_eq_zero_iff m 9).mp (by rw [map_natCast] at red; exact red.trans (by decide))
  have h27 : ¬ 3^3 ∣ m := fun H => (by decide : (9:ZMod 27) ≠ 0) (he.symm.trans ((ZMod.natCast_eq_zero_iff m 27).mpr H))
  have prime : Nat.Prime 3 := by decide
  have hm : m≠0 := by dsimp [m]; positivity
  change m.factorization 3 = 2
  exact le_antisymm (by have := mt (prime.pow_dvd_iff_le_factorization hm).mpr h27; omega) ((prime.pow_dvd_iff_le_factorization hm).mp h9)

end NormalityChecker.Localized
