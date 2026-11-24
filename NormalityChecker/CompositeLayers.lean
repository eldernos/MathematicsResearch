module

public import NormalityChecker.LocalizedLayers

/-! Primewise separation when the coprime generator is composite. -/
@[expose] public section
open Finset
namespace NormalityChecker.Localized.Composite

def index (q c : ℕ) (v : ℕ × ℕ) := q^v.1*c^v.2

def allowed (q c n : ℕ) := (range (n+1) ×ˢ range (n+1)).filter (fun v => index q c v ≤ n)

def powerPrefix (b q c order n : ℕ) : ℚ := (b:ℚ)^n * ∑ v∈allowed q c n,
  1/((index q c v:ℚ)^order*(b:ℚ)^(index q c v))

lemma mem_allowed {q c n : ℕ} (hq : 2≤q) (hc : 2≤c) {v : ℕ × ℕ} : v∈allowed q c n ↔ index q c v≤n := by
    refine ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,h⟩⟩
    · have H := (Nat.lt_pow_self hq (n:=v.1)).trans_le ((Nat.le_mul_of_pos_right _ (pow_pos (by omega : 0<c) _)).trans h); simpa using H.le
    · have H := (Nat.lt_pow_self hc (n:=v.2)).trans_le ((Nat.le_mul_of_pos_left _ (pow_pos (by omega : 0<q) _)).trans h); simpa using H.le

/-- Shifted rational prefix including every insertion up to and including `n`. -/
def shiftedPrefix (b q c n : ℕ) : ℚ := powerPrefix b q c 1 n

/-- Primewise separation for every positive polylogarithm order. -/
theorem power_separated {b q c p s t a j order : ℕ} (hs : 0<order) (hq : 2≤q) (hc : 2≤c) (hp : p.Prime)
    (hpc : p ∣ c) (hb : ¬p ∣ b) (hqp : ¬p ∣ q) (left : s < q^a*c^j)
    (right : q^a*c^j ≤ t) (short : t ≤ q*s) :
    (((padicNorm p (c:ℚ))⁻¹)^order)^j ≤ max (padicNorm p (powerPrefix b q c order s)) (padicNorm p (powerPrefix b q c order t)) := by
  let : Fact p.Prime := ⟨hp⟩
  let I := allowed q c
  let w (v : ℕ × ℕ) : ℚ := 1/((index q c v:ℚ)^order*(b:ℚ)^index q c v)
  let A := I t \ I s
  have included : (a,j) ∈ A := mem_sdiff.mpr ⟨(mem_allowed hq hc).mpr right,mt (mem_allowed hq hc).mp left.not_ge⟩
  have unique : Set.InjOn Prod.snd (↑A : Set (ℕ × ℕ)) := by
    rintro ⟨e,j⟩ he ⟨f,l⟩ hf eqn
    change j=l at eqn; subst l
    have ordered {e f : ℕ} (he : (e,j)∈A) (hf : (f,j)∈A) : ¬ e<f := by
      intro h
      have cut : s < q^e*c^j := lt_of_not_ge (fun h => (mem_sdiff.mp he).2 ((mem_allowed (v:=(e,j)) hq hc).mpr h))
      have cap : q^f*c^j ≤ t := (mem_allowed hq hc).mp (mem_sdiff.mp hf).1
      have gap := Nat.mul_le_mul_right (c^j) (Nat.pow_le_pow_right (by omega : 0<q) (show e+1≤f from h))
      rw [pow_succ',Nat.mul_assoc] at gap
      exact (not_lt_of_ge (gap.trans cap)) (short.trans_lt (Nat.mul_lt_mul_of_pos_left cut (by omega)))
    exact Prod.ext (le_antisymm (not_lt.mp (ordered hf he)) (not_lt.mp (ordered he hf))) rfl
  have normPow (x : ℚ) (n : ℕ) : padicNorm p (x^n)=(padicNorm p x)^n := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ,ih]
  have baseUnit := (padicNorm.nat_eq_one_iff b).mpr hb
  have cofactorUnit := (padicNorm.nat_eq_one_iff q).mpr hqp
  have normWeight (v : ℕ × ℕ) : padicNorm p (w v) = ((padicNorm p (c:ℚ))⁻¹ ^ order)^v.2 := by
    dsimp only [w]; rw [padicNorm.div]
    simp only [index,padicNorm.one,Nat.cast_mul,Nat.cast_pow,padicNorm.mul,
      normPow,baseUnit,cofactorUnit,one_pow,one_mul,mul_one,one_div,inv_pow]
    rw [pow_right_comm]
  have growth : 1<((padicNorm p (c:ℚ))⁻¹)^order := by
    apply one_lt_pow₀ _ hs.ne'
    apply (one_lt_inv₀ (lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.ne_zero (by exact_mod_cast (show c≠0 by omega)))))).mpr
    exact (padicNorm.nat_lt_one_iff c).mpr hpc
  obtain ⟨v,hv,hmax⟩ := A.exists_max_image Prod.snd ⟨_,included⟩
  have ultra : IsNonarchimedean (padicNorm p) := fun _ _ => padicNorm.nonarchimedean
  have leading := ultra.apply_sum_eq_of_lt w padicNorm.neg hv (fun z hz hne => by
    rw [normWeight,normWeight]; exact pow_lt_pow_right₀ growth (lt_of_le_of_ne (hmax z hz) (fun eqn => hne (unique hz hv eqn))))
  have subset : I s ⊆ I t := fun v hv => (mem_allowed hq hc).mpr (((mem_allowed hq hc).mp hv).trans (left.le.trans right))
  have diff : ∑ v ∈ A,w v = (∑ v ∈ I t,w v)-(∑ v ∈ I s,w v) := eq_sub_of_add_eq (sum_sdiff subset)
  have shiftNorm (n : ℕ) : padicNorm p (powerPrefix b q c order n) = padicNorm p (∑ v ∈ I n,w v) := by
    change padicNorm p ((b:ℚ)^n*_) = _; rw [padicNorm.mul,normPow,baseUnit,one_pow,one_mul]
  rw [diff,normWeight] at leading
  rw [shiftNorm,shiftNorm,max_comm]
  exact (pow_le_pow_right₀ growth.le (hmax (a,j) included)).trans (leading ▸ padicNorm.sub)

/-- Every prime divisor `p` of `c` forces separation of two cutoffs at each
insertion between them. Neither squarefreeness of `c` nor `q ∣ b` is needed. -/
theorem separated_prefixes {b q c p s t a j : ℕ} (hq : 2≤q) (hc : 2≤c) (hp : p.Prime)
    (hpc : p ∣ c) (hb : ¬p ∣ b) (hqp : ¬p ∣ q) (left : s < q^a*c^j)
    (right : q^a*c^j ≤ t) (short : t ≤ q*s) :
    ((padicNorm p (c:ℚ))⁻¹)^j ≤ max (padicNorm p (shiftedPrefix b q c s)) (padicNorm p (shiftedPrefix b q c t)) := by
  simpa only [shiftedPrefix,pow_one] using
    (power_separated (order:=1) (by decide) hq hc hp hpc hb hqp left right short)

end NormalityChecker.Localized.Composite
