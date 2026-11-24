module

public import NormalityChecker.LocalizedSupport

/-! Finite sufficient certificates for denominator survival on every sufficiently large scale.
`ell` is the precision minus one. The finite grid refines every insertion cell. -/
@[expose] public section
open Finset
namespace NormalityChecker.LocalizedSupport

/-- Reduction of a rational with a unit denominator, retaining the integer cross-products. -/
def Represents {M : ℕ} (x : ℚ) (z : ZMod M) : Prop :=
  ∃ a d : ℕ, IsUnit (d : ZMod M) ∧ (d:ℚ)*x = a ∧ (d:ZMod M)*z = a

private lemma rep_sum {M : ℕ} {α : Type*} (s : Finset α) (x : α → ℚ) (z : α → ZMod M)
    (h : ∀ i ∈ s, Represents (x i) (z i)) : Represents (∑ i ∈ s, x i) (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,1,by simp,by simp,by simp⟩
  | insert i s hi ih =>
    obtain ⟨a,d,hd,eqd,modd⟩ := h i (mem_insert_self ..)
    obtain ⟨c,e,he,eqe,mode⟩ := ih (fun j hj => h j (mem_insert_of_mem hj))
    refine ⟨e*a+d*c,d*e,by simpa using hd.mul he,?_,?_⟩ <;>
      rw [sum_insert hi] <;> push_cast
    · linear_combination (e:ℚ)*eqd + (d:ℚ)*eqe
    · linear_combination (e:ZMod M)*modd + (d:ZMod M)*mode

/-- A computable inverse-base residue. The checker verifies the fixed-point equation. -/
def inverseLift (b p ell seed : ℕ) : ZMod (p^(ell+1)) := ((b:ZMod _)⁻¹)^(p^seed)

/-- At precision `p^(ell+1)`, raising the inverse base to `p^ell` always gives
an exact fixed point. Smaller seeds can be certified directly. -/
theorem canonical_lift_fixed {p b : ℕ} (hp : p.Prime) (hb : b.Coprime p) (ell : ℕ) :
    (inverseLift b p ell ell)^p = inverseLift b p ell ell := by
  let M := p^(ell+1)
  obtain ⟨v,hv⟩ := (ZMod.isUnit_iff_coprime b M).mpr (hb.pow_right _)
  have unit := congrArg (fun z : (ZMod M)ˣ => (z:ZMod M)) (ZMod.pow_totient v⁻¹)
  change ((v⁻¹: (ZMod M)ˣ) : ZMod M)^M.totient = 1 at unit
  rw [← ZMod.inv_coe_unit,hv,Nat.totient_prime_pow_succ hp] at unit
  have ex : p^ell*p = p^ell*(p-1)+p^ell := by
    have h := congrArg (p^ell * ·) (Nat.sub_add_cancel hp.one_le)
    simpa [Nat.mul_add] using h.symm
  change (((b:ZMod M)⁻¹)^(p^ell))^p = ((b:ZMod M)⁻¹)^(p^ell)
  rw [← pow_mul,ex,pow_add,unit,one_mul]

/-- The integer grid coordinate is `floor(n / p^(k-ell))`. -/
def powerCellResidue (order p ell : ℕ) (S : Finset ℕ) (w : ZMod (p^(ell+1))) (u : ℕ) :=
  ∑ i ∈ range (ell+1), ∑ r ∈ indices S (u/p^(ell-i)),
    ((p:ZMod (p^(ell+1)))^i * (r:ZMod _)⁻¹)^order * w^r

def cellResidue := powerCellResidue 1

/-- Left endpoints of the exact half-open cells, in units of `1 / p^ell`. -/
def cellStarts (p ell : ℕ) (S : Finset ℕ) : Finset ℕ :=
  insert (p^ell) (((range (ell+1)).biUnion (fun i =>
    (indices S (p^(i+1)-1)).image (fun r => r*p^(ell-i)))).filter (fun u => p^ell ≤ u))

def passesPower (order b p ell seed : ℕ) (S : Finset ℕ) : Bool :=
  let w := inverseLift b p ell seed
  decide (w^p = w) && decide (∀ u ∈ cellStarts p ell S, powerCellResidue order p ell S w u ≠ 0)

def passes := passesPower 1

private lemma cell_cover (order : ℕ) {p ell u : ℕ} (hp : 0 < p) (S : Finset ℕ)
    (w : ZMod (p^(ell+1))) (lo : p^ell ≤ u) (hi : u < p^(ell+1)) :
    ∃ v ∈ cellStarts p ell S, powerCellResidue order p ell S w u = powerCellResidue order p ell S w v := by
  let starts := (cellStarts p ell S).filter (· ≤ u)
  have left : p^ell ∈ starts := mem_filter.mpr ⟨mem_insert_self ..,lo⟩
  let v := starts.max' ⟨_,left⟩
  have hv : v ∈ starts := starts.max'_mem _
  have hvu := (mem_filter.mp hv).2
  refine ⟨v,(mem_filter.mp hv).1,?_⟩
  unfold powerCellResidue; apply sum_congr rfl; intro i h
  have hei : i ≤ ell := by simpa using mem_range.mp h
  have e : p^(i+1)*p^(ell-i)=p^(ell+1) := by rw [← pow_add]; congr 1; omega
  have heq : indices S (u/p^(ell-i)) = indices S (v/p^(ell-i)) := by
    ext r; rw [mem_indices,mem_indices]; constructor
    · rintro ⟨hr,hs⟩
      have cut := (Nat.le_div_iff_mul_le (pow_pos hp _)).mp hr
      refine ⟨(Nat.le_div_iff_mul_le (pow_pos hp _)).mpr ?_,hs⟩
      by_cases first : r*p^(ell-i) < p^ell
      · exact first.le.trans (starts.le_max' _ left)
      · have bound := (Nat.lt_of_mul_lt_mul_right (cut.trans_lt (hi.trans_eq e.symm)))
        have member : r*p^(ell-i) ∈ cellStarts p ell S := mem_insert_of_mem (mem_filter.mpr
          ⟨mem_biUnion.mpr ⟨i,h,mem_image.mpr ⟨r,mem_indices.mpr ⟨by omega,hs⟩,rfl⟩⟩,le_of_not_gt first⟩)
        exact starts.le_max' _ (mem_filter.mpr ⟨member,cut⟩)
    · rintro ⟨hr,hs⟩; exact ⟨hr.trans (Nat.div_le_div_right hvu),hs⟩
  rw [heq]

private lemma fixed_lift {b p ell seed j : ℕ} (hj : seed ≤ j)
    (fixed : (inverseLift b p ell seed)^p = inverseLift b p ell seed) :
    ((b:ZMod (p^(ell+1)))⁻¹)^(p^j) = inverseLift b p ell seed := by
  induction j,hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [pow_succ p j,pow_mul,ih,fixed]

def powerWeight (b order m : ℕ) : ℚ := 1 / ((m:ℚ)^order * (b:ℚ)^m)

def powerPartial (b order : ℕ) (S : Finset ℕ) (n : ℕ) := ∑ m ∈ indices S n, powerWeight b order m

def powerShifted (b order : ℕ) (S : Finset ℕ) (n : ℕ) := (b:ℚ)^n * powerPartial b order S n

/-- The cell residue is the reduction of the full unshifted, normalized prefix. -/
theorem power_prefix_residue {order : ℕ} (positive : 0 < order) {b p ell seed k n : ℕ} {S : Finset ℕ} (hp : p.Prime) (hs : p ∉ S)
    (hb : b.Coprime p) (hk : seed+ell ≤ k) (hi : n < p^(k+1))
    (fixed : (inverseLift b p ell seed)^p = inverseLift b p ell seed) :
    Represents (((p:ℚ)^k)^order*powerPartial b order (insert p S) n)
      (powerCellResidue order p ell S (inverseLift b p ell seed) (n/p^(k-ell))) := by
  let M := p^(ell+1)
  let w := inverseLift b p ell seed
  let row (i : ℕ) := ∑ r ∈ indices S (n/p^(k-i)), ((p:ZMod M)^i * (r:ZMod M)⁻¹)^order * w^r
  have row_eq : ∑ i ∈ range (k+1), row i = powerCellResidue order p ell S w (n/p^(k-ell)) := by
    unfold powerCellResidue
    calc _ = ∑ i ∈ range (ell+1), row i := by
           symm; apply sum_subset (range_mono (by omega))
           intro i _ h; have hi' : ell+1 ≤ i := by simpa using h
           have hz : (p:ZMod M)^i=0 := by
             exact_mod_cast (ZMod.natCast_eq_zero_iff (p^i) M).mpr (pow_dvd_pow p hi')
           simp [row,hz,positive.ne']
         _ = _ := by
           apply sum_congr rfl; intro i hi'; dsimp only [row]
           have hei : i ≤ ell := by simpa using mem_range.mp hi'
           rw [Nat.div_div_eq_div_mul,← pow_add,show k-ell+(ell-i)=k-i by omega]
  rw [← row_eq,powerPartial,sum_layers hp hs n k hi,← sum_range_reflect (fun j => ∑ r ∈ indices S (n/p^j), powerWeight b order (p^j*r)) (k+1)]
  simp only [Nat.add_sub_cancel,mul_sum]
  apply rep_sum; intro i hi'
  have hik : i ≤ k := by simpa using mem_range.mp hi'
  dsimp only [row]; apply rep_sum; intro r hr
  have hsr := (mem_indices.mp hr).2
  let j := k-i
  let m := p^j*r
  have hu : IsUnit (r:ZMod M) := (ZMod.isUnit_iff_coprime ..).mpr ((hp.factoredNumbers_coprime hs hsr).symm.pow_right _)
  have hbu : IsUnit (b:ZMod M) := (ZMod.isUnit_iff_coprime ..).mpr (hb.pow_right _)
  refine ⟨(p^i)^order,r^order*b^m,by simpa using (hu.pow order).mul (hbu.pow m),?_,?_⟩
  · have hb0 : b ≠ 0 := by intro h; subst b; simp [hp.ne_one] at hb
    have hr0 := hsr.1
    have e : (p:ℚ)^i*(p:ℚ)^j = (p:ℚ)^k := by rw [← pow_add]; congr 1; dsimp [j]; omega
    change ((r^order*b^m:ℕ):ℚ)*(((p:ℚ)^k)^order*powerWeight b order m) = ((p^i)^order:ℕ)
    simp only [powerWeight,Nat.cast_mul,Nat.cast_pow]
    rw [← e]; dsimp [m]; push_cast; rw [mul_pow,mul_pow]; field_simp [hp.ne_zero]
  · push_cast
    by_cases h : i ≤ ell
    · have hl := fixed_lift (j:=j) (by dsimp [j]; omega : seed ≤ j) fixed
      have cancel : (b:ZMod M)^m * w^r = 1 := by
        change (b:ZMod M)^(p^j*r) * (inverseLift b p ell seed)^r = 1
        rw [← hl,pow_mul,← mul_pow,← mul_pow,ZMod.mul_inv_of_unit _ hbu,one_pow,one_pow]
      calc (r:ZMod M)^order*b^m*(((p:ZMod M)^i*(r:ZMod M)⁻¹)^order*w^r) =
          ((p:ZMod M)^i)^order * ((r:ZMod M)*(r:ZMod M)⁻¹)^order * ((b:ZMod M)^m*w^r) := by simp only [mul_pow]; ring
        _ = _ := by rw [ZMod.mul_inv_of_unit _ hu,cancel]; simp
    · have hz : (p:ZMod M)^i=0 := by
        exact_mod_cast (ZMod.natCast_eq_zero_iff (p^i) M).mpr (pow_dvd_pow p (Nat.succ_le_of_lt (lt_of_not_ge h)))
      simp [hz,positive.ne']

theorem prefix_residue {b p ell seed k n : ℕ} {S : Finset ℕ} (hp : p.Prime) (hs : p ∉ S)
    (hb : b.Coprime p) (hk : seed+ell ≤ k) (hi : n < p^(k+1))
    (fixed : (inverseLift b p ell seed)^p = inverseLift b p ell seed) :
    Represents ((p:ℚ)^k*partialSum b (insert p S) n)
      (cellResidue p ell S (inverseLift b p ell seed) (n/p^(k-ell))) := by
  simpa only [powerPartial,partialSum,powerWeight,weight,pow_one,cellResidue] using
    power_prefix_residue (order:=1) (by decide) hp hs hb hk hi fixed

private lemma den_of_rep {p ell k : ℕ} (hp : p.Prime) {x : ℚ} {z : ZMod (p^(ell+1))}
    (hz : z ≠ 0) (h : Represents ((p:ℚ)^k*x) z) : p^(k-ell) ∣ x.den := by
  obtain ⟨a,d,hd,e,hm⟩ := h
  have hnd : ¬ p^(ell+1) ∣ a := by
    intro h; have H := (ZMod.natCast_eq_zero_iff ..).mpr h
    exact hz ((hd.mul_right_inj).mp (by rw [hm,H,mul_zero]))
  have ha : a ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
  have ha' := mt (hp.pow_dvd_iff_le_factorization ha).mpr hnd
  have cross := (reduced_info (L:=d*p^k) (S:=a) (x:=x) (by
    apply Nat.mul_pos _ (pow_pos hp.pos _); by_contra! he; have : d=0 := by omega
    simp [this] at e; exact ha (by exact_mod_cast e.symm)) (by push_cast; linear_combination -e)).2
  have dv : p^k ∣ a*x.den := by rw [cross]; exact (dvd_mul_left ..).trans (dvd_mul_right ..)
  have v := (hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero ha x.den_ne_zero)).mp dv
  rw [Nat.factorization_mul ha x.den_ne_zero,Finsupp.add_apply] at v
  exact (hp.pow_dvd_iff_le_factorization x.den_ne_zero).mpr (by omega)

/-- Success certifies the selected prime power in the reduced *shifted* denominator. -/
theorem passes_power_denominator {order : ℕ} (positive : 0 < order) {b p ell seed k n : ℕ} {S : Finset ℕ} (hp : p.Prime) (hs : p ∉ S)
    (hb : b.Coprime p) (hk : seed+ell ≤ k) (lo : p^k ≤ n) (hi : n < p^(k+1))
    (pass : passesPower order b p ell seed S = true) : p^(k*order-ell) ∣ (powerShifted b order (insert p S) n).den := by
  simp only [passesPower,Bool.and_eq_true,decide_eq_true_eq] at pass
  have he : p^ell*p^(k-ell)=p^k := by rw [← pow_add]; congr 1; omega
  have he' : p^(ell+1)*p^(k-ell)=p^(k+1) := by rw [← pow_add]; congr 1; omega
  obtain ⟨v,hv,eqn⟩ := cell_cover order hp.pos S (inverseLift b p ell seed)
    ((Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mpr (he ▸ lo))
    ((Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr (he' ▸ hi))
  let z := powerCellResidue order p ell S (inverseLift b p ell seed) (n/p^(k-ell))
  have hz : z ≠ 0 := by dsimp [z]; rw [eqn]; exact pass.2 v hv
  have hbunit : IsUnit ((b:ZMod (p^(ell+1)))^n) := ((ZMod.isUnit_iff_coprime ..).mpr (hb.pow_right _)).pow n
  apply den_of_rep hp (z:=(b:ZMod _)^n*z) (by intro h; exact hz (hbunit.mul_right_inj.mp (by simpa using h)))
  obtain ⟨a,d,hd,e,hm⟩ := power_prefix_residue positive hp hs hb hk hi pass.1
  refine ⟨b^n*a,d,hd,?_,?_⟩
  · unfold powerShifted; rw [pow_mul]; push_cast; linear_combination (b:ℚ)^n * e
  · push_cast; linear_combination (b:ZMod _)^n * hm

theorem passes_denominator {b p ell seed k n : ℕ} {S : Finset ℕ} (hp : p.Prime) (hs : p ∉ S)
    (hb : b.Coprime p) (hk : seed+ell ≤ k) (lo : p^k ≤ n) (hi : n < p^(k+1))
    (pass : passes b p ell seed S = true) : p^(k-ell) ∣ (shifted b (insert p S) n).den := by
  simpa only [Nat.mul_one,powerShifted,shifted,powerPartial,partialSum,powerWeight,weight,pow_one] using
    passes_power_denominator (order:=1) (by decide) hp hs hb hk lo hi pass

end NormalityChecker.LocalizedSupport
