module

public import NormalityChecker.CyclotomicLift
public import NormalityChecker.StonehamComponents

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker
namespace CyclotomicCell

variable {b p : ℕ} [Fact p.Prime]

private lemma projected_dvd (t : ℕ) (x : ℤ_[p]) :
    PadicInt.toZModPow t x=0 ↔ (p:ℤ_[p])^t ∣ x := by
  rw [← RingHom.mem_ker,PadicInt.ker_toZModPow,Ideal.mem_span_singleton]

/-- Numerator of the shifted finite prefix after multiplying by p-1.
Its residue only depends on the last insertion depth. -/
private lemma prefix_num (hb : 1<b) (w : ℤ_[p])
    (hw : ∀ j : ℕ, (p:ℤ_[p])^j ∣ (b:ℤ_[p])^(p^j)*w-1)
    (m n J : ℕ) (hn : m*p^J ≤ n) : ∃ A : ℤ,
    (A:ℝ)/(p:ℝ)^J = ((p:ℝ)-1) * ∑ j ∈ range (J+1), (b:ℝ)^n*weightedTerm b p m j ∧
    (p:ℤ_[p])^J ∣ (A:ℤ_[p])+(b:ℤ_[p])^n*w^m := by
  have hp := Fact.out (p:=p.Prime)
  have term (j : ℕ) (h : m*p^j≤n) : (b:ℝ)^n*weightedTerm b p m j = (b:ℝ)^(n-m*p^j)/(p:ℝ)^j := by
    unfold weightedTerm
    conv_lhs => rw [← Nat.add_sub_of_le h,pow_add,one_div_pow]
    field_simp
  induction J with
  | zero =>
    refine ⟨((p:ℤ)-1)*b^(n-m),?_,by simp⟩
    rw [sum_range_one,term 0 hn]; simp
  | succ j ih =>
    obtain ⟨A,hA,hmod⟩ := ih ((Nat.mul_le_mul_left m (Nat.pow_le_pow_right hp.pos j.le_succ)).trans hn)
    let s := n-m*p^(j+1)
    refine ⟨(p:ℤ)*A+((p:ℤ)-1)*b^s,?_,?_⟩
    · rw [sum_range_succ,term _ hn,mul_add,← hA,pow_succ (p:ℝ)]; push_cast; dsimp [s]; field_simp [hp.ne_zero]
    · let q := p^(j+1)
      let π := PadicInt.toZModPow (p:=p) (j+1)
      have e := (projected_dvd (j+1) _).mpr (hw (j+1))
      change π (_-1)=0 at e
      rw [map_sub,map_one,sub_eq_zero,map_mul,map_pow,map_natCast] at e
      have leq : (b:ZMod q)^n*π w^m = (b:ZMod q)^s := by
        have hn' : n=s+q*m := by rw [mul_comm q m]; exact (Nat.sub_add_cancel hn).symm
        conv_lhs => rw [hn',pow_add (b:ZMod q) s (q*m),pow_mul (b:ZMod q) q m]
        rw [mul_assoc, ← mul_pow]; change _*((b:ZMod q)^q*π w)^m=_
        rw [e,one_pow,mul_one]
      have hd := mul_dvd_mul_left (p:ℤ_[p]) hmod
      rw [← pow_succ'] at hd
      apply (projected_dvd _ _).mp
      have zero := (projected_dvd _ _).mpr hd
      change π _=0 at zero ⊢
      simp only [map_add,map_sub,map_one,map_mul,map_pow,map_natCast,map_intCast, Int.cast_add,Int.cast_mul,
        Int.cast_sub,Int.cast_one,Int.cast_natCast,Int.cast_pow,leq] at zero ⊢
      linear_combination zero

noncomputable def value (M : Finset ℕ) (c : ℕ → ℤ) (j : ℕ → ℕ) (E : ℕ) (w : ℤ_[p]) :=
  ∑ m ∈ M, (c m:ℤ_[p])*w^m*(p:ℤ_[p])^(E-j m)

noncomputable def scaled (b p : ℕ) (M : Finset ℕ) (c : ℕ → ℤ) :=
  ((p:ℝ)-1)*∑ m ∈ M, (c m:ℝ)*((m:ℝ)*radixComponent b p m)

/-- At offset i, the whole family follows a single rational orbit up to
an integer and a uniform O(p⁻ᵏ) real error. -/
theorem model (hb : 1<b) (w : ℤ_[p])
    (hw : ∀ j : ℕ, (p:ℤ_[p])^j ∣ (b:ℤ_[p])^(p^j)*w-1)
    (M : Finset ℕ) (c : ℕ → ℤ) (j : ℕ → ℕ) {u E : ℕ}
    (hm : ∀ m ∈ M, 0<m) (hl : ∀ m ∈ M, m*p^(j m)≤u)
    (hu : ∀ m ∈ M, u+1≤m*p^(j m+1)) (hE : ∀ m ∈ M, j m≤E)
    (k i : ℕ) (hi : i<p^k) (A : ℤ)
    (hA : (A:ZMod (p^(k+E))) = PadicInt.toZModPow (k+E) (-(b:ℤ_[p])^(u*p^k)*value M c j E w)) :
    ∃ z : ℤ, |(b:ℝ)^(u*p^k+i)*scaled b p M c - A*(b:ℝ)^i/(p:ℝ)^(k+E)-z| ≤
      (∑ m ∈ M, |(c m:ℝ)|)/(p:ℝ)^k := by
  classical
  let n := u*p^k+i
  let t := k+E
  let J (m : ℕ) := k+j m
  have hp := Fact.out (p:=p.Prime)
  have hpr : 1<(p:ℝ) := by exact_mod_cast hp.one_lt
  have lower (m : ℕ) (h : m∈M) : m*p^(J m)≤n := by
    dsimp [J,n]; rw [pow_add]; nlinarith [Nat.mul_le_mul_right (p^k) (hl m h)]
  have upper (m : ℕ) (h : m∈M) : n≤m*p^(J m+1) := by
    dsimp [J,n]; rw [Nat.add_assoc,pow_add]; nlinarith [Nat.mul_le_mul_right (p^k) (hu m h)]
  choose B hB hd using fun (m : M) => prefix_num hb w hw m n (J m) (lower m m.property)
  let Z : ℤ := ∑ m ∈ M.attach, c m * (p:ℤ)^(E-j m)*B m
  have powers (m : M) : (E-j m)+J m=t := by have := hE m m.property; dsimp [J,t]; omega
  have dvd : (p:ℤ_[p])^t ∣ (Z:ℤ_[p])+(b:ℤ_[p])^n*value M c j E w := by
    dsimp only [Z,value]; rw [← sum_attach M (fun m => (c m:ℤ_[p])*w^m*(p:ℤ_[p])^(E-j m))]
    push_cast; rw [mul_sum,← sum_add_distrib]
    apply Finset.dvd_sum; intro m _
    have hh := mul_dvd_mul_left ((p:ℤ_[p])^(E-j m)) (hd m)
    rw [← pow_add,powers] at hh
    convert dvd_mul_of_dvd_right hh (c m:ℤ_[p]) using 1; ring
  have red := (projected_dvd t _).mpr dvd
  let π := PadicInt.toZModPow (p:=p) t
  change π _=0 at red
  simp only [map_add,map_mul,map_pow,map_natCast,map_intCast] at red
  have hcast : (Z:ZMod (p^t))=(A:ZMod (p^t))*(b:ZMod (p^t))^i := by
    change (A:ZMod (p^t))=π _ at hA
    rw [hA]; simp only [map_mul,map_neg,map_pow,map_natCast]
    dsimp only [n] at red; rw [pow_add (b:ZMod (p^t)) (u*p^k) i] at red
    linear_combination red
  have dvd' : ((p^t:ℕ):ℤ) ∣ Z-A*(b:ℤ)^i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by push_cast; exact hcast.symm)
  obtain ⟨z,hz⟩ := dvd'
  refine ⟨z,?_⟩
  have eqn : (Z:ℝ)/(p:ℝ)^t=(A:ℝ)*(b:ℝ)^i/(p:ℝ)^t+z := by
    have H : (Z:ℝ)-A*(b:ℝ)^i=(p:ℝ)^t*z := by exact_mod_cast hz
    field_simp; linarith
  change |(b:ℝ)^n*_ - _/(p:ℝ)^t-z| ≤ _
  rw [sub_sub,← eqn]
  have split : (Z:ℝ)/(p:ℝ)^t=∑ m ∈ M.attach, (c m:ℝ)*((B m:ℝ)/(p:ℝ)^(J m)) := by
    dsimp only [Z]; push_cast; rw [sum_div]
    apply sum_congr rfl; intro m _
    rw [← powers m,pow_add]; field_simp
  rw [split,scaled,← sum_attach M (fun m => (c m:ℝ)*((m:ℝ)*radixComponent b p m)),mul_sum,mul_sum, ← sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  rw [← sum_attach M (fun m => |(c m:ℝ)|),sum_div]
  apply sum_le_sum; intro m _
  rw [hB m]
  have err := weighted_tail_bound hb hp.one_lt (hm m m.property) (upper m m.property)
  rw [show ∀ x y s d f : ℝ, x*(y*(s*d))-s*(y*f)=s*y*(x*d-f) by intros; ring,abs_mul,abs_mul,abs_of_pos (sub_pos.mpr hpr)]
  apply (mul_le_mul_of_nonneg_left err (by positivity)).trans
  calc
    _ = |(c m:ℝ)|/(p:ℝ)^(J m) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      (pow_le_pow_right₀ hpr.le (by dsimp [J]; omega))

end CyclotomicCell
end NormalityChecker
