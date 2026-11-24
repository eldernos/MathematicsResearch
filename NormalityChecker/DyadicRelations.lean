module

public import NormalityChecker.LogarithmBands

/-! Valuation reduction of finite dyadic logarithm identities. The primitive-divisor
input is local to the finite list, and can be discharged by a finite check or by Bang. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.DyadicRelations

/-- Odd-prime valuations of the cleared identity determine every coefficient except
those at 1 and 6. The hypothesis on largest strides is Bang's classical input. -/
theorem coefficients_of_valuations (a : ℕ →₀ ℤ) (pos : a 0=0)
    (balance : ∀ p : ℕ,p.Prime → p≠2 →
      ∑ k∈a.support, a k * (((2^k-1:ℕ).factorization p:ℕ):ℤ)=0)
    (primitive : ∀ k∈a.support,6<k → ∃ p : ℕ,p.Prime ∧ p≠2 ∧ p∣2^k-1 ∧
      ∀ j : ℕ,0<j → j<k → ¬p∣2^j-1) :
    (∀ k∈a.support,k∈({1,2,3,6}:Finset ℕ)) ∧ a 2= -2*a 6 ∧ a 3= -a 6 := by
  classical
  have cutoff : a.support ⊆ range 7 := by
    intro i hi; by_contra missing
    have lg : 6 < i := by simp only [mem_range,not_lt] at missing; omega
    let k := a.support.max' ⟨i,hi⟩
    have mem : k∈a.support := max'_mem ..
    have ik : i≤k := le_max' _ _ hi
    obtain ⟨p,pr,odd,dv,newp⟩ := primitive k mem (by omega)
    have ident := balance p pr odd
    rw [sum_eq_single_of_mem k mem] at ident
    · have pk : 1<(2:ℕ)^k := one_lt_pow₀ (by decide) (by omega)
      have val := (pr.dvd_iff_one_le_factorization (by omega : 2^k-1≠0)).mp dv
      exact (mul_ne_zero (Finsupp.mem_support_iff.mp mem) (by exact_mod_cast (show (2^k-1:ℕ).factorization p≠0 by omega))) ident
    · intro j hj ne
      have le : j≤k := le_max' _ _ hj
      have jp : 0<j := Nat.pos_of_ne_zero (fun zero => (Finsupp.mem_support_iff.mp hj) (zero ▸ pos))
      simp [Nat.factorization_eq_zero_of_not_dvd (newp j jp (lt_of_le_of_ne le ne))]
  have eqn (p : ℕ) (pr : p.Prime) (odd : p≠2) :
      ∑ k∈range 7,a k * (((2^k-1:ℕ).factorization p:ℕ):ℤ)=0 := by
    rw [←sum_subset cutoff]; exact balance p pr odd
    intro j _ absent
    simp [(Finsupp.notMem_support_iff.mp absent : a j=0)]
  have b31 := eqn 31 (by decide) (by decide)
  have b5 := eqn 5 (by decide) (by decide)
  have b7 := eqn 7 (by decide) (by decide)
  have b3 := eqn 3 (by decide) (by decide)
  norm_num [sum_range_succ, Nat.factorization] at b31 b5 b7 b3
  refine ⟨?_,by linarith,by linarith⟩
  intro k hk; have top := mem_range.mp (cutoff hk)
  have ne := Finsupp.mem_support_iff.mp hk
  interval_cases k <;> simp_all

/-- If the first partial sum survives, its prime band alone costs one half
and a finite set of missing later bands can never exhaust the other half. -/
theorem strict_half_of_first_band (Z : Finset ℕ) (positive : ∀ j∈Z,2≤j) :
    1/2 < 1-∑ j∈Z,(1/(j:ℝ)-1/((j:ℝ)+1)) := by
  let m := Z.sup id
  have sub : Z ⊆ Ico 2 (m+2) := fun j hj => mem_Ico.mpr ⟨positive j hj,by have := le_sup (f:=id) hj; change j≤m at this; omega⟩
  have le := sum_le_sum_of_subset_of_nonneg (f:=fun j : ℕ => 1/(j:ℝ)-1/((j:ℝ)+1)) sub (fun j h _ => by
    have p : (0:ℝ)<j := by exact_mod_cast (show 0<j by have := (mem_Ico.mp h).1; omega)
    exact sub_nonneg.mpr (one_div_le_one_div_of_le p (by linarith)))
  have tel : ∑ j∈Ico 2 (m+2),(1/(j:ℝ)-1/((j:ℝ)+1))=1/2-1/((m:ℝ)+2) := by
    induction m with
    | zero => norm_num
    | succ n ih =>
      rw [show n+1+2=(n+2)+1 by omega,sum_Ico_succ_top (by omega : 2≤n+2),ih]; push_cast; ring
  rw [tel] at le; linarith [show (0:ℝ)<1/((m:ℝ)+2) by positivity]


/-- The grouped coefficient of 1/(n*2^n) after reducing plus-strides to minus-strides. -/
def grouped (a : ℕ →₀ ℤ) (n : ℕ) : ℤ :=
  -∑ j∈a.support, if j∣n then (j:ℤ)*a j else 0

private lemma invariance (a : ℕ →₀ ℤ) (pos : a 0=0) :
    ∀ᶠ p : ℕ in atTop,p.Prime → ∀ n,grouped a (p*n)=grouped a n := by
  filter_upwards [eventually_gt_atTop (a.support.sup id)] with p h pr n
  unfold grouped; congr 1; apply sum_congr rfl; intro j hj
  have j0 : 0<j := Nat.pos_of_ne_zero (fun zero => Finsupp.mem_support_iff.mp hj (zero ▸ pos))
  have jp := (le_sup (f:=id) hj).trans_lt h
  have cop := (pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt j0 jp)).symm
  simp only [cop.dvd_mul_left]

private lemma grouped_form (a : ℕ →₀ ℤ)
    (supp : ∀ j∈a.support,j∈({1,2,3,6}:Finset ℕ)) (a2 : a 2= -2*a 6) (a3 : a 3= -a 6) (n : ℕ) :
    grouped a n= -a 1+a 6*StrideDenominatorRate.weight n := by
  classical
  unfold grouped
  rw [sum_subset (show a.support ⊆ {1,2,3,6} from supp) (fun j _ hj => by simp [Finsupp.notMem_support_iff.mp hj])]
  simp only [sum_insert (by decide : (1:ℕ)∉{2,3,6}),sum_insert (by decide : (2:ℕ)∉{3,6}),
    sum_insert (by decide : (3:ℕ)∉{6}),sum_singleton,one_dvd,ite_true,Nat.cast_ofNat,Nat.cast_one,a2,a3,StrideDenominatorRate.weight]
  split_ifs <;> ring

/-- Optimality for every finite valuation-balanced dyadic identity, with the
primitive divisors needed by its finite support supplied explicitly. -/
theorem optimal_rate (a : ℕ →₀ ℤ) (pos : a 0=0)
    (balance : ∀ p : ℕ,p.Prime → p≠2 →
      ∑ k∈a.support,a k * (((2^k-1:ℕ).factorization p:ℕ):ℤ)=0)
    (primitive : ∀ k∈a.support,6<k → ∃ p : ℕ,p.Prime ∧ p≠2 ∧ p∣2^k-1 ∧
      ∀ j : ℕ,0<j → j<k → ¬p∣2^j-1)
    (Y : ℕ → ℚ) (base : Y 0=0)
    (step : ∀ n,Y (n+1)=2*Y n+(grouped a (n+1):ℚ)/(n+1))
    (Z : Finset ℕ) (zeros : ∀ v,v∈Z ↔ 0<v ∧ Y v=0) :
    ∃ R : ℝ, Tendsto (fun n : ℕ => Real.log (Y n).den/n) atTop (𝓝 R) ∧
      1/2≤R ∧ (R=1/2 ↔ a 1=0) := by
  let R := 1-∑ v∈Z,(1/(v:ℝ)-1/((v:ℝ)+1))
  refine ⟨R,LogarithmBands.denominator_rate Y _ base step (invariance a pos) Z zeros,?_⟩
  obtain ⟨support,a2,a3⟩ := coefficients_of_valuations a pos balance primitive
  have form := grouped_form a support a2 a3
  by_cases no : a 1=0
  · have terms (n : ℕ) : Y n=(a 6:ℚ)*twoStridePrefix n := by
      induction n with
      | zero => simp [base,twoStridePrefix,stridedPrefix]
      | succ n ih => rw [step,form,no,StrideDenominatorRate.step,ih]; push_cast; ring
    have unit : a 6≠0 := by
      intro h
      let j := Z.sup id+1
      have mem := (zeros j).mpr ⟨Nat.succ_pos _,by simp [terms,h]⟩
      have le : j≤Z.sup id := Finset.le_sup (f:=id) mem
      dsimp [j] at le; omega
    have eqn : Z={1} := by
      ext n; rw [zeros,mem_singleton]
      constructor
      · rintro ⟨np,z⟩; by_contra bad
        rw [terms] at z
        exact (mul_ne_zero (by exact_mod_cast unit : (a 6:ℚ)≠0) (StrideDenominatorRate.prefix_pos (by omega : 2≤n)).ne') z
      · rintro rfl; exact ⟨by decide,by rw [terms]; norm_num [twoStridePrefix,stridedPrefix]⟩
    have v : R=1/2 := by norm_num [R,eqn]
    exact ⟨v.ge,iff_of_true v no⟩
  · have one : Y 1≠0 := by
      have v := step 0
      simp [base,form,StrideDenominatorRate.weight] at v
      simpa [v] using no
    have high := strict_half_of_first_band Z (fun j hj => by
      obtain ⟨jp,zero⟩ := (zeros j).mp hj
      have ne : j≠1 := fun e => one (e ▸ zero)
      omega)
    exact ⟨high.le,iff_of_false high.ne' no⟩

end NormalityChecker.DyadicRelations
