module

public import NormalityChecker.BinaryDiscrepancy

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- The Kempner number, with ones at the binary positions 1, 2, 4, 8, ... . -/
noncomputable def kempner : ℝ := ∑' j : ℕ, (1/2:ℝ)^(2^j : ℕ)

private lemma kempner_summable : Summable (fun j : ℕ => (1/2:ℝ)^(2^j : ℕ)) :=
  .of_nonneg_of_le (fun _ => by positivity) (fun j => pow_le_pow_of_le_one (by norm_num)
    (by norm_num : (1/2:ℝ)≤1) (show j≤2^j from Nat.lt_two_pow_self.le)) summable_geometric_two

/-- The next power of two gives a lower bound on the tail; subsequent
exponents are at least two places apart. -/
private theorem kempner_shift_bounds {n : ℕ} (hn : 0<n) :
    let s := 2^(Nat.log 2 n+1)
    (1/2:ℝ)^(s-n) ≤ shift 2 kempner n ∧ shift 2 kempner n ≤ (4/3)*(1/2:ℝ)^(s-n) := by
  let k := Nat.log 2 n+1
  let s := 2^k
  have hs : n<s := Nat.lt_pow_succ_log_self (by decide) n
  let f (j : ℕ) := (2:ℝ)^n*(1/2:ℝ)^(2^j : ℕ)
  let tail := ∑' i : ℕ, f (i+k)
  have hf : Summable f := kempner_summable.mul_left _
  have ht : Summable (fun i => f (i+k)) := (summable_nat_add_iff k).mpr hf
  have cut := hf.sum_add_tsum_nat_add k
  have approx : (2:ℝ)^n*kempner=((∑ j∈range k,(2:ℤ)^(n-2^j)):ℤ)+tail := by
    have start (j : ℕ) (hj : j∈range k) : 2^j≤n := by
      have le : j≤Nat.log 2 n := by simpa [k] using mem_range.mp hj
      exact (Nat.pow_le_pow_right (by decide) le).trans (Nat.pow_log_le_self _ hn.ne')
    change (2:ℝ)^n * (∑' j : ℕ, (1/2:ℝ)^(2^j : ℕ)) = _
    rw [← tsum_mul_left]
    change (∑' j, f j)=_
    rw [← cut]; push_cast; congr 1; apply sum_congr rfl; intro j hj
    dsimp [f]; rw [one_div_pow,mul_one_div,eq_comm,pow_sub₀ _ (by norm_num) (start j hj),div_eq_mul_inv]
  have term (i : ℕ) : f (i+k)=(1/2:ℝ)^(2^(i+k)-n) := by
    have le : n≤2^(i+k) := hs.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    dsimp [f]; rw [one_div_pow,one_div_pow,pow_sub₀ _ (by norm_num) le]; field_simp
  let a := (1/2:ℝ)^(s-n)
  have major (i : ℕ) : f (i+k)≤a*(1/4:ℝ)^i := by
    have expBound (j : ℕ) : s+2*j≤2^(j+k) := by
      induction j with
      | zero => simp [s]
      | succ j ih =>
        have hs₂ : 2≤s := by dsimp [s,k]; rw [pow_succ']; have := pow_pos (by decide : 0<2) (Nat.log 2 n); omega
        rw [Nat.succ_add,pow_succ]; omega
    rw [term]; dsimp [a]
    rw [show (1/4:ℝ)=(1/2)^2 by norm_num,← pow_mul,← pow_add]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by have := expBound i; omega)
  have bounds : a≤tail ∧ tail≤(4/3)*a := by
    constructor
    · have H := ht.le_tsum 0 (fun i _ => by dsimp [f]; positivity)
      rwa [term,zero_add] at H
    · apply (ht.tsum_le_tsum major ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left a)).trans_eq
      rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  have ha : a≤1/2 := by
    simpa [a] using (pow_le_pow_of_le_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num) (by omega : 1≤s-n))
  have hfrac : shift 2 kempner n=tail := by
    change Int.fract ((2:ℝ)^n*kempner)=_
    rw [approx,Int.fract_intCast_add,Int.fract_eq_self.mpr ⟨(by dsimp [a]; positivity : 0≤a).trans bounds.1,by linarith [bounds.2]⟩]
  rw [hfrac]; exact bounds

/-- The sparse example has much stronger dyadic separation than needed
for the logarithmic count, yet its upper limiting discrepancy equals one. -/
theorem kempner_dyadic_separation {n : ℕ} (hn : 2≤n) (z : ℤ) :
    (1/2:ℝ)^n ≤ |(2:ℝ)^n*kempner-z| := by
  let s := 2^(Nat.log 2 n+1)
  obtain ⟨lo,hi⟩ := kempner_shift_bounds (show 0<n by omega)
  have hs : n<s := Nat.lt_pow_succ_log_self (by decide) n
  have hs' : s≤2*n := by dsimp [s]; rw [pow_succ']; exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))
  have delta := pow_le_pow_of_le_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num) (by omega : s-n≤n)
  have ha : (1/2:ℝ)^(s-n)≤1/2 := by simpa using (pow_le_pow_of_le_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num) (by omega : 1≤s-n))
  let v := (2:ℝ)^n*kempner
  change _≤Int.fract v at lo
  change Int.fract v≤(4/3)*(1/2:ℝ)^(s-n) at hi
  have hn' := pow_le_pow_of_le_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num) hn
  have eqn := Int.fract_add_floor v
  by_cases h : z≤⌊v⌋
  · apply le_trans _ (le_abs_self _)
    change _≤v-z; have hz : (z:ℝ)≤⌊v⌋ := by exact_mod_cast h
    change (1/2:ℝ)^(s-n)≤Int.fract v at lo
    linarith
  · apply le_trans _ (neg_le_abs _)
    have hh : ⌊v⌋+1≤z := by omega
    have hz : (⌊v⌋:ℝ)+1≤z := by exact_mod_cast hh
    change _≤ -(v-z); linarith

theorem kempner_discrepancy_one : asymptoticDiscrepancy kempner=1 := by
  classical
  let T (n : ℕ) := 1/4≤shift 2 kempner n ∧ shift 2 kempner n<3/4
  have count (k : ℕ) : ((range (2^k)).filter T).card ≤ 1+2*k := by
    let B (j : ℕ) : Finset ℕ := {2^(j+1)-1,2^(j+1)-2}
    have hs : (range (2^k)).filter T ⊆ {0} ∪ (range k).biUnion B := by
      intro n h
      obtain ⟨hn,hT⟩ := mem_filter.mp h
      by_cases h : n=0
      · exact mem_union_left _ (by simpa using h)
      have hn' := mem_range.mp hn
      let j := Nat.log 2 n
      have hj : j<k := (Nat.log_lt_iff_lt_pow (by decide) h).mpr hn'
      have H := (kempner_shift_bounds (Nat.pos_of_ne_zero h)).2
      have hgap : 2^(j+1)-n<3 := by
        by_contra! hg
        have le := pow_le_pow_of_le_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num) hg
        change shift 2 kempner n≤(4/3)*(1/2:ℝ)^(2^(j+1)-n) at H
        change 1/4≤shift 2 kempner n ∧ _ at hT
        linarith [hT.1]
      have ht : n<2^(j+1) := Nat.lt_pow_succ_log_self (by decide) n
      apply mem_union_right _ (mem_biUnion.mpr ⟨j,mem_range.mpr hj,?_⟩)
      dsimp [B]; simp only [mem_insert,mem_singleton]; omega
    have C : ∑ j ∈ range k, (B j).card ≤ 2*k := by
      have h (j : ℕ) : (B j).card≤2 := Finset.card_le_two
      simpa [mul_comm] using (sum_le_sum (s:=range k) (fun j _ => h j))
    have hh := (card_le_card hs).trans (card_union_le ..)
    have HH := card_biUnion_le (s:=range k) (t:=B)
    simp only [card_singleton] at hh; omega
  have zero : Tendsto (fun k : ℕ => transitionFrequency kempner (2^k)) atTop (𝓝 0) := by
    apply squeeze_zero (g:=fun k : ℕ => (1+2*(k:ℝ))/(2:ℝ)^k) (fun k => (frequency_bounds _ _ _ _).1)
    · intro k; change ((range (2^k)).filter T).card/((2^k:ℕ):ℝ)≤_
      push_cast
      exact div_le_div_of_nonneg_right (by exact_mod_cast count k) (by positivity)
    · have H := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul 2
      have hi := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
      simpa [add_div,mul_div_assoc,one_div,Function.comp_def] using hi.add H
  apply le_antisymm (limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (discrepancy_bounds _ N).1))
    (.of_forall (fun N => (discrepancy_bounds _ N).2)))
  apply le_of_not_gt; intro h
  have hpos := (discrepancy_lt_one_iff_transitions kempner).mp h
  have E := eventually_lt_of_lt_liminf (half_lt_self hpos)
    (isBoundedUnder_of_eventually_ge (.of_forall (fun n => (frequency_bounds (shift 2 kempner) (1/4) (3/4) n).1)))
  have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  obtain ⟨k,h₁,h₂⟩ := ((grow.eventually E).and (zero.eventually_lt_const (half_pos hpos))).exists
  exact h₁.not_gt h₂

end NormalityChecker
