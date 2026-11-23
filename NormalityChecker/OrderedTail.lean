module

public import NormalityChecker.FiniteClassification
public import NormalityChecker.FourierTest

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

noncomputable def orderedPrefix (K : ℕ) : ℝ :=
  ∑ m ∈ (Icc 1 K).filter (fun m => ¬ 3 ∣ m), component m

private noncomputable def term (m j : ℕ) := (1/2:ℝ)^(m*3^j)/((m:ℝ)*3^j)

private lemma term_le (m j : ℕ) : term m j ≤ ((1/2:ℝ)^m/m)*(1/3:ℝ)^j := by
  have he := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Nat.le_mul_of_pos_right m (by positivity : 0<3^j))
  dsimp only [term]; rw [one_div_pow (3:ℝ)]; rw [show (1/2:ℝ)^m/m*(1/(3:ℝ)^j) = (1/2:ℝ)^m/(m*3^j) by ring]
  exact div_le_div_of_nonneg_right he (by positivity)

private lemma term_summable (m : ℕ) : Summable (term m) :=
  .of_nonneg_of_le (fun j => by unfold term; positivity) (term_le m)
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)<1)).mul_left _)

private lemma component_bounds {m : ℕ} (hm : 0<m) :
    (1/2:ℝ)^m/m ≤ component m ∧ component m ≤ 2*(1/2:ℝ)^m/m := by
  let g := term m
  have hs := term_summable m
  have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)<1)).mul_left ((1/2:ℝ)^m/m)
  change _ ≤ ∑' j, g j ∧ (∑' j, g j) ≤ _
  refine ⟨?_,(hs.tsum_le_tsum (term_le m) hg).trans ?_⟩
  · simpa [g,term] using hs.le_tsum 0 (fun j _ => by unfold term; positivity)
  · rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num : (1/3:ℝ)<1)]
    have h : 0 ≤ (1/2:ℝ)^m/m := by positivity
    norm_num; linarith [show 2*(1/2:ℝ)^m/m = 2*((1/2:ℝ)^m/m) by ring]

private noncomputable def activeComponent (m : ℕ) := if ¬3∣m then component m else 0

private lemma active_nonneg (i : ℕ) : 0≤activeComponent i := by
  by_cases h : 3∣i
  · simp [activeComponent,h]
  · simp only [activeComponent,h,not_false_eq_true,ite_true,component]
    exact tsum_nonneg (fun j => by positivity)

private lemma ordered_tail_sum (K : ℕ) :
    Summable (fun i => activeComponent (i+(K+1))) ∧
    Real.log 2-orderedPrefix K = ∑' i, activeComponent (i+(K+1)) := by
  classical
  have hs : HasSum activeComponent (Real.log 2) := by
    apply ((hasSum_subtype_iff_indicator (s:={m : ℕ | ¬3∣m}) (f:=component)).mp hasSum_components_logTwo).congr_fun
    intro i; simp [activeComponent,Set.indicator_apply]
  have he : orderedPrefix K = ∑ m ∈ range (K+1), activeComponent m := by
    unfold orderedPrefix
    have subsets : (Icc 1 K).filter (fun m => ¬3∣m) = (range (K+1)).filter (fun m => ¬3∣m) := by
      ext m; simp only [mem_filter,mem_Icc,mem_range]; omega
    rw [subsets,sum_filter]; rfl
  have split := hs.summable.sum_add_tsum_nat_add (K+1)
  rw [hs.tsum_eq, ← he] at split
  exact ⟨(summable_nat_add_iff (K+1)).mpr hs.summable,by linarith⟩

/-- Two-sided bounds on the total omitted mass, with constants independent of K. -/
theorem ordered_tail_bounds (K : ℕ) :
    (1/2:ℝ)^(K+2)/(K+2) ≤ Real.log 2-orderedPrefix K ∧
      Real.log 2-orderedPrefix K ≤ 2*(1/2:ℝ)^K/(K+1) := by
  obtain ⟨ts,he⟩ := ordered_tail_sum K
  rw [he]
  constructor
  · obtain ⟨i,hi,hdiv⟩ : ∃ i : ℕ, i≤1 ∧ ¬3∣i+(K+1) := by
      by_cases h : 3∣K+1
      · exact ⟨1,by decide,by omega⟩
      · exact ⟨0,by decide,by simpa using h⟩
    let m := i+(K+1)
    have hm : 0<m := by dsimp [m]; omega
    have htop : m≤K+2 := by dsimp [m]; omega
    calc
      _ ≤ (1/2:ℝ)^m/m := by
        apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) htop) (by positivity)
        exact_mod_cast htop
      _ ≤ component m := (component_bounds hm).1
      _ = activeComponent (i+(K+1)) := by simp [m,activeComponent,hdiv]
      _ ≤ _ := ts.le_tsum i (fun j _ => active_nonneg _)
  · let C := 2*(1/2:ℝ)^(K+1)/(K+1)
    have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left C
    have h (i : ℕ) : activeComponent (i+(K+1)) ≤ C*(1/2:ℝ)^i := by
      by_cases hi : 3∣i+(K+1)
      · simp [activeComponent,hi]; dsimp [C]; positivity
      · simp only [activeComponent,hi,not_false_eq_true,ite_true]
        apply (component_bounds (m:=i+(K+1)) (by omega)).2.trans
        rw [pow_add]; push_cast
        have H : (K:ℝ)+1 ≤ i+(K+1) := by linarith [Nat.cast_nonneg (α:=ℝ) i]
        apply (div_le_div_of_nonneg_left (by positivity) (by positivity) H).trans_eq
        dsimp [C]; ring
    apply (ts.tsum_le_tsum h hg).trans_eq
    rw [tsum_mul_left,tsum_geometric_two]; dsimp [C]; rw [pow_succ]; ring

theorem ordered_shift_bounds (n K : ℕ) :
    let B := (2:ℝ)^n/(((K:ℝ)+1)*2^K)
    let E := (2:ℝ)^n*(Real.log 2-orderedPrefix K)
    B ≤ 8*E ∧ E ≤ 2*B := by
  let B := (2:ℝ)^n/(((K:ℝ)+1)*2^K)
  let E := (2:ℝ)^n*(Real.log 2-orderedPrefix K)
  have lo : B ≤ 8*E := by
    obtain ⟨h,_⟩ := ordered_tail_bounds K
    have H := mul_le_mul_of_nonneg_left h (by positivity : 0≤(2:ℝ)^n)
    apply (le_trans _ (mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤8)))
    dsimp [B]; rw [one_div_pow,pow_add]; norm_num
    field_simp
    nlinarith [mul_nonneg (show 0≤(2:ℝ)^n*(2:ℝ)^K by positivity) (Nat.cast_nonneg (α:=ℝ) K)]
  have hi : E ≤ 2*B := by
    apply (mul_le_mul_of_nonneg_left (ordered_tail_bounds K).2 (by positivity : 0≤(2:ℝ)^n)).trans_eq
    dsimp [B]; rw [one_div_pow]; field_simp
  exact ⟨lo,hi⟩

/-- Exact accuracy criterion for using a growing family of normal finite sums
as an unwrapped approximation at growing digit positions. -/
theorem ordered_shift_error_iff (n K : ℕ → ℕ) :
    Tendsto (fun i => (2:ℝ)^(n i)*(Real.log 2-orderedPrefix (K i))) atTop (𝓝 0) ↔
      Tendsto (fun i => (2:ℝ)^(n i)/((K i+1:ℝ)*2^(K i))) atTop (𝓝 0) := by
  let B (i : ℕ) := (2:ℝ)^(n i)/((K i+1:ℝ)*2^(K i))
  let E (i : ℕ) := (2:ℝ)^(n i)*(Real.log 2-orderedPrefix (K i))
  have lo (i : ℕ) : B i ≤ 8*E i := (ordered_shift_bounds (n i) (K i)).1
  have hi (i : ℕ) : E i ≤ 2*B i := (ordered_shift_bounds (n i) (K i)).2
  change Tendsto E atTop (𝓝 0) ↔ Tendsto B atTop (𝓝 0)
  constructor
  · intro h; exact squeeze_zero (fun i => by dsimp [B]; positivity) lo (by simpa using (tendsto_const_nhds (x:=(8:ℝ))).mul h)
  · intro h
    apply squeeze_zero _ hi (by simpa using (tendsto_const_nhds (x:=(2:ℝ))).mul h)
    intro i
    have : 0≤B i := by dsimp [B]; positivity
    linarith [lo i]

/-- At this critical shift the omitted tail stays separated even modulo one. -/
theorem ordered_critical_shift {K : ℕ} (hK : 2≤K) :
    let n := K-2+Nat.log 2 (K+1)
    let E := (2:ℝ)^n*(Real.log 2-orderedPrefix K)
    1/64 < E ∧ E ≤ 1/2 ∧ ∀ z : ℤ, 1/64 < |E-z| := by
  let k := Nat.log 2 (K+1)
  let n := K-2+k
  let E := (2:ℝ)^n*(Real.log 2-orderedPrefix K)
  let B := (2:ℝ)^n/(((K:ℝ)+1)*2^K)
  obtain ⟨hlo,hhi⟩ := ordered_shift_bounds n K
  have e : B=(2:ℝ)^k/(4*(K+1)) := by
    have eqn : n+2=K+k := by dsimp [n]; omega
    have pw := congrArg (fun j : ℕ => (2:ℝ)^j) eqn
    simp only [pow_add] at pw
    dsimp [B]; field_simp; linarith
  have low : (1:ℝ)/8 < B := by
    rw [e,lt_div_iff₀ (by positivity)]
    have hx : K+1 < 2^(k+1) := Nat.lt_pow_succ_log_self (by decide) _
    have hr : (K:ℝ)+1 < 2^k*2 := by exact_mod_cast (pow_succ 2 k ▸ hx)
    linarith
  have high : B≤1/4 := by
    rw [e,div_le_iff₀ (by positivity)]
    have hx : 2^k≤K+1 := Nat.pow_log_le_self _ (by omega)
    have hr : (2:ℝ)^k≤K+1 := by exact_mod_cast hx
    linarith
  change B ≤ 8*E at hlo
  change E ≤ 2*B at hhi
  have bounds : 1/64<E ∧ E≤1/2 := ⟨by linarith,by linarith⟩
  refine ⟨bounds.1,bounds.2,fun z => ?_⟩
  by_cases h : z≤0
  · have hr : (z:ℝ)≤0 := by exact_mod_cast h
    exact (show 1/64<E-z by linarith [bounds.1]).trans_le (le_abs_self _)
  · have hr : (1:ℝ)≤z := by exact_mod_cast (show 1≤z by omega)
    exact (show 1/64< -(E-z) by linarith [bounds.2]).trans_le (neg_le_abs _)

/-- Leading coefficient of the omitted tail, indexed by the cutoff modulo three. -/
def tailCoefficient (K : ℕ) : ℚ :=
  match K % 3 with
  | 0 => 6/7
  | 1 => 5/7
  | _ => 3/7

private noncomputable def digitWeight (i : ℕ) : ℝ := (1/2:ℝ)^(i+1)

private noncomputable def activeWeight (K i : ℕ) : ℝ :=
  if 3∣i+(K+1) then 0 else digitWeight i

private lemma weights_sum (K : ℕ) : HasSum (activeWeight K) (tailCoefficient K : ℝ) := by
  have hw : Summable digitWeight := by
    change Summable (fun i : ℕ => (1/2:ℝ)^(i+1))
    simpa [digitWeight,pow_succ] using (summable_geometric_two.mul_right (1/2:ℝ))
  have hs : Summable (activeWeight K) := .of_nonneg_of_le
    (fun i => by unfold activeWeight digitWeight; split_ifs <;> positivity)
    (fun i => by unfold activeWeight; split_ifs <;> simp [digitWeight]) hw
  let S := ∑' i, activeWeight K i
  have step (i : ℕ) : activeWeight K (i+3) = (1/8)*activeWeight K i := by
    have h : 3∣i+3+(K+1) ↔ 3∣i+(K+1) := by omega
    simp only [activeWeight,h]; split_ifs
    · ring
    · dsimp [digitWeight]; rw [show i+3+1=(i+1)+3 by omega,pow_add]; ring
  have split := hs.sum_add_tsum_nat_add 3
  simp_rw [step] at split
  rw [tsum_mul_left] at split
  change (∑ i ∈ range 3, activeWeight K i) + 1/8*S=S at split
  suffices e : S=(tailCoefficient K:ℝ) by exact e ▸ hs.hasSum
  have F : (∑ i ∈ range 3, activeWeight K i) = (7/8)*(tailCoefficient K : ℝ) := by
    simp only [sum_range_succ,sum_range_zero,zero_add,activeWeight,digitWeight]
    have cases : K%3=0 ∨ K%3=1 ∨ K%3=2 := by omega
    rcases cases with h | h | h <;> simp [tailCoefficient,h] <;> split_ifs <;> first | omega | norm_num
  rw [F] at split; linarith

private lemma component_excess {m : ℕ} (hm : 0<m) :
    component m-(1/2:ℝ)^m/m ≤ (1/2:ℝ)^m/(m:ℝ)^2 := by
  have split := (term_summable m).sum_add_tsum_nat_add 1
  have next (i : ℕ) : term m (i+1) = term (3*m) i := by
    dsimp [term]; rw [pow_succ 3 i,pow_succ (3:ℝ) i]; push_cast
    rw [show m*(3^i*3)=3*m*3^i by ring]; ring
  simp_rw [next] at split
  have eqn : (1/2:ℝ)^m/m + component (3*m) = component m := by
    simpa [term,component] using split
  rw [← eqn,add_sub_cancel_left]
  apply (component_bounds (m:=3*m) (by omega)).2.trans
  have hp : (m:ℝ) ≤ 2^(2*m) := by
    exact_mod_cast (show m < 2^m from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega : m≤2*m))
  rw [show 3*m=m+2*m by omega,pow_add]
  simp only [one_div_pow]
  push_cast
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤ (m:ℝ)*2^m by positivity),
    show (0:ℝ)≤ (m:ℝ)*2^m*2^(2*m) by positivity]

/-- The three possible leading terms have an explicit uniform error. -/
theorem ordered_tail_profile (K : ℕ) :
    |((K:ℝ)+1)*2^K*(Real.log 2-orderedPrefix K) - (tailCoefficient K:ℝ)| ≤ 1/((K:ℝ)+1) := by
  let A := (K:ℝ)+1
  let C := A*2^K
  let f (i : ℕ) := C*activeComponent (i+(K+1))
  let g := activeWeight K
  obtain ⟨hs,he⟩ := ordered_tail_sum K
  have hf : HasSum f (C*(Real.log 2-orderedPrefix K)) := he ▸ hs.hasSum.mul_left C
  have hg : HasSum g (tailCoefficient K:ℝ) := weights_sum K
  have block (i : ℕ) :
      -(i*digitWeight i/A) ≤ f i-g i ∧ f i-g i ≤ digitWeight i/A := by
    let m := i+(K+1)
    have hm : 0<m := by dsimp [m]; omega
    have hm' : (m:ℝ) = i+A := by dsimp [m,A]; push_cast; ring
    have hA : 0<A := by dsimp [A]; positivity
    have hC : 0<C := by dsimp [C]; positivity
    have hW : 0<digitWeight i := by dsimp [digitWeight]; positivity
    by_cases h : 3∣m
    · simp [f,g,activeComponent,activeWeight,show 3∣i+(K+1) from h, hW.le, div_nonneg, mul_nonneg,hA.le]
    change _ ≤ C*activeComponent m-activeWeight K i ∧ C*activeComponent m-activeWeight K i ≤ _
    simp only [activeComponent,h,not_false_eq_true,ite_true,activeWeight,show ¬3∣i+(K+1) from h,ite_false]
    have ew : C*(1/2:ℝ)^m = A*digitWeight i := by
      dsimp [C,m,digitWeight]; rw [show i+(K+1)=K+(i+1) by omega,pow_add,one_div_pow]; field_simp
    have h₀ := mul_le_mul_of_nonneg_left (component_bounds hm).1 hC.le
    have h₁ := mul_le_mul_of_nonneg_left (component_excess hm) hC.le
    rw [← mul_div_assoc,ew] at h₀
    rw [mul_sub,← mul_div_assoc,← mul_div_assoc,ew] at h₁
    have hmA : A ≤ (m:ℝ) := by rw [hm']; linarith [Nat.cast_nonneg (α:=ℝ) i]
    have hlow : -(i*digitWeight i/A) ≤ A*digitWeight i/m - digitWeight i := by
      have e : A*digitWeight i/m-digitWeight i = -(i*digitWeight i/m) := by field_simp; rw [hm']; ring
      rw [e,neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) hA hmA
    have hbase : A*digitWeight i/m ≤ digitWeight i := (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hmA hW.le)
    have hrem : A*digitWeight i/(m:ℝ)^2 ≤ digitWeight i/A := by
      rw [div_le_div_iff₀ (by positivity) hA]
      nlinarith [mul_le_mul_of_nonneg_right (sq_le_sq₀ hA.le (by positivity) |>.mpr hmA) hW.le]
    constructor <;> linarith
  have geom : HasSum digitWeight 1 := by
    change HasSum (fun i : ℕ => (1/2:ℝ)^(i+1)) 1
    simpa [digitWeight,pow_succ] using (hasSum_geometric_two.mul_right (1/2:ℝ))
  have moment : HasSum (fun i : ℕ => i*digitWeight i) 1 := by
    have H := (hasSum_coe_mul_geometric_of_norm_lt_one (r:=(1/2:ℝ)) (by norm_num)).mul_right (1/2:ℝ)
    convert H using 1
    · funext i; dsimp [digitWeight]; rw [pow_succ]; ring
    · norm_num
  apply abs_le.mpr
  exact ⟨hasSum_le (fun i => (block i).1) (moment.div_const A |>.neg) (hf.sub hg),
    hasSum_le (fun i => (block i).2) (hf.sub hg) (geom.div_const A)⟩

/-- Correct the leading truncation error by a rational depending only on K. -/
def tailCorrection (K : ℕ) : ℚ := tailCoefficient K / (((K:ℚ)+1)*2^K)

noncomputable def correctedPrefix (K : ℕ) : ℝ := orderedPrefix K + tailCorrection K

theorem corrected_shift_bound (K n : ℕ) :
    |(2:ℝ)^n*(Real.log 2-correctedPrefix K)| ≤
      (2:ℝ)^n/(((K:ℝ)+1)^2*2^K) := by
  let A := (K:ℝ)+1
  let C := A*2^K
  have hA : 0<A := by dsimp [A]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  have eqn : Real.log 2-correctedPrefix K =
      (C*(Real.log 2-orderedPrefix K)-(tailCoefficient K:ℝ))/C := by
    dsimp [correctedPrefix,tailCorrection,C,A]; push_cast; field_simp; ring
  rw [eqn,abs_mul,abs_div,abs_of_pos hC,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) n)]
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (ordered_tail_profile K) hC.le)
    (pow_nonneg (by norm_num : (0:ℝ)≤2) n)).trans_eq
  dsimp [C,A]; field_simp

theorem corrected_critical_shift (K : ℕ) :
    |(2:ℝ)^(K+Nat.log 2 (K+1))*(Real.log 2-correctedPrefix K)| ≤ 1/((K:ℝ)+1) := by
  apply (corrected_shift_bound ..).trans
  rw [pow_add]
  have h : (2:ℝ)^(Nat.log 2 (K+1)) ≤ K+1 := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.succ_ne_zero K)
  have hp : (0:ℝ)<2^K := by positivity
  have hk : (0:ℝ)<K+1 := by positivity
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hp.le hk.le)]

theorem correctedPrefix_normal {K : ℕ} (hK : 0<K) : NormalIn 2 (correctedPrefix K) := by
  exact (normal_add_rat_iff (by decide) (orderedPrefix K) (tailCorrection K)).mpr (ordered_sum_binary_normal hK)

end NormalityChecker
