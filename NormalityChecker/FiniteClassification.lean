module

public import NormalityChecker.CellModel
public import NormalityChecker.Concentration
public import NormalityChecker.Dilation
public import NormalityChecker.OrderedComponents

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Last ternary insertion depth of component m at the unscaled grid point u. -/
def depth (u m : ℕ) := Nat.log 3 (u/m)

/-- The rational resonance coefficient on the cell from u·3^k to (u+1)·3^k. -/
def resonanceCoefficient (M : Finset ℕ) (a : ℕ → ℚ) (u : ℕ) : ℚ :=
  ∑ m ∈ M, (a m / m)*(-1)^m/(3:ℚ)^(depth u m)

noncomputable def componentSum (M : Finset ℕ) (a : ℕ → ℚ) : ℝ :=
  ∑ m ∈ M, (a m:ℝ)*component m

private lemma depths {m u : ℕ} (hm : 0<m) (hmu : m≤u) :
    m*3^(depth u m) ≤ u ∧ u+1 ≤ m*3^(depth u m+1) := by
  have hd : 0 < u/m := Nat.div_pos hmu hm
  constructor
  · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm).mp (Nat.pow_log_le_self _ hd.ne')
  · have hi := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_pow_succ_log_self (by decide : 1<3) (u/m))
    rw [mul_comm m]; exact hi

/-- Common denominator used to clear the weights a_m/m. -/
def weightDen (M : Finset ℕ) (a : ℕ → ℚ) := ∏ m ∈ M, (a m/m).den

def integerWeight (M : Finset ℕ) (a : ℕ → ℚ) (m : ℕ) : ℤ :=
  (weightDen M a / (a m/m).den : ℕ) * (a m/m).num

lemma weightDen_pos (M : Finset ℕ) (a : ℕ → ℚ) : 0<weightDen M a :=
  prod_pos (fun m _ => (a m/m).pos)

lemma integerWeight_spec (M : Finset ℕ) (a : ℕ → ℚ) :
    ∀ m ∈ M, (integerWeight M a m:ℚ)=weightDen M a*(a m/m) := by
  let w (m : ℕ) := a m/m
  let D := ∏ m ∈ M, (w m).den
  intro m hm
  have he := Nat.div_mul_cancel (dvd_prod_of_mem (fun m => (w m).den) hm)
  change (((D / (w m).den:ℕ)*(w m).num:ℤ):ℚ) = (D:ℚ)*w m
  conv_rhs => rw [← (w m).num_div_den]
  rw [Int.cast_mul,Int.cast_natCast]
  have he' : ((D/(w m).den:ℕ):ℚ)*(w m).den = D := by exact_mod_cast he
  rw [← he', mul_assoc]; congr 1; field_simp

private lemma clear_weights (M : Finset ℕ) (a : ℕ → ℚ) :
    ∃ (D : ℕ) (c : ℕ → ℤ), 0<D ∧ ∀ m∈M, (c m:ℚ)=D*(a m/m) :=
  ⟨_,_,weightDen_pos M a,integerWeight_spec M a⟩

private lemma scaled_sum {M : Finset ℕ} {a : ℕ → ℚ} {D : ℕ} {c : ℕ → ℤ}
    (hc : ∀ m ∈ M, (c m:ℚ)=D*(a m/m)) (hm : ∀ m ∈ M, 0<m) :
    (D:ℝ)*componentSum M a = ∑ m ∈ M, (c m:ℝ)*((m:ℝ)*component m) := by
  rw [componentSum,mul_sum]
  apply sum_congr rfl; intro m h
  have he : (c m:ℝ) = D*((a m:ℝ)/m) := by exact_mod_cast hc m h
  rw [he]; field_simp [Nat.ne_of_gt (hm m h)]

private lemma scaled_coefficient {M : Finset ℕ} {a : ℕ → ℚ} {D : ℕ} {c : ℕ → ℤ}
    (hc : ∀ m ∈ M, (c m:ℚ)=D*(a m/m)) (u : ℕ) :
    (cellNumerator M c (depth u) (M.sup (depth u)):ℚ) =
      (D:ℚ)*3^(M.sup (depth u))*resonanceCoefficient M a u := by
  rw [resonanceCoefficient,mul_sum]; unfold cellNumerator; push_cast
  apply sum_congr rfl; intro m h
  have hd := Finset.le_sup (f:=depth u) h
  have he : (3:ℚ)^(M.sup (depth u)) = 3^(M.sup (depth u)-depth u m)*3^(depth u m) := by
    rw [← pow_add,Nat.sub_add_cancel hd]
  rw [he,hc m h]; field_simp

/-- Sufficient direction for all finite rational combinations of positive components. -/
theorem normal_of_nonresonance {M : Finset ℕ} {a : ℕ → ℚ} {S : ℕ} (hS : 0<S)
    (hm : ∀ m ∈ M, 0<m ∧ m≤S)
    (H : ∀ u ∈ Ico S (3*S), resonanceCoefficient M a u ≠ 0) :
    NormalIn 2 (componentSum M a) := by
  obtain ⟨D,c,hD,hc⟩ := clear_weights M a
  have hF := scaled_sum hc (fun m h => (hm m h).1)
  apply binary_normal_of_dilated_fourier _ (2*D) (by positivity)
  intro h hh
  apply mean_zero_of_cells hS
  intro u hu
  have hdepth (m : ℕ) (h : m ∈ M) := depths (hm m h).1 ((hm m h).2.trans (mem_Ico.mp hu).1)
  have hC : cellNumerator M c (depth u) (M.sup (depth u)) ≠ 0 := by
    have he := scaled_coefficient hc u
    intro hz; rw [hz,Int.cast_zero] at he
    exact (mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) (H u hu)) he.symm
  have HH := cell_cancellation M c (depth u) (fun m h => (hm m h).1)
    (fun m h => (hdepth m h).1) (fun m h => (hdepth m h).2)
    (fun m h => Finset.le_sup (f:=depth u) h) hC h hh
  convert HH using 1
  funext n; rw [← hF,pow_succ]; push_cast; ring_nf

/-- A zero coefficient on one cell keeps all its shifts close to a fixed rational grid. -/
theorem not_normal_of_resonance {M : Finset ℕ} {a : ℕ → ℚ} {u : ℕ}
    (hm : ∀ m ∈ M, 0<m ∧ m≤u) (H : resonanceCoefficient M a u = 0) :
    ¬ NormalIn 2 (componentSum M a) := by
  obtain ⟨D,c,hD,hc⟩ := clear_weights M a
  have hF := scaled_sum hc (fun m h => (hm m h).1)
  have hdepth (m : ℕ) (h : m ∈ M) := depths (hm m h).1 (hm m h).2
  have hC : cellNumerator M c (depth u) (M.sup (depth u)) = 0 := by
    have he := scaled_coefficient hc u
    rw [H,mul_zero] at he; exact_mod_cast he
  apply not_normal_of_grid_cell (u:=u) hD (B:=∑ m ∈ M, |(c m:ℝ)| *2)
  intro k i hi
  obtain ⟨z,hz⟩ := cell_orbit_approx M c (depth u) (fun m h => (hm m h).1)
    (fun m h => (hdepth m h).1) (fun m h => (hdepth m h).2)
    (fun m h => Finset.le_sup (f:=depth u) h) k i hi
  refine ⟨z,?_⟩
  simpa only [hC,Int.cast_zero,zero_div,mul_zero,add_zero, ← hF,mul_left_comm,Nat.cast_ofNat] using hz

/-- A finite rational arithmetic decision criterion. S can be any positive
integer at least as large as every index in the sum. -/
theorem finite_normal_iff {M : Finset ℕ} {a : ℕ → ℚ} {S : ℕ} (hS : 0<S)
    (hm : ∀ m ∈ M, 0<m ∧ m≤S) :
    NormalIn 2 (componentSum M a) ↔
      ∀ u ∈ Ico S (3*S), resonanceCoefficient M a u ≠ 0 := by
  refine ⟨fun hn u hu hzero => ?_,normal_of_nonresonance hS hm⟩
  exact not_normal_of_resonance (fun m h => ⟨(hm m h).1, (hm m h).2.trans (mem_Ico.mp hu).1⟩) hzero hn

/-- Executable finite rational test. A coefficient function is only evaluated at indices in M. -/
def binaryNormalTest (M : Finset ℕ) (a : ℕ → ℚ) : Bool :=
  let S := max 1 (M.sup id)
  decide (((Ico S (3*S)).filter fun u => resonanceCoefficient M a u = 0) = ∅)

theorem binaryNormalTest_correct {M : Finset ℕ} (hm : ∀ m ∈ M, 0<m) (a : ℕ → ℚ) :
    binaryNormalTest M a = true ↔ NormalIn 2 (componentSum M a) := by
  rw [binaryNormalTest,decide_eq_true_eq,filter_eq_empty_iff]
  exact (finite_normal_iff (by omega : 0<max 1 (M.sup id)) (fun m h =>
    ⟨hm m h,(Finset.le_sup (f:=id) h).trans (le_max_right ..)⟩)).symm

/-- An unweighted three-component resonance. The failed cell can be checked by rational arithmetic. -/
theorem three_component_resonance :
    ¬ NormalIn 2 (componentSum {20,28,35} (fun _ => 1)) := by
  apply not_normal_of_resonance (u:=84) (by decide)
  norm_num [resonanceCoefficient,depth,Nat.log,Nat.log.go]

theorem component_binary_normal {m : ℕ} (hm : 0<m) : NormalIn 2 (component m) := by
  have H := normal_of_nonresonance (M:={m}) (a:=fun _ => 1) (S:=m) hm
    (by simpa) (by intro u _; simp [resonanceCoefficient,hm.ne'])
  simpa [componentSum] using H

/-- Every initial segment of the logarithmic decomposition is binary normal. -/
theorem ordered_sum_binary_normal {K : ℕ} (hK : 0<K) :
    NormalIn 2 (∑ m ∈ (Icc 1 K).filter (fun m => ¬ 3 ∣ m), component m) := by
  let M := (Icc 1 K).filter (fun m => ¬ 3 ∣ m)
  have hm (m : ℕ) (h : m ∈ M) : 0<m ∧ m≤K := mem_Icc.mp (mem_filter.mp h).1
  have H := normal_of_nonresonance (M:=M) (a:=fun _ => 1) hK hm (by
    intro u _ hzero
    let E := M.sup (depth u)
    let w (m : ℕ) := (-1:ℤ)^m*3^(E-depth u m)
    have hw (m : ℕ) : Odd (w m) := (Odd.pow (by decide : Odd (-1:ℤ))).mul ((by decide : Odd (3:ℤ)).pow)
    apply ordered_phase_ne_zero hK w hw
    change (∑ m ∈ M, (w m:ℚ)/m)=0
    rw [← mul_zero ((3:ℚ)^E), ← hzero,resonanceCoefficient,mul_sum]
    apply sum_congr rfl; intro m h
    have hd : depth u m ≤ E := Finset.le_sup h
    have he : (3:ℚ)^E = 3^(E-depth u m)*3^(depth u m) := by rw [← pow_add,Nat.sub_add_cancel hd]
    rw [he]; dsimp [w]; push_cast; field_simp)
  simpa [componentSum,M] using H

/-- Both directions of the proposed rational two-component milestone. -/
theorem two_component_normal_iff (a : ℚ) :
    NormalIn 2 (component 1 + (a:ℝ)*component 2) ↔ a ≠ 2/3 ∧ a ≠ 2 := by
  refine ⟨two_component_normal_necessary a, ?_⟩
  rintro ⟨h₁,h₂⟩
  let M : Finset ℕ := {1,2}
  let w (m : ℕ) := if m=1 then (1:ℚ) else a
  have h := normal_of_nonresonance (M:=M) (a:=w) (S:=2) (by decide)
    (by simp [M]) (by
      intro u hu; have h := mem_Ico.mp hu
      change 2 ≤ u ∧ u < 6 at h
      obtain ⟨hlo,hhi⟩ := h
      interval_cases u <;> norm_num [resonanceCoefficient,depth,M,w,Nat.log,Nat.log.go] <;>
        intro he <;> first | exact h₁ (by linarith) | exact h₂ (by linarith))
  simpa [componentSum,M,w] using h

end NormalityChecker
