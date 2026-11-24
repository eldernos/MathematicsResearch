module

public import NormalityChecker.ArithmeticCertificate

/-! Real tails for radix expansions with an arbitrary injective insertion schedule. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Bounded nonnegative coefficients tending to zero at late insertions give a
vanishing shifted tail. The schedule may have gaps of any length. -/
theorem indexed_shift_error {ι : Type*} {b : ℕ} (hb : 2≤b) (g : ι → ℕ) (inj : Function.Injective g)
    (a : ι → ℚ) (nonneg : ∀ i, 0≤a i) (bounded : ∀ i, a i≤1)
    (small : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ i, N≤g i → (a i:ℝ)≤ε)
    (I : ℕ → Finset ι) (mem : ∀ n i, i∈I n ↔ g i≤n) :
    Tendsto (fun n => (b:ℝ)^n*(∑' i, (a i:ℝ)/(b:ℝ)^(g i)) -
        (((b:ℚ)^n * ∑ i∈I n, a i/(b:ℚ)^(g i):ℚ):ℝ)) atTop (𝓝 0) := by
  classical
  let A := Function.extend g (fun i => (a i:ℝ)) (fun _ => 0)
  let f (m : ℕ) := A m/(b:ℝ)^m
  have hit (i : ι) : A (g i)=(a i:ℝ) := inj.extend_apply ..
  have outside {m : ℕ} (h : m ∉ Set.range g) : A m=0 := Function.extend_apply' _ _ _ h
  have bounds (m : ℕ) : 0≤A m ∧ A m≤1 := by
    by_cases h : m ∈ Set.range g
    · obtain ⟨i,rfl⟩ := h; rw [hit]; exact_mod_cast And.intro (nonneg i) (bounded i)
    · rw [outside h]; norm_num
  have br : (2:ℝ)≤b := by exact_mod_cast hb
  have bp : (0:ℝ)<b := by linarith
  have hg := summable_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)
  have summ : Summable f := Summable.of_nonneg_of_le (fun m => div_nonneg (bounds m).1 (by positivity)) (fun m => by
    dsimp [f]; rw [one_div_pow]; apply div_le_div₀ (by norm_num) (bounds m).2 (by positivity) (pow_le_pow_left₀ (by norm_num) br m)) hg
  have H := (inj.hasSum_iff (f:=f) (fun m h => by simp [f,outside h])).mpr summ.hasSum
  have total : (∑' i, (a i:ℝ)/(b:ℝ)^g i)=∑' m,f m := by simpa [Function.comp_def,f,hit] using H.tsum_eq
  have trunc (n : ℕ) : ∑ i∈I n,(a i:ℝ)/(b:ℝ)^g i = ∑ m∈range (n+1),f m := by
    have eqn : (I n).image g = (range (n+1)).filter (·∈Set.range g) := by
      ext m; simp only [mem_image,mem_filter,mem_range,mem,Set.mem_range]; grind
    calc _ = ∑ m∈(I n).image g,f m := by rw [sum_image inj.injOn]; simp [f,hit]
         _ = _ := by rw [eqn,sum_filter]; apply sum_congr rfl; intro m _; split_ifs with h <;> simp_all [f]
  rw [Metric.tendsto_atTop]; intro ε pos
  obtain ⟨N,sm⟩ := small (ε/2) (half_pos pos)
  refine ⟨N,fun n hn => ?_⟩
  have sm' (m : ℕ) (hm : n≤m) : A m ≤ ε/2 := by
    by_cases h : m∈Set.range g
    · obtain ⟨i,rfl⟩ := h; rw [hit]; exact sm i (hn.trans hm)
    · rw [outside h]; linarith
  have split := summ.sum_add_tsum_nat_add (n+1)
  push_cast; rw [total,trunc,← split,mul_add,add_sub_cancel_left,Real.dist_eq,sub_zero,
    abs_of_nonneg (mul_nonneg (by positivity) (tsum_nonneg (fun i => div_nonneg (bounds _).1 (by positivity)))),← tsum_mul_left]
  apply lt_of_le_of_lt _ (half_lt_self pos)
  have major := hg.mul_left (ε/4)
  apply (((summable_nat_add_iff (n+1)).mpr summ).mul_left ((b:ℝ)^n)).tsum_le_tsum (g:=fun i => ε/4*(1/2:ℝ)^i) _ major |>.trans_eq
  · rw [tsum_mul_left,tsum_geometric_two]; ring
  · intro i
    have id : (b:ℝ)^n*f (i+(n+1))=A (i+(n+1))/(b:ℝ)^(i+1) := by
      dsimp [f]; rw [show i+(n+1)=i+1+n by omega,pow_add]; field_simp [bp.ne']
    rw [id,one_div_pow]; calc _ ≤ (ε/2)/2^(i+1) := div_le_div₀ (by linarith) (sm' _ (by omega)) (by positivity) (pow_le_pow_left₀ (by norm_num) br _)
                              _ = _ := by rw [pow_succ]; ring

end NormalityChecker
