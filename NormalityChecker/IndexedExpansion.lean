module

public import NormalityChecker.ArithmeticCertificate

/-! Real tails for radix expansions with an arbitrary injective insertion schedule. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Signed coefficients tending to zero along an injective insertion schedule have
vanishing shifted tails. The absolute values need only be bounded eventually. -/
theorem indexed_shift_error_signed {ι : Type*} {b : ℕ} (hb : 2≤b) (g : ι → ℕ) (inj : Function.Injective g)
    (a : ι → ℚ)
    (small : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ i, N≤g i → |(a i:ℝ)|≤ε)
    (I : ℕ → Finset ι) (mem : ∀ n i, i∈I n ↔ g i≤n) :
    Tendsto (fun n => (b:ℝ)^n*(∑' i, (a i:ℝ)/(b:ℝ)^(g i)) -
        (((b:ℚ)^n * ∑ i∈I n, a i/(b:ℚ)^(g i):ℚ):ℝ)) atTop (𝓝 0) := by
  classical
  let A := Function.extend g (fun i => (a i:ℝ)) (fun _ => 0)
  let f (m : ℕ) := A m/(b:ℝ)^m
  have hit (i : ι) : A (g i)=(a i:ℝ) := inj.extend_apply ..
  have outside {m : ℕ} (h : m ∉ Set.range g) : A m=0 := Function.extend_apply' _ _ _ h
  have sm' {ε : ℝ} (pos : 0<ε) : ∀ᶠ m : ℕ in atTop, |A m|≤ε := by
    obtain ⟨N,hN⟩ := small ε pos
    filter_upwards [eventually_ge_atTop N] with m hm
    by_cases h : m∈Set.range g
    · obtain ⟨i,rfl⟩ := h; rw [hit]; exact hN i hm
    · simp [outside h,pos.le]
  have br : (2:ℝ)≤b := by exact_mod_cast hb
  have bp : (0:ℝ)<b := by linarith
  have hg := summable_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)
  have summ : Summable f := Summable.of_norm_bounded_eventually_nat hg (by
    filter_upwards [sm' zero_lt_one] with m hm
    dsimp [f]; rw [abs_div,abs_of_pos (pow_pos bp _),one_div_pow]
    exact div_le_div₀ zero_le_one hm (by positivity) (pow_le_pow_left₀ (by norm_num) br _))
  have H := (inj.hasSum_iff (f:=f) (fun m h => by simp [f,outside h])).mpr summ.hasSum
  have total : (∑' i, (a i:ℝ)/(b:ℝ)^g i)=∑' m,f m := by simpa [Function.comp_def,f,hit] using H.tsum_eq
  have trunc (n : ℕ) : ∑ i∈I n,(a i:ℝ)/(b:ℝ)^g i = ∑ m∈range (n+1),f m := by
    have eqn : (I n).image g = (range (n+1)).filter (·∈Set.range g) := by
      ext m; simp only [mem_image,mem_filter,mem_range,mem,Set.mem_range]; grind
    calc _ = ∑ m∈(I n).image g,f m := by rw [sum_image inj.injOn]; simp [f,hit]
         _ = _ := by rw [eqn,sum_filter]; apply sum_congr rfl; intro m _; split_ifs with h <;> simp_all [f]
  rw [Metric.tendsto_atTop]; intro ε pos
  obtain ⟨N,sm⟩ := eventually_atTop.mp (sm' (half_pos pos))
  refine ⟨N,fun n hn => ?_⟩
  have split := summ.sum_add_tsum_nat_add (n+1)
  push_cast; rw [total,trunc,← split,mul_add,add_sub_cancel_left,Real.dist_eq,sub_zero,
    ← Real.norm_eq_abs,← tsum_mul_left]
  apply lt_of_le_of_lt _ (half_lt_self pos)
  have major := hg.mul_left (ε/4)
  have summTail := ((summable_nat_add_iff (n+1)).mpr summ).mul_left ((b:ℝ)^n)
  apply (norm_tsum_le_tsum_norm summTail.norm).trans
  apply (summTail.norm.tsum_le_tsum (g:=fun i => ε/4*(1/2:ℝ)^i) _ major).trans_eq
  · rw [tsum_mul_left,tsum_geometric_two]; ring
  · intro i
    have id : (b:ℝ)^n*f (i+(n+1))=A (i+(n+1))/(b:ℝ)^(i+1) := by
      dsimp [f]; rw [show i+(n+1)=i+1+n by omega,pow_add]; field_simp [bp.ne']
    rw [id,Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos bp _),one_div_pow]; calc _ ≤ (ε/2)/2^(i+1) := div_le_div₀ (by linarith) (sm _ (by omega)) (by positivity) (pow_le_pow_left₀ (by norm_num) br _)
                              _ = _ := by rw [pow_succ]; ring

/-- The nonnegative unit-bounded formulation used by the original expansions. -/
theorem indexed_shift_error {ι : Type*} {b : ℕ} (hb : 2≤b) (g : ι → ℕ) (inj : Function.Injective g)
    (a : ι → ℚ) (nonneg : ∀ i, 0≤a i) (bounded : ∀ i, a i≤1)
    (small : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ i, N≤g i → (a i:ℝ)≤ε)
    (I : ℕ → Finset ι) (mem : ∀ n i, i∈I n ↔ g i≤n) :
    Tendsto (fun n => (b:ℝ)^n*(∑' i, (a i:ℝ)/(b:ℝ)^(g i)) -
        (((b:ℚ)^n * ∑ i∈I n, a i/(b:ℚ)^(g i):ℚ):ℝ)) atTop (𝓝 0) := by
  have _ := bounded
  apply indexed_shift_error_signed hb g inj a _ I mem
  intro ε pos; obtain ⟨N,hN⟩ := small ε pos
  exact ⟨N, fun i hi => (abs_of_nonneg (by exact_mod_cast nonneg i)).le.trans (hN i hi)⟩

end NormalityChecker
