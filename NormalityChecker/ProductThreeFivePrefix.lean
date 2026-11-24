module

public import NormalityChecker.PartialUniformity
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-! Rational prefixes and the shifted tail of the product of two binary Stoneham series. -/
@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker.ProductThreeFive

/-- The binary Stoneham series with parameter `p`, starting at exponent one. -/
noncomputable def alpha (p : ℕ) : ℝ :=
  ∑' j : ℕ, 1 / ((p : ℝ)^(j+1) * (2 : ℝ)^(p^(j+1) : ℕ))

def location (v : ℕ × ℕ) : ℕ := 3^(v.1+1) + 5^(v.2+1)
def weightDen (v : ℕ × ℕ) : ℕ := 3^(v.1+1) * 5^(v.2+1)
def active (n : ℕ) := ((range (Nat.log 3 n)) ×ˢ (range (Nat.log 5 n))).filter
  (fun v => location v ≤ n)

lemma mem_active {n : ℕ} {v : ℕ × ℕ} : v ∈ active n ↔ location v ≤ n := by
  refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,h⟩⟩
  · exact mem_range.mpr (Nat.le_log_of_pow_le (by decide) ((Nat.le_add_right ..).trans h))
  · exact mem_range.mpr (Nat.le_log_of_pow_le (by decide) ((Nat.le_add_left ..).trans h))

def pre (n : ℕ) : ℚ := ∑ v ∈ active n, (2:ℚ)^(n-location v)/weightDen v

private lemma geometric_majorant (p : ℕ) (hp : 1 < p) :
    Summable (fun j : ℕ => (1/(p:ℝ))^(j+1)) ∧
    Summable (fun j : ℕ => 1 / ((p:ℝ)^(j+1)*(2:ℝ)^(p^(j+1):ℕ))) := by
  have pr : (1:ℝ) < p := by exact_mod_cast hp
  have geom := (summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (by positivity : 0 ≤ 1/(p:ℝ))
      ((div_lt_one (by positivity)).mpr pr))
  refine ⟨geom, geom.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)⟩
  rw [one_div_pow, ← div_div]
  exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))

/-- After shifting by `n` binary digits, the discarded terms tend to zero.
Distinct pairs of indices are allowed to insert at the same position. -/
theorem shifted_tail :
    Tendsto (fun n : ℕ => (2:ℝ)^n * (alpha 3 * alpha 5) - (pre n:ℝ)) atTop (𝓝 0) := by
  let a (p j : ℕ) := 1 / ((p:ℝ)^(j+1)*(2:ℝ)^(p^(j+1):ℕ))
  let c (p j : ℕ) := (1/(p:ℝ))^(j+1)
  have cp (p j : ℕ) : 0 ≤ c p j := by dsimp [c]; positivity
  have ap (p j : ℕ) : 0 ≤ a p j := by dsimp [a]; positivity
  obtain ⟨sc₃,sa₃⟩ := geometric_majorant 3 (by decide)
  obtain ⟨sc₅,sa₅⟩ := geometric_majorant 5 (by decide)
  have sp := sa₃.mul_of_nonneg sa₅ (ap 3) (ap 5)
  have prod : alpha 3 * alpha 5 = ∑' v : ℕ × ℕ, a 3 v.1 * a 5 v.2 :=
    sa₃.tsum_mul_tsum sa₅ sp
  let tail (n : ℕ) (v : ℕ × ℕ) := if location v ≤ n then 0 else
    (2:ℝ)^n * (a 3 v.1 * a 5 v.2)
  have form (n : ℕ) (v : ℕ × ℕ) :
      (2:ℝ)^n * (a 3 v.1 * a 5 v.2) = (2:ℝ)^n / ((weightDen v:ℝ) * 2^location v) := by
    simp [a,weightDen,location,pow_add]; ring
  have dom (n : ℕ) (v : ℕ × ℕ) : ‖tail n v‖ ≤ c 3 v.1 * c 5 v.2 := by
    dsimp only [tail]
    split_ifs with incl
    · simpa using mul_nonneg (cp 3 _) (cp 5 _)
    · rw [form,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have pow : (2:ℝ)^n ≤ 2^location v := pow_le_pow_right₀ (by norm_num) (by omega)
      have pos : 0 < weightDen v := by unfold weightDen; positivity
      dsimp only [c]
      rw [one_div_pow,one_div_pow,div_le_iff₀ (by positivity)]
      apply pow.trans_eq
      simp [weightDen]; field_simp
  have major := sc₃.mul_of_nonneg sc₅ (cp 3) (cp 5)
  have decay := tendsto_tsum_of_dominated_convergence (g:=fun _ : ℕ × ℕ => (0:ℝ))
    major (f:=tail) (fun v => tendsto_const_nhds.congr'
      ((eventually_ge_atTop (location v)).mono fun n hn => by simp [tail,hn])) (.of_forall dom)
  simp only [tsum_zero] at decay
  apply decay.congr
  intro n
  change (∑' v, tail n v) = _
  have spl (v : ℕ × ℕ) : (2:ℝ)^n*(a 3 v.1*a 5 v.2) = tail n v +
      (if v ∈ active n then (2:ℝ)^(n-location v)/weightDen v else 0) := by
    dsimp only [tail]
    by_cases incl : location v ≤ n
    · simp only [mem_active,incl,ite_true,zero_add,form,pow_sub₀ _ (by norm_num : (2:ℝ) ≠ 0) incl]
      ring
    · simp [mem_active,incl]
  have fin : Summable (fun v : ℕ × ℕ => if v ∈ active n then
      (2:ℝ)^(n-location v)/weightDen v else 0) :=
    summable_of_ne_finset_zero (s:=active n) (fun _ h => by simp [h])
  have eqn := (Summable.of_norm_bounded major (dom n)).tsum_add fin
  simp_rw [← spl] at eqn
  have finiteEq : (∑' v, if v ∈ active n then (2:ℝ)^(n-location v)/weightDen v else 0)
      = ∑ v ∈ active n, (2:ℝ)^(n-location v)/weightDen v := by
    rw [tsum_eq_sum (s:=active n) (fun _ h => by simp [h])]
    exact sum_congr rfl (fun v hv => ite_eq_left hv)
  rw [tsum_mul_left, ← prod, finiteEq] at eqn
  simp only [pre,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]
  rw [eqn]; simp

lemma transport {n i : ℕ} :
    ∑ v ∈ active n, (2:ℚ)^(n+i-location v)/weightDen v = (2:ℚ)^i * pre n := by
  simp only [pre,mul_sum]
  apply sum_congr rfl; intro v hv
  have lo := mem_active.mp hv
  rw [show n+i-location v = i+(n-location v) by omega,pow_add,mul_div_assoc]

lemma follows {n i : ℕ} (free : ∀ v, n < location v → n+i < location v) :
    pre (n+i) = (2:ℚ)^i * pre n := by
  have same : active (n+i) = active n := by
    ext v; rw [mem_active,mem_active]; constructor
    · intro h; exact le_of_not_gt (fun gt => (free v gt).not_ge h)
    · omega
  rw [pre,same,transport]

/-- All terms through position `n` have a common 15-smooth denominator of size at most `n²`
when `n` is positive. -/
theorem prefix_denominator {n : ℕ} (hn : 0 < n) :
    (∃ t : ℕ, (pre n).den ∣ 15^t) ∧ (pre n).den ≤ n^2 := by
  let i := Nat.log 3 n
  let j := Nat.log 5 n
  have dv : (pre n).den ∣ 3^i*5^j := by
    apply (Rat.den_sum_dvd_lcm_den ..).trans
    apply Finset.lcm_dvd
    intro v hv
    have inds := mem_product.mp (mem_filter.mp hv).1
    have small : weightDen v ∣ 3^i*5^j := mul_dvd_mul
      (pow_dvd_pow 3 (mem_range.mp inds.1)) (pow_dvd_pow 5 (mem_range.mp inds.2))
    have wd : 0 < weightDen v := by unfold weightDen; positivity
    rw [div_eq_mul_inv]
    have integral : ((2:ℚ)^(n-location v)).den = 1 := by
      exact_mod_cast (Rat.den_natCast (2^(n-location v)))
    apply (Rat.mul_den_dvd ..).trans
    simpa [integral,Rat.inv_natCast_den_of_pos wd] using small
  refine ⟨⟨max i j,dv.trans ?_⟩,(Nat.le_of_dvd (by positivity) dv).trans ?_⟩
  · rw [show 15=3*5 by decide,mul_pow]
    exact mul_dvd_mul (pow_dvd_pow 3 (le_max_left ..)) (pow_dvd_pow 5 (le_max_right ..))
  · rw [sq]
    exact Nat.mul_le_mul (Nat.pow_log_le_self _ hn.ne') (Nat.pow_log_le_self _ hn.ne')

end NormalityChecker.ProductThreeFive
