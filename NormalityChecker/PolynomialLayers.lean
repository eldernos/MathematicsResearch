module

public import NormalityChecker.MixedPowers
public import Mathlib.Topology.Algebra.Order.Polynomial
public import Mathlib.Algebra.Polynomial.Div

/-! Polynomial numerators at geometric denominator layers. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.Localized.Composite.Generators
variable (d : Generators)

abbrev sample (G : ℤ[X]) (m : ℕ) : ℤ := G.eval (m:ℤ)

private lemma norm_pow (x : ℚ) (i : ℕ) : padicNorm d.p (x^i)=(padicNorm d.p x)^i := by
  let : Fact d.p.Prime := ⟨d.prime⟩
  induction i with | zero => simp | succ _ ih => simp [pow_succ,ih]

private lemma norm_idx (v : ℕ × ℕ) : padicNorm d.p (d.idx v:ℚ)=(padicNorm d.p (d.c:ℚ))^v.2 := by
  let : Fact d.p.Prime := ⟨d.prime⟩
  simp [idx,index,d.norm_pow,(padicNorm.nat_eq_one_iff _).mpr (d.unit_at d.qc)]

/-- For high layers the numerator has the local norm of its constant term,
uniformly over the exponent of the base-sharing generator. -/
theorem eval_norm_stabilizes (G : ℤ[X]) (hg : sample G 0≠0) :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℕ, padicNorm d.p (sample G (d.idx (a,j)):ℚ)=padicNorm d.p (sample G 0:ℚ) := by
  let : Fact d.p.Prime := ⟨d.prime⟩
  have small := tendsto_pow_atTop_nhds_zero_of_lt_one (padicNorm.nonneg _) ((padicNorm.nat_lt_one_iff (p:=d.p) d.c).mpr (Nat.minFac_dvd _))
  have pos := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.ne_zero (by exact_mod_cast hg) : padicNorm d.p (sample G 0:ℚ)≠0))
  filter_upwards [small.eventually_lt_const pos] with j hj a
  let m := d.idx (a,j)
  obtain ⟨z,hz⟩ : (m:ℤ) ∣ sample G m-sample G 0 := by simpa [sample] using sub_dvd_eval_sub (m:ℤ) 0 G
  have eqn : (sample G m:ℚ)=(sample G 0:ℚ)+(m:ℚ)*(z:ℚ) := by exact_mod_cast (show sample G m=sample G 0+(m:ℤ)*z by omega)
  have hnorm : padicNorm d.p ((m:ℚ)*z) < padicNorm d.p (sample G 0:ℚ) := by
    rw [padicNorm.mul]; exact (mul_le_of_le_one_right (padicNorm.nonneg _) (padicNorm.of_int z)).trans_lt ((d.norm_idx (a,j)) ▸ hj)
  change padicNorm d.p (sample G m:ℚ)=_; rw [eqn,padicNorm.add_eq_max_of_ne hnorm.ne',max_eq_left hnorm.le]

def term (G : ℤ[X]) (s : ℕ) (v : ℕ × ℕ) : ℚ :=
  (sample G (d.idx v):ℚ)*(1/((d.idx v:ℚ)^s*(d.b:ℚ)^d.idx v))

/-- A finite set with distinct layer numbers has a large local norm as soon as
it contains a sufficiently high layer. The threshold is uniform in the set. -/
theorem large_layer_sum (G : ℤ[X]) (hg : sample G 0≠0) {s : ℕ} (hs : 0<s) (M : ℕ) :
    ∃ J : ℕ, ∀ A : Finset (ℕ × ℕ), Set.InjOn Prod.snd (↑A : Set (ℕ × ℕ)) →
      ∀ v∈A, J≤v.2 → (M:ℚ)≤padicNorm d.p (∑ z∈A,d.term G s z) := by
  let : Fact d.p.Prime := ⟨d.prime⟩
  let W := (padicNorm d.p (d.c:ℚ))⁻¹^s
  let α := padicNorm d.p (sample G 0:ℚ)
  have wp : 1<W := one_lt_pow₀ d.norm_growth hs.ne'
  have ap : 0<α := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.ne_zero (by exact_mod_cast hg)))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (d.eval_norm_stabilizes G hg)
  have grow := (tendsto_pow_atTop_atTop_of_one_lt wp).const_mul_atTop ap
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (grow.eventually_gt_atTop (max (M:ℚ) (W^K)))
  have norm (v : ℕ × ℕ) : padicNorm d.p (d.term G s v)=padicNorm d.p (sample G (d.idx v):ℚ)*W^v.2 := by
    unfold term; rw [padicNorm.mul,padicNorm.div,padicNorm.mul]
    simp only [padicNorm.one,d.norm_pow,d.norm_idx,
      (padicNorm.nat_eq_one_iff _).mpr (d.unit_at d.cop),one_pow,mul_one,one_div,W,inv_pow]; rw [pow_right_comm]
  refine ⟨max J K,fun A unique v hv hj => ?_⟩
  obtain ⟨w,hw,top⟩ := A.exists_max_image Prod.snd ⟨v,hv⟩
  have late := hj.trans (top v hv)
  have stable := hK w.2 ((le_max_right ..).trans late) w.1
  have big := hJ w.2 ((le_max_left ..).trans late)
  have ultra : IsNonarchimedean (padicNorm d.p) := fun _ _ => padicNorm.nonarchimedean
  rw [ultra.apply_sum_eq_of_lt (d.term G s) padicNorm.neg hw, norm,stable]
  · exact ((le_max_left ..).trans_lt big).le
  · intro z hz hne; rw [norm,norm,stable]
    have lt := lt_of_le_of_ne (top z hz) (fun eqn => hne (unique hz hw eqn))
    by_cases high : K≤z.2
    · rw [hK _ high z.1]; exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ wp lt) ap
    · exact (mul_le_of_le_one_left (pow_nonneg (zero_lt_one.trans wp).le _) (padicNorm.of_int _)).trans_lt
        ((pow_le_pow_right₀ wp.le (le_of_not_ge high)).trans_lt ((le_max_right ..).trans_lt big))

def numerator (keep : ℕ × ℕ → Bool) (G : ℤ[X]) (v : ℕ × ℕ) : ℤ :=
  if keep v then sample G (d.idx v) else 0

private lemma prefix_eq (keep : ℕ × ℕ → Bool) (G : ℤ[X]) (s n : ℕ) :
    d.weightedPrefix (d.numerator keep G) s n = (d.b:ℚ)^n *
      ∑ v ∈ (allowed d.q d.c n).filter (fun v => keep v), d.term G s v := by
  simp only [weightedPrefix,numerator,term,sum_filter]; congr 1; apply sum_congr rfl
  intro v _; split_ifs <;> simp

noncomputable def weightedValue (keep : ℕ × ℕ → Bool) (G : ℤ[X]) (s : ℕ) :=
  ∑' v : ℕ × ℕ, (d.numerator keep G v:ℝ) / (d.idx v:ℝ)^s / (d.b:ℝ)^d.idx v

private lemma weighted_tail (keep : ℕ × ℕ → Bool) (G : ℤ[X]) {s : ℕ} (deg : G.natDegree<s) :
    Tendsto (fun n => (d.b:ℝ)^n*d.weightedValue keep G s-(d.weightedPrefix (d.numerator keep G) s n:ℝ)) atTop (𝓝 0) := by
  let f := G.map (Int.castRingHom ℝ)
  have lt : f.degree < ((X:ℝ[X])^s).degree := by
    rw [degree_X_pow]; exact degree_le_natDegree.trans_lt (by exact_mod_cast (natDegree_map_le.trans_lt deg : f.natDegree<s))
  have decay := (f.div_tendsto_atTop_zero_of_degree_lt lt).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  let a (v : ℕ × ℕ) := (d.numerator keep G v:ℚ)/(d.idx v:ℚ)^s
  have tail := indexed_shift_error_signed d.hb d.idx d.injective a (by
    intro ε pos
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp decay ε pos
    refine ⟨N,fun v hv => ?_⟩
    have h := hN (d.idx v) hv
    have ev : f.eval (d.idx v:ℝ)=(sample G (d.idx v):ℝ) := by
      exact_mod_cast eval_map_apply (p:=G) (Int.castRingHom ℝ) (d.idx v:ℤ)
    dsimp only [Function.comp_apply] at h
    simp only [ev,eval_pow,eval_X,Real.dist_eq,sub_zero] at h
    dsimp [a,numerator]; split_ifs <;> push_cast <;> first | exact h.le | simpa using pos.le) (allowed d.q d.c) (fun _ _ => mem_allowed d.hq d.hc)
  convert tail using 2 with n
  simp only [weightedValue,a,weightedPrefix,Rat.cast_mul,Rat.cast_pow,Rat.cast_sum,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,Rat.cast_one]
  congr 2; apply sum_congr rfl; intro v _; ring

/-- With full mixed support, a high insertion separates two small-denominator
prefixes. The layer mesh then forces the bad block starts into a short interval. -/
theorem mixed_normal_reduced (G : ℤ[X]) (hg : sample G 0≠0) {s : ℕ} (deg : G.natDegree<s) :
    NormalIn d.b (d.weightedValue (fun _ => true) G s) := by
  let keep : ℕ × ℕ → Bool := fun _ => true
  let Z := d.weightedPrefix (d.numerator keep G) s
  apply d.normal_weighted _ s _ (d.weighted_tail keep G deg)
  intro u hu M δ pos
  apply d.exceptional_of_separated Z M _ u hu pos
  obtain ⟨J,large⟩ := d.large_layer_sum G hg ((Nat.zero_le _).trans_lt deg) M
  refine ⟨J,fun {a j n m} hj lo hi short => ?_⟩
  let I := allowed d.q d.c
  let A := I m \ I n
  have sub : I n ⊆ I m := fun v hv => (mem_allowed d.hq d.hc).mpr (((mem_allowed d.hq d.hc).mp hv).trans (lo.le.trans hi))
  have has : (a,j)∈A := mem_sdiff.mpr ⟨(mem_allowed d.hq d.hc).mpr hi, mt (mem_allowed d.hq d.hc).mp lo.not_ge⟩
  have big := large A (layer_injective d.hq d.hc short) (a,j) has hj
  have shifted (l : ℕ) : padicNorm d.p (Z l)=padicNorm d.p (∑ v∈I l,d.term G s v) := by
    let : Fact d.p.Prime := ⟨d.prime⟩
    simp [Z,d.prefix_eq,keep,I,padicNorm.mul,d.norm_pow,(padicNorm.nat_eq_one_iff _).mpr (d.unit_at d.cop)]
  have diff : ∑ v∈A,d.term G s v=(∑ v∈I m,d.term G s v)-(∑ v∈I n,d.term G s v) := eq_sub_of_add_eq (sum_sdiff sub)
  rw [diff] at big
  let : Fact d.p.Prime := ⟨d.prime⟩
  have sizes := big.trans padicNorm.sub
  rw [← shifted,← shifted,max_comm] at sizes
  exact_mod_cast sizes.trans (max_le_max (padicNorm_le_den d.prime _) (padicNorm_le_den d.prime _))

/-- On the single axis the entire prefix has distinct layers. Every sufficiently
late block start has a large denominator, including starts at insertion positions. -/
theorem axis_normal_reduced (mask : ℕ → Bool) (unbounded : ∀ J : ℕ, ∃ j≥J, mask j=true)
    (G : ℤ[X]) (hg : sample G 0≠0) {s : ℕ} (deg : G.natDegree<s) :
    NormalIn d.b (d.weightedValue (fun v => (v.1==0) && mask v.2) G s) := by
  let keep : ℕ × ℕ → Bool := fun v => (v.1==0) && mask v.2
  apply d.normal_weighted _ s _ (d.weighted_tail keep G deg)
  intro u hu M δ pos
  obtain ⟨J,large⟩ := d.large_layer_sum G hg ((Nat.zero_le _).trans_lt deg) M
  obtain ⟨j,hj,hit⟩ := unbounded J
  filter_upwards [eventually_ge_atTop j] with k hk
  let K := d.c^k
  suffices ∀ l : ℕ, M≤(d.weightedPrefix (d.numerator keep G) s ((u*K+l)*K)).den by
    have empty : ((range K).filter (fun l => (d.weightedPrefix (d.numerator keep G) s ((u*K+l)*K)).den<M))=∅ :=
      filter_eq_empty_iff.mpr (fun l _ => (this l).not_gt)
    change ((_:Finset ℕ).card:ℝ)≤δ*K+1; rw [empty]; simp; positivity
  intro l
  let n := (u*K+l)*K
  let A := (allowed d.q d.c n).filter (fun v => keep v)
  have first {v : ℕ × ℕ} (hv : v∈A) : v.1=0 := by exact (beq_iff_eq.mp (Bool.and_eq_true_iff.mp (mem_filter.mp hv).2).1)
  have kp : 0<K := pow_pos (by have := d.hc; omega) _
  have uniq : Set.InjOn Prod.snd (↑A : Set (ℕ × ℕ)) := fun x hx y hy h => Prod.ext ((first hx).trans (first hy).symm) h
  have has : (0,j)∈A := mem_filter.mpr ⟨(mem_allowed d.hq d.hc).mpr (by
    change d.q^0*d.c^j≤(u*K+l)*K; rw [pow_zero,one_mul]; apply (Nat.pow_le_pow_right (by have := d.hc; omega : 0<d.c) hk).trans; apply Nat.le_mul_of_pos_left
    have := Nat.mul_pos hu kp; omega),by simp [keep,hit]⟩
  have big := large A uniq (0,j) has hj
  let : Fact d.p.Prime := ⟨d.prime⟩
  have norm : padicNorm d.p (d.weightedPrefix (d.numerator keep G) s n)=padicNorm d.p (∑ v∈A,d.term G s v) := by
    rw [d.prefix_eq,padicNorm.mul,d.norm_pow,(padicNorm.nat_eq_one_iff _).mpr (d.unit_at d.cop),one_pow,one_mul]
  exact_mod_cast (big.trans (norm ▸ padicNorm_le_den d.prime _))

end NormalityChecker.Localized.Composite.Generators
