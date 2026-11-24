module

public import NormalityChecker.WeightedBlocks

/-! Fixed-support orbit cancellation on selected positions of a localized series. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Uniform bounds for interval discrepancy in every integer base. -/
theorem radix_discrepancy_bounds (b : ℕ) (x : ℝ) (N : ℕ) : 0≤radixDiscrepancy b x N ∧ radixDiscrepancy b x N≤1 := by
  let U := {d | ∃ a c : ℝ, 0≤a ∧ a<c ∧ c≤1 ∧ d=|frequency (shift b x) a c N-(c-a)|}
  have cap : ∀ y∈U,y≤1 := by
    rintro _ ⟨a,c,ha,lt,hc,rfl⟩; have := frequency_bounds (shift b x) a c N; rw [abs_le]; constructor <;> linarith [this.1,this.2]
  have h : |frequency (shift b x) 0 1 N-(1-0)|∈U := ⟨0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩
  exact ⟨(abs_nonneg _).trans (le_csSup ⟨1,cap⟩ h),csSup_le ⟨_,h⟩ cap⟩

/-- A vanishing sequence of uniform discrepancy upper bounds gives digit normality. -/
theorem normal_of_radix_limsup_zero {b : ℕ} (hb : 2≤b) {x : ℝ} (hz : limsup (radixDiscrepancy b x) atTop ≤ 0) : NormalIn b x := by
  refine ⟨hb,fun k m _ hm => ?_⟩
  let q := (b:ℝ)^k
  have hq : 0<q := pow_pos (by exact_mod_cast (show 0<b by omega)) _
  have hi : ((m:ℝ)+1)/q≤1 := (div_le_one hq).mpr (by dsimp [q]; exact_mod_cast (show m+1≤b^k from hm))
  rw [Metric.tendsto_atTop]; intro ε he
  obtain ⟨N,large⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt (hz.trans_lt he) (isBoundedUnder_of_eventually_le (.of_forall fun n => (radix_discrepancy_bounds b x n).2)))
  refine ⟨N,fun n hn => ?_⟩
  have h := le_csSup (s:={d | ∃ a c : ℝ, 0≤a ∧ a<c ∧ c≤1 ∧ d=|frequency (shift b x) a c n-(c-a)|}) (a:=|frequency (shift b x) (m/q) ((m+1)/q) n-((m+1)/q-m/q)|)
    (show BddAbove _ from ⟨1,by rintro _ ⟨a,c,ha,lt,hc,rfl⟩; have := frequency_bounds (shift b x) a c n; rw [abs_le]; constructor <;> linarith [this.1,this.2]⟩)
    ⟨_,_,by positivity,(div_lt_div_iff_of_pos_right hq).mpr (by linarith),hi,rfl⟩
  simpa only [Real.dist_eq,show ((m:ℝ)+1)/q-m/q=1/q by ring] using h.trans_lt (large n hn)

/-- A single cutoff works for all intervals and all sufficiently large clean
orbits. `M` is a cutoff for the reduced denominator at the start of the block. -/
theorem smooth_interval_block {b c d : ℕ} (estimate : SmoothOrbitEstimate b c) (x : ℝ) (P : ℕ → ℚ)
    (tail : Tendsto (fun n => (b:ℝ)^n*x-(P n:ℝ)) atTop (𝓝 0)) {η : ℝ} (he : 0<η) :
    ∃ M n₀ : ℕ, ∀ B n : ℕ, n₀≤n → M≤(P n).den → (∃ t : ℕ, (P n).den∣c^t) → (P n).den≤B^d →
      (∀ i<B,P (n+i)=(b:ℚ)^i*P n) → ∀ a e : ℝ, 0≤a → a≤e → e≤1 →
      ‖∑ i∈range B, Localized.centered (shift b x) a e (n+i)‖ ≤ η*B := by
  let w := η/32
  have wp : 0<w := by dsimp [w]; positivity
  obtain ⟨H,hH⟩ := exists_nat_gt ((3+(1/w)^2)/w)
  have hp : (0:ℝ)<H := (by positivity : 0<(3+(1/w)^2)/w).trans hH
  let : NeZero H := ⟨by exact_mod_cast hp.ne'⟩
  let α := w/(H:ℝ)
  have ap : 0<α := div_pos wp hp
  obtain ⟨M,bound⟩ := estimate d α ap
  have C : 0<2*Real.pi*H := by positivity
  obtain ⟨K,little⟩ := (Metric.tendsto_atTop.mp tail) (α/(2*Real.pi*H)) (div_pos ap C)
  refine ⟨H*M,K,fun B n nk lo ⟨t,div⟩ top orb a e ha hae he₁ => ?_⟩
  let u (i : ℕ) := shift b x (n+i)
  have fourier (h : ℤ) (hn : h≠0) (hs : h.natAbs<H) : ‖∑ i∈range B,phase (h*u i)‖≤2*α*B := by
    have model := model_orbit_bound h hn (P n) bound ((Nat.mul_le_mul_right M hs.le).trans lo) div top
    let f i := phase ((h:ℝ)*u i)
    let g i := phase ((h:ℝ)*((b:ℝ)^i*P n))
    have each (i : ℕ) (hi : i∈range B) : ‖f i-g i‖≤α := by
      have near := little (n+i) (nk.trans (Nat.le_add_right ..)); rw [Real.dist_eq,sub_zero] at near
      have exactOrbit := congrArg (fun z : ℚ => (z:ℝ)) (orb i (mem_range.mp hi)); push_cast at exactOrbit
      dsimp [f,g,u,shift]; rw [phase_fract,← exactOrbit]; apply (phase_sub_le ..).trans
      rw [← mul_sub,abs_mul,← mul_assoc,← Int.cast_abs,← Nat.cast_natAbs]
      have high : (h.natAbs:ℝ)≤H := by exact_mod_cast hs.le
      calc _ ≤ (2*Real.pi*H)*|((b:ℝ)^(n+i)*x-(P (n+i):ℝ))| := by gcongr
           _ ≤ α := by linarith only [(lt_div_iff₀ C).mp near]
    have err := (norm_sum_le (range B) (fun i => f i-g i)).trans (sum_le_sum each)
    rw [sum_sub_distrib] at err; simp only [sum_const,card_range,nsmul_eq_mul] at err
    have tri := norm_le_norm_add_norm_sub' (∑ i∈range B,f i) (∑ i∈range B,g i)
    change ‖∑ i∈range B,g i‖≤α*B at model
    linarith only [tri,err,model]
  have bnd := IntervalFourier.interval_count_bound (H:=H) (T:=B) u (fun _ => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩) ha hae he₁ wp (by positivity : 0≤2*α*B) fourier
  rw [Localized.centered_sum]; apply bnd.trans
  have tiny : 3/(H:ℝ)+(1/w)^2/H≤w := by rw [← add_div,div_le_iff₀ hp]; linarith only [(div_lt_iff₀ wp).mp hH]
  have id : (H:ℝ)*α=w := by dsimp [α]; field_simp
  have cap : 4*w+3/H+(1/w)^2/H ≤5*w := by linarith
  nlinarith only [mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg B),congrArg (fun z : ℝ => 2*z*B) id,
    show 14*w≤η by dsimp [w]; linarith, mul_le_mul_of_nonneg_right (show 14*w≤η by dsimp [w]; linarith) (Nat.cast_nonneg B)]

namespace LocalizedSupport
/-- On every clean block the reduced denominator at a later position divides
the starting denominator. One surviving position suffices for the full block. -/
theorem discrepancy_of_survival {b c s : ℕ} (A : Finset ℕ) (hb : 2≤b) (hc : 1<c) (cop : b.Coprime c)
    (hs : 0<s) (support : ∀ p∈A,p∣b*c) (bad : ℕ → Bool)
    (survives : ∀ M : ℕ, ∀ᶠ n : ℕ in atTop, bad n=false → M≤(powerShifted b s A n).den)
    {D : ℝ} (cost : ∀ᶠ N : ℕ in atTop, (∑ i∈range N, if bad i then (1:ℝ) else 0) ≤ D*N) :
    limsup (radixDiscrepancy b (powerValue b s A)) atTop ≤ D := by
  let x := powerValue b s A
  let P := powerShifted b s A
  let w (n : ℕ) : ℝ := if bad n then 1 else 0
  let I := {v : ℝ × ℝ // 0≤v.1 ∧ v.1≤v.2 ∧ v.2≤1}
  let f (j : I) := Localized.centered (shift b x) j.val.1 j.val.2
  have transfer := transfer_clean_blocks (s:=s) A hb hc.le support f (fun j => Localized.centered_norm _ j.prop.1 j.prop.2.1 j.prop.2.2) w (fun _ => by dsimp [w]; split <;> norm_num) (by
    intro η pos
    obtain ⟨M,K,hK⟩ := smooth_interval_block (d:=4*c*s) (fixed_support_orbit_estimate hb hc cop) x P (power_tail hb hs A) pos
    obtain ⟨K',large⟩ := eventually_atTop.mp (survives M)
    refine ⟨max K K',fun B n nk bp div top orb j => ?_⟩
    by_cases some : ∃ i<B,bad (n+i)=false
    · obtain ⟨i,hi,ok⟩ := some
      have dvd := Rat.mul_den_dvd ((b:ℚ)^i) (P n)
      have integral : ((b:ℚ)^i).den=1 := by rw [← Nat.cast_pow]; simp
      rw [← orb i hi,integral,one_mul] at dvd
      have lo := (large (n+i) ((le_max_right ..).trans (nk.trans (Nat.le_add_right ..))) ok).trans (Nat.le_of_dvd (P n).pos dvd)
      apply (hK B n ((le_max_left ..).trans nk) lo div top orb _ _ j.prop.1 j.prop.2.1 j.prop.2.2).trans
      exact le_add_of_nonneg_right (sum_nonneg (fun _ _ => by dsimp [w]; split <;> norm_num))
    · have allBad (i : ℕ) (hi : i∈range B) : w (n+i)=1 := by dsimp [w]; split <;> grind
      rw [sum_congr rfl allBad]; simp only [sum_const,card_range,nsmul_eq_mul,mul_one]
      exact (norm_sum_le ..).trans ((sum_le_sum (fun i (_ : i∈range B) => Localized.centered_norm _ j.prop.1 j.prop.2.1 j.prop.2.2 _)).trans (by simp; positivity)))
  apply le_of_forall_pos_le_add; intro ε pos
  apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds b x N).1))
  filter_upwards [transfer ε pos,cost,eventually_gt_atTop 0] with N ht price hN
  unfold radixDiscrepancy
  refine csSup_le ?_ ?_
  · exact ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩
  rintro _ ⟨a,e,ha,lt,he,rfl⟩
  have H := ht ⟨(a,e),ha,lt.le,he⟩; dsimp only [f] at H
  have convertSum := Localized.centered_sum (shift b x) a e 0 N
  simp only [zero_add] at convertSum; rw [convertSum] at H
  change |((IntervalFourier.count (shift b x) a e N:ℝ)/N)-(e-a)| ≤ _
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [div_sub' hn.ne',abs_div,abs_of_pos hn,div_le_iff₀ hn]
  simpa [mul_comm,add_mul,add_comm,add_left_comm,x,w] using H.trans (add_le_add_right price (ε*N))

end LocalizedSupport
end NormalityChecker
