module

public import NormalityChecker.MaskedSeries

/-! Discrepancy transfer for rational prefixes with signed polynomial-growth tails. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

/-- A single model orbit accurate only on the given block suffices. -/
theorem interval_block {b c d : ℕ} (estimate : SmoothOrbitEstimate b c) {η : ℝ} (he : 0<η) :
    ∃ M : ℕ, ∃ δ : ℝ, 0<δ ∧ ∀ (x : ℝ) (y : ℚ) (B n : ℕ), M≤y.den →
      (∃ t : ℕ, y.den∣c^t) → y.den≤B^d →
      (∀ i<B, |(b:ℝ)^(n+i)*x-(b:ℝ)^i*y| < δ) → ∀ a e : ℝ, 0≤a → a≤e → e≤1 →
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
  refine ⟨H*M,α/(2*Real.pi*H),div_pos ap C,fun x y B n lo ⟨t,div⟩ top close a e ha hae he₁ => ?_⟩
  let u (i : ℕ) := shift b x (n+i)
  have fourier (h : ℤ) (hn : h≠0) (hs : h.natAbs<H) : ‖∑ i∈range B,phase (h*u i)‖≤2*α*B := by
    have model := model_orbit_bound h hn y bound ((Nat.mul_le_mul_right M hs.le).trans lo) div top
    let f i := phase ((h:ℝ)*u i)
    let g i := phase ((h:ℝ)*((b:ℝ)^i*y))
    have each (i : ℕ) (hi : i∈range B) : ‖f i-g i‖≤α := by
      have near := close i (mem_range.mp hi)
      dsimp [f,g,u,shift]; rw [phase_fract]; apply (phase_sub_le ..).trans
      rw [← mul_sub,abs_mul,← mul_assoc,← Int.cast_abs,← Nat.cast_natAbs]
      have high : (h.natAbs:ℝ)≤H := by exact_mod_cast hs.le
      calc _ ≤ (2*Real.pi*H)*|((b:ℝ)^(n+i)*x-(b:ℝ)^i*y)| := by gcongr
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


theorem clean_orbit {b k n : ℕ} {S : Finset ℕ} {a : ℕ → ℚ}
    (supp : ∀ m, m ∉ Nat.factoredNumbers S → a m = 0) (h : Clean S k n) {i : ℕ} (hi : i<2^k) :
    pre b a (n+i) = (b:ℚ)^i * pre b a n := by
  rw [pre, pre, mul_sum]
  have cutoff : (range (n+1)).filter (fun m => m ∈ Nat.factoredNumbers S) =
      (range (n+i+1)).filter (fun m => m ∈ Nat.factoredNumbers S) := by
    ext m; simp only [mem_filter,mem_range]; constructor
    · grind
    · rintro ⟨hm,ms⟩; have := h.old m ms (by omega); exact ⟨by omega, ms⟩
  have restrict (u : ℕ) (g : ℕ → ℚ) : (∑ m ∈ range (u+1),g m*a m) =
      ∑ m ∈ (range (u+1)).filter (fun m => m∈Nat.factoredNumbers S), g m*a m := by
    rw [sum_filter]; apply sum_congr rfl; intro m _; split_ifs with hm
    · rfl
    · simp [supp m hm]
  simp only [← mul_assoc]
  rw [restrict (n+i),restrict n,← cutoff]
  apply sum_congr rfl; intro m hm
  have mn := mem_range_succ_iff.mp (mem_filter.mp hm).1
  simp only [show n+i-m=i+(n-m) by omega,pow_add]

theorem clean_approx {b : ℕ} (hb : 2≤b) {S : Finset ℕ} {a : ℕ → ℚ}
    (growth : PolyGrowth a) (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0) {δ : ℝ}
    (pos : 0<δ) : ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n → ∀ i<2^k,
      |(b:ℝ)^(n+i)*series b a-(b:ℝ)^i*(pre b a n : ℝ)|<δ := by
  have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  filter_upwards [grow.eventually (gap_approximation hb growth pos)] with k approx n h i hi
  have orbit := congrArg (fun z : ℚ => (z : ℝ)) (clean_orbit (b:=b) supp h hi)
  change ((pre b a (n+i):ℚ):ℝ) = _ at orbit
  push_cast at orbit
  rw [← orbit]
  apply approx _ ((show n+i ≤ n+2^k by omega).trans h.bound)
  intro j hj; apply supp; intro hm
  have := h.old _ hm (by omega); omega

/-- The density of positions with certified growing denominators controls
the full interval discrepancy. The rational weights may be arbitrary. -/
theorem discrepancy_of_windows {b c d : ℕ} {S : Finset ℕ} {a : ℕ → ℚ} (hb : 2≤b)
    (estimate : SmoothOrbitEstimate b c) (growth : PolyGrowth a)
    (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (clear : ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n →
      (∃ t : ℕ, (pre b a n).den ∣ c^t) ∧ (pre b a n).den ≤ (2^k)^d)
    (bad : ℕ → Bool)
    (survives : ∀ M : ℕ, ∀ᶠ n : ℕ in atTop, bad n=false → M≤(pre b a n).den)
    {D : ℝ} (cost : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      (∑ i∈range N, if bad i then (1:ℝ) else 0) ≤ (D+ε)*N) :
    limsup (radixDiscrepancy b (series b a)) atTop ≤ D := by
  let x := series b a
  let P := pre b a
  let w (n : ℕ) : ℝ := if bad n then 1 else 0
  let I := {v : ℝ × ℝ // 0≤v.1 ∧ v.1≤v.2 ∧ v.2≤1}
  let f (j : I) := Localized.centered (shift b x) j.val.1 j.val.2
  have transfer := transfer S f (fun j => Localized.centered_norm _ j.prop.1 j.prop.2.1 j.prop.2.2) w (fun _ => by dsimp [w]; split <;> norm_num) (by
    intro η pos
    obtain ⟨M,δ,dp,hK⟩ := interval_block (d:=d) estimate pos
    obtain ⟨K',large⟩ := eventually_atTop.mp (survives M)
    have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
    filter_upwards [grow.eventually_ge_atTop K',clear,clean_approx hb growth supp dp] with k late cleared near n hn j
    let B := 2^k
    obtain ⟨div,top⟩ := cleared n hn
    have orb (i : ℕ) (hi : i<B) := clean_orbit (b:=b) supp hn hi
    by_cases some : ∃ i<B,bad (n+i)=false
    · obtain ⟨i,hi,ok⟩ := some
      have dvd := Rat.mul_den_dvd ((b:ℚ)^i) (P n)
      have integral : ((b:ℚ)^i).den=1 := by rw [← Nat.cast_pow]; simp
      change ((b:ℚ)^i * pre b a n).den ∣ _ at dvd
      rw [← orb i hi,integral,one_mul] at dvd
      have lo := (large (n+i) (late.trans (hn.start.trans (Nat.le_add_right ..))) ok).trans (Nat.le_of_dvd (P n).pos dvd)
      apply (hK x (P n) B n lo div top (near n hn) _ _ j.prop.1 j.prop.2.1 j.prop.2.2).trans
      exact le_add_of_nonneg_right (sum_nonneg (fun _ _ => by dsimp [w]; split <;> norm_num))
    · have allBad (i : ℕ) (hi : i∈range B) : w (n+i)=1 := by dsimp [w]; split <;> grind
      rw [sum_congr rfl allBad]; simp only [sum_const,card_range,nsmul_eq_mul,mul_one]
      exact (norm_sum_le ..).trans ((sum_le_sum (fun i (_ : i∈range B) => Localized.centered_norm _ j.prop.1 j.prop.2.1 j.prop.2.2 _)).trans (by simp; positivity)))
  apply le_of_forall_pos_le_add; intro ε pos
  apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds b x N).1))
  filter_upwards [transfer (ε/2) (by positivity),cost (ε/2) (by positivity),eventually_gt_atTop 0] with N ht price hN
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
  change _ ≤ ε/2*N + ∑ i∈range N,w i at H
  change (∑ i∈range N,w i) ≤ _ at price
  linarith only [H, price]

end NormalityChecker.PolynomialMasks
