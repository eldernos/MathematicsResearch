module

public import NormalityChecker.QuadraticOrbitTransfer
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! Logarithmically weighted interval counts for sparse exceptional half-shells. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.QuadraticOrbit

noncomputable def harmonicWeight (n : ℕ) := ((n:ℝ)+1)⁻¹

/-- The harmonic measure of the first N starts in a half-open interval,
normalized by the total harmonic mass. -/
noncomputable def logFrequency (u : ℕ → ℝ) (a c : ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ range N, if a ≤ u i ∧ u i < c then harmonicWeight i else 0) / (harmonic N : ℝ)

private lemma harmonic_mass (N : ℕ) : (harmonic N:ℝ) = ∑ i ∈ range N, harmonicWeight i := by
  simp [harmonic,harmonicWeight]

/-- Discrete partial summation with a decreasing weight. -/
private theorem abel_bound (f : ℕ → ℂ) (w : ℕ → ℝ) (positive : ∀ i, 0 ≤ w i)
    (anti : Antitone w) (T : ℕ) (C : ℝ) (sums : ∀ t ≤ T, ‖∑ i ∈ range t, f i‖ ≤ C) :
    ‖∑ i ∈ range T, w i • f i‖ ≤ w 0*C := by
  let S (t : ℕ) := ∑ i ∈ range t, f i
  let W (t : ℕ) := ∑ i ∈ range t, w i • f i
  have step (t : ℕ) (ht : t ≤ T) : ‖W t - w t • S t‖ ≤ (w 0-w t)*C := by
    induction t with
    | zero => simp [W,S]
    | succ t ih =>
      have eqStep : W (t+1)-w (t+1) • S (t+1) =
          (W t-w t • S t) + (w t-w (t+1)) • S (t+1) := by
        simp only [W,S,sum_range_succ,sub_smul,smul_add]; abel
      have diff := sub_nonneg.mpr (anti (Nat.le_succ t))
      rw [eqStep]
      apply (norm_add_le ..).trans
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg diff]
      linarith only [ih (by omega),mul_le_mul_of_nonneg_left (sums _ ht) diff]
  have id : W T = (W T - w T • S T) + w T • S T := by abel
  change ‖W T‖ ≤ _
  conv_lhs => rw [id]
  apply (norm_add_le ..).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (positive _)]
  linarith only [step T le_rfl, mul_le_mul_of_nonneg_left (sums T le_rfl) (positive T)]

private theorem weighted_half (f : ℕ → ℂ) (r u T : ℕ) (hu : 1 ≤ u) {e : ℝ} (he : 0 ≤ e)
    (sums : ∀ t ≤ T, ‖∑ i ∈ range t, f (u*2^r+i)‖ ≤ e*(2:ℝ)^r) :
    ‖∑ i ∈ range T, harmonicWeight (u*2^r+i) • f (u*2^r+i)‖ ≤ e := by
  apply (abel_bound _ (fun i => harmonicWeight (u*2^r+i)) (fun i => by dsimp [harmonicWeight]; positivity)
    (fun i j hij => by dsimp [harmonicWeight]; gcongr) T _ sums).trans
  simp only [add_zero,harmonicWeight,inv_mul_eq_div]
  rw [div_le_iff₀ (by positivity)]
  apply mul_le_mul_of_nonneg_left _ he
  push_cast
  have h : (1:ℝ) ≤ u := by exact_mod_cast hu
  nlinarith only [mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (2:ℝ)^r)]

private theorem count_sparse {q : ℕ → ℕ} {K M H : ℕ} (hp : 0 < H)
    (uniq : ∀ t ≥ K, ∀ i ∈ Ico t (t+H), ∀ j ∈ Ico t (t+H), q i < M → q j < M → i=j) (m : ℕ) :
    ((range m).filter (fun j => q (K+j)<M)).card ≤ m/H+1 := by
  rw [← card_range (m/H+1)]
  apply card_le_card_of_injOn (fun i => i/H)
  · intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hi).1).le))
  · intro i hi j hj eqn
    have block (n : ℕ) : K+n ∈ Ico (K+(n/H)*H) (K+(n/H)*H+H) := by
      have lo := Nat.div_mul_le_self n H
      have high := Nat.lt_mul_div_succ n hp
      rw [Nat.mul_succ, Nat.mul_comm H (n/H)] at high
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    change i/H=j/H at eqn
    have bj := block j
    rw [← eqn] at bj
    exact Nat.add_left_cancel (uniq _ (Nat.le_add_right ..) _ (block i) _ bj
      (mem_filter.mp hi).2 (mem_filter.mp hj).2)

/-- Every good half costs at most the error supplied by its partial counts
in harmonic mass. An exceptional half costs at most one unit of mass. -/
theorem log_equidistribution_of_separated {b : ℕ} {x : ℝ} {q : ℕ → ℕ}
    (good : GoodHalves b x q) (sep : Separated q) (a c : ℝ) (ha : 0 ≤ a)
    (hac : a ≤ c) (hc : c ≤ 1) :
    Tendsto (logFrequency (shift b x) a c) atTop (𝓝 (c-a)) := by
  classical
  let f := Localized.centered (shift b x) a c
  let g (n : ℕ) := harmonicWeight n • f n
  let S (n : ℕ) := ∑ i ∈ range n, g i
  have unit (n : ℕ) : ‖f n‖ ≤ 1 := Localized.centered_norm _ ha hac hc n
  have trivial (u r T : ℕ) (hu : 1 ≤ u) (ht : T ≤ 2^r) :
      ‖∑ i ∈ range T, g (u*2^r+i)‖ ≤ 1 := by
    apply weighted_half f r u T hu zero_le_one
    intro t h
    apply (norm_sum_le ..).trans ((sum_le_sum (fun i _ => unit (u*2^r+i))).trans _)
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one, one_mul]
    exact_mod_cast h.trans ht
  have eqn (n : ℕ) : ‖S n‖ = |(∑ i ∈ range n, if a ≤ shift b x i ∧ shift b x i < c then harmonicWeight i else 0) -
      (harmonic n:ℝ)*(c-a)| := by
    have rep (i : ℕ) : g i = (((if a ≤ shift b x i ∧ shift b x i < c then harmonicWeight i else 0) -
        harmonicWeight i*(c-a) : ℝ):ℂ) := by
      dsimp [g,f,Localized.centered]; split_ifs <;> push_cast <;> ring
    dsimp only [S]; simp_rw [rep]
    rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,sum_sub_distrib,←sum_mul,harmonic_mass]
  rw [Metric.tendsto_atTop]
  intro ε ep
  let δ := ε*Real.log 2/8
  have lp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have dp : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H,hH⟩ := exists_nat_gt (1/δ)
  have hp : 0 < H := by exact_mod_cast (div_pos zero_lt_one dp).trans hH
  have hr : 1 ≤ δ*H := by linarith only [(div_lt_iff₀ dp).mp hH]
  obtain ⟨M,est⟩ := good δ dp
  obtain ⟨K,late⟩ := eventually_atTop.mp (est.and (sep M H))
  have full (m : ℕ) : ‖S (2^(K+m+1))‖ ≤ ‖S (2^(K+1))‖ + 2*δ*m +
      ∑ j ∈ range m, (if q (K+j)<M then (1:ℝ) else 0) := by
    induction m with
    | zero => simp
    | succ m ih =>
      let r := K+m
      have cell (u : ℕ) (hu : u=2 ∨ u=3 ∧ M≤q r) : ‖∑ i ∈ range (2^r),g (u*2^r+i)‖ ≤ δ := by
        apply weighted_half f r u _ (by rcases hu with h|⟨h,_⟩ <;> omega) dp.le
        intro t ht; exact (late r (Nat.le_add_right ..)).1 u hu t ht a c ha hac hc
      have up : ‖∑ i ∈ range (2^r), g (3*2^r+i)‖ ≤ δ+(if q r<M then 1 else 0) := by
        split_ifs with small
        · linarith only [trivial 3 r (2^r) (by decide) le_rfl,dp]
        · simpa using cell 3 (Or.inr ⟨rfl,by omega⟩)
      have split : S (2^(K+(m+1)+1)) = S (2^(r+1)) + (∑ i ∈ range (2^r), g (2*2^r+i)) +
          ∑ i ∈ range (2^r),g (3*2^r+i) := by
        dsimp only [S]
        have stop : 2^(K+(m+1)+1) = (2^(r+1)+2^r)+2^r := by
          change 2^((r+1)+1) = _; rw [pow_succ,pow_succ]; ring
        rw [stop,sum_range_add,sum_range_add]
        simp only [pow_succ',show 2*2^r+2^r = 3*2^r by omega]
      rw [split,sum_range_succ]
      apply (norm_add_le ..).trans
      have h := (norm_add_le (S (2^(r+1))) (∑ i ∈ range (2^r),g (2*2^r+i))).trans
        (add_le_add ih (cell 2 (Or.inl rfl)))
      push_cast; dsimp only [r] at h up ⊢
      linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt ((‖S (2^(K+1))‖+2)/δ)
  refine ⟨2^(max K J+1),fun N large => ?_⟩
  let k := Nat.log 2 N
  have np := (pow_pos (by decide : 0 < 2) _).trans_le large
  have big : max K J+1 ≤ k := Nat.le_log_of_pow_le (by decide) large
  let m := k-(K+1)
  have km : K+m+1 = k := by dsimp [m]; omega
  have lo : 2^k ≤ N := Nat.pow_log_le_self _ np.ne'
  have hi : N < 2^k+2^k := by simpa only [pow_succ,two_mul,mul_two] using Nat.lt_pow_succ_log_self (by decide : 1<2) N
  have endpt : S N = S (2^k) + ∑ i ∈ range (N-2^k),g (1*2^k+i) := by
    dsimp [S]; rw [one_mul,←sum_range_add, Nat.add_sub_of_le lo]
  have rem := trivial 1 k (N-2^k) (by decide) (by omega)
  have sparse := count_sparse hp (fun t ht => (late t ht).2) m
  have cnt : (∑ j ∈ range m, (if q (K+j)<M then (1:ℝ) else 0)) ≤ δ*m+1 := by
    rw [← sum_filter]; simp only [sum_const,nsmul_eq_mul,mul_one]
    have sc : (((range m).filter (fun j => q (K+j)<M)).card : ℝ) ≤ (m/H:ℕ)+1 := by exact_mod_cast sparse
    have leanDiv : ((m/H:ℕ):ℝ)*H ≤ m := by exact_mod_cast Nat.div_mul_le_self m H
    nlinarith only [sc,mul_le_mul_of_nonneg_left leanDiv dp.le,
      mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α:=ℝ) (m/H))]
  have old : ‖S (2^(K+1))‖+2 ≤ δ*k := by
    have jk : (J:ℝ) ≤ k := by exact_mod_cast (by omega : J≤k)
    linarith only [(div_lt_iff₀ dp).mp (hJ.trans_le jk)]
  have mass : (k:ℝ)*Real.log 2 ≤ (harmonic N:ℝ) := by
    calc _ = Real.log ((2:ℝ)^k) := (Real.log_pow ..).symm
         _ ≤ Real.log ((N+1:ℕ):ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast lo.trans (Nat.le_succ N))
         _ ≤ _ := log_add_one_le_harmonic N
  have normBound : ‖S N‖ ≤ 4*δ*k := by
    rw [endpt]; apply (norm_add_le ..).trans
    have all := full m; rw [km] at all
    have mk : (m:ℝ) ≤ k := by exact_mod_cast (by dsimp [m]; omega : m ≤ k)
    linarith only [mul_le_mul_of_nonneg_left mk dp.le,all,cnt,old,rem]
  have hpos : 0 < (harmonic N:ℝ) := (mul_pos (by exact_mod_cast (by omega : 0<k)) lp).trans_le mass
  rw [Real.dist_eq,logFrequency,div_sub' hpos.ne',abs_div, abs_of_pos hpos,div_lt_iff₀ hpos,
    ← eqn]
  refine normBound.trans_lt ?_
  have hhalf : 4*δ*k = (ε/2)*((k:ℝ)*Real.log 2) := by dsimp [δ]; ring
  rw [hhalf]
  exact (mul_le_mul_of_nonneg_left mass (half_pos ep).le).trans_lt (mul_lt_mul_of_pos_right (half_lt_self ep) hpos)

end NormalityChecker.QuadraticOrbit
