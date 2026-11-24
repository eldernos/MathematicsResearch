module

public import NormalityChecker.JointPersistent

/-! Prefix-by-prefix discrepancy bounds for finite-support polylogarithms of every order. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

/-- Fraction of positions before a given cutoff having the specified property. -/
noncomputable def prefixShare (P : ℕ → Prop) [DecidablePred P] (N : ℕ) : ℝ :=
  (((range N).filter P).card : ℝ) / N

private lemma discrepancy_ge_interval {b N : ℕ} {x a e : ℝ} (ha : 0 ≤ a)
    (hlt : a < e) (he : e ≤ 1) :
    |frequency (shift b x) a e N - (e-a)| ≤ radixDiscrepancy b x N := by
  unfold radixDiscrepancy
  refine le_csSup (s := {d | ∃ u v : ℝ, 0≤u ∧ u<v ∧ v≤1 ∧ d=|frequency (shift b x) u v N-(v-u)|}) ?_ ⟨a,e,ha,hlt,he,rfl⟩
  refine ⟨1, ?_⟩
  rintro _ ⟨u,v,hu,huv,hv,rfl⟩
  have h := frequency_bounds (shift b x) u v N
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]

/-- At every sufficiently large cutoff, the positions at which all off-base
denominators have cleared give a discrepancy lower bound, with vanishing loss.
The modulus may be one. -/
theorem prefix_discrepancy_lower {b c s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b)
    (hc : 0 < c) (hs : 0 < s) (support : ∀ p ∈ A, p ∣ b*c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      prefixShare (fun n => c.Coprime (powerShifted b s A n).den) N - ε
        ≤ radixDiscrepancy b (powerValue b s A) N := by
  classical
  let x := powerValue b s A
  let P := powerShifted b s A
  let δ := min (ε/4) (1/4)
  have dp : 0 < δ := lt_min (by positivity) (by norm_num)
  have small : δ < 1/2 := (min_le_right ..).trans_lt (by norm_num)
  let inner (n : ℕ) := δ ≤ shift b x n ∧ shift b x n < 1-δ
  let f (_ : Unit) (n : ℕ) : ℂ := if inner n then 1 else 0
  let w (n : ℕ) : ℝ := if c.Coprime (P n).den then 0 else 1
  obtain ⟨K,tail⟩ := eventually_atTop.mp ((power_tail hb hs A).abs.eventually_lt_const
    (by simpa using dp : |(0:ℝ)| < δ))
  have transfer := transfer_clean_blocks (s:=s) A hb hc support f
    (fun _ _ => by simp only [f]; split <;> simp)
    w (fun _ => by dsimp [w]; split <;> norm_num) (by
      intro η hη
      refine ⟨K,fun B n hn _ div _ orbit _ => ?_⟩
      obtain ⟨t,ht⟩ := div
      apply (norm_sum_le ..).trans
      apply le_trans _ (le_add_of_nonneg_left (by positivity))
      apply sum_le_sum
      intro i hi
      by_cases clear : c.Coprime (P (n+i)).den
      · have dvd := Rat.mul_den_dvd ((b:ℚ)^i) (P n)
        have den : ((b:ℚ)^i).den=1 := by rw [← Nat.cast_pow]; simp
        rw [← orbit i (mem_range.mp hi),den,one_mul] at dvd
        have integral := Nat.eq_one_of_dvd_coprimes (clear.symm.pow_right t) dvd_rfl (dvd.trans ht)
        let z := (P (n+i)).num
        have eqn : (P (n+i):ℝ) = (z:ℝ) := by
          exact_mod_cast (by simpa [z,integral] using (P (n+i)).num_div_den.symm :
            P (n+i) = (z:ℚ))
        have near : |(b:ℝ)^(n+i)*x-(P (n+i):ℝ)| < δ := tail _ (hn.trans (Nat.le_add_right ..))
        rw [eqn] at near
        have miss : ¬inner (n+i) := by
          dsimp only [inner,shift]
          rw [← Int.fract_sub_intCast _ z]
          have h := abs_lt.mp near
          by_cases pos : 0 ≤ (b:ℝ)^(n+i)*x-z
          · rw [Int.fract_eq_self.mpr ⟨pos,by linarith⟩]; grind
          · rw [← Int.fract_add_one,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]; grind
        simp only [f,w,ite_eq_right miss,norm_zero]; split <;> norm_num
      · simp only [f,w,clear,ite_false]; split <;> simp)
  filter_upwards [transfer δ dp,eventually_gt_atTop 0] with N hT hN
  have h := hT ()
  simp only [f,w,sum_boole,Complex.norm_natCast] at h
  have complement : (∑ n ∈ range N, if c.Coprime (P n).den then (0:ℝ) else 1)
      = N - (((range N).filter (fun n => c.Coprime (P n).den)).card:ℝ) := by
    rw [eq_sub_iff_add_eq, ← sum_boole, ← sum_add_distrib]
    calc _ = ∑ _n ∈ range N, (1:ℝ) := by
           apply sum_congr rfl
           intro n _
           split <;> simp_all
         _ = _ := by simp
  rw [complement] at h
  have interval := (abs_le.mp (discrepancy_ge_interval (b:=b) (N:=N) (x:=x)
    dp.le (by linarith : δ < 1-δ) (by linarith))).1
  change -radixDiscrepancy b x N ≤ (((range N).filter inner).card:ℝ)/N - _ at interval
  change (((range N).filter (fun n => c.Coprime (P n).den)).card:ℝ)/N - ε ≤ _
  have np : (0:ℝ)<N := by exact_mod_cast hN
  rw [sub_le_iff_le_add,div_le_iff₀ np]
  have hi := (le_div_iff₀ np).mp (show 1-δ-δ-radixDiscrepancy b x N ≤
    (((range N).filter inner).card:ℝ)/N by linarith only [interval])
  have tiny : δ ≤ ε/4 := min_le_left ..
  change _ ≤ (radixDiscrepancy b x N + ε)*N
  nlinarith only [h,hi,mul_le_mul_of_nonneg_right tiny np.le, mul_nonneg dp.le np.le]

/-- A surviving position controls its whole clean block. The exceptional share
is measured at the same cutoff as the discrepancy. -/
theorem prefix_discrepancy_of_survival {b c s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b)
    (hc : 1 < c) (cop : b.Coprime c) (hs : 0 < s) (support : ∀ p ∈ A, p ∣ b*c)
    (bad : ℕ → Prop) [DecidablePred bad]
    (survives : ∀ M : ℕ, ∀ᶠ n : ℕ in atTop, ¬bad n → M ≤ (powerShifted b s A n).den) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, radixDiscrepancy b (powerValue b s A) N ≤
      prefixShare bad N + ε := by
  classical
  let x := powerValue b s A
  let P := powerShifted b s A
  let w (n : ℕ) : ℝ := if bad n then 1 else 0
  let I := {v : ℝ × ℝ // 0≤v.1 ∧ v.1≤v.2 ∧ v.2≤1}
  let f (j : I) := Localized.centered (shift b x) j.val.1 j.val.2
  have transfer := transfer_clean_blocks (s:=s) A hb hc.le support f
    (fun j => Localized.centered_norm _ j.prop.1 j.prop.2.1 j.prop.2.2) w
    (fun _ => by dsimp [w]; split <;> norm_num) (by
      intro η pos
      obtain ⟨M,K,hK⟩ := smooth_interval_block (d:=4*c*s) (fixed_support_orbit_estimate hb hc cop)
        x P (power_tail hb hs A) pos
      obtain ⟨K',large⟩ := eventually_atTop.mp (survives M)
      refine ⟨max K K',fun B n nk _ div top orb j => ?_⟩
      by_cases some : ∃ i<B, ¬ bad (n+i)
      · obtain ⟨i,hi,ok⟩ := some
        have dvd := Rat.mul_den_dvd ((b:ℚ)^i) (P n)
        have den : ((b:ℚ)^i).den=1 := by rw [← Nat.cast_pow]; simp
        rw [← orb i hi,den,one_mul] at dvd
        have lo := (large (n+i) ((le_max_right ..).trans (nk.trans (Nat.le_add_right ..))) ok).trans
          (Nat.le_of_dvd (P n).pos dvd)
        apply (hK B n ((le_max_left ..).trans nk) lo div top orb _ _ j.prop.1 j.prop.2.1 j.prop.2.2).trans
        exact le_add_of_nonneg_right (sum_nonneg (fun _ _ => by dsimp [w]; split <;> norm_num))
      · have allBad (i : ℕ) (hi : i∈range B) : w (n+i)=1 := by dsimp [w]; split <;> grind
        rw [sum_congr rfl allBad]
        simp only [sum_const,card_range,nsmul_eq_mul,mul_one]
        exact (norm_sum_le ..).trans ((sum_le_sum (fun i (_ : i∈range B) =>
          Localized.centered_norm _ j.prop.1 j.prop.2.1 j.prop.2.2 _)).trans (by simp; positivity)))
  filter_upwards [transfer ε hε,eventually_gt_atTop 0] with N ht hN
  refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
  rintro _ ⟨a,e,ha,lt,he,rfl⟩
  have h := ht ⟨(a,e),ha,lt.le,he⟩
  dsimp only [f] at h
  have eqn := Localized.centered_sum (shift b x) a e 0 N
  simp only [zero_add] at eqn
  rw [eqn] at h
  change |((IntervalFourier.count (shift b x) a e N:ℝ)/N)-(e-a)| ≤ _
  have np : (0:ℝ)<N := by exact_mod_cast hN
  rw [div_sub' np.ne',abs_div,abs_of_pos np,div_le_iff₀ np]
  simp only [prefixShare,add_mul,div_mul_cancel₀ _ np.ne']
  simpa only [w,sum_boole,add_comm, mul_comm] using h

/-- Every diverging denominator threshold gives an upper bound on each prefix. -/
theorem prefix_discrepancy_upper {b c s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b)
    (hc : 1 < c) (cop : b.Coprime c) (hs : 0 < s) (support : ∀ p ∈ A, p ∣ b*c)
    (T : ℕ → ℕ) (grow : Tendsto T atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, radixDiscrepancy b (powerValue b s A) N ≤
      prefixShare (fun n => (powerShifted b s A n).den < T n) N + ε := by
  apply prefix_discrepancy_of_survival A hb hc cop hs support _ _ hε
  intro M
  filter_upwards [grow.eventually_ge_atTop M] with n hn large
  exact hn.trans (le_of_not_gt large)

/-- For all-base supports discrepancy converges to one along every cutoff. -/
theorem prefix_discrepancy_tendsTo_one {b s : ℕ} (A : Finset ℕ) (hb : 2 ≤ b) (hs : 0 < s)
    (base : ∀ p ∈ A, p ∣ b) :
    Tendsto (radixDiscrepancy b (powerValue b s A)) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [prefix_discrepancy_lower (c:=1) A hb (by decide) hs (by simpa using base)
      (half_pos hε), eventually_gt_atTop 0] with N lower hN
  simp [prefixShare, hN.ne'] at lower
  have upper := (radix_discrepancy_bounds b (powerValue b s A) N).2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end NormalityChecker.LocalizedSupport
