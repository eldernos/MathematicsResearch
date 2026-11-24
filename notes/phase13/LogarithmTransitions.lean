import NormalityChecker.FirstFrequency

/-! A finite-prefix consequence of the integral estimate for log 2. -/

open Finset Filter
namespace NormalityChecker.Phase13

/-- A narrow interval meeting the central part of the orbit cannot contain
two consecutive shifts. Counting this case also handles intervals far from zero. -/
theorem discrepancy_of_interior (x : ℝ) {N : ℕ} (hN : 2 ≤ N) {r : ℝ}
    (hr : 0 < r) (hr' : r ≤ 1/4) :
    binaryDiscrepancy x N ≤ max (1-r) (1-frequency (shift 2 x) (2*r) (1-2*r) N) := by
  classical
  let v := shift 2 x
  let G := (range N).filter (fun n => 2*r ≤ v n ∧ v n < 1-2*r)
  let g := (G.card : ℝ)/N
  let M := max (1-r) (1-g)
  have w : 1-r ≤ M := le_max_left ..
  have u : 1-g ≤ M := le_max_right ..
  have hpos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  apply discrepancy_le
  intro a c ha hac hc
  let P (n : ℕ) := a ≤ v n ∧ v n < c
  let I := (range N).filter P
  let f := (I.card : ℝ)/N
  obtain ⟨hf₀,hf₁⟩ := (show 0 ≤ f ∧ f ≤ 1 from frequency_bounds v a c N)
  change |f-(c-a)| ≤ M
  apply abs_le.mpr
  constructor
  · by_cases h : c-a ≤ 1-r
    · linarith
    have sub : G ⊆ I := by
      intro n hn
      obtain ⟨hNn,hl,hu⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hNn,by change a ≤ v n ∧ v n < c; constructor <;> linarith⟩
    have : g ≤ f := div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card sub)) hpos.le
    linarith
  · by_cases h : r ≤ c-a
    · linarith
    by_cases ends : c ≤ 2*r ∨ 1-2*r ≤ a
    · have dis : Disjoint I G := by
        apply disjoint_left.mpr
        intro n hn hn'
        obtain ⟨h₁,h₂⟩ := (mem_filter.mp hn).2
        obtain ⟨h₃,h₄⟩ := (mem_filter.mp hn').2
        rcases ends with h|h <;> linarith
      have sub : I ∪ G ⊆ range N := union_subset (filter_subset ..) (filter_subset ..)
      have card := card_le_card sub
      rw [card_union_of_disjoint dis,card_range] at card
      have : f+g ≤ 1 := by
        change _ / (N:ℝ) + _ / N ≤ 1
        rw [← add_div,div_le_one hpos]
        exact_mod_cast card
      linarith
    · have miss (n : ℕ) (_ : True) : ∃ j≤1, ¬P (n+j) := by
        by_cases hp : P n
        · refine ⟨1,le_rfl,?_⟩
          intro hs
          obtain ⟨h₁,h₂⟩ := hp
          obtain ⟨h₃,h₄⟩ := hs
          change a ≤ shift 2 x (n+1) at h₃
          change shift 2 x (n+1) < c at h₄
          change a ≤ shift 2 x n at h₁
          change shift 2 x n < c at h₂
          rw [binary_shift_step] at h₃ h₄
          push Not at ends
          split_ifs at h₃ h₄ <;> linarith
        · exact ⟨0,by decide,by simpa using hp⟩
      have cnt := count_within_steps (P:=fun _ => True) (Q:=fun n => ¬P n) N 1 miss
      simp at cnt
      have split := card_filter_add_card_filter_not (s:=range N) P
      rw [card_range] at split
      have num : 2 * I.card ≤ N + 1 := by dsimp [I]; omega
      have realNum : 2 * (I.card : ℝ) ≤ N+1 := by exact_mod_cast num
      have two : (2:ℝ) ≤ N := by exact_mod_cast hN
      have : f ≤ 3/4 := by
        apply (div_le_iff₀ hpos).mpr
        linarith
      linarith

/-- Pull a transition back through any number of binary shifts. -/
theorem interior_before_transition {x : ℝ} (n j : ℕ)
    (h : 1/4 ≤ shift 2 x (n+j) ∧ shift 2 x (n+j) < 3/4) :
    (1/2:ℝ)^j/4 ≤ shift 2 x n ∧ shift 2 x n < 1-(1/2:ℝ)^j/4 := by
  induction j generalizing n with
  | zero => norm_num at h ⊢; exact h
  | succ j ih =>
    have step := ih (n+1) (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using h)
    rw [binary_shift_step] at step
    rw [pow_succ]
    split_ifs at step <;> constructor <;> linarith [step.1,step.2]

/-- Each of k disjoint geometric shells supplies k earlier interior shifts. -/
private theorem shell_count : ∃ K : ℕ, ∀ k ≥ K, ∀ N : ℕ, 68^(2*k) ≤ N →
    let a := (1/2:ℝ)^k/4
    k*k ≤ ((range N).filter (fun n => a ≤ shift 2 (Real.log 2) n ∧
      shift 2 (Real.log 2) n < 1-a)).card := by
  classical
  obtain ⟨K,hK⟩ := eventually_atTop.mp logTwo_window_hit
  refine ⟨K,fun k hk N hN => ?_⟩
  let a := (1/2:ℝ)^k/4
  let S (m : ℕ) := (range m).filter (fun n => a ≤ shift 2 (Real.log 2) n ∧
    shift 2 (Real.log 2) n < 1-a)
  have mono : Monotone S := fun _ _ h => filter_subset_filter _ (range_mono h)
  have count (j : ℕ) : j*k ≤ (S (68^(k+j))).card := by
    induction j with
    | zero => simp
    | succ j ih =>
      let s : ℕ := 68^(k+j)
      have ks : k ≤ s :=
        (show k ≤ 2^(k+j) from (by omega : k≤k+j).trans Nat.lt_two_pow_self.le).trans
          (Nat.pow_le_pow_left (by decide : 2≤68) _)
      obtain ⟨t,lt₁,lt₂,_,bits⟩ := hK (2*s) (by omega)
      let B := Ico (t+1-k) (t+1)
      have cardB : B.card=k := by simp only [B,Nat.card_Ico]; omega
      have dis : Disjoint (S s) B := by
        apply disjoint_left.mpr
        intro n hn hb
        have := mem_range.mp (mem_filter.mp hn).1
        have := (mem_Ico.mp hb).1
        omega
      have sub : S s ∪ B ⊆ S (68*s) := by
        apply union_subset (mono (by omega))
        intro n hn
        obtain ⟨lower,upper⟩ := mem_Ico.mp hn
        have le : n ≤ t := by omega
        have dist : t-n ≤ k := by omega
        have interior := interior_before_transition n (t-n) (by
          simpa [Nat.add_sub_of_le le] using (transition_iff_bits _ _).mpr bits)
        have width := pow_le_pow_of_le_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num) dist
        apply mem_filter.mpr
        exact ⟨mem_range.mpr (by omega),by dsimp [a]; linarith [interior.1],
          by dsimp [a]; linarith [interior.2]⟩
      have card := card_le_card sub
      rw [card_union_of_disjoint dis,cardB] at card
      change j*k ≤ (S s).card at ih
      rw [show k + (j + 1) = (k+j)+1 by omega, pow_succ',Nat.succ_mul]
      exact (Nat.add_le_add_right ih k).trans card
  exact (count k).trans (card_le_card (mono (by simpa [two_mul] using hN)))

/-- For all sufficiently large k, every prefix of at least 68^(2k) shifts
has discrepancy gap at least k²/N. Taking k = floor((log base 68 of N)/2)
gives an unconditional squared-logarithm numerator at every large cutoff. -/
theorem logTwo_squared_log_gap :
    ∃ K : ℕ, ∀ k ≥ K, ∀ N : ℕ, 68^(2*k) ≤ N →
      binaryDiscrepancy (Real.log 2) N ≤ 1-((k*k:ℕ):ℝ)/N := by
  classical
  obtain ⟨K,hK⟩ := shell_count
  refine ⟨max K 1,fun k hk N hN => ?_⟩
  have hk' : 1 ≤ k := (le_max_right ..).trans hk
  have two : 2 ≤ N := (show 2 ≤ 68^(2*k) by
    calc
      2 ≤ 68^1 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)).trans hN
  have pos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  let r := (1/2:ℝ)^k/8
  have rpos : 0<r := by dsimp [r]; positivity
  have rb : r≤1/4 := by
    dsimp [r]
    linarith [pow_le_one₀ (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)≤1) (n:=k)]
  have mass : ((k*k:ℕ):ℝ)/N ≤ frequency (shift 2 (Real.log 2)) (2*r) (1-2*r) N := by
    rw [show 2*r=(1/2:ℝ)^k/4 by dsimp [r]; ring]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hK k ((le_max_left ..).trans hk) N hN)) pos.le
  have size : ((k*k:ℕ):ℝ)/N ≤ r := by
    have kpow : k ≤ 2^k := Nat.lt_two_pow_self.le
    have h8 : 8 ≤ 8^k := (show 8 ≤ 8^1 by decide).trans (Nat.pow_le_pow_right (by decide) hk')
    have num : 8*2^k*(k*k) ≤ N := calc
      _ ≤ 8^k*2^k*(2^k*2^k) := by gcongr
      _ = 64^k := by rw [← mul_pow,← mul_pow,← mul_pow]; norm_num
      _ ≤ 68^(2*k) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) _
      _ ≤ N := hN
    have bound : 8*(2:ℝ)^k*((k*k:ℕ):ℝ) ≤ N := by exact_mod_cast num
    dsimp only [r]
    rw [one_div_pow,div_le_iff₀ pos]
    field_simp
    nlinarith only [bound]
  exact (discrepancy_of_interior _ two rpos rb).trans
    (max_le (sub_le_sub_left size 1) (sub_le_sub_left mass 1))

/-- All sufficiently large prefixes, with the block length chosen as a function of N. -/
theorem logTwo_all_prefix_gap :
    ∀ᶠ N : ℕ in atTop,
      let k := Nat.log 68 N / 2
      binaryDiscrepancy (Real.log 2) N ≤ 1-((k*k:ℕ):ℝ)/N := by
  obtain ⟨K,hK⟩ := logTwo_squared_log_gap
  filter_upwards [eventually_ge_atTop (68^(2*K)),eventually_gt_atTop 0] with N hN pos
  have grow := Nat.le_log_of_pow_le (by decide : 1<68) hN
  apply hK _ (by omega) N
  exact (Nat.pow_le_pow_right (by decide : 0<68)
    (show 2*(Nat.log 68 N/2) ≤ Nat.log 68 N by omega)).trans (Nat.pow_log_le_self _ pos.ne')

open Real

private theorem reverse_triangle_sqrt_sum (s : Finset ℕ) (f g : ℕ → ℝ) :
    |√(∑ n ∈ s, f n ^ 2) - √(∑ n ∈ s, g n ^ 2)| ≤ √(∑ n ∈ s, (f n - g n)^2) := by
  have cs := Real.sum_mul_le_sqrt_mul_sqrt s f g
  have split : ∑ n ∈ s, (f n - g n)^2 =
      (∑ n ∈ s, f n ^ 2) + (∑ n ∈ s, g n ^ 2) - 2*(∑ n ∈ s, f n*g n) := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs,split]
  nlinarith only [cs, Real.sq_sqrt (show 0 ≤ ∑ n ∈ s, f n^2 by positivity),
    Real.sq_sqrt (show 0 ≤ ∑ n ∈ s, g n^2 by positivity)]

/-- Unnormalized Fourier costs on a tail interval: their square roots differ
by at most π sqrt(2/M), uniformly in the interval length. -/
theorem logTwo_fourier_tail_stability {M : ℕ} (hM : 0 < M) (k : ℕ) :
    |√(∑ j ∈ range k, cosineEscape ((2:ℝ)^(M+j)*log 2)) -
      √(∑ j ∈ range k, cosineEscape (logPrefix (M+j)))| ≤ π*√(2/(M:ℝ)) := by
  let a (j : ℕ) := (2:ℝ)^(M+j)*log 2
  let b (j : ℕ) := (logPrefix (M+j):ℝ)
  let f (u : ℝ) := √2 * sin (π*u)
  have sqf (u : ℝ) : f u ^ 2 = cosineEscape u := by
    dsimp [f,cosineEscape]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2), mul_assoc,cos_two_mul]
    nlinarith only [sin_sq_add_cos_sq (π*u)]
  have Mpos : (0:ℝ)<M := by exact_mod_cast hM
  have cost (j : ℕ) : (f (a j)-f (b j))^2 ≤
      (2*π^2) * ((1/((M:ℝ)+j)) - 1/((M:ℝ)+j+1)) := by
    obtain ⟨lo,hi⟩ := logTwo_tail_bounds (M+j)
    change 0 ≤ a j - b j at lo
    change a j - b j ≤ 1/((M+j:ℕ)+1:ℝ) at hi
    push_cast at hi
    have lip := abs_sin_sub_sin_le (π*a j) (π*b j)
    rw [← mul_sub,abs_mul,abs_of_pos pi_pos,abs_of_nonneg lo] at lip
    have upper := lip.trans (mul_le_mul_of_nonneg_left hi pi_pos.le)
    have sqBound := sq_le_sq' ((neg_abs_le _).trans' (neg_le_neg upper))
      ((le_abs_self _).trans upper)
    have A : 0 < (M:ℝ)+j := by positivity
    have B : 0 < (M:ℝ)+j+1 := by positivity
    have frac : (1/((M:ℝ)+j+1))^2 ≤ (1/((M:ℝ)+j)) - 1/((M:ℝ)+j+1) := by
      field_simp
      nlinarith only [A,B]
    dsimp [f]
    rw [← mul_sub,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    rw [mul_pow] at sqBound
    nlinarith only [sqBound, mul_le_mul_of_nonneg_left frac (sq_nonneg π)]
  have bound := sum_le_sum (s:=range k) (fun j _ => cost j)
  rw [← Finset.mul_sum] at bound
  have telesc := sum_range_sub (fun j : ℕ => -(1/((M:ℝ)+j))) k
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero,sub_neg_eq_add] at telesc
  have tsum : (∑ j ∈ range k, (1/((M:ℝ)+j) - 1/((M:ℝ)+j+1))) =
      1/(M:ℝ)-1/((M:ℝ)+k) := by
    simpa only [add_assoc,sub_eq_add_neg,add_comm (-(1 / _ : ℝ))] using telesc
  rw [tsum] at bound
  have total : (∑ j ∈ range k, (f (a j)-f (b j))^2) ≤ (π*√(2/(M:ℝ)))^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity : 0≤2/(M:ℝ))]
    apply bound.trans
    calc
      _ ≤ (2*π^2)*(1/(M:ℝ)) := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
      _ = _ := by ring
  have triangle := reverse_triangle_sqrt_sum (range k) (fun j => f (a j)) (fun j => f (b j))
  simp only [sqf] at triangle
  exact triangle.trans ((Real.sqrt_le_sqrt total).trans_eq (Real.sqrt_sq (by positivity)))

end NormalityChecker.Phase13
