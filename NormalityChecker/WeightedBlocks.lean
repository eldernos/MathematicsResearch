module

public import NormalityChecker.SmoothCertificates
public import NormalityChecker.LocalizedDiscrepancy

/-! Charge uncontrolled positions individually, including the last partial scale. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- A bad full block costs its length. A nonnegative charge on good blocks is
summed only over observations actually present in the prefix. -/
theorem charged_prefix_bound (f : ℕ → ℂ) (unit : ∀ n, ‖f n‖ ≤ 1)
    (w : ℕ → ℝ) (pos : ∀ n, 0≤w n) {N B : ℕ} (hb : 0<B) (E : Finset ℕ) {η : ℝ} (he : 0≤η)
    (good : ∀ l<N/B, l∉E → ‖∑ i ∈ range B,f (l*B+i)‖ ≤ η*B+∑ i ∈ range B,w (l*B+i)) :
    ‖∑ i ∈ range N,f i‖ ≤ η*N+(∑ i ∈ range N,w i)+(E.card+1:ℝ)*B := by
  let K := N/B
  have cut : K*B+N%B=N := by simpa [K,Nat.mul_comm] using Nat.div_add_mod N B
  have kb : K*B≤N := by omega
  have trivial (s t : ℕ) : ‖∑ i ∈ range t, f (s+i)‖≤t :=
    (norm_sum_le ..).trans ((sum_le_sum (fun i _ => unit (s+i))).trans_eq (by simp))
  have each (l : ℕ) (hl : l∈range K) : ‖∑ i ∈ range B,f (l*B+i)‖ ≤
      η*B+(∑ i ∈ range B,w (l*B+i))+(if l∈E then (B:ℝ) else 0) := by
    split_ifs with h
    · have := trivial (l*B) B; have := sum_nonneg (s:=range B) (fun i _ => pos (l*B+i)); nlinarith only [‹_ ≤ (B:ℝ)›,this,mul_nonneg he (Nat.cast_nonneg B)]
    · simpa using good l (mem_range.mp hl) h
  have charge : (∑ l∈range K,∑ i∈range B,w (l*B+i)) ≤ ∑ i∈range N,w i := by
    have split : ∀ k, (∑ l∈range k,∑ i∈range B,w (l*B+i)) = ∑ i∈range (k*B),w i := by
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [sum_range_succ,ih,Nat.succ_mul,sum_range_add]
    rw [split]; exact sum_le_sum_of_subset_of_nonneg (range_mono kb) (fun i _ _ => pos i)
  have bulk := (norm_sum_le _ _).trans (sum_le_sum each)
  simp only [sum_add_distrib,← sum_filter,sum_const,card_range,nsmul_eq_mul] at bulk
  have exc := card_le_card (show (range K).filter (·∈E) ⊆ E from fun _ h => (mem_filter.mp h).2)
  have budget : (K:ℝ)*(η*B)≤η*N := by rw [mul_left_comm,← Nat.cast_mul]; gcongr
  have tail := (trivial (K*B) (N%B)).trans (by exact_mod_cast (Nat.mod_lt N hb).le : ((N%B:ℕ):ℝ)≤B)
  have decomp : (∑ i∈range N,f i) = (∑ l∈range K,∑ i∈range B,f (l*B+i)) + ∑ i∈range (N%B),f (K*B+i) := by
    conv_lhs => rw [← cut,sum_range_add]
    simpa using congrArg (· + ∑ i∈range (N%B),f (K*B+i)) (split_blocks f 0 B K)
  rw [decomp]; apply (norm_add_le ..).trans
  have weighted := mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr exc) (Nat.cast_nonneg B)
  linarith only [bulk,tail,budget,charge,weighted]

namespace LocalizedSupport
/-- Transfer a local bound to all prefix lengths, uniformly over a family of
observables (for example, all intervals). The cutoff and errors may depend on the support. -/
theorem transfer_clean_blocks {ι : Type*} {b c s : ℕ} (A : Finset ℕ) (hb : 2≤b) (hc : 0<c)
    (support : ∀ p∈A, p∣b*c) (f : ι → ℕ → ℂ) (unit : ∀ j n, ‖f j n‖≤1) (w : ℕ → ℝ) (hw : ∀ n, 0≤w n)
    (localBound : ∀ η : ℝ, 0<η → ∃ n₀ : ℕ, ∀ B n : ℕ, n₀≤n → 0<B →
      let P := powerShifted b s A
      (∃ t : ℕ, (P n).den∣c^t) → (P n).den≤B^(4*c*s) → (∀ i<B, P (n+i)=(b:ℚ)^i*P n) →
      ∀ j, ‖∑ i∈range B,f j (n+i)‖ ≤ η*B + ∑ i∈range B,w (n+i)) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, ∀ j, ‖∑ i∈range N,f j i‖ ≤ ε*N+∑ i∈range N,w i := by
  intro ε pos
  obtain ⟨n₀,localEst⟩ := localBound (ε/2) (by positivity)
  have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have err := (tendsto_pow_const_div_const_pow_of_one_lt A.card (by norm_num : (1:ℝ)<2)).const_mul (4*5^A.card)
  have clear := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul (4*(s:ℝ))
  simp only [mul_zero,pow_one] at err clear
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((grow.eventually_ge_atTop n₀).and ((eventually_ge_atTop 3).and
    ((err.eventually_le_const (show 0<ε/2 by positivity)).and (clear.eventually_le_const zero_lt_one))))
  filter_upwards [eventually_ge_atTop (4^K)] with N hN j
  let k := Nat.log 4 N
  obtain ⟨large,hk,small,budget⟩ := hK k (Nat.le_log_of_pow_le (by decide) hN)
  let B := 2^k
  let D := 2*(k+1)
  have bp : 0<B := pow_pos (by decide) _
  have npos : 0<N := (pow_pos (by decide) K).trans_le hN
  have sq : B*B≤N := by
    change 2^k*2^k≤N; rw [← mul_pow]; exact Nat.pow_log_le_self 4 npos.ne'
  have up : N≤2^D := by simpa [D,pow_mul] using (Nat.lt_pow_succ_log_self (by decide : 1<4) N).le
  have delay : D*s≤B := by
    rw [← mul_div_assoc,div_le_iff₀ (by positivity),one_mul] at budget
    have h : 4*s*k≤2^k := by exact_mod_cast budget
    dsimp [D,B]; nlinarith
  let E := insert 0 (insertionBlocks (indices A (2^D)) B 0)
  have card : E.card+1≤4*(D+1)^A.card := by
    have h := (card_insertionBlocks (indices A (2^D)) B 0).trans (Nat.mul_le_mul_left 2 (insertion_count A D))
    have h' := card_insert_le 0 (insertionBlocks (indices A (2^D)) B 0)
    have := Nat.one_le_pow A.card (D+1) (by omega); dsimp [E]; omega
  have price : (E.card+1:ℝ)*B≤(ε/2)*N := by
    have dk : (D:ℝ)+1 ≤ 5*k := by
      dsimp [D]; push_cast
      have hkr : (3:ℝ)≤k := by exact_mod_cast hk
      linarith
    have cc : (E.card+1:ℝ)≤4*((D:ℝ)+1)^A.card := by exact_mod_cast card
    have v := cc.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) dk A.card) (by norm_num))
    rw [mul_pow] at v; rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at small
    have v' : (E.card+1:ℝ) ≤ ε/2*(B:ℝ) := by push_cast [B]; linarith only [v,small]
    calc _ ≤ ε/2*(B:ℝ)*B := by gcongr
         _ ≤ ε/2*N := by rw [mul_assoc,← Nat.cast_mul]; gcongr
  apply (charged_prefix_bound (f j) (unit j) w hw bp E (by positivity : 0≤ε/2) ?_).trans
  · linarith only [price]
  intro l hl good
  have ne : l≠0 := fun h => good (h ▸ mem_insert_self ..)
  have endpt : (l+1)*B ≤ N := (Nat.le_div_iff_mul_le bp).mp hl
  have start := Nat.le_mul_of_pos_left B (Nat.pos_of_ne_zero ne)
  have old {m} (hm : m∈Nat.factoredNumbers A) (lt : m<(l+1)*B) : m+B≤l*B := by
    simpa using insertionBlocks_free (U:=0) bp (fun h => good (mem_insert_of_mem h))
      (mem_indices.mpr ⟨lt.le.trans (endpt.trans up),hm⟩) (by simpa using lt)
  have le : l*B≤2^D := (Nat.mul_le_mul_right _ (Nat.le_succ l)).trans (endpt.trans up)
  have dd := clean_power_denominator (n:=l*B) (order:=s) (by omega : 0<b) hc support le (fun m hm => by
    obtain ⟨mn,ms⟩ := mem_indices.mp hm; have h := old ms (by rw [Nat.succ_mul]; omega : m<(l+1)*B); omega)
  have top : (c^D)^s ≤ B^(4*c*s) := by
    rw [pow_mul B (4*c)]; apply Nat.pow_le_pow_left _ _
    calc c^D ≤ (2^c)^D := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
         _ ≤ B^(4*c) := by dsimp [B,D]; rw [← pow_mul,← pow_mul]; apply Nat.pow_le_pow_right (by decide); nlinarith
  apply localEst B (l*B) (large.trans start) bp ⟨D*s,by simpa [pow_mul] using dd⟩ ((Nat.le_of_dvd (by positivity) dd).trans top) _ j
  intro i hi
  have equal : indices A (l*B+i)=indices A (l*B) := by
    ext m; simp only [mem_indices]; constructor
    · rintro ⟨le,hm⟩; have h := old hm (by rw [Nat.succ_mul]; omega : m<(l+1)*B); exact ⟨by omega,hm⟩
    · rintro ⟨le,hm⟩; exact ⟨by omega,hm⟩
  simp only [powerShifted,powerPartial,equal,pow_add]; ring

end LocalizedSupport
end NormalityChecker
