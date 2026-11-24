module

public import NormalityChecker.PolynomialMasks
public import NormalityChecker.SupportDiscrepancy
public import Mathlib.RingTheory.Localization.Integral

/-! Signed radix series on sparse smooth supports, including polynomial growth. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

/-- A signed rational weight has at most polynomial growth in its index. -/
def PolyGrowth (a : ℕ → ℚ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ m, |(a m : ℝ)| ≤ C * ((m : ℝ) + 1) ^ d

noncomputable def series (b : ℕ) (a : ℕ → ℚ) : ℝ := ∑' m, (a m : ℝ) / (b : ℝ) ^ m

def pre (b : ℕ) (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ range (n+1), (b : ℚ) ^ (n-m) * a m

/-- Polynomial coefficient growth gives absolute summability after radix discounting. -/
theorem summable_weight {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℚ} (growth : PolyGrowth a) :
    Summable (fun m => (a m : ℝ) / (b : ℝ) ^ m) := by
  obtain ⟨C, hC, d, bound⟩ := growth
  let q := (b : ℝ)⁻¹
  have b1 : (1:ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hq : 0 < q := inv_pos.mpr (zero_lt_one.trans b1)
  have hq' : q < 1 := inv_lt_one_of_one_lt₀ b1
  have sm := summable_pow_mul_geometric_of_norm_lt_one d (by simpa [Real.norm_eq_abs, abs_of_pos hq] : ‖q‖ < 1)
  have shifted := (((summable_nat_add_iff 1).mpr sm).mul_right q⁻¹).mul_left C
  apply shifted.of_norm_bounded
  intro m
  simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α:=ℝ) b) m)]
  calc _ ≤ C * ((m:ℝ)+1)^d * q^m := by
         simpa [q, div_eq_mul_inv] using div_le_div_of_nonneg_right (bound m) (pow_nonneg (Nat.cast_nonneg (α:=ℝ) b) m)
       _ = _ := by simp [pow_succ, hq.ne', mul_assoc]

/-- On blocks of length B at height O(B²), a forward gap of length B
makes the signed shifted tail uniformly small. -/
theorem gap_approximation {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℚ} (growth : PolyGrowth a)
    {δ : ℝ} (pos : 0 < δ) : ∀ᶠ B : ℕ in atTop, ∀ n ≤ 4*B^2,
      (∀ j < B, a (n+1+j) = 0) → |(b : ℝ)^n * series b a - (pre b a n : ℝ)| < δ := by
  let q := (b:ℝ)⁻¹
  have b1 : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have hq : 0<q := inv_pos.mpr (zero_lt_one.trans b1)
  have hq' : q<1 := inv_lt_one_of_one_lt₀ b1
  obtain ⟨C,hC,d,bound⟩ := growth
  obtain ⟨K,hK,tail⟩ := polynomial_gap_tail hq hq' d
  have limit := (tendsto_pow_const_div_const_pow_of_one_lt (2*d) b1).const_mul (q*C*7^d*K)
  simp only [mul_zero] at limit
  filter_upwards [eventually_ge_atTop 1, limit.eventually_lt_const pos] with B bp little n cap gap
  let f (m : ℕ) := (a m : ℝ)/(b:ℝ)^m
  have sm : Summable f := summable_weight hb ⟨C,hC,d,bound⟩
  have head : (b:ℝ)^n * (∑ m ∈ range (n+1), f m) = (pre b a n : ℝ) := by
    simp only [pre, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, mul_sum]
    apply sum_congr rfl
    intro m hm
    have mn : m ≤ n := mem_range_succ_iff.mp hm
    dsimp [f]
    rw [pow_sub₀ _ (zero_lt_one.trans b1).ne' mn]
    ring
  have split : (b:ℝ)^n * series b a - (pre b a n : ℝ) =
      q * ∑' j : ℕ, (a (n+1+j) : ℝ) * q^j := by
    change (b:ℝ)^n * (∑' m, f m) - _ = _
    rw [← sm.sum_add_tsum_nat_add (n+1), mul_add, head, add_sub_cancel_left,
      ← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro j
    simp [f, q, Nat.add_comm j (n+1), pow_add, pow_succ, field]
  have err := tail (fun m => (a m : ℝ)) C hC bound (n+1) B (by simpa using gap)
  have size : ((n+1:ℕ):ℝ)+B+1 ≤ 7*(B:ℝ)^2 := by
    push_cast
    have h : (n:ℝ) ≤ 4*(B:ℝ)^2 := by exact_mod_cast cap
    have one : (1:ℝ)≤B := by exact_mod_cast bp
    nlinarith [mul_nonneg (sub_nonneg.mpr one) (Nat.cast_nonneg (α:=ℝ) B)]
  rw [split, abs_mul, abs_of_pos hq]
  apply (mul_le_mul_of_nonneg_left err hq.le).trans_lt
  apply lt_of_le_of_lt _ little
  calc _ ≤ q*(C*(7*(B:ℝ)^2)^d*q^B*K) := by gcongr
       _ = _ := by simp [q, mul_pow, pow_mul, div_eq_mul_inv]; ring

/-- The series of the rational polynomial P(m)/mᵗ on the retained smooth indices. -/
def weights (S : Finset ℕ) (keep : ℕ → Bool) (P : ℚ[X]) (t m : ℕ) : ℚ :=
  if m ∈ Nat.factoredNumbers S ∧ keep m = true then P.eval (m:ℚ)/(m:ℚ)^t else 0

noncomputable def maskedValue (b : ℕ) (S : Finset ℕ) (keep : ℕ → Bool) (P : ℚ[X]) (t : ℕ) :=
  series b (weights S keep P t)

theorem weights_growth (S : Finset ℕ) (keep : ℕ → Bool) (P : ℚ[X]) (t : ℕ) :
    PolyGrowth (weights S keep P t) := by
  let C := ∑ i ∈ P.support, |(P.coeff i : ℝ)|
  refine ⟨C, sum_nonneg (fun _ _ => abs_nonneg _), P.natDegree, fun m => ?_⟩
  unfold weights
  split
  next h =>
    have mpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h.1.1
    rw [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, abs_div, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)^t)]
    apply (div_le_self (abs_nonneg _) (one_le_pow₀ (by exact_mod_cast mpos) : (1:ℝ) ≤ (m:ℝ)^t)).trans
    rw [eval_eq_sum, Polynomial.sum_def, Rat.cast_sum]
    apply (abs_sum_le_sum_abs ..).trans
    rw [show C = ∑ i ∈ P.support, |(P.coeff i : ℝ)| from rfl, sum_mul]
    apply sum_le_sum
    intro i hi
    simp only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)^i)]
    gcongr
    exact (pow_le_pow_left₀ (by positivity : 0 ≤ (m:ℝ)) (by linarith : (m:ℝ) ≤ m+1) i).trans
      (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) m] : (1:ℝ) ≤ m+1) (le_natDegree_of_mem_supp i hi))
  next => simp only [Rat.cast_zero, abs_zero]; exact mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)


/-- Geometric data shared by every smooth mask on a clean dyadic block. -/
structure Clean (S : Finset ℕ) (k n : ℕ) : Prop where
  start : 2^k ≤ n
  bound : n+2^k ≤ 4*(2^k)^2
  old : ∀ m ∈ Nat.factoredNumbers S, m < n+2*2^k → m+2^k ≤ n

/-- Transfer estimates on blocks with a forward and backward gap, charging
uncontrolled positions individually up to the actual cutoff. -/
theorem transfer {ι : Type*} (S : Finset ℕ) (f : ι → ℕ → ℂ) (unit : ∀ j n, ‖f j n‖ ≤ 1)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (localEst : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n → ∀ j,
      ‖∑ i ∈ range (2^k), f j (n+i)‖ ≤ η*((2^k:ℕ):ℝ) + ∑ i ∈ range (2^k), w (n+i)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ j,
      ‖∑ i ∈ range N, f j i‖ ≤ ε*N + ∑ i ∈ range N, w i := by
  intro ε pos
  have err := (tendsto_pow_const_div_const_pow_of_one_lt S.card (by norm_num : (1:ℝ)<2)).const_mul (5*5^S.card)
  simp only [mul_zero] at err
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((localEst (ε/2) (by positivity)).and
    ((eventually_ge_atTop 3).and (err.eventually_le_const (show 0<ε/2 by positivity))))
  filter_upwards [eventually_ge_atTop (4^K)] with N hN j
  let k := Nat.log 4 N
  obtain ⟨localBound,hk,small⟩ := hK k (Nat.le_log_of_pow_le (by decide) hN)
  let B := 2^k
  let D := 2*(k+2)
  have bp : 0<B := pow_pos (by decide) _
  have npos : 0<N := (pow_pos (by decide) K).trans_le hN
  have sq : B*B≤N := by
    change 2^k*2^k≤N; rw [← mul_pow]; exact Nat.pow_log_le_self 4 npos.ne'
  have up : N≤4*B^2 := by
    have h := (Nat.lt_pow_succ_log_self (by decide : 1<4) N).le
    simpa [B,k,pow_succ,sq,← mul_pow, Nat.mul_comm] using h
  have cap : N+B ≤ 2^D := by
    have hp : 2^D = 16*B^2 := by dsimp [B,D]; rw [pow_mul,pow_add,← pow_mul, Nat.mul_comm 2 k,pow_mul]; norm_num; ring
    rw [hp]; nlinarith
  let A := LocalizedSupport.indices S (2^D)
  let E := insert 0 (insertionBlocks A B 0 ∪ A.image (fun m => m/B-1))
  have card : E.card+1≤5*(D+1)^S.card := by
    have h := card_insertionBlocks A B 0
    have hu := card_union_le (insertionBlocks A B 0) (A.image fun m => m/B-1)
    have hi := card_insert_le 0 (insertionBlocks A B 0 ∪ A.image fun m => m/B-1)
    have hc : (A.image fun m => m/B-1).card ≤ A.card := card_image_le
    have ht : A.card ≤ (D+1)^S.card := LocalizedSupport.insertion_count S D
    have := Nat.one_le_pow S.card (D+1) (by omega)
    dsimp only [E]; omega
  have price : (E.card+1:ℝ)*B≤(ε/2)*N := by
    have dk : (D:ℝ)+1 ≤ 5*k := by
      dsimp [D]; push_cast
      have hkr : (3:ℝ)≤k := by exact_mod_cast hk
      linarith
    have cc : (E.card+1:ℝ)≤5*((D:ℝ)+1)^S.card := by exact_mod_cast card
    have v := cc.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) dk S.card) (by norm_num))
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

  rw [Nat.succ_mul] at endpt
  apply localBound (l*B) ⟨start, endpt.trans up, ?_⟩ j
  intro m hm hlt
  change m < l*B+2*B at hlt
  have hin : m∈A := LocalizedSupport.mem_indices.mpr ⟨by omega,hm⟩
  by_cases past : m < (l+1)*B
  · simpa using insertionBlocks_free (U:=0) bp (fun h => good (mem_insert_of_mem (mem_union_left _ h)))
      hin (by simpa using past)
  · have lo : l+1 ≤ m/B := (Nat.le_div_iff_mul_le bp).mpr (by omega)
    have hi : m/B < l+2 := (Nat.div_lt_iff_lt_mul bp).mpr (by simpa [Nat.add_mul] using hlt)
    exact False.elim (good (mem_insert_of_mem (mem_union_right _ (mem_image.mpr ⟨m,hin,by omega⟩))))

end NormalityChecker.PolynomialMasks
