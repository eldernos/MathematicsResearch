module

public import NormalityChecker.HigherOrderCells
public import NormalityChecker.ThresholdDifferences

/-! Cofactor differences of the checker's infinite local moment. -/
@[expose] public section
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
namespace NormalityChecker.LocalizedSupport.Unsigned

variable {p : ℕ} [hp : Fact p.Prime]

lemma prime_power_mem {S : Finset ℕ} {q : ℕ} (hq : q.Prime) (qS : q ∈ S) (a : ℕ) :
    q^a ∈ Nat.factoredNumbers S := by
  apply Nat.mem_factoredNumbers'.mpr
  intro d hd dv
  rcases (Nat.dvd_prime hq).mp (hd.dvd_of_dvd_pow dv) with one | eqn
  · exact (hd.ne_one one).elim
  · exact eqn ▸ qS

def row (S : Finset ℕ) (A : ℕ → ℤ_[p]) (s cut : ℕ) : ℤ_[p] :=
  ∑ m ∈ indices S cut, A m * (m : ℤ_[p]).inv ^ s

def moment (S : Finset ℕ) (A : ℕ → ℤ_[p]) (s : ℕ) (t : ℝ) : ℤ_[p] :=
  ∑' i : ℕ, ((p : ℤ_[p])^s)^i * row S A s ⌊t * (p : ℝ)^i⌋₊

theorem moment_unsigned (S : Finset ℕ) (w : ℤ_[p]) (s : ℕ) (t : ℝ) :
    moment S (fun m => w^m) s t = phaseMoment S w s t := rfl

lemma rows_summable {s : ℕ} (hs : 0 < s) (v : ℕ → ℤ_[p]) :
    Summable (fun i : ℕ => ((p : ℤ_[p])^s)^i * v i) := by
  have small : ‖(p : ℤ_[p])^s‖ < 1 := by
    rw [norm_pow, PadicInt.norm_p]
    exact pow_lt_one₀ (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)) hs.ne'
  apply (summable_geometric_of_lt_one (norm_nonneg _) small).of_norm_bounded
  intro i
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

lemma moment_tail (S : Finset ℕ) (A : ℕ → ℤ_[p]) {s : ℕ} (hs : 0 < s) (t : ℝ) (k : ℕ) :
    ∃ e : ℤ_[p], moment S A s t =
      (∑ i ∈ range k, ((p : ℤ_[p])^s)^i * row S A s ⌊t * (p : ℝ)^i⌋₊) +
      ((p : ℤ_[p])^s)^k * e := by
  let v (i : ℕ) := row S A s ⌊t * (p : ℝ)^i⌋₊
  refine ⟨∑' i : ℕ, ((p : ℤ_[p])^s)^i * v (i+k), ?_⟩
  rw [moment, ← (rows_summable hs v).sum_add_tsum_nat_add k,
    ← (rows_summable hs (fun i => v (i+k))).tsum_mul_left]
  congr 1
  apply tsum_congr
  intro i
  rw [pow_add]
  ring

/-- At phases below one the first row is empty. Scaling up by a power of the
selected prime therefore preserves zeros as long as the final phase is below p. -/
lemma moment_scale_down (S : Finset ℕ) (A : ℕ → ℤ_[p]) {s : ℕ} (hs : 0 < s)
    {t : ℝ} (ht : t < p) (k : ℕ) :
    moment S A s (t / (p : ℝ)^k) = ((p : ℤ_[p])^s)^k * moment S A s t := by
  have pp : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have step (x : ℝ) (hx : x < p) : moment S A s (x/p) = (p : ℤ_[p])^s * moment S A s x := by
    have floor0 : ⌊x/(p:ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one pp).mpr hx)
    have emp : indices S 0 = ∅ := by
      ext m
      simp only [mem_indices, Nat.le_zero, notMem_empty, iff_false]
      rintro ⟨rfl, h⟩
      exact h.1 rfl
    unfold moment
    rw [(rows_summable hs _).tsum_eq_zero_add, ← (rows_summable hs _).tsum_mul_left]
    simp only [pow_zero, mul_one, floor0, row, emp, sum_empty, mul_zero, zero_add]
    apply tsum_congr
    intro i
    rw [pow_succ, pow_succ, div_mul_eq_mul_div, ← mul_assoc x, mul_div_cancel_right₀ _ pp.ne']
    ring
  induction k with
  | zero => simp
  | succ k ih =>
    have upper : t/(p:ℝ)^k < p := by
      apply (div_lt_iff₀ (pow_pos pp _)).mpr
      exact ht.trans_le (le_mul_of_one_le_right pp.le (one_le_pow₀ (by exact_mod_cast hp.out.one_le)))
    rw [pow_succ, ← div_div, step _ upper, ih, pow_succ]
    ring

/-- Multiplying a cofactor by Q shifts the argument and the denominator together. -/
def shiftedWeight (Q : ℕ) (A : ℕ → ℤ_[p]) (m : ℕ) : ℤ_[p] :=
  if Q ∣ m then A (m / Q) else 0

def difference (Q : ℕ) (A : ℕ → ℤ_[p]) (m : ℕ) : ℤ_[p] := A m - shiftedWeight Q A m

lemma invNat_mul {Q m : ℕ} (hQ : p.Coprime Q) (hm : p.Coprime m) :
    ((Q*m : ℕ) : ℤ_[p]).inv = (Q : ℤ_[p]).inv * (m : ℤ_[p]).inv := by
  have hu := PadicInt.norm_natCast_eq_one_iff.mpr (hQ.mul_right hm)
  apply mul_right_cancel₀ (b := ((Q*m : ℕ) : ℤ_[p])) (Nat.cast_ne_zero.mpr
    (fun h => by rw [h, Nat.cast_zero, norm_zero] at hu; exact zero_ne_one hu))
  rw [PadicInt.inv_mul hu, Nat.cast_mul]
  rw [mul_mul_mul_comm, PadicInt.inv_mul (PadicInt.norm_natCast_eq_one_iff.mpr hQ),
    PadicInt.inv_mul (PadicInt.norm_natCast_eq_one_iff.mpr hm), one_mul]

theorem row_shift {S : Finset ℕ} (out : p ∉ S) {Q : ℕ} (hQ : Q ∈ Nat.factoredNumbers S)
    (A : ℕ → ℤ_[p]) (s n : ℕ) :
    row S (shiftedWeight Q A) s n = (Q : ℤ_[p]).inv^s * row S A s (n/Q) := by
  classical
  have pos := Nat.pos_of_ne_zero hQ.1
  have hcop := hp.out.factoredNumbers_coprime out hQ
  let U := (indices S n).filter (Q ∣ ·)
  have eqn : U = ((indices S (n/Q)).image (Q * ·)) := by
    ext m
    simp only [U, mem_filter, mem_indices, mem_image]
    constructor
    · rintro ⟨⟨hn,hm⟩,⟨k,rfl⟩⟩
      refine ⟨k,⟨(Nat.le_div_iff_mul_le pos).mpr (by simpa [mul_comm] using hn),
        Nat.mem_factoredNumbers_of_dvd hm (dvd_mul_left ..)⟩,rfl⟩
    · rintro ⟨k,⟨hk,hkS⟩,rfl⟩
      exact ⟨⟨by simpa [mul_comm] using (Nat.le_div_iff_mul_le pos).mp hk,
        Nat.mul_mem_factoredNumbers hQ hkS⟩,dvd_mul_right ..⟩
  unfold row
  rw [← sum_subset (s₁:=U) (filter_subset _ _) (fun m hm hn => by
    have nd : ¬ Q ∣ m := fun d => hn (mem_filter.mpr ⟨hm,d⟩)
    simp [shiftedWeight, nd]), eqn, sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left pos h),
    mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [invNat_mul hcop (hp.out.factoredNumbers_coprime out (mem_indices.mp hm).2)]
  simp [shiftedWeight, hQ.1, mul_pow, mul_left_comm]

/-- Exact cofactor difference on the actual infinite weighted phase. -/
theorem moment_difference {S : Finset ℕ} (out : p ∉ S) {Q : ℕ} (hQ : Q ∈ Nat.factoredNumbers S)
    (A : ℕ → ℤ_[p]) {s : ℕ} (hs : 0 < s) (t : ℝ) :
    moment S (difference Q A) s t =
      moment S A s t - (Q : ℤ_[p]).inv^s * moment S A s (t/Q) := by
  unfold moment
  rw [← (rows_summable hs _).tsum_mul_left,
    ← (rows_summable hs _).tsum_sub ((rows_summable hs _).mul_left _)]
  apply tsum_congr
  intro i
  have cut : ⌊t/(Q:ℝ)*(p:ℝ)^i⌋₊ = ⌊t*(p:ℝ)^i⌋₊ / Q := by
    rw [div_mul_eq_mul_div, Nat.floor_div_natCast]
  have row_sub (n : ℕ) : row S (difference Q A) s n = row S A s n - row S (shiftedWeight Q A) s n := by
    simp only [row, difference, sub_mul, sum_sub_distrib]
  rw [cut, row_sub, row_shift out hQ]
  ring

end NormalityChecker.LocalizedSupport.Unsigned
