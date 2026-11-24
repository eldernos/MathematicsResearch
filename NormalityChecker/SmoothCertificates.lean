module

public import NormalityChecker.IndexedExpansion
public import NormalityChecker.LocalizedExamples

/-! The fixed-prime-support short-orbit estimate and its certificate applications. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

namespace LocalizedSupport
/-- After base factors clear, the denominator divides a power of the fixed
cofactor modulus `c`, even when several primes survive. -/
theorem clean_power_denominator {b c D n order : ℕ} {S : Finset ℕ} (hb : 0<b) (hc : 0<c)
    (support : ∀ p ∈ S, p ∣ b*c) (size : n≤2^D) (clean : ∀ m∈indices S n, m+D*order≤n) :
    (powerShifted b order S n).den ∣ (c^D)^order := by
  let A (m : ℕ) := ((c^D)^order*b^(n-m))/m^order
  apply (reduced_info (S:=∑ m ∈ indices S n,A m) (pow_pos (pow_pos hc _) _) _).1
  simp only [powerShifted,powerPartial,Nat.cast_sum,mul_sum]
  apply sum_congr rfl; intro m hm
  obtain ⟨mn,ms⟩ := mem_indices.mp hm
  have hd := cofactor_dvd (Nat.mul_pos hb hc) support ms (mn.trans size)
  rw [mul_pow,mul_comm] at hd
  have left := clean m hm
  have hd' := pow_dvd_pow_of_dvd hd order
  rw [mul_pow, ← pow_mul b] at hd'
  have dvd := hd'.trans (Nat.mul_dvd_mul_left _ (pow_dvd_pow b (show D*order≤n-m by omega)))
  have eqn := congrArg (fun z : ℕ => (z:ℚ)) (Nat.div_mul_cancel dvd)
  have pw : (b:ℚ)^n = (b:ℚ)^(n-m)*(b:ℚ)^m := by rw [← pow_add,Nat.sub_add_cancel mn]
  change ((A m:ℕ):ℚ) = _
  dsimp only [A]; push_cast at eqn ⊢; rw [powerWeight,pw]; field_simp [ms.1,hb.ne']; exact eqn

theorem clean_smooth_denominator {b c D n : ℕ} {S : Finset ℕ} (hb : 0<b) (hc : 0<c)
    (support : ∀ p ∈ S, p ∣ b*c) (size : n≤2^D) (clean : ∀ m∈indices S n, m+D≤n) :
    (shifted b S n).den ∣ c^D := by
  simpa only [powerShifted,powerPartial,powerWeight,shifted,partialSum,weight,pow_one] using
    clean_power_denominator (order:=1) hb hc support size (by simpa using clean)

def powerCoefficient (order : ℕ) (S : Finset ℕ) (i : ℕ) : ℚ :=
  if i+1 ∈ Nat.factoredNumbers S then 1/((i:ℚ)+1)^order else 0

/-- The localized polylogarithm, with one coefficient for each positive integer in the support. -/
noncomputable def powerValue (b order : ℕ) (S : Finset ℕ) : ℝ :=
  ∑' i, (powerCoefficient order S i:ℝ)/(b:ℝ)^(i+1)

private lemma value_one (b : ℕ) (S : Finset ℕ) : powerValue b 1 S = value b S := by
  apply tsum_congr; intro i; unfold powerCoefficient term
  split_ifs <;> simp [div_eq_mul_inv,mul_comm]

theorem power_tail {b order : ℕ} (hb : 2≤b) (hs : 0<order) (S : Finset ℕ) :
    Tendsto (fun n => (b:ℝ)^n*powerValue b order S-(powerShifted b order S n:ℝ)) atTop (𝓝 0) := by
  have little {i : ℕ} : 1 ≤ ((i:ℚ)+1)^order := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℚ) i])
  have tail := indexed_shift_error hb (fun i : ℕ => i+1) (fun _ _ h => Nat.add_right_cancel h)
    (powerCoefficient order S) (fun i => by unfold powerCoefficient; split_ifs <;> positivity)
    (fun i => by unfold powerCoefficient; split_ifs <;> first | exact (div_le_one (by positivity)).mpr little | norm_num)
    (I:=range) (mem:=by intros; simp) (small:=by
      intro ε pos; obtain ⟨N,large⟩ := exists_nat_gt (1/ε)
      refine ⟨N,fun i hi => ?_⟩; unfold powerCoefficient; split_ifs
      · push_cast; apply (div_le_iff₀ (by positivity)).mpr
        have cap : N ≤ (i+1)^order := hi.trans (by simpa using Nat.pow_le_pow_right (Nat.succ_pos i) hs)
        have cap' : (N:ℝ) ≤ ((i:ℝ)+1)^order := by exact_mod_cast cap
        linarith only [(div_lt_iff₀ pos).mp (large.trans_le cap')]
      · simpa using pos.le)
  have pref (n : ℕ) : powerPartial b order S n = ∑ i∈range n,powerCoefficient order S i/(b:ℚ)^(i+1) := by
    simp only [powerPartial,indices,sum_filter,sum_range_succ']
    have hz : 0 ∉ Nat.factoredNumbers S := fun h => h.1 rfl
    simp [hz,powerCoefficient,powerWeight,div_eq_mul_inv,mul_comm]
  simpa only [powerValue,powerShifted,pref] using tail

/-- A passing certificate with any number of surviving denominator primes.
`c` can be their product. The analytic input is explicit. -/
theorem power_normal_of_smooth_estimate {order : ℕ} (positive : 0<order) {b p c ell seed : ℕ} {S : Finset ℕ} (hb : 2≤b)
    (hc : 0<c) (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p)
    (support : ∀ r∈insert p S, r ∣ b*c) (pass : passesPower order b p ell seed S = true)
    (estimate : SmoothOrbitEstimate b c) : NormalIn b (powerValue b order (insert p S)) := by
  let A := insert p S
  let P := powerShifted b order A
  apply normal_of_arithmetic_certificate (B:=2) (L:=2) hb (by decide) (by decide) _ P
    (power_tail hb positive A) estimate (4*c*order)
  intro u hu M η pos
  have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have err := (tendsto_pow_const_div_const_pow_of_one_lt A.card (by norm_num : (1:ℝ)<2)).const_mul (2*5^A.card)
  simp only [mul_zero] at err
  have clearing := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul (4*(order:ℝ))
  simp only [mul_zero,pow_one] at clearing
  filter_upwards [clearing.eventually_le_const zero_lt_one,eventually_ge_atTop 3,grow.eventually_ge_atTop (p^(seed+ell)),
    grow.eventually_ge_atTop (p^(ell+1)*M),err.eventually_le_const pos] with k budget hk stable large small
  let D := 2*(k+1)
  let B := 2^k
  let U := u*B
  let E := insertionBlocks (indices A (2^D)) B U
  have bpos : 0<B := pow_pos (by decide) _
  have dB : D*order≤B := by
    rw [← mul_div_assoc,div_le_iff₀ (by positivity),one_mul] at budget
    have H : 4*order*k≤2^k := by exact_mod_cast budget
    dsimp [D,B]; nlinarith
  have cap : 4*(B*B)=2^D := by dsimp [B,D]; rw [Nat.mul_comm 2 (k+1),pow_mul,pow_succ]; ring
  refine ⟨E,?_,?_⟩
  · have count := (card_insertionBlocks (indices A (2^D)) B U).trans (Nat.mul_le_mul_left 2 (insertion_count A D))
    change (E.card:ℝ) ≤ _
    have hc' : (E.card:ℝ) ≤ 2*((D:ℝ)+1)^A.card := by exact_mod_cast count
    have dk : (D:ℝ)+1 ≤ 5*k := by
      dsimp [D]; push_cast
      have hkr : (3:ℝ)≤k := by exact_mod_cast hk
      linarith
    apply hc'.trans; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) dk A.card) (by norm_num : (0:ℝ)≤2)).trans
    rw [mul_pow]; rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at small; simpa [mul_assoc] using small
  · intro l hl good
    let s := (U+l)*B
    have low : B≤s := Nat.le_mul_of_pos_left B (show 0<U+l by dsimp [U]; have := (mem_Ico.mp hu).1; positivity)
    have high : (U+l+1)*B≤2^D := by
      rw [← cap]; apply (Nat.mul_le_mul_right B (show U+l+1 ≤ 4*B from calc
        U+l+1 ≤ u*B+B := by dsimp [U]; omega
        _ = (u+1)*B := by ring
        _ ≤ 4*B := Nat.mul_le_mul_right _ (mem_Ico.mp hu).2)).trans_eq; ring
    have before {m : ℕ} (hm : m∈Nat.factoredNumbers A) (le : m<(U+l+1)*B) : m+B≤s :=
      insertionBlocks_free bpos good (mem_indices.mpr ⟨le.le.trans high,hm⟩) le
    have endpt : (U+l+1)*B = s+B := by simp [s,Nat.add_mul]
    have ds := clean_power_denominator (order:=order) (by omega : 0<b) hc support
      (n:=s) (by rw [endpt] at high; omega : s≤2^D) (fun m hm => by
        obtain ⟨mn,ms⟩ := mem_indices.mp hm; have H := before ms (by rw [endpt]; omega); omega)
    let j := Nat.log p s
    have hj : seed+ell≤j := Nat.le_log_of_pow_le hp.one_lt (stable.trans low)
    have survives := passes_power_denominator positive hp outside cop hj (Nat.pow_log_le_self p (bpos.trans_le low).ne')
      (Nat.lt_pow_succ_log_self hp.one_lt s) pass
    have ex : j≤j*order := by simpa using Nat.mul_le_mul_left j positive
    have lower := (pow_dvd_pow p (Nat.sub_le_sub_right ex ell)).trans survives
    have bot : M≤(P s).den := by
      have hr := Nat.le_of_dvd (P s).pos lower
      have id : p^(j+1)=p^(ell+1)*p^(j-ell) := by rw [← pow_add]; congr 1; omega
      have H := (large.trans low).trans (Nat.lt_pow_succ_log_self hp.one_lt s).le
      rw [id] at H
      exact Nat.le_of_mul_le_mul_left (H.trans (Nat.mul_le_mul_left _ hr)) (pow_pos hp.pos _)
    have top : (c^D)^order≤B^(4*c*order) := by
      rw [pow_mul B (4*c)]; apply Nat.pow_le_pow_left _ _
      calc c^D ≤ (2^c)^D := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
           _ ≤ B^(4*c) := by dsimp [B,D]; rw [← pow_mul,← pow_mul]; apply Nat.pow_le_pow_right (by decide); nlinarith
    refine ⟨bot,⟨D*order,by simpa [pow_mul] using ds⟩,(Nat.le_of_dvd (pow_pos (pow_pos hc _) _) ds).trans top,?_⟩
    intro i hi
    have equal : indices A (s+i)=indices A s := by
      ext m; simp only [mem_indices]; constructor
      · rintro ⟨le,hm⟩; have H := before hm (by rw [endpt]; omega); exact ⟨by omega,hm⟩
      · rintro ⟨le,hm⟩; exact ⟨by omega,hm⟩
    change P (s+i) = (b:ℚ)^i*P s
    simp only [P,powerShifted,powerPartial,equal,pow_add]; ring

theorem normal_of_smooth_estimate {b p c ell seed : ℕ} {S : Finset ℕ} (hb : 2≤b)
    (hc : 0<c) (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p)
    (support : ∀ r∈insert p S, r ∣ b*c) (pass : passes b p ell seed S = true)
    (estimate : SmoothOrbitEstimate b c) : NormalIn b (value b (insert p S)) := by
  rw [← value_one]; exact power_normal_of_smooth_estimate (order:=1) (by decide) hb hc hp outside cop support pass estimate

/-- The finite modular test applies to every positive order and any finite prime support. -/
theorem normal_of_power_certificate {order b p c ell seed : ℕ} {S : Finset ℕ} (positive : 0<order) (hb : 2≤b)
    (hc : 1<c) (base_unit : b.Coprime c) (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p)
    (support : ∀ r∈insert p S, r ∣ b*c) (pass : passesPower order b p ell seed S = true) :
    NormalIn b (powerValue b order (insert p S)) :=
  power_normal_of_smooth_estimate positive hb (by omega) hp outside cop support pass
    (fixed_support_orbit_estimate hb hc base_unit)

/-- A successful finite test implies normality when every support prime divides
`b*c` and the fixed modulus `c` is coprime to the base. -/
theorem normal_of_certificate {b p c ell seed : ℕ} {S : Finset ℕ} (hb : 2≤b)
    (hc : 1<c) (base_unit : b.Coprime c) (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p)
    (support : ∀ r∈insert p S, r ∣ b*c) (pass : passes b p ell seed S = true) :
    NormalIn b (value b (insert p S)) :=
  normal_of_smooth_estimate hb (by omega) hp outside cop support pass
    (fixed_support_orbit_estimate hb hc base_unit)

/-- All three binary denominators divide powers of 5005 = 5·7·11·13. -/
theorem binary_normal_of_smooth_estimate (est : SmoothOrbitEstimate 2 5005) :
    NormalIn 2 (value 2 {2,5,7}) ∧ NormalIn 2 (value 2 {2,5,11}) ∧ NormalIn 2 (value 2 {2,5,7,11,13}) := by
  have app {p ell seed : ℕ} {S : Finset ℕ} := @normal_of_smooth_estimate 2 p 5005 ell seed S (by decide) (by decide)
  constructor
  · convert app (by decide : Nat.Prime 7) (by decide) (by decide) (by decide) binary_certificates.1 est using 2; decide
  constructor
  · convert app (by decide : Nat.Prime 11) (by decide) (by decide) (by decide) binary_certificates.2.1 est using 2; decide
  · convert app (by decide : Nat.Prime 13) (by decide) (by decide) (by decide) binary_certificates.2.2 est using 2; decide

/-- The three previously certified binary supports are normal unconditionally. -/
theorem binary_certified_normal : NormalIn 2 (value 2 {2,5,7}) ∧ NormalIn 2 (value 2 {2,5,11}) ∧
    NormalIn 2 (value 2 {2,5,7,11,13}) :=
  binary_normal_of_smooth_estimate (fixed_support_orbit_estimate (by decide) (by decide) (by decide))

end LocalizedSupport
end NormalityChecker
