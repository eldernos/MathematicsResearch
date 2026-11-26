module

public import NormalityChecker.DiscrepancyGeometry

/-! # Character-difference discrepancy transfer for Lambert series (Track E1)

Kernel-checked finite transfer lemmas connecting residue-class Lambert sums and the odd-index
Erdős–Borwein sum via real Dirichlet characters:

1. **Radix shift invariance (`radixDiscrepancy_mul_pow_sub_le`).**
   For every integer radix `b ≥ 1`, real `x`, `k : ℕ`, and `N > 0`,
     `|D_N(b^k x; b) - D_N(x; b)| ≤ k / N`.
2. **General power-of-radix linear discrepancy transfer (`radix_pow_linear_transfer`).**
   If `b^k x - y = ∑ i, c_i z_i` with integer coefficients `c_i`, then for every `N > 0`,
     `|D_N(x; b) - D_N(y; b)| ≤ k / N + ∑ i, |c_i| · (1 - D_N(z_i; b))`.
   This covers every modulus `q` whose unit group `(ℤ/qℤ)ˣ` has exponent `2` (`q ∈ {3,4,6,8,12,24}`)
   and every 2-elementary character quotient in base 2.
3. **Exact mod-8 Lambert identities and transfer (`mod8_odd_discrepancy_diff`,
   `mod8_class_discrepancy_diff`, `mod8_asymptotic_equivalence`).**
   For `A_r = ∑_{m ≡ r (mod 8)} 1/(2^m - 1)` (`r ∈ {1, 3, 5, 7}`) and
   `E_odd = ∑_{m odd} 1/(2^m - 1)`:
     `4 A_r - E_odd = ± L_{χ_4} ± L_{χ_8} ± L_{χ_{-8}}`,
   so for every `N > 0`,
     `|D_N(E_odd; 2) - D_N(A_r; 2)| ≤ 2/N + (1 - D_N(L_{χ_4}; 2)) + (1 - D_N(L_{χ_8}; 2)) + (1 - D_N(L_{χ_{-8}}; 2))`,
   and similarly for `|D_N(A_r; 2) - D_N(A_s; 2)|`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.CharacterLambertTransfer

open SharpTranslation DiscrepancyGeometry

/-! ### Part 1: Radix shift invariance -/

theorem shift_mul_pow (b : ℕ) (x : ℝ) (k n : ℕ) :
    shift b ((b : ℝ) ^ k * x) n = shift b x (n + k) := by
  unfold shift
  rw [← mul_assoc, ← pow_add]

private lemma card_filter_shift_diff (P : ℕ → Prop) [DecidablePred P] (N k : ℕ) :
    (((range N).filter P).card : ℝ) - (((range N).filter (fun n => P (n + k))).card : ℝ) ≤ (k : ℝ) ∧
    (((range N).filter (fun n => P (n + k))).card : ℝ) - (((range N).filter P).card : ℝ) ≤ (k : ℝ) := by
  have hmap : ((range N).filter (fun n => P (n + k))).card = ((Ico k (N + k)).filter P).card := by
    refine card_bij (fun n _ => n + k) ?_ ?_ ?_
    · intro n hn
      obtain ⟨hnN, hP⟩ := mem_filter.mp hn
      rw [mem_range] at hnN
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hP⟩
    · intro n₁ _ n₂ _ h; omega
    · intro m hm
      obtain ⟨hmI, hP⟩ := mem_filter.mp hm
      rw [mem_Ico] at hmI
      exact ⟨m - k, mem_filter.mpr ⟨mem_range.mpr (by omega), by rwa [Nat.sub_add_cancel hmI.1]⟩,
        Nat.sub_add_cancel hmI.1⟩
  rw [hmap]
  constructor
  · have hsub : (range N).filter P ⊆ ((Ico k (N + k)).filter P) ∪ range k := by
      intro m hm
      obtain ⟨hmN, hP⟩ := mem_filter.mp hm
      rw [mem_range] at hmN
      rw [mem_union]
      by_cases hmk : m < k
      · exact Or.inr (mem_range.mpr hmk)
      · exact Or.inl (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hP⟩)
    have hcard : ((range N).filter P).card ≤ ((Ico k (N + k)).filter P).card + k := by
      calc ((range N).filter P).card
          ≤ (((Ico k (N + k)).filter P) ∪ range k).card := card_le_card hsub
        _ ≤ ((Ico k (N + k)).filter P).card + (range k).card := card_union_le _ _
        _ = ((Ico k (N + k)).filter P).card + k := by rw [card_range]
    have hcard_r : (((range N).filter P).card : ℝ) ≤ (((Ico k (N + k)).filter P).card : ℝ) + (k : ℝ) := by
      exact_mod_cast hcard
    linarith
  · have hsub : (Ico k (N + k)).filter P ⊆ ((range N).filter P) ∪ Ico N (N + k) := by
      intro m hm
      obtain ⟨hmI, hP⟩ := mem_filter.mp hm
      rw [mem_Ico] at hmI
      rw [mem_union]
      by_cases hmN : m < N
      · exact Or.inl (mem_filter.mpr ⟨mem_range.mpr hmN, hP⟩)
      · exact Or.inr (mem_Ico.mpr ⟨by omega, hmI.2⟩)
    have hcard : ((Ico k (N + k)).filter P).card ≤ ((range N).filter P).card + k := by
      calc ((Ico k (N + k)).filter P).card
          ≤ (((range N).filter P) ∪ Ico N (N + k)).card := card_le_card hsub
        _ ≤ ((range N).filter P).card + (Ico N (N + k)).card := card_union_le _ _
        _ = ((range N).filter P).card + k := by rw [Nat.card_Ico, Nat.add_sub_cancel_left]
    have hcard_r : (((Ico k (N + k)).filter P).card : ℝ) ≤ (((range N).filter P).card : ℝ) + (k : ℝ) := by
      exact_mod_cast hcard
    linarith

/-- **Radix shift invariance of finite extreme discrepancy.**
For every integer radix `b`, real `x`, `k : ℕ`, and `N > 0`,
`|D_N(b^k x; b) - D_N(x; b)| ≤ k / N`. -/
theorem radixDiscrepancy_mul_pow_sub_le (b : ℕ) (x : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b x N| ≤ (k : ℝ) / (N : ℝ) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfreq : ∀ a c : ℝ,
      |frequency (shift b ((b : ℝ) ^ k * x)) a c N - frequency (shift b x) a c N| ≤
        (k : ℝ) / (N : ℝ) := by
    intro a c
    unfold frequency
    have heq : (range N).filter (fun i => a ≤ shift b ((b : ℝ) ^ k * x) i ∧ shift b ((b : ℝ) ^ k * x) i < c) =
        (range N).filter (fun i => a ≤ shift b x (i + k) ∧ shift b x (i + k) < c) := by
      congr 1; ext i; rw [shift_mul_pow]
    rw [heq, ← sub_div, abs_div, abs_of_pos hNr]
    apply div_le_div_of_nonneg_right _ hNr.le
    have hdiff := card_filter_shift_diff (fun i => a ≤ shift b x i ∧ shift b x i < c) N k
    rw [abs_le]
    constructor <;> linarith
  rw [radixDiscrepancy_eq_sampleDisc, radixDiscrepancy_eq_sampleDisc, abs_le]
  constructor
  · suffices h : sampleDisc (shift b x) N ≤ sampleDisc (shift b ((b : ℝ) ^ k * x)) N + (k : ℝ) / (N : ℝ) by
      linarith
    refine sampleDisc_le_of (fun a c ha hac hc => ?_)
    have h1 := interval_le_sampleDisc (shift b ((b : ℝ) ^ k * x)) N ha hac hc
    have h2 := hfreq a c
    have htri : |frequency (shift b x) a c N - (c - a)| ≤
        |frequency (shift b ((b : ℝ) ^ k * x)) a c N - (c - a)| +
          |frequency (shift b ((b : ℝ) ^ k * x)) a c N - frequency (shift b x) a c N| := by
      have : frequency (shift b x) a c N - (c - a) =
          (frequency (shift b ((b : ℝ) ^ k * x)) a c N - (c - a)) -
            (frequency (shift b ((b : ℝ) ^ k * x)) a c N - frequency (shift b x) a c N) := by ring
      rw [this]
      exact abs_sub _ _
    linarith
  · suffices h : sampleDisc (shift b ((b : ℝ) ^ k * x)) N ≤ sampleDisc (shift b x) N + (k : ℝ) / (N : ℝ) by
      linarith
    refine sampleDisc_le_of (fun a c ha hac hc => ?_)
    have h1 := interval_le_sampleDisc (shift b x) N ha hac hc
    have h2 := hfreq a c
    have htri : |frequency (shift b ((b : ℝ) ^ k * x)) a c N - (c - a)| ≤
        |frequency (shift b x) a c N - (c - a)| +
          |frequency (shift b ((b : ℝ) ^ k * x)) a c N - frequency (shift b x) a c N| := by
      have : frequency (shift b ((b : ℝ) ^ k * x)) a c N - (c - a) =
          (frequency (shift b x) a c N - (c - a)) +
            (frequency (shift b ((b : ℝ) ^ k * x)) a c N - frequency (shift b x) a c N) := by ring
      rw [this]
      exact abs_add_le _ _
    linarith

/-! ### Part 2: General linear combination transfer via discrepancy distance -/

/-- `discDist` of a finite integer linear combination from `0` is bounded by the weighted sum
of individual deficits `1 - D_N(z_i)`. -/
theorem discDist_sum_intMul_le (b : ℕ) {N : ℕ} (hN : 0 < N) {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (z : ι → ℝ) :
    discDist b N (∑ i ∈ s, (c i : ℝ) * z i) 0 ≤
      ∑ i ∈ s, |(c i : ℝ)| * (1 - radixDiscrepancy b (z i) N) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [discDist_self]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have htri := discDist_triangle b hN ((c a : ℝ) * z a + ∑ i ∈ s, (c i : ℝ) * z i)
      (∑ i ∈ s, (c i : ℝ) * z i) 0
    have hshift : discDist b N ((c a : ℝ) * z a + ∑ i ∈ s, (c i : ℝ) * z i)
        (∑ i ∈ s, (c i : ℝ) * z i) = discDist b N ((c a : ℝ) * z a) 0 := by
      have := discDist_translate b N ((c a : ℝ) * z a) 0 (∑ i ∈ s, (c i : ℝ) * z i)
      simpa [zero_add] using this
    have hmul := discDist_intMul_le b hN (c a) (z a) 0
    simp only [mul_zero] at hmul
    have hdef : discDist b N (z a) 0 = 1 - radixDiscrepancy b (z a) N := by
      simp [discDist]
    rw [hdef] at hmul
    linarith

/-- **General power-of-radix linear discrepancy transfer.**
If `b^k x - y = ∑ i ∈ s, c_i z_i` with integer coefficients `c_i`, then for every `N > 0`,
`|D_N(x; b) - D_N(y; b)| ≤ k / N + ∑ i ∈ s, |c_i| · (1 - D_N(z_i; b))`. -/
theorem radix_pow_linear_transfer (b : ℕ) {N : ℕ} (hN : 0 < N) (k : ℕ) (x y : ℝ)
    {ι : Type*} (s : Finset ι) (c : ι → ℤ) (z : ι → ℝ)
    (hrel : (b : ℝ) ^ k * x - y = ∑ i ∈ s, (c i : ℝ) * z i) :
    |radixDiscrepancy b x N - radixDiscrepancy b y N| ≤
      (k : ℝ) / (N : ℝ) + ∑ i ∈ s, |(c i : ℝ)| * (1 - radixDiscrepancy b (z i) N) := by
  have h1 := radixDiscrepancy_mul_pow_sub_le b x k hN
  have h2 := radixDiscrepancy_lipschitz b hN ((b : ℝ) ^ k * x) y
  have hd : discDist b N ((b : ℝ) ^ k * x) y = discDist b N (∑ i ∈ s, (c i : ℝ) * z i) 0 := by
    unfold discDist
    rw [hrel, sub_zero]
  rw [hd] at h2
  have h3 := discDist_sum_intMul_le b hN s c z
  have htri : |radixDiscrepancy b x N - radixDiscrepancy b y N| ≤
      |radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b x N| +
        |radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b y N| := by
    have : radixDiscrepancy b x N - radixDiscrepancy b y N =
        (radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b y N) -
          (radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b x N) := by ring
    rw [this]
    linarith [abs_sub (radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b y N)
      (radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b x N)]
  linarith

/-! ### Part 3: Mod-8 residue-class Lambert series and the odd-index Erdős–Borwein sum -/

/-- Binary Lambert series `∑_{m ≥ 1} w(m) / (2^m - 1)` for a weight `w : ℕ → ℤ`. -/
noncomputable def binaryLambert (w : ℕ → ℤ) : ℝ :=
  ∑' m : ℕ, (w (m + 1) : ℝ) / ((2 : ℝ) ^ (m + 1) - 1)

/-- Residue-class indicator `1_{m ≡ r (mod q)}`. -/
def classInd (q r m : ℕ) : ℤ := if m % q = r then 1 else 0

/-- Odd-index indicator `1_{2 ∤ m}`. -/
def oddInd (m : ℕ) : ℤ := if m % 2 = 1 then 1 else 0

/-- The nonprincipal real Dirichlet character `χ₄` modulo 4 (induced modulo 8). -/
def chi4 (m : ℕ) : ℤ :=
  if m % 4 = 1 then 1 else if m % 4 = 3 then -1 else 0

/-- The Kronecker character `χ₈ = (8 / ·)` modulo 8 (`+1` on `1, 7`, `-1` on `3, 5`). -/
def chi8 (m : ℕ) : ℤ :=
  if m % 8 = 1 ∨ m % 8 = 7 then 1 else if m % 8 = 3 ∨ m % 8 = 5 then -1 else 0

/-- The Kronecker character `χ_{-8} = (-8 / ·)` modulo 8 (`+1` on `1, 3`, `-1` on `5, 7`). -/
def chiNeg8 (m : ℕ) : ℤ :=
  if m % 8 = 1 ∨ m % 8 = 3 then 1 else if m % 8 = 5 ∨ m % 8 = 7 then -1 else 0

/-- The residue-class Lambert sum `A_r = ∑_{m ≡ r (mod 8)} 1 / (2^m - 1)`. -/
noncomputable def lambertMod8 (r : ℕ) : ℝ := binaryLambert (classInd 8 r)

/-- The odd-index Erdős–Borwein sum `E_odd = ∑_{m odd} 1 / (2^m - 1)`. -/
noncomputable def erdosBorweinOdd : ℝ := binaryLambert oddInd

/-- Summability of `binaryLambert w` for any bounded weight `|w(m)| ≤ B`. -/
theorem summable_binaryLambert {w : ℕ → ℤ} {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ m, |(w m : ℝ)| ≤ B) :
    Summable (fun m : ℕ => (w (m + 1) : ℝ) / ((2 : ℝ) ^ (m + 1) - 1)) := by
  have hgeo : Summable (fun m : ℕ => B * ((1 / 2 : ℝ)) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left B
  refine Summable.of_norm_bounded hgeo (fun m => ?_)
  have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hden : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) - 1 := by
    rw [pow_succ]; linarith
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ (m + 1) - 1 := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
  calc |(w (m + 1) : ℝ)| / ((2 : ℝ) ^ (m + 1) - 1)
      ≤ B / ((2 : ℝ) ^ (m + 1) - 1) := div_le_div_of_nonneg_right (hw (m + 1)) hden_pos.le
    _ ≤ B / (2 : ℝ) ^ m := div_le_div_of_nonneg_left hB (by positivity) hden
    _ = B * ((1 / 2 : ℝ)) ^ m := by rw [one_div, inv_pow, div_eq_mul_inv]

private lemma abs_le_one_classInd (q r m : ℕ) : |(classInd q r m : ℝ)| ≤ 1 := by
  unfold classInd; split_ifs <;> norm_num

private lemma abs_le_one_oddInd (m : ℕ) : |(oddInd m : ℝ)| ≤ 1 := by
  unfold oddInd; split_ifs <;> norm_num

private lemma abs_le_one_chi4 (m : ℕ) : |(chi4 m : ℝ)| ≤ 1 := by
  unfold chi4; split_ifs <;> norm_num

private lemma abs_le_one_chi8 (m : ℕ) : |(chi8 m : ℝ)| ≤ 1 := by
  unfold chi8; split_ifs <;> norm_num

private lemma abs_le_one_chiNeg8 (m : ℕ) : |(chiNeg8 m : ℝ)| ≤ 1 := by
  unfold chiNeg8; split_ifs <;> norm_num

private lemma pointwise_mod8_orthogonality (m : ℕ) :
    (4 * classInd 8 1 m = oddInd m + chi4 m + chi8 m + chiNeg8 m) ∧
    (4 * classInd 8 3 m = oddInd m - chi4 m - chi8 m + chiNeg8 m) ∧
    (4 * classInd 8 5 m = oddInd m + chi4 m - chi8 m - chiNeg8 m) ∧
    (4 * classInd 8 7 m = oddInd m - chi4 m + chi8 m - chiNeg8 m) := by
  unfold classInd oddInd chi4 chi8 chiNeg8
  have h2 : m % 2 = (m % 8) % 2 := by omega
  have h4 : m % 4 = (m % 8) % 4 := by omega
  have h8 : m % 8 < 8 := Nat.mod_lt m (by omega)
  rw [h2, h4]
  interval_cases (m % 8) <;> decide

private lemma binaryLambert_linear_eq {w₀ w₁ w₂ w₃ w₄ : ℕ → ℤ} (c₁ c₂ c₃ c₄ : ℤ)
    (h1 : Summable (fun m : ℕ => (w₁ (m + 1) : ℝ) / ((2 : ℝ) ^ (m + 1) - 1)))
    (h2 : Summable (fun m : ℕ => (w₂ (m + 1) : ℝ) / ((2 : ℝ) ^ (m + 1) - 1)))
    (h3 : Summable (fun m : ℕ => (w₃ (m + 1) : ℝ) / ((2 : ℝ) ^ (m + 1) - 1)))
    (h4 : Summable (fun m : ℕ => (w₄ (m + 1) : ℝ) / ((2 : ℝ) ^ (m + 1) - 1)))
    (hpt : ∀ m, 4 * w₀ m = c₁ * w₁ m + c₂ * w₂ m + c₃ * w₃ m + c₄ * w₄ m) :
    4 * binaryLambert w₀ =
      (c₁ : ℝ) * binaryLambert w₁ + (c₂ : ℝ) * binaryLambert w₂ +
        (c₃ : ℝ) * binaryLambert w₃ + (c₄ : ℝ) * binaryLambert w₄ := by
  unfold binaryLambert
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  rw [← Summable.tsum_add (h1.mul_left _) (h2.mul_left _)]
  rw [← Summable.tsum_add ((h1.mul_left _).add (h2.mul_left _)) (h3.mul_left _)]
  rw [← Summable.tsum_add (((h1.mul_left _).add (h2.mul_left _)).add (h3.mul_left _)) (h4.mul_left _)]
  congr 1
  ext m
  have hm : (4 : ℝ) * (w₀ (m + 1) : ℝ) =
      (c₁ : ℝ) * (w₁ (m + 1) : ℝ) + (c₂ : ℝ) * (w₂ (m + 1) : ℝ) +
        (c₃ : ℝ) * (w₃ (m + 1) : ℝ) + (c₄ : ℝ) * (w₄ (m + 1) : ℝ) := by
    exact_mod_cast hpt (m + 1)
  have hden : (2 : ℝ) ^ (m + 1) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := le_self_pow₀ (by norm_num) (Nat.succ_ne_zero m)
    linarith
  field_simp [hden]
  linarith

/-- Exact mod-8 character-orthogonality identities for `4 A_r - E_odd` (`r ∈ {1, 3, 5, 7}`). -/
theorem mod8_character_identities :
    (4 * lambertMod8 1 - erdosBorweinOdd =
      binaryLambert chi4 + binaryLambert chi8 + binaryLambert chiNeg8) ∧
    (4 * lambertMod8 3 - erdosBorweinOdd =
      -binaryLambert chi4 - binaryLambert chi8 + binaryLambert chiNeg8) ∧
    (4 * lambertMod8 5 - erdosBorweinOdd =
      binaryLambert chi4 - binaryLambert chi8 - binaryLambert chiNeg8) ∧
    (4 * lambertMod8 7 - erdosBorweinOdd =
      -binaryLambert chi4 + binaryLambert chi8 - binaryLambert chiNeg8) := by
  have hodd := summable_binaryLambert zero_le_one abs_le_one_oddInd
  have h4 := summable_binaryLambert zero_le_one abs_le_one_chi4
  have h8 := summable_binaryLambert zero_le_one abs_le_one_chi8
  have hn8 := summable_binaryLambert zero_le_one abs_le_one_chiNeg8
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := binaryLambert_linear_eq (w₀ := classInd 8 1) 1 1 1 1 hodd h4 h8 hn8
      (fun m => by linarith [(pointwise_mod8_orthogonality m).1])
    unfold lambertMod8 erdosBorweinOdd; push_cast at h; linarith
  · have h := binaryLambert_linear_eq (w₀ := classInd 8 3) 1 (-1) (-1) 1 hodd h4 h8 hn8
      (fun m => by linarith [(pointwise_mod8_orthogonality m).2.1])
    unfold lambertMod8 erdosBorweinOdd; push_cast at h; linarith
  · have h := binaryLambert_linear_eq (w₀ := classInd 8 5) 1 1 (-1) (-1) hodd h4 h8 hn8
      (fun m => by linarith [(pointwise_mod8_orthogonality m).2.2.1])
    unfold lambertMod8 erdosBorweinOdd; push_cast at h; linarith
  · have h := binaryLambert_linear_eq (w₀ := classInd 8 7) 1 (-1) 1 (-1) hodd h4 h8 hn8
      (fun m => by linarith [(pointwise_mod8_orthogonality m).2.2.2])
    unfold lambertMod8 erdosBorweinOdd; push_cast at h; linarith

/-- **Finite mod-8 transfer to the odd-index Erdős–Borwein sum (Track E1).**
For every `r ∈ {1, 3, 5, 7}` and every `N > 0`,
`|D_N(A_r; 2) - D_N(E_odd; 2)| ≤ 2/N + (1 - D_N(L_{χ₄}; 2)) + (1 - D_N(L_{χ₈}; 2)) + (1 - D_N(L_{χ_{-8}}; 2))`. -/
theorem mod8_odd_discrepancy_diff {r : ℕ} (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7)
    {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 erdosBorweinOdd N| ≤
      2 / (N : ℝ) +
        (1 - radixDiscrepancy 2 (binaryLambert chi4) N) +
        (1 - radixDiscrepancy 2 (binaryLambert chi8) N) +
        (1 - radixDiscrepancy 2 (binaryLambert chiNeg8) N) := by
  let z : Fin 3 → ℝ := fun i =>
    match i with
    | ⟨0, _⟩ => binaryLambert chi4
    | ⟨1, _⟩ => binaryLambert chi8
    | ⟨2, _⟩ => binaryLambert chiNeg8
  have hids := mod8_character_identities
  have apply_signs : ∀ (s₀ s₁ s₂ : ℤ),
      |s₀| = 1 → |s₁| = 1 → |s₂| = 1 →
      (2 : ℝ) ^ 2 * lambertMod8 r - erdosBorweinOdd =
        (s₀ : ℝ) * binaryLambert chi4 + (s₁ : ℝ) * binaryLambert chi8 +
          (s₂ : ℝ) * binaryLambert chiNeg8 →
      |radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 erdosBorweinOdd N| ≤
        2 / (N : ℝ) +
          (1 - radixDiscrepancy 2 (binaryLambert chi4) N) +
          (1 - radixDiscrepancy 2 (binaryLambert chi8) N) +
          (1 - radixDiscrepancy 2 (binaryLambert chiNeg8) N) := by
    intro s₀ s₁ s₂ hs₀ hs₁ hs₂ hrel
    let c : Fin 3 → ℤ := fun i =>
      match i with
      | ⟨0, _⟩ => s₀
      | ⟨1, _⟩ => s₁
      | ⟨2, _⟩ => s₂
    have htr := radix_pow_linear_transfer 2 hN 2 (lambertMod8 r) erdosBorweinOdd univ c z (by
      rw [Fin.sum_univ_three]
      simpa [c, z] using hrel)
    rw [Fin.sum_univ_three] at htr
    have hcs0 : |(s₀ : ℝ)| = 1 := by exact_mod_cast hs₀
    have hcs1 : |(s₁ : ℝ)| = 1 := by exact_mod_cast hs₁
    have hcs2 : |(s₂ : ℝ)| = 1 := by exact_mod_cast hs₂
    dsimp only [c, z] at htr
    rw [hcs0, hcs1, hcs2] at htr
    norm_num at htr
    linarith
  rcases hr with rfl | rfl | rfl | rfl
  · exact apply_signs 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num; linarith [hids.1])
  · exact apply_signs (-1) (-1) 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; linarith [hids.2.1])
  · exact apply_signs 1 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; linarith [hids.2.2.1])
  · exact apply_signs (-1) 1 (-1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; linarith [hids.2.2.2])

/-- **Pairwise mod-8 residue-class discrepancy transfer (Track E1).**
For every `r, s ∈ {1, 3, 5, 7}` and `N > 0`,
`|D_N(A_r; 2) - D_N(A_s; 2)| ≤ 4/N + 2·((1 - D_N(L_{χ₄})) + (1 - D_N(L_{χ₈})) + (1 - D_N(L_{χ_{-8}})))`. -/
theorem mod8_class_discrepancy_diff {r s : ℕ}
    (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7)
    (hs : s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 7)
    {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 (lambertMod8 s) N| ≤
      4 / (N : ℝ) +
        2 * ((1 - radixDiscrepancy 2 (binaryLambert chi4) N) +
             (1 - radixDiscrepancy 2 (binaryLambert chi8) N) +
             (1 - radixDiscrepancy 2 (binaryLambert chiNeg8) N)) := by
  have h1 := mod8_odd_discrepancy_diff hr hN
  have h2 := mod8_odd_discrepancy_diff hs hN
  have htri : |radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 (lambertMod8 s) N| ≤
      |radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 erdosBorweinOdd N| +
        |radixDiscrepancy 2 (lambertMod8 s) N - radixDiscrepancy 2 erdosBorweinOdd N| := by
    have : radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 (lambertMod8 s) N =
        (radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 erdosBorweinOdd N) -
          (radixDiscrepancy 2 (lambertMod8 s) N - radixDiscrepancy 2 erdosBorweinOdd N) := by ring
    rw [this]
    exact abs_sub _ _
  have h4N : (4 : ℝ) / (N : ℝ) = 2 / (N : ℝ) + 2 / (N : ℝ) := by ring
  linarith

/-- **Asymptotic discrepancy equivalence of mod-8 Lambert classes and `E_odd` (Track E1).**
Given `D_N(L_{χ}; 2) → 1` for the three nonprincipal real characters mod 8 (established in
Phase 17 / Paper VI), all four `A_r` (`r ∈ {1, 3, 5, 7}`) and `E_odd` have asymptotically
identical binary discrepancy: `D_N(A_r; 2) - D_N(E_odd; 2) → 0`. -/
theorem mod8_asymptotic_equivalence
    (h4 : Tendsto (fun N => radixDiscrepancy 2 (binaryLambert chi4) N) atTop (𝓝 1))
    (h8 : Tendsto (fun N => radixDiscrepancy 2 (binaryLambert chi8) N) atTop (𝓝 1))
    (hn8 : Tendsto (fun N => radixDiscrepancy 2 (binaryLambert chiNeg8) N) atTop (𝓝 1))
    {r : ℕ} (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) :
    Tendsto (fun N => radixDiscrepancy 2 (lambertMod8 r) N - radixDiscrepancy 2 erdosBorweinOdd N)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (2 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hg4 : Tendsto (fun N => 1 - radixDiscrepancy 2 (binaryLambert chi4) N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h4
  have hg8 : Tendsto (fun N => 1 - radixDiscrepancy 2 (binaryLambert chi8) N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h8
  have hgn8 : Tendsto (fun N => 1 - radixDiscrepancy 2 (binaryLambert chiNeg8) N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hn8
  have hsum : Tendsto (fun N : ℕ =>
      2 / (N : ℝ) +
        (1 - radixDiscrepancy 2 (binaryLambert chi4) N) +
        (1 - radixDiscrepancy 2 (binaryLambert chi8) N) +
        (1 - radixDiscrepancy 2 (binaryLambert chiNeg8) N)) atTop (𝓝 0) := by
    simpa using ((hinv.add hg4).add hg8).add hgn8
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact mod8_odd_discrepancy_diff hr hN

end NormalityChecker.CharacterLambertTransfer
