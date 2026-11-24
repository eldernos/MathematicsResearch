module

public import NormalityChecker.ScaleTransfer
public import NormalityChecker.FourierTest

/-! A block criterion for expansions with sparse exceptional orbit segments. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Block numbers meeting an insertion or immediately following its block. -/
def insertionBlocks (A : Finset ℕ) (B U : ℕ) : Finset ℕ :=
  A.image (fun m => m/B-U) ∪ A.image (fun m => m/B+1-U)

lemma card_insertionBlocks (A : Finset ℕ) (B U : ℕ) : (insertionBlocks A B U).card ≤ 2*A.card :=
  (card_union_le ..).trans ((add_le_add card_image_le card_image_le).trans_eq (by omega))

lemma insertionBlocks_free {A : Finset ℕ} {B U l m : ℕ} (hB : 0<B)
    (hg : l ∉ insertionBlocks A B U) (hm : m ∈ A) (hi : m < (U+l+1)*B) : m+B ≤ (U+l)*B := by
  have neither : m/B ≠ U+l ∧ m/B+1 ≠ U+l := by
    constructor <;> intro e <;> apply hg
    · exact mem_union_left _ (mem_image.mpr ⟨m,hm,by rw [e]; omega⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨m,hm,by rw [e]; omega⟩)
  have hq := (Nat.div_lt_iff_lt_mul hB).mpr hi
  have H := Nat.mul_le_mul_right B (show m/B+2 ≤ U+l by omega)
  have bound := Nat.lt_mul_div_succ m hB
  rw [Nat.add_mul] at H; rw [Nat.mul_add,Nat.mul_comm B (m/B)] at bound; omega

private lemma split_blocks (f : ℕ → ℂ) (s B L : ℕ) :
    ∑ i ∈ range (L*B), f (s+i) = ∑ l ∈ range L, ∑ j ∈ range B, f (s+l*B+j) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]; simp [Nat.add_assoc]

/-- Full blocks suffice. The final partial block costs at most `B` at every cutoff. -/
theorem prefix_block_bound (f : ℕ → ℂ) (unit : ∀ n, ‖f n‖ ≤ 1) {s B L T : ℕ}
    (hB : 0<B) (hT : T≤L*B) (E : Finset ℕ) {η : ℝ} (hη : 0≤η)
    (good : ∀ l<L, l∉E → ‖∑ i ∈ range B, f (s+l*B+i)‖ ≤ η*B) :
    ‖∑ i ∈ range T, f (s+i)‖ ≤ η*(L*B) + (E.card+1:ℝ)*B := by
  let g (l : ℕ) := ∑ i ∈ range B, f (s+l*B+i)
  have trivial (n t : ℕ) : ‖∑ i ∈ range t, f (n+i)‖ ≤ t := by
    exact (norm_sum_le ..).trans ((sum_le_sum (fun i _ => unit (n+i))).trans_eq (by simp))
  have len : T/B≤L := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hT)
  have each (l : ℕ) (hl : l∈range (T/B)) : ‖g l‖ ≤ η*B + (if l∈E then (B:ℝ) else 0) := by
    split_ifs with he
    · exact (trivial _ _).trans (le_add_of_nonneg_left (by positivity))
    · simpa using good l ((mem_range.mp hl).trans_le len) he
  have bulk := (norm_sum_le (range (T/B)) g).trans (sum_le_sum each)
  rw [sum_add_distrib,← sum_filter] at bulk
  simp only [sum_const,card_range,nsmul_eq_mul] at bulk
  have card := card_le_card (show (range (T/B)).filter (·∈E) ⊆ E from fun _ hl => (mem_filter.mp hl).2)
  have bound : ‖∑ l∈range (T/B),g l‖ ≤ (L:ℝ)*(η*B)+E.card*B := by
    apply bulk.trans; gcongr
  have tail := trivial (s+(T/B)*B) (T%B)
  simp only [Nat.add_assoc] at tail
  have cut : T=(T/B)*B+T%B := by rw [Nat.mul_comm,Nat.div_add_mod]
  conv_lhs => rw [cut,sum_range_add,split_blocks]
  apply (norm_add_le ..).trans ((add_le_add bound tail).trans _)
  have hr : ((T%B:ℕ):ℝ) ≤ B := by exact_mod_cast (Nat.mod_lt T hB).le
  linarith only [hr]

/-- A geometric cell contains `L^k` full blocks of length `B^k`. Both the relative
size of the exceptional set and the normalized sums on its complement may be made
arbitrarily small, separately for each fixed Fourier frequency. -/
theorem normal_of_sparse_blocks {b B L : ℕ} (hb : 2≤b) (hB : 0<B) (hL : 1<L)
    (x : ℝ) (P : ℕ → ℚ) (tail : Tendsto (fun n => (b:ℝ)^n*x-(P n:ℝ)) atTop (𝓝 0))
    (blocks : ∀ h : ℤ, h≠0 → ∀ u ∈ Ico 1 (L*B), ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop,
      ∃ E : Finset ℕ, (E.card:ℝ) ≤ η*(L:ℝ)^k ∧ ∀ l<L^k, l∉E →
        ‖∑ i ∈ range (B^k), phase ((h:ℝ)*P ((u*L^k+l)*B^k+i))‖ ≤ η*(B:ℝ)^k) :
    NormalIn b x := by
  apply (normalIn_iff_prefix_fourier hb x _ tail).mpr
  intro h hh; rw [mean_phase]
  have hc : 1<L*B := hL.trans_le (Nat.le_mul_of_pos_right _ hB)
  apply mean_zero_of_radix_cells (S:=1) hc (by decide)
  intro u hu ε hε
  let η := ε/3
  have pos : 0<η := by dsimp [η]; positivity
  have grow : Tendsto (fun k : ℕ => (L:ℝ)^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hL)
  filter_upwards [blocks h hh u (by simpa using hu) η pos,grow.eventually_ge_atTop (1/η)] with k hk large T hT
  obtain ⟨E,card,good⟩ := hk
  let f (n : ℕ) := phase ((h:ℝ)*P n)
  have bound := prefix_block_bound f (fun n => (norm_phase _).le) (s:=u*(L*B)^k)
    (pow_pos hB k) (by simpa [mul_pow] using hT : T≤L^k*B^k) E pos.le (fun l hl he => by
      simpa [f,Nat.add_mul,mul_pow,Nat.mul_assoc] using good l hl he)
  have one := (div_le_iff₀ pos).mp large
  change ‖∑ i ∈ range T, f (u*(L*B)^k+i)‖ ≤ ε*((L*B:ℕ):ℝ)^k
  apply bound.trans; push_cast; rw [mul_pow]
  have H := mul_le_mul_of_nonneg_right (add_le_add card one) (show 0≤(B:ℝ)^k by positivity)
  dsimp [η] at *; linarith only [H]

end NormalityChecker
