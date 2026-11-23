module

public import NormalityChecker.Correlations
public import NormalityChecker.OrbitSum

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- An arbitrary prefix in cell u, measured in units of c^k. -/
def RadixCellCancellation (c : ℕ) (f : ℕ → ℂ) (u : ℕ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ T ≤ c^k,
    ‖∑ i ∈ range T, f (u*c^k+i)‖ ≤ ε*(c:ℝ)^k

/-- Control of all partial cells at large scales controls every prefix endpoint. -/
theorem mean_zero_of_radix_cells {c S : ℕ} (hc : 1<c) (hS : 0<S) {f : ℕ → ℂ}
    (h : ∀ u ∈ Ico S (c*S), RadixCellCancellation c f u) : Tendsto (mean f) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε/(2*((c:ℝ)+1)*S)
  have hc₁ : 1 ≤ c := by omega
  have hwidth : S+(c-1)*S=c*S := by nlinarith [Nat.sub_add_cancel hc₁, Nat.mul_sub_left_distrib S c 1]
  have hδ : 0<δ := by dsimp [δ]; positivity
  have HE := (eventually_all_finset (Ico S (c*S))).mpr (fun u hu => h u hu δ hδ)
  obtain ⟨K,hK⟩ := eventually_atTop.mp HE
  let P (n : ℕ) := ∑ i ∈ range n, f i
  have segment (k : ℕ) (hk : K≤k) (l : ℕ) (hl : l≤(c-1)*S) :
      ‖P ((S+l)*c^k)-P (S*c^k)‖ ≤ l*(δ*(c:ℝ)^k) := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hu : S+l ∈ Ico S (c*S) := mem_Ico.mpr ⟨by omega,by omega⟩
      have he : P ((S+(l+1))*c^k) = P ((S+l)*c^k)+
          ∑ i ∈ range (c^k), f ((S+l)*c^k+i) := by
        dsimp [P]; rw [show (S+(l+1))*c^k = (S+l)*c^k + c^k by ring, sum_range_add]
      rw [he, show ∀ a b c : ℂ, a+b-c = (a-c)+b by intros; ring]
      apply (norm_add_le _ _).trans
      have := add_le_add (ih (by omega)) (hK k hk _ hu _ le_rfl)
      push_cast; linarith
  let C := ‖P (S*c^K)‖
  have boundary (k : ℕ) (hk : K≤k) : ‖P (S*c^k)‖ ≤ C+(S:ℝ)*δ*c^k := by
    induction k, hk using Nat.le_induction with
    | base => exact le_add_of_nonneg_right (by positivity)
    | succ k hk ih =>
      have he : S*c^(k+1)=(S+(c-1)*S)*c^k := by rw [hwidth,pow_succ]; ring
      have H := segment k hk ((c-1)*S) le_rfl
      rw [← he] at H
      have H' := norm_add_le (P (S*c^(k+1))-P (S*c^k)) (P (S*c^k))
      rw [sub_add_cancel] at H'
      push_cast [Nat.cast_sub hc₁] at H; rw [pow_succ (c:ℝ) k]; linarith
  have hlim : Tendsto (fun n : ℕ => C/(n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat C
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlim.eventually_lt_const (half_pos hε))
  refine ⟨max N₀ (S*c^K),fun N hN => ?_⟩
  have hlow := (le_max_right _ _).trans hN
  have h₀ := hN₀ N ((le_max_left _ _).trans hN)
  let k := Nat.log c (N/S)
  have hNS : c^K ≤ N/S := (Nat.le_div_iff_mul_le hS).mpr (by simpa [mul_comm] using hlow)
  have hNSpos := (pow_pos (by omega : 0<c) K).trans_le hNS
  have hk : K≤k := (Nat.le_log_iff_pow_le hc (by have := pow_pos (by omega : 0<c) K; omega)).mpr hNS
  let q := c^k
  have hq : 0<q := pow_pos (by omega : 0<c) _
  have hu₀ : S*q ≤ N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hS).mp (Nat.pow_log_le_self _ (by omega : N/S≠0))
  have hu₁ : N < c*S*q := by
    have he := Nat.lt_pow_succ_log_self hc (N/S)
    change N/S < c^(k+1) at he
    rw [Nat.div_lt_iff_lt_mul hS,pow_succ] at he
    dsimp [q]; nlinarith
  let u := N/q
  let r := N%q
  have hus : S≤u := (Nat.le_div_iff_mul_le hq).mpr hu₀
  have hut : u<c*S := (Nat.div_lt_iff_lt_mul hq).mpr hu₁
  have hpos : (0:ℝ)<N := by exact_mod_cast (Nat.mul_pos hS hq).trans_le hu₀
  have hu := segment k hk (u-S) (by omega)
  rw [Nat.add_sub_of_le hus] at hu
  have he : P N = P (u*q) + ∑ i ∈ range r, f (u*q+i) := by
    dsimp only [P]; rw [← sum_range_add]; congr 2; simpa [u,r,Nat.mul_comm] using (Nat.div_add_mod N q).symm
  have h_end := hK k hk u (mem_Ico.mpr ⟨hus,hut⟩) r (Nat.mod_lt _ hq).le
  have htri := norm_add_le (P (u*q)-P (S*q)) (P (S*q))
  rw [sub_add_cancel] at htri
  have hpartial : ‖P N‖ ≤ C + ((c:ℝ)+1)*(S:ℝ)*δ*(c:ℝ)^k := by
    rw [he]
    have H := norm_add_le (P (u*q)) (∑ i ∈ range r, f (u*q+i))
    have hz := Nat.cast_le (α:=ℝ).mpr (show u-S ≤ (c-1)*S by omega)
    push_cast [Nat.cast_sub hus,Nat.cast_sub hc₁] at hz
    have hs' : (1:ℝ) ≤ S := by exact_mod_cast hS
    rw [Nat.cast_sub hus] at hu
    nlinarith [boundary k hk, mul_le_mul_of_nonneg_right hz (by positivity : 0≤δ*(c:ℝ)^k),
      mul_le_mul_of_nonneg_right hs' (by positivity : 0≤δ*(c:ℝ)^k)]
  have hqN : (c:ℝ)^k ≤ N := by exact_mod_cast (Nat.le_mul_of_pos_left q hS).trans hu₀
  have hS' : (0:ℝ)<S := by exact_mod_cast hS
  have hd' : ((c:ℝ)+1)*(S:ℝ)*δ = ε/2 := by dsimp [δ]; field_simp
  rw [show ∀ a b c d : ℝ, a*b*c*d = (a*b*c)*d by intros; ring,hd'] at hpartial
  rw [Real.dist_eq, sub_zero,abs_of_nonneg (norm_nonneg _),mean,norm_div,Complex.norm_natCast, div_lt_iff₀ hpos]
  change ‖P N‖ < _
  have HC := (div_lt_iff₀ hpos).mp h₀
  nlinarith [mul_le_mul_of_nonneg_left hqN (half_pos hε).le]

abbrev CellCancellation := RadixCellCancellation 3

theorem mean_zero_of_cells {S : ℕ} (hS : 0<S) {f : ℕ → ℂ}
    (h : ∀ u ∈ Ico S (3*S), CellCancellation f u) : Tendsto (mean f) atTop (𝓝 0) :=
  mean_zero_of_radix_cells (by decide) hS h

/-- Cancellation of means is equivalent to uniform cancellation on the
initial segments of each dyadic block [2^k,2^(k+1)). -/
theorem mean_zero_iff_dyadic_cells (f : ℕ → ℂ) :
    Tendsto (mean f) atTop (𝓝 0) ↔ RadixCellCancellation 2 f 1 := by
  constructor
  · intro H ε hε
    have small := (tendsto_zero_iff_norm_tendsto_zero.mp H).eventually_lt_const
      (show 0<ε/3 by positivity)
    obtain ⟨M,hM⟩ := eventually_atTop.mp small
    have hg : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
    filter_upwards [hg.eventually_ge_atTop M] with k hk T hT
    let q := 2^k
    let P (N : ℕ) := ∑ i ∈ range N, f i
    have bound (N : ℕ) (hN : q≤N) : ‖P N‖ ≤ (ε/3)*N := by
      have pos : (0:ℝ)<N := by exact_mod_cast (pow_pos (by decide : 0<2) k).trans_le hN
      have h := hM N (hk.trans hN)
      rw [mean,norm_div,Complex.norm_natCast,div_lt_iff₀ pos] at h
      exact h.le
    have eqn : ∑ i ∈ range T, f (1*2^k+i) = P (q+T)-P q := by simp [P,sum_range_add,q]
    rw [eqn]
    have h := (norm_sub_le _ _).trans (add_le_add (bound (q+T) (by omega)) (bound q le_rfl))
    have hT' : (T:ℝ)≤q := by exact_mod_cast hT
    have hq' : (q:ℝ)=(2:ℝ)^k := by dsimp [q]; push_cast; rfl
    push_cast at h
    change ‖P (q+T)-P q‖ ≤ ε*(2:ℝ)^k
    nlinarith [mul_le_mul_of_nonneg_left hT' hε.le]
  · intro H
    apply mean_zero_of_radix_cells (c:=2) (S:=1) (by decide) (by decide)
    intro u hu
    have : u=1 := by obtain ⟨hl,hh⟩ := mem_Ico.mp hu; omega
    simpa [this] using H

end NormalityChecker
