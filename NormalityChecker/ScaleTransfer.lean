module

public import NormalityChecker.Correlations
public import NormalityChecker.OrbitSum

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- An arbitrary prefix in cell u, measured in units of 3^k. -/
def CellCancellation (f : ℕ → ℂ) (u : ℕ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ T ≤ 3^k,
    ‖∑ i ∈ range T, f (u*3^k+i)‖ ≤ ε*(3:ℝ)^k

/-- Control of all partial cells at large scales controls every prefix endpoint. -/
theorem mean_zero_of_cells {S : ℕ} (hS : 0<S) {f : ℕ → ℂ}
    (h : ∀ u ∈ Ico S (3*S), CellCancellation f u) : Tendsto (mean f) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε/(8*S)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have HE := (eventually_all_finset (Ico S (3*S))).mpr (fun u hu => h u hu δ hδ)
  obtain ⟨K,hK⟩ := eventually_atTop.mp HE
  let P (n : ℕ) := ∑ i ∈ range n, f i
  have segment (k : ℕ) (hk : K≤k) (l : ℕ) (hl : l≤2*S) :
      ‖P ((S+l)*3^k)-P (S*3^k)‖ ≤ l*(δ*(3:ℝ)^k) := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hu : S+l ∈ Ico S (3*S) := mem_Ico.mpr ⟨by omega,by omega⟩
      have he : P ((S+(l+1))*3^k) = P ((S+l)*3^k)+
          ∑ i ∈ range (3^k), f ((S+l)*3^k+i) := by
        dsimp [P]; rw [show (S+(l+1))*3^k = (S+l)*3^k + 3^k by ring, sum_range_add]
      rw [he, show ∀ a b c : ℂ, a+b-c = (a-c)+b by intros; ring]
      apply (norm_add_le _ _).trans
      have := add_le_add (ih (by omega)) (hK k hk _ hu _ le_rfl)
      push_cast; linarith
  let C := ‖P (S*3^K)‖
  have boundary (k : ℕ) (hk : K≤k) : ‖P (S*3^k)‖ ≤ C+(S:ℝ)*δ*3^k := by
    induction k, hk using Nat.le_induction with
    | base => exact le_add_of_nonneg_right (by positivity)
    | succ k hk ih =>
      have he : S*3^(k+1)=(S+2*S)*3^k := by ring
      have H := segment k hk (2*S) le_rfl
      rw [← he] at H
      have H' := norm_add_le (P (S*3^(k+1))-P (S*3^k)) (P (S*3^k))
      rw [sub_add_cancel] at H'
      push_cast at H; rw [pow_succ (3:ℝ) k]; linarith
  have hc : Tendsto (fun n : ℕ => C/(n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat C
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hc.eventually_lt_const (half_pos hε))
  refine ⟨max N₀ (S*3^K),fun N hN => ?_⟩
  have hlow := (le_max_right _ _).trans hN
  have h₀ := hN₀ N ((le_max_left _ _).trans hN)
  let k := Nat.log 3 (N/S)
  have hNS : 3^K ≤ N/S := (Nat.le_div_iff_mul_le hS).mpr (by simpa [mul_comm] using hlow)
  have hNSpos := (pow_pos (by decide : 0<3) K).trans_le hNS
  have hk : K≤k := (Nat.le_log_iff_pow_le (by decide) (by have := pow_pos (by decide : 0<3) K; omega)).mpr hNS
  let q := 3^k
  have hq : 0<q := pow_pos (by decide) _
  have hu₀ : S*q ≤ N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hS).mp (Nat.pow_log_le_self _ (by omega : N/S≠0))
  have hu₁ : N < 3*S*q := by
    have he := Nat.lt_pow_succ_log_self (by decide : 1<3) (N/S)
    change N/S < 3^(k+1) at he
    rw [Nat.div_lt_iff_lt_mul hS,pow_succ] at he
    dsimp [q]; nlinarith
  let u := N/q
  let r := N%q
  have hus : S≤u := (Nat.le_div_iff_mul_le hq).mpr hu₀
  have hut : u<3*S := (Nat.div_lt_iff_lt_mul hq).mpr hu₁
  have hpos : (0:ℝ)<N := by exact_mod_cast (Nat.mul_pos hS hq).trans_le hu₀
  have hu := segment k hk (u-S) (by omega)
  rw [Nat.add_sub_of_le hus] at hu
  have he : P N = P (u*q) + ∑ i ∈ range r, f (u*q+i) := by
    dsimp only [P]; rw [← sum_range_add]; congr 2; simpa [u,r,Nat.mul_comm] using (Nat.div_add_mod N q).symm
  have h_end := hK k hk u (mem_Ico.mpr ⟨hus,hut⟩) r (Nat.mod_lt _ hq).le
  have htri := norm_add_le (P (u*q)-P (S*q)) (P (S*q))
  rw [sub_add_cancel] at htri
  have hpartial : ‖P N‖ ≤ C + 4*(S:ℝ)*δ*(3:ℝ)^k := by
    rw [he]
    have H := norm_add_le (P (u*q)) (∑ i ∈ range r, f (u*q+i))
    have hz : ((u-S:ℕ):ℝ) ≤ 2*S := by exact_mod_cast (show u-S ≤ 2*S by omega)
    have hs' : (1:ℝ) ≤ S := by exact_mod_cast hS
    nlinarith [boundary k hk, mul_le_mul_of_nonneg_right hz (by positivity : 0≤δ*(3:ℝ)^k),
      mul_le_mul_of_nonneg_right hs' (by positivity : 0≤δ*(3:ℝ)^k)]
  have hqN : (3:ℝ)^k ≤ N := by exact_mod_cast (Nat.le_mul_of_pos_left q hS).trans hu₀
  have hS' : (0:ℝ)<S := by exact_mod_cast hS
  have hd' : 4*(S:ℝ)*δ = ε/2 := by dsimp [δ]; field_simp; ring
  rw [show ∀ a b c d : ℝ, a*b*c*d = (a*b*c)*d by intros; ring,hd'] at hpartial
  rw [Real.dist_eq, sub_zero,abs_of_nonneg (norm_nonneg _),mean,norm_div,Complex.norm_natCast, div_lt_iff₀ hpos]
  change ‖P N‖ < _
  have HC := (div_lt_iff₀ hpos).mp h₀
  nlinarith [mul_le_mul_of_nonneg_left hqN (half_pos hε).le]

end NormalityChecker
