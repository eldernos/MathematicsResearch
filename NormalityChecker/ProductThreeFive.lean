module

public import NormalityChecker.ProductThreeFiveWindows
public import NormalityChecker.QualityCoverage

/-! Binary discrepancy and irrationality of the product α(2,3) · α(2,5). -/
@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker.ProductThreeFive

/-- Four successive scales suffice at every large cutoff. For `R=3^k` with
`238R ≤ N < 714R`, use the windows for `P=3R,9R,27R,81R`. The largest
possible endpoint is `44·81R/15 ≤ 238R`; their total length is at least
`32R-4`, which exceeds `2N/45` for large `R`. -/
private theorem four_windows {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∃ piece : ℕ → Finset ℕ,
      (∀ j ∈ range 4, piece j ⊆ range N) ∧ ((range 4 : Finset ℕ) : Set ℕ).PairwiseDisjoint piece ∧
      2*N ≤ 45*((range 4).biUnion piece).card ∧
      ∀ a c : ℝ, 0≤a → a<c → c≤1 → ∀ j ∈ range 4,
        ‖∑ i ∈ piece j, Localized.centered (shift 2 (alpha 3 * alpha 5)) a c i‖ ≤ δ*(piece j).card := by
  classical
  obtain ⟨K,good⟩ := eventually_atTop.mp (uniform_windows hδ)
  filter_upwards [eventually_ge_atTop (238*3^(K+4))] with N hN
  let k := Nat.log 3 (N/238)
  let R := 3^k
  let P (j : ℕ) := R*3^(j+1)
  let B (j : ℕ) := 4*P j/15
  have large : 3^(K+4) ≤ N/238 := by omega
  have hk : K+4 ≤ k := Nat.le_log_of_pow_le (by decide) large
  have rbig : 81 ≤ R := Nat.pow_le_pow_right (by decide : 0<3) (show 4 ≤ k by omega)
  have npos : 0 < N/238 := (pow_pos (by decide : 0<3) _).trans_le large
  have lower : 238*R ≤ N := by have h := Nat.pow_log_le_self 3 npos.ne'; change R ≤ N/238 at h; omega
  have upper : N < 714*R := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<3) (N/238)
    change N/238 < 3^(k+1) at h
    rw [pow_succ] at h; change N/238 < R*3 at h; omega
  have windows (j : ℕ) := good (k+j) (by omega)
  simp only [Nat.add_assoc,pow_add 3 k] at windows
  choose n start stop cert using windows
  change ∀ j, P j ≤ n j at start
  change ∀ j, 15*(n j+B j) ≤ 44*P j at stop
  let piece (j : ℕ) := Ico (n j) (n j+B j)
  have card (j : ℕ) : (piece j).card = B j := by simp [piece,Nat.card_Ico]
  have order {j l : ℕ} (h : j<l) : n j+B j ≤ n l := by
    have gap : 3*P j ≤ P l := calc
      3*P j = R*3^(j+1+1) := by dsimp [P]; rw [pow_succ]; ring
      _ ≤ P l := Nat.mul_le_mul_left R (Nat.pow_le_pow_right (by decide) (by omega))
    have lo := start l
    have hi := stop j
    omega
  have dis : ((range 4 : Finset ℕ) : Set ℕ).PairwiseDisjoint piece := by
    intro j _ l _ ne
    apply disjoint_left.mpr; intro t hj hl
    obtain ⟨jl,jh⟩ := mem_Ico.mp hj; obtain ⟨ll,lh⟩ := mem_Ico.mp hl
    rcases lt_or_gt_of_ne ne with h | h
    · exact (jh.trans_le (order h)).not_ge ll
    · exact (lh.trans_le (order h)).not_ge jl
  refine ⟨piece,?_,dis,?_,?_⟩
  · intro j hj t ht
    have h := mem_range.mp hj
    have cap : P j ≤ R*81 := Nat.mul_le_mul_left R
      (Nat.pow_le_pow_right (by decide : 0<3) (show j+1≤4 by omega))
    have hi := (mem_Ico.mp ht).2
    have fin := stop j
    apply mem_range.mpr; omega
  · rw [card_biUnion dis]
    simp only [card,sum_range_succ,sum_range_zero,zero_add]
    dsimp [B,P]
    omega
  · intro a c ha hac hc j _
    rw [card,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
    exact cert j a c ha hac.le hc

/-- The upper limit of the binary extreme interval discrepancy of the product
of the two standard Stoneham series is at most `43/45`. -/
theorem discrepancy : asymptoticDiscrepancy (alpha 3 * alpha 5) ≤ 43/45 := by
  apply le_of_forall_pos_le_add; intro ε he
  let δ := min ε 1
  have pos : 0 < δ := lt_min he zero_lt_one
  have H := Coverage.asymptotic_fixed_quality (b:=2) (x:=alpha 3 * alpha 5)
    (g:=2/45) (d:=δ) (min_le_right ..) (by
      intro e ep
      filter_upwards [four_windows pos,eventually_gt_atTop 0] with N ⟨piece,sub,dis,size,cert⟩ hn
      refine ⟨range 4,piece,sub,dis,?_,cert⟩
      have count : 2*(N:ℝ) ≤ 45*(((range 4).biUnion piece).card:ℝ) := by exact_mod_cast size
      rw [le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<N)]
      linarith only [count,mul_nonneg ep.le (Nat.cast_nonneg (α:=ℝ) N)])
  exact H.trans (by linarith [show δ ≤ ε from min_le_left ..])

/-- Rational binary shifts are confined to a finite grid. The uniform windows
of the product visit an interval strictly between consecutive grid points. -/
theorem irrational : Irrational (alpha 3 * alpha 5) := by
  rintro ⟨q,hq⟩
  let a : ℝ := 1/(q.den:ℝ)
  have dq : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have ap : 0 < a := by dsimp [a]; positivity
  have a1 : a ≤ 1 := (div_le_one dq).mpr (by exact_mod_cast q.pos)
  have miss (m : ℕ) : ¬ (a/2 ≤ shift 2 (q:ℝ) m ∧ shift 2 q m < a) := by
    let z : ℤ := (2:ℤ)^m*q.num
    have grid : shift 2 (q:ℝ) m = ((z % q.den : ℤ):ℝ) / q.den := by
      unfold shift
      rw [Rat.cast_def,mul_div_assoc',Nat.cast_ofNat,show ((2:ℝ)^m*q.num) = (z:ℝ) by simp [z],
        Int.fract_div_intCast_eq_div_intCast_mod]
    rw [grid]
    rintro ⟨lo,hi⟩
    have small : (z % q.den : ℤ) < 1 := by
      exact_mod_cast (div_lt_div_iff_of_pos_right dq).mp hi
    have positive : (0:ℤ) < z % q.den := by
      exact_mod_cast (div_pos_iff_of_pos_right dq).mp ((half_pos ap).trans_le lo)
    omega
  obtain ⟨k,large,⟨n,_,_,cert⟩⟩ := ((eventually_ge_atTop 1).and
    (uniform_windows (show 0 < a/4 by positivity))).exists
  let B := 4*3^(k+1)/15
  have big : 9 ≤ 3^(k+1) := Nat.pow_le_pow_right (by decide : 0<3) (show 2 ≤ k+1 by omega)
  have bp : (0:ℝ) < B := by exact_mod_cast (show 0<B by dsimp [B]; omega)
  have H := cert (a/2) a (half_pos ap).le (half_lt_self ap).le a1
  rw [← hq,Localized.centered_sum] at H
  have none : IntervalFourier.count (fun i => shift 2 (q:ℝ) (n+i)) (a/2) a B = 0 := by
    simp [IntervalFourier.count,miss]
  change |(IntervalFourier.count _ (a/2) a B : ℝ) - B*(a-a/2)| ≤ a/4*B at H
  rw [none,Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (mul_nonneg bp.le (by linarith))] at H
  nlinarith only [H,mul_pos ap bp]

end NormalityChecker.ProductThreeFive
