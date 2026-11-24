module

public import NormalityChecker.ProductThreeFivePrefix

/-! Isolated insertions with a surviving ternary denominator on an adjacent interval. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ProductThreeFive

/-- The chosen power of five is the first one strictly above `P/3`. -/
private lemma choose_five (k : ℕ) :
    ∃ l : ℕ, 3^(k+1) ≤ 3*5^(l+1) ∧ 3*5^(l+1) ≤ 5*3^(k+1) := by
  let l := Nat.log 5 (3^k)
  refine ⟨l,?_,?_⟩
  · have h := Nat.lt_pow_succ_log_self (by decide : 1<5) (3^k)
    rw [pow_succ']; dsimp [l]; omega
  · have h := Nat.pow_log_le_self 5 (by positivity : (3:ℕ)^k≠0)
    dsimp [l]; rw [pow_succ' (5:ℕ),pow_succ' (3:ℕ)]; omega

/-- Every other insertion lies beyond one of the two adjacent open gaps. -/
private lemma separated {k l : ℕ} (low : 3^(k+1) ≤ 3*5^(l+1))
    (high : 3*5^(l+1) ≤ 5*3^(k+1)) (v : ℕ × ℕ) (ne : v ≠ (k,l)) :
    let B := 4*3^(k+1)/15
    location v + B ≤ location (k,l) ∨ location (k,l) + B ≤ location v := by
  rcases v with ⟨i,j⟩
  change 3^(i+1)+5^(j+1)+4*3^(k+1)/15 ≤ 3^(k+1)+5^(l+1) ∨
    3^(k+1)+5^(l+1)+4*3^(k+1)/15 ≤ 3^(i+1)+5^(j+1)
  by_cases a : k < i
  · have h := Nat.pow_le_pow_right (by decide : 0 < 3) (show k + 1 + 1 ≤ i + 1 by omega)
    rw [pow_succ] at h
    right; apply le_trans _ (Nat.le_add_right ..); omega
  by_cases b : l < j
  · have h := Nat.pow_le_pow_right (by decide : 0 < 5) (show l + 1 + 1 ≤ j + 1 by omega)
    rw [pow_succ] at h
    right; apply le_trans _ (Nat.le_add_left ..); omega
  left
  have h₁ := Nat.pow_le_pow_right (by decide : 0 < 3) (show i + 1 ≤ k + 1 by omega)
  have h₂ := Nat.pow_le_pow_right (by decide : 0 < 5) (show j + 1 ≤ l + 1 by omega)
  by_cases eq : i=k
  · have different : j≠l := by rintro rfl; exact ne (by rw [eq])
    have h := Nat.pow_le_pow_right (by decide : 0 < 5) (show j + 1 + 1 ≤ l + 1 by omega)
    rw [pow_succ] at h; omega
  · have h := Nat.pow_le_pow_right (by decide : 0 < 3) (show i + 1 + 1 ≤ k + 1 by omega)
    rw [pow_succ] at h; omega

private lemma jump {v : ℕ × ℕ} {n B : ℕ} (endpt : n+B=location v)
    (positive : 0<B) (isolated : ∀ w ≠ v, location w ≤ n ∨ n+B < location w) :
    pre (n+B) - (2:ℚ)^B * pre n = (weightDen v : ℚ)⁻¹ := by
  have absent : v ∉ active n := by rw [mem_active,← endpt]; omega
  have eqn : active (n+B) = insert v (active n) := by
    ext w
    rw [mem_insert,mem_active,mem_active]
    by_cases eq : w=v
    · simp [eq,endpt]
    · have h := isolated w eq
      simp only [eq,false_or]; omega
  rw [pre,eqn,sum_insert absent,transport,endpt,Nat.sub_self,pow_zero,one_div]
  ring

private lemma prime_power_survives (x y : ℚ) (k : ℕ) (h : 3^k ∣ (x-y).den) :
    3^k ∣ x.den ∨ 3^k ∣ y.den := by
  have d := h.trans (Rat.sub_den_dvd_lcm x y)
  rw [Nat.prime_three.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero x.pos.ne' y.pos.ne'),
      Nat.factorization_lcm x.pos.ne' y.pos.ne',Finsupp.sup_apply,le_sup_iff] at d
  simpa only [Nat.prime_three.pow_dvd_iff_le_factorization x.pos.ne',
    Nat.prime_three.pow_dvd_iff_le_factorization y.pos.ne'] using d

/-- On each ternary shell from `P=9` onward, a clean interval of length
`⌊4P/15⌋` has a starting denominator divisible by `P`. Its right endpoint
is at most `44P/15`, a little before the end of the shell. -/
theorem surviving_window (k : ℕ) (hk : 1 ≤ k) :
    let P := 3^(k+1)
    let B := 4*P/15
    ∃ n : ℕ, P ≤ n ∧ 15*(n+B) ≤ 44*P ∧ P ∣ (pre n).den ∧
      ∀ i<B, pre (n+i) = (2:ℚ)^i * pre n := by
  let P := 3^(k+1)
  let B := 4*P/15
  obtain ⟨l,lo,hi⟩ := choose_five k
  let Q := 5^(l+1)
  change P ≤ 3*Q at lo
  change 3*Q ≤ 5*P at hi
  let s := P+Q
  have loc : location (k,l) = s := rfl
  have sep (w : ℕ × ℕ) (ne : w ≠ (k,l)) : location w+B ≤ s ∨ s+B ≤ location w :=
    separated lo hi w ne
  have big : 9 ≤ P := Nat.pow_le_pow_right (by decide : 0 < 3) (show 2 ≤ k + 1 by omega)
  have bp : 0 < B := by dsimp [B]; omega
  have room : B ≤ Q := by dsimp [B]; omega
  have ceiling : 15*(s+B) ≤ 44*P := by dsimp [s,B]; omega
  let n := s-B
  have endpt : n+B=s := by dsimp [n,s]; omega
  have start : P ≤ n := by dsimp [n,s]; omega
  have eqn := jump (v:=(k,l)) (endpt.trans loc.symm) bp (by
    intro w ne; have h := sep w ne; omega)
  have dv : P ∣ (pre (n+B) - (2:ℚ)^B * pre n).den := by
    rw [eqn,Rat.inv_natCast_den_of_pos (by unfold weightDen; positivity)]
    exact dvd_mul_right ..
  rcases prime_power_survives _ _ (k+1) dv with right | left
  · refine ⟨s,by dsimp [s]; omega,ceiling,endpt ▸ right,?_⟩
    intro i hi'; change i < B at hi'; apply follows; intro w gt
    have ne : w ≠ (k,l) := by rintro rfl; omega
    have h := sep w ne
    omega
  · have divides : ((2:ℚ)^B * pre n).den ∣ (pre n).den := by
      have integral : ((2:ℚ)^B).den = 1 := by exact_mod_cast Rat.den_natCast (2^B)
      simpa only [integral,one_mul] using
        Rat.mul_den_dvd ((2:ℚ)^B) (pre n)
    refine ⟨n,start,by rw [endpt]; omega,left.trans divides,?_⟩
    intro i hi'; change i < B at hi'; apply follows; intro w gt
    by_cases eq : w=(k,l)
    · rw [eq,loc]; omega
    · have h := sep w eq; omega

/-- The true binary orbit is uniformly distributed on one interval of the
specified length in every sufficiently late ternary shell. -/
theorem uniform_windows {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,
      let P := 3^(k+1)
      let B := 4*P/15
      ∃ n : ℕ, P ≤ n ∧ 15*(n+B) ≤ 44*P ∧
        ∀ a c : ℝ, 0≤a → a≤c → c≤1 →
          ‖∑ i ∈ range B, Localized.centered (shift 2 (alpha 3 * alpha 5)) a c (n+i)‖ ≤ ε*B := by
  obtain ⟨M,K,block⟩ := smooth_interval_block (b:=2) (c:=15) (d:=4)
    (fixed_support_orbit_estimate (by decide) (by decide) (by decide))
    (alpha 3 * alpha 5) pre (by simpa only [Nat.cast_ofNat] using shifted_tail) hε
  filter_upwards [eventually_ge_atTop (max (max M K) 100)] with k hk
  let P := 3^(k+1)
  let B := 4*P/15
  have kp : k ≤ P := (Nat.lt_pow_self (by decide : 1<3) (n:=k+1)).le.trans' (by omega)
  obtain ⟨n,lo,hi,dv,orb⟩ := surviving_window k (by omega)
  change P ≤ n at lo
  change 15*(n+B) ≤ 44*P at hi
  obtain ⟨support,cap⟩ := prefix_denominator (n:=n) (by omega)
  have b₁ : 15 ≤ B := by dsimp [B]; omega
  have b₂ : n ≤ 15*B := by dsimp [B] at *; omega
  have bound : (pre n).den ≤ B^4 := calc
    _ ≤ n^2 := cap
    _ ≤ (B*B)^2 := Nat.pow_le_pow_left (b₂.trans (Nat.mul_le_mul_right B b₁)) _
    _ = B^4 := by ring
  exact ⟨n,lo,hi,block B n (by omega) ((show M ≤ P by omega).trans
    (Nat.le_of_dvd (pre n).pos dv)) support bound orb⟩

end NormalityChecker.ProductThreeFive
