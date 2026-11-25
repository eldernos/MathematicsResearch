module

public import NormalityChecker.QuantitativeStonehamDiscrepancy

/-! Lengths of the clean pieces between insertions of a polynomial on one axis. -/
@[expose] public section
open Finset
namespace NormalityChecker.QuantitativeStoneham

/-- An insertion position, allowing zero padding from any lower degree. -/
def PowerInsertion (c d n : ℕ) : Prop :=
  ∃ w : Fin d → ℕ, (∀ i, w i = 0 ∨ ∃ j : ℕ, w i = c^j) ∧ ∑ i, w i = n

/-- A set with spacing `U` has at most `W` points per covering interval of width `W*U`. -/
private theorem separated_card {ι : Type*} [Fintype ι] {U W : ℕ} (hU : 0 < U)
    (s : Finset ℕ) (z : ι → ℕ)
    (cover : ∀ n ∈ s, ∃ t, z t ≤ n ∧ n < z t + W*U)
    (sep : ∀ x ∈ s, ∀ y ∈ s, x < y → x+U ≤ y) : s.card ≤ Fintype.card ι * W := by
  classical
  choose t lower upper using fun x : s => cover x x.property
  let idx (x : s) : Fin W := ⟨(x.val-z (t x))/U,
    (Nat.div_lt_iff_lt_mul hU).mpr (by have := upper x; have := lower x; omega)⟩
  let code (x : s) := (t x, idx x)
  have inj : Function.Injective code := by
    intro x y eqn
    have eqc := congrArg Prod.fst eqn
    have eqi := congrArg (fun a : ι × Fin W => a.2.val) eqn
    change t x = t y at eqc
    change (x.val - z (t x))/U = (y.val-z (t y))/U at eqi
    rw [eqc] at eqi
    have xlo := lower x
    rw [eqc] at xlo
    have ylo := lower y
    have ex := Nat.mod_add_div (x.val-z (t y)) U
    have ey := Nat.mod_add_div (y.val-z (t y)) U
    rw [eqi] at ex
    have mx := Nat.mod_lt (x.val-z (t y)) hU
    have my := Nat.mod_lt (y.val-z (t y)) hU
    apply Subtype.ext
    rcases lt_trichotomy x.val y.val with lt | eq | gt
    · have := sep _ x.property _ y.property lt; omega
    · exact eq
    · have := sep _ y.property _ x.property gt; omega
  simpa using Fintype.card_le_of_injective code inj

/-- Above resolution `U`, at most `m+1` different powers of `c` occur below
`U*2^m`. Replacing smaller coordinates by zero covers all insertion positions
by `(m+2)^d` short intervals, independently of the size of `U`. -/
theorem separated_insertions {c d U m : ℕ} (hc : 2 ≤ c) (hU : 0 < U) (s : Finset ℕ)
    (bounded : ∀ n ∈ s, n < U*2^m) (event : ∀ n ∈ s, PowerInsertion c d n)
    (sep : ∀ x ∈ s, ∀ y ∈ s, x < y → x+U ≤ y) : s.card ≤ (m+2)^d * (d+1) := by
  classical
  let a := Nat.log c U
  let digit (v : Fin (m+2)) := if v.val = 0 then 0 else c^(a+(v.val-1))
  have letter (w : ℕ) (bound : w < U*2^m) (power : w = 0 ∨ ∃ j : ℕ, w = c^j) :
      ∃ v, digit v ≤ w ∧ w ≤ digit v + U := by
    by_cases small : w < U
    · exact ⟨0, by simp [digit], by simpa [digit] using small.le⟩
    obtain h | ⟨j, rfl⟩ := power
    · omega
    have lower : a ≤ j := (Nat.log_mono_right (le_of_not_gt small)).trans_eq (Nat.log_pow (by omega) j)
    have upper : j ≤ a+m := by
      by_contra! h
      have h₁ : U*2^m ≤ c^(a+1)*c^m :=
        Nat.mul_le_mul (Nat.lt_pow_succ_log_self (by omega : 1 < c) U).le (Nat.pow_le_pow_left hc _)
      rw [← pow_add] at h₁
      exact bound.not_ge (h₁.trans (Nat.pow_le_pow_right (by omega) (by omega)))
    let v : Fin (m+2) := ⟨j-a+1, by omega⟩
    have hv : digit v = c^j := by simp [digit, v, Nat.add_sub_of_le lower]
    exact ⟨v, hv.le, by rw [hv]; omega⟩
  let z (t : Fin d → Fin (m+2)) := ∑ i, digit (t i)
  have cover (n : ℕ) (hn : n ∈ s) : ∃ t, z t ≤ n ∧ n < z t + (d+1)*U := by
    obtain ⟨w, hw, sum⟩ := event n hn
    have bound (i) : w i < U*2^m :=
      (single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans_lt (sum ▸ bounded n hn)
    choose t lo hi using fun i => letter (w i) (bound i) (hw i)
    refine ⟨t, (sum_le_sum (fun i _ => lo i)).trans_eq sum, ?_⟩
    have h := sum_le_sum (s := univ) (fun i _ => hi i)
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum] at h
    dsimp [z]; rw [Nat.add_mul, one_mul]; omega
  simpa [Fintype.card_fun] using separated_card hU s z cover sep

/-- Moment bound for *every* partial partition of a dyadic shell. `s` lists
left endpoints and `len` the actual (possibly truncated) lengths. The shell
start can be arbitrary; all other starts must be insertion positions. -/
theorem clean_length_moment {c d k : ℕ} (hc : 2 ≤ c) (s : Finset ℕ) (len : ℕ → ℕ)
    (ends : ∀ n ∈ s, n < 2^(k+1)) (bounded : ∀ n ∈ s, 0 < len n ∧ len n ≤ 2^k)
    (event : ∀ n ∈ s, n ≠ 2^k → PowerInsertion c d n)
    (disjoint : ∀ x ∈ s, ∀ y ∈ s, x < y → x + len x ≤ y) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∑ n ∈ s, (len n : ℝ)^γ ≤
      ∑ j ∈ range (k+1), ((1 + (k+1-j+2)^d * (d+1) : ℕ) : ℝ) * (((2 : ℝ)^(j+1))^γ) := by
  let level (n : ℕ) := Nat.log 2 (len n)
  have into (n : ℕ) (hn : n ∈ s) : level n ∈ range (k+1) := mem_range.mpr (by
    have := (Nat.log_mono_right (b := 2) (bounded n hn).2).trans_eq (Nat.log_pow (by decide) k)
    dsimp [level]; omega)
  rw [← sum_fiberwise_of_maps_to into (fun n => (len n : ℝ)^γ)]
  apply sum_le_sum
  intro j hj
  let A := s.filter (fun n => level n = j)
  have le : j ≤ k := by have := mem_range.mp hj; omega
  have scale : 2^j * 2^(k+1-j) = 2^(k+1) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
  have card := separated_insertions (d := d) (U := 2^j) (m := k+1-j) hc (by positivity) (A.erase (2^k))
    (fun n hn => scale ▸ ends n (mem_filter.mp (mem_of_mem_erase hn)).1)
    (fun n hn => event n (mem_filter.mp (mem_of_mem_erase hn)).1 (ne_of_mem_erase hn)) (by
      intro x hx y hy lt
      obtain ⟨xs, xj⟩ := mem_filter.mp (mem_of_mem_erase hx)
      have ys := (mem_filter.mp (mem_of_mem_erase hy)).1
      have small : 2^j ≤ len x := xj ▸ Nat.pow_log_le_self 2 (bounded x xs).1.ne'
      exact (Nat.add_le_add_left small x).trans (disjoint x xs y ys lt))
  have size : A.card ≤ 1 + (k+1-j+2)^d * (d+1) := by
    by_cases hit : 2^k ∈ A
    · rw [card_erase_of_mem hit] at card; omega
    · rw [erase_eq_of_notMem hit] at card; omega
  calc
    _ ≤ ∑ _n ∈ A, ((2 : ℝ)^(j+1))^γ := by
      apply sum_le_sum
      intro n hn
      have nj : level n = j := (mem_filter.mp hn).2
      have hi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (len n)
      change len n < 2^(level n + 1) at hi
      rw [nj] at hi
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hi.le) hγ
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]; gcongr

end NormalityChecker.QuantitativeStoneham
