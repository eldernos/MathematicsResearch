module

public import NormalityChecker.MaskClassification

/-! Explicit discrepancy savings for all late powers and for bounded exponent gaps. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

/-- Lower bound through *every* cutoff for selected windows [uᵢ,2uᵢ).
Only the maximum ratio of successive left endpoints enters the bound. -/
theorem bounded_ratio_count (u : ℕ → ℕ) (R : ℕ) (hR : 2≤R)
    (unbounded : Tendsto u atTop atTop) (apart : ∀ j, 2*u j ≤ u (j+1))
    (gap : ∀ j, u (j+1) ≤ R*u j) (good : ℕ → Bool)
    (hit : ∀ j n, u j≤n → n<2*u j → good n=true) (N : ℕ) :
    N ≤ u 0 + (R-1)*((range N).filter (fun n => good n=true)).card := by
  let F (n : ℕ) := ((range n).filter (fun i => good i=true)).card
  have mono : Monotone F := fun _ _ h => card_le_card (filter_subset_filter _ (range_mono h))
  have chunk (j t : ℕ) (le : t≤u j) : F (u j+t)=F (u j)+t := by
    have count (n : ℕ) : F n = ∑ i ∈ range n, if good i=true then (1:ℕ) else 0 := by simp [F]
    rw [count,count,sum_range_add]
    have eqn : ∀ i ∈ range t, (if good (u j+i)=true then (1:ℕ) else 0)=1 := by
      intro i hi; have := mem_range.mp hi; simp [hit j (u j+i) (by omega) (by omega)]
    rw [sum_congr rfl eqn]; simp
  have budget (j : ℕ) : u j ≤ u 0 + (R-1)*F (u j) := by
    induction j with
    | zero => omega
    | succ j ih =>
      have h := mono (apart j)
      rw [two_mul,chunk j _ le_rfl] at h
      have price := Nat.mul_le_mul_left (R-1) h
      have eqn : R=(R-1)+1 := by omega
      calc u (j+1) ≤ R*u j := gap j
           _ = (R-1)*u j+u j := by rw [← Nat.succ_mul]; congr 1
           _ ≤ _ := by rw [Nat.mul_add] at price; omega
  by_cases small : N < u 0
  · omega
  obtain ⟨j,_,lo,hi⟩ := unbounded.exists_le_lt_succ (le_of_not_gt small)
  by_cases inside : N≤2*u j
  · let t := N-u j
    have cut : N=u j+t := by dsimp [t]; omega
    change N ≤ u 0 + (R-1)*F N
    rw [cut,chunk j t (by dsimp [t]; omega), Nat.mul_add]
    have := Nat.le_mul_of_pos_left t (by omega : 0<R-1)
    have := budget j; omega
  · have h := mono (le_of_not_ge inside)
    rw [two_mul,chunk j _ le_rfl] at h
    have price := Nat.mul_le_mul_left (R-1) h
    rw [Nat.mul_add] at price
    have := gap j
    have eqn : R*u j = (R-1)*u j+u j := by rw [← Nat.succ_mul]; congr 1; omega
    change N ≤ u 0 + (R-1)*F N
    have := budget j; omega

/-- Arbitrary smooth masks with eventually bounded gaps between retained power
exponents. The numerator is rational, signed, and has no degree bound. -/
theorem bounded_gap_discrepancy {b p t h : ℕ} (hb : 2≤b) (hp : p.Prime) (unit : ¬p∣b)
    (ht : 0<t) {P : ℚ[X]} (p0 : P.eval 0 ≠ 0) (S : Finset ℕ) (primes : ∀ r∈S,r.Prime)
    (mem : p∈S) (keep : ℕ → Bool) (e : ℕ → ℕ) (inc : StrictMono e)
    (retained : ∀ᶠ j : ℕ in atTop, keep (p^(e j))=true)
    (gaps : ∀ᶠ j : ℕ in atTop, e (j+1) ≤ e j+h) :
    limsup (radixDiscrepancy b (maskedValue b S keep P t)) atTop ≤ 1-1/((p:ℝ)^h-1) := by
  classical
  obtain ⟨K,stable⟩ := eventually_atTop.mp (retained.and gaps)
  let u (j : ℕ) := p^(e (K+j))
  let R := p^h
  let good (n : ℕ) := decide (Window p keep n)
  have hpos : 0<h := by have := (stable K le_rfl).2; have h : e K < e (K+1) := inc (Nat.lt_succ_self K); omega
  have hR : 2≤R := hp.two_le.trans (by simpa [R] using Nat.pow_le_pow_right hp.pos hpos)
  have grow : StrictMono u := fun i j hij => pow_lt_pow_right₀ hp.one_lt (inc (Nat.add_lt_add_left hij K))
  have apart (j : ℕ) : 2*u j ≤ u (j+1) := by
    calc 2*u j ≤ p*u j := Nat.mul_le_mul_right _ hp.two_le
         _ = p^(e (K+j)+1) := (pow_succ' ..).symm
         _ ≤ u (j+1) := Nat.pow_le_pow_right hp.pos (inc (by omega))
  have gap (j : ℕ) : u (j+1) ≤ R*u j := by
    dsimp [u,R]; rw [← pow_add, Nat.add_comm h]
    exact (Nat.pow_le_pow_right hp.pos (stable (K+j) (by omega)).2)
  have hit (j n : ℕ) (lo : u j ≤ n) (hi : n<2*u j) : good n=true :=
    decide_eq_true ⟨e (K+j),(stable _ (by omega)).1,lo,hi⟩
  apply rational_window_bound hb hp unit ht p0 S primes mem keep (fun n => !(good n))
    (.of_forall fun n hn => by simpa [good] using hn)
  intro ε pos
  have realR : (1:ℝ)<R := by exact_mod_cast (show 1<R by omega)
  have nn : (0:ℝ)<(R:ℝ)-1 := by linarith
  obtain ⟨N₀,hn₀⟩ := exists_nat_gt ((u 0:ℝ)/(ε*((R:ℝ)-1)))
  filter_upwards [eventually_ge_atTop N₀] with N hn
  have cut := bounded_ratio_count u R hR grow.tendsto_atTop apart gap good hit N
  let F := ((range N).filter (fun n => good n=true)).card
  have realCut : (N:ℝ) ≤ u 0+((R:ℝ)-1)*F := by
    have z : (N:ℝ) ≤ u 0 + ((R-1:ℕ):ℝ)*F := by exact_mod_cast cut
    simpa [Nat.cast_sub (by omega : 1≤R)] using z
  have eqn : (∑ i∈range N, if !(good i) then (1:ℝ) else 0) = N-F := by
    have sum := card_filter_add_card_filter_not (s:=range N) (fun n => good n=true)
    rw [card_range] at sum
    have sums : (F:ℝ)+(((range N).filter (fun i => ¬good i=true)).card:ℝ)=N := by exact_mod_cast sum
    simp only [Bool.not_eq_true',sum_boole] at *
    simpa only [← Bool.not_eq_true] using (show _ = (N:ℝ)-F by linarith only [sums])
  rw [eqn]
  change _ ≤ (1-1/((p:ℝ)^h-1)+ε)*N
  rw [← Nat.cast_pow]; change _ ≤ (1-1/((R:ℝ)-1)+ε)*N
  have enough := (div_lt_iff₀ (mul_pos pos nn)).mp (hn₀.trans_le (Nat.cast_le.mpr hn))
  apply (mul_le_mul_iff_left₀ nn).mp
  field_simp [nn.ne']
  nlinarith

theorem late_powers_discrepancy {b p t : ℕ} (hb : 2≤b) (hp : p.Prime) (unit : ¬p∣b)
    (ht : 0<t) {P : ℚ[X]} (p0 : P.eval 0 ≠ 0) (S : Finset ℕ) (primes : ∀ r∈S,r.Prime)
    (mem : p∈S) (keep : ℕ → Bool) (retained : ∀ᶠ k : ℕ in atTop, keep (p^k)=true) :
    limsup (radixDiscrepancy b (maskedValue b S keep P t)) atTop ≤ 1-1/((p:ℝ)-1) := by
  simpa using bounded_gap_discrepancy (h:=1) hb hp unit ht p0 S primes mem keep id strictMono_id retained
    (.of_forall fun _ => le_rfl)

theorem normal_of_late_twos {b t : ℕ} (hb : 2≤b) (odd : ¬2∣b) (ht : 0<t)
    {P : ℚ[X]} (p0 : P.eval 0 ≠ 0) (S : Finset ℕ) (primes : ∀ r∈S,r.Prime) (mem : 2∈S)
    (keep : ℕ → Bool) (retained : ∀ᶠ k : ℕ in atTop, keep (2^k)=true) :
    NormalIn b (maskedValue b S keep P t) := by
  apply normal_of_radix_limsup_zero hb
  have H := late_powers_discrepancy hb Nat.prime_two odd ht p0 S primes mem keep retained
  norm_num at H; exact H

end NormalityChecker.PolynomialMasks
