module

meta import Lean
public import NormalityChecker.ProductThreeFiveNonrectangular
import all NormalityChecker.ProductThreeFiveOrdinary

/-! A rational phase cover for the nonrectangular joint failure charge. -/

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ProductThreeFive
namespace NonrectangularOrdinary

open Ordinary (phaseDen start stop down up)

private abbrev Span := ℕ × ℕ
private meta abbrev failureNum := 4631
private meta abbrev failureDen := 12500

-- All three safe intervals for a fixed exponent pair have the same lower
-- endpoint. Their union ends at the largest of the three upper endpoints.
private meta def window (a b i j : ℕ) : Span :=
  let p := 3^i
  let q := 5^j
  let lo := p + up b q
  let qNext := down a (5*q)
  let rect := min (3*p) qNext
  let row := if j%2 ≠ 0 then min (3*p) (p+qNext) else 0
  let col := if i%4 ≠ 0 then min qNext (down a q+3*p) else 0
  (lo, min stop (max rect (max row col)))

private meta def hinted (a b : ℕ) (keys : List ℕ) : List Span :=
  keys.map fun key => window a b (key/32) (key%32)

private lemma window_safe {k l a b i j n : ℕ}
    (bound : a*81^k ≤ phaseDen*25^l) (bound' : phaseDen*25^l ≤ b*81^k)
    (left : (window a b i j).1*81^k ≤ n) (right : n < (window a b i j).2*81^k) :
    nonrectangularCost n = 0 := by
  let B := 81^k
  let Q := 25^l
  let p := 3^i
  let q := 5^j
  have bp : 0<B := pow_pos (by decide) _
  have Pdef : 3^(4*k+i)=p*B := by dsimp [p,B]; rw [pow_add,pow_mul]; ring
  have Qdef : 5^(2*l+j)=Q*q := by dsimp [q,Q]; rw [pow_add,pow_mul]; rfl
  obtain ⟨_,qhi⟩ := Ordinary.bracket bound bound' q
  obtain ⟨qlo,_⟩ := Ordinary.bracket bound bound' (5*q)
  change Q*q ≤ up b q*B at qhi
  change down a (5*q)*B ≤ Q*(5*q) at qlo
  rw [show Q*(5*q)=5*(Q*q) by ring] at qlo
  change (p+up b q)*B ≤ n at left
  have low : p*B+Q*q ≤ n := by rw [Nat.add_mul] at left; omega
  have ordinary {s : Span} (h : s ∈ Ordinary.windows a b i j)
      (lo : s.1*B ≤ n) (hi : n<s.2*B) : nonrectangularCost n=0 := by
    simp [nonrectangularCost, Ordinary.window_safe bound bound' h lo hi]
  unfold window at right
  dsimp only at right
  simp only [min_mul_of_nonneg, max_mul_of_nonneg, Nat.zero_le, lt_min_iff, lt_max_iff] at right
  obtain ⟨cap, rect | row | col⟩ := right
  · have lp := Nat.log_eq_of_pow_le_of_lt_pow (b:=3)
      (Pdef ▸ (by omega : p*B≤n))
      (by rw [pow_succ',Pdef]; simpa only [Nat.mul_assoc] using rect.1)
    have lq := Nat.log_eq_of_pow_le_of_lt_pow (b:=5)
      (Qdef ▸ (by omega : Q*q≤n)) (by rw [pow_succ',Qdef]; exact rect.2.trans_le qlo)
    simp only [nonrectangularCost,lp,lq,Pdef,Qdef,ite_eq_left low]
  · split at row
    · rename_i odd
      let r := min stop (min (3*p) (p+down a (5*q)))
      have hi : n<r*B := by simpa only [r,min_mul_of_nonneg, Nat.zero_le, lt_min_iff]
                              using And.intro cap (show n<min (3*p) (p+down a (5*q))*B from row)
      have hl : p+up b q < r := Nat.lt_of_mul_lt_mul_right (left.trans_lt hi)
      apply ordinary (s:=(p+up b q,r)) _ left hi
      simp [Ordinary.windows,p,q,r,odd,hl]
    · simp at row
  · split at col
    · rename_i survives
      let r := min stop (min (down a (5*q)) (down a q+3*p))
      have hi : n<r*B := by simpa only [r,min_mul_of_nonneg, Nat.zero_le, lt_min_iff]
                              using And.intro cap (show n<min (down a (5*q)) (down a q+3*p)*B from col)
      have hl : p+up b q < r := Nat.lt_of_mul_lt_mul_right (left.trans_lt hi)
      apply ordinary (s:=(p+up b q,r)) _ left hi
      simp [Ordinary.windows,p,q,r,survives,hl]
    · simp at col

private def charge (N : ℕ) := ∑ n ∈ range N, nonrectangularCost n

private lemma extend {s t c : ℕ} (h : s ≤ t) (hc : ∀ n, s ≤ n → n < t → nonrectangularCost n ≤ c) :
    charge t ≤ charge s + (t-s)*c := by
  unfold charge
  conv_lhs => rw [show t=s+(t-s) by omega,sum_range_add]
  gcongr
  simpa using sum_le_sum (s:=range (t-s)) (fun i hi => hc (s+i) (by omega)
    (by have := mem_range.mp hi; omega))

private lemma grow {s t : ℕ} (h : s ≤ t) : charge t ≤ charge s + (t-s) := by
  simpa using extend (c:=1) h (fun _ _ _ => by unfold nonrectangularCost jointCost columnCost; split_ifs <;> decide)

-- Traverse guaranteed zero-cost windows in increasing order. The test
-- also works on an unsorted list, possibly certifying less coverage.
private meta def scan (cursor spent : ℕ) : List Span → Bool
  | [] => failureDen * (spent + (stop-cursor)) ≤ failureNum * stop
  | (left,right)::rest =>
    let edge := max left cursor
    if edge < right then
      let used := spent + (edge-cursor)
      decide (failureDen*used ≤ failureNum*max start edge) && scan right used rest
    else scan cursor spent rest

private lemma gap_bound {B cursor spent edge N : ℕ}
    (prior : charge (cursor*B) ≤ spent*B) (started : cursor*B ≤ N) (ends : N ≤ edge*B)
    (large : start*B ≤ N) (ok : failureDen*(spent+(edge-cursor)) ≤ failureNum*(max start edge))
    (ordered : cursor ≤ edge) (bp : 0 < B) : failureDen*charge N ≤ failureNum*N := by
  have e : start ≤ edge := Nat.le_of_mul_le_mul_right (large.trans ends) bp
  rw [max_eq_right e] at ok
  have G := grow started
  have H := Nat.mul_le_mul_right B ok
  rw [Nat.mul_assoc,Nat.mul_assoc,Nat.add_mul,Nat.sub_mul] at H
  unfold failureDen failureNum at H ⊢
  have cb := Nat.mul_le_mul_right B ordered
  omega

private lemma scan_sound {B N : ℕ} (bp : 0<B) (low : start*B ≤ N) (high : N ≤ stop*B)
    (xs : List Span) {cursor spent : ℕ} (begun : cursor*B ≤ N)
    (prior : charge (cursor*B) ≤ spent*B)
    (safe : ∀ s ∈ xs, ∀ n, s.1*B ≤ n → n < s.2*B → nonrectangularCost n = 0)
    (ok : scan cursor spent xs = true) : failureDen * charge N ≤ failureNum * N := by
  induction xs generalizing cursor spent with
  | nil =>
    have endOk : failureDen*(spent+(stop-cursor)) ≤ failureNum*stop := of_decide_eq_true ok
    apply gap_bound prior begun high low _ (Nat.le_of_mul_le_mul_right (begun.trans high) bp) bp
    simpa using endOk
  | cons s rest ih =>
    obtain ⟨left,right⟩ := s
    let edge := max left cursor
    have next := fun s hs => safe s (List.mem_cons_of_mem _ hs)
    simp only [scan] at ok
    split at ok
    · rename_i h
      obtain ⟨cap,tail⟩ := Bool.and_eq_true_iff.mp ok
      have cap' : failureDen*(spent+(edge-cursor)) ≤ failureNum*max start edge := of_decide_eq_true cap
      have order : cursor ≤ edge := le_max_right ..
      by_cases early : N ≤ edge*B
      · exact gap_bound prior begun early low cap' order bp
      have upto := grow (Nat.mul_le_mul_right B order)
      have cost : charge (edge*B) ≤ (spent+(edge-cursor))*B := by
        rw [Nat.add_mul,Nat.sub_mul]; omega
      have zero {u : ℕ} (lo : edge*B ≤ u) (hi : u ≤ right*B) : charge u ≤ charge (edge*B) := by
        simpa using extend (c:=0) lo (fun n le lt => (safe _ (List.mem_cons_self ..) n
          ((Nat.mul_le_mul_right B (le_max_left ..)).trans le) (lt.trans_le hi)).le)
      by_cases mid : N ≤ right*B
      · have H := (zero (by omega) mid).trans cost
        have edgeLow : max start edge * B ≤ N := by rw [max_mul_of_nonneg _ _ (Nat.zero_le _)]; omega
        have bound := Nat.mul_le_mul_right B cap'
        rw [Nat.mul_assoc,Nat.mul_assoc] at bound
        exact (Nat.mul_le_mul_left failureDen H).trans (bound.trans (Nat.mul_le_mul_left failureNum edgeLow))
      exact ih (by omega) ((zero (Nat.mul_le_mul_right B h.le) le_rfl).trans cost) next tail
    · exact ih begun prior next ok

-- Each leaf supplies its windows in traversal order. A split covers its
-- midpoint on both sides. Even the choice of split points is untrusted.
private inductive Cover : ℕ → ℕ → Prop
  | leaf (a b : ℕ) (keys : List ℕ) (ok : scan 0 0 (hinted a b keys) = true) : Cover a b
  | split {a b m : ℕ} (left : Cover a m) (right : Cover m b) : Cover a b

private lemma cover_sound {k l N a b : ℕ} (low : start * 81^k ≤ N) (high : N ≤ stop * 81^k)
    (lo : a*81^k ≤ phaseDen*25^l) (hi : phaseDen*25^l ≤ b*81^k) (cover : Cover a b) :
    failureDen*charge N ≤ failureNum*N := by
  induction cover with
  | leaf a b keys test =>
    apply scan_sound (pow_pos (by decide : 0<81) k) low high (hinted a b keys)
      (cursor:=0) (spent:=0) (by simp) (by simp [charge]) _ test
    intro s hs n h₁ h₂
    obtain ⟨key,_,rfl⟩ := List.mem_map.mp hs
    exact window_safe lo hi h₁ h₂
  | @split a b m _ _ left right =>
    by_cases h : phaseDen*25^l ≤ m*81^k
    · exact left lo h
    · exact right (by omega) hi

-- Search at elaboration time. Keep only windows that extend the covered
-- union. The kernel recomputes the surviving windows from the exponent pairs.
private meta def hints (a b : ℕ) : List ℕ := Id.run do
  let mut spans : Array (ℕ × ℕ × ℕ) := #[]
  for i in [:24] do
    for j in [:17] do
      let (lo,hi) := window a b i j
      if lo < hi then
        spans := spans.push (lo,hi,32*i+j)
  let mut cursor := 0
  let mut result := []
  for (_,hi,key) in spans.qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.1 > y.2.1)) do
    if hi > cursor then
      result := key :: result
      cursor := hi
  return result.reverse

open Lean Meta in
private meta def proveCover (fuel a b : ℕ) : MetaM Expr := do
  let keys := hints a b
  if scan 0 0 (hinted a b keys) then
    let test := mkApp3 (mkConst ``hinted) (toExpr a) (toExpr b) (toExpr keys)
    let checked := mkApp3 (mkConst ``scan) (toExpr (0:ℕ)) (toExpr (0:ℕ)) test
    let statement ← mkEq checked (toExpr true)
    let name ← withOptions (Elab.async.set · false) <|
      mkAuxLemma [] statement (← mkEqRefl (toExpr true))
    return mkApp4 (mkConst ``Cover.leaf) (toExpr a) (toExpr b) (toExpr keys) (mkConst name)
  match fuel with
  | 0 => throwError "phase bracket did not certify"
  | f+1 =>
    let m := (a+b)/2
    let left ← proveCover f a m
    let right ← proveCover f m b
    return mkApp5 (mkConst ``Cover.split) (toExpr a) (toExpr b) (toExpr m) left right

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem certificate : Cover phaseDen (25*phaseDen) := by
  run_tac (← Lean.Elab.Tactic.getMainGoal).assign (← proveCover 30 phaseDen (25*phaseDen))

/-- Every prefix of length at least 81⁵ has nonrectangular joint failure
frequency at most 4631/12500, including an unfinished final shell. -/
theorem nonrectangular_cost_bound {N : ℕ} (large : 3486784401 ≤ N) :
    12500 * (∑ n ∈ range N, nonrectangularCost n) ≤ 4631 * N := by
  let k := Nat.log 81 (N/start)
  let B := 81^k
  have divpos : 0 < N/start := Nat.div_pos large (by decide)
  have bot : B ≤ N/start := Nat.pow_log_le_self _ divpos.ne'
  have top : N/start < 81*B := by
    simpa [B,k,pow_succ'] using Nat.lt_pow_succ_log_self (by decide : 1<81) (N/start)
  have low : start*B ≤ N := by simpa [mul_comm] using (Nat.le_div_iff_mul_le (by decide)).mp bot
  have high : N ≤ stop*B := by
    have h := (Nat.div_lt_iff_lt_mul (by decide : 0<start)).mp top
    exact h.le.trans_eq (by dsimp [stop]; ring)
  let l := Nat.log 25 B + 1
  have bp : 0<B := pow_pos (by decide) _
  have qlo : B ≤ 25^l := (Nat.lt_pow_succ_log_self (by decide : 1<25) B).le
  have qhi : 25^l ≤ 25*B := by
    rw [show l=Nat.log 25 B+1 from rfl,pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ bp.ne')
  apply cover_sound (k:=k) (l:=l) low high _ _ certificate
  · exact Nat.mul_le_mul_left phaseDen qlo
  · simpa [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left phaseDen qhi

/-- Upper binary extreme interval discrepancy of the actual Stoneham product. -/
theorem mixed_product_discrepancy :
    asymptoticDiscrepancy (StonehamStatements.stoneham 2 3 * StonehamStatements.stoneham 2 5)
      ≤ 4631/12500 := by
  change asymptoticDiscrepancy (alpha 3 * alpha 5) ≤ _
  apply le_of_forall_pos_le_add
  intro ε ep
  apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds 2 _ N).1))
  filter_upwards [nonrectangular_prefix_discrepancy ep,eventually_ge_atTop 3486784401] with N uniform hN
  have count : 12500 * (∑ n ∈ range N, (nonrectangularCost n : ℝ)) ≤ 4631 * N := by
    exact_mod_cast nonrectangular_cost_bound hN
  have pos : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  refine uniform.trans (add_le_add_left ?_ ε)
  rw [div_le_iff₀ pos]
  linarith

end NonrectangularOrdinary
end NormalityChecker.ProductThreeFive
