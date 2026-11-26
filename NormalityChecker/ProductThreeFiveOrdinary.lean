module

meta import Lean
public import NormalityChecker.ProductThreeFiveCoverage

/-! An ordinary prefix bound using both first-precision tests. The finite
certificate covers the phase between a power of 81 and a power of 25. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.ProductThreeFive
namespace Ordinary

private abbrev Span := ℕ × ℕ
private meta abbrev phaseDen := 1073741824
private meta abbrev start := 3486784401
private meta abbrev stop := 81 * start
private meta abbrev failureNum := 143881
private meta abbrev failureDen := 250000

-- In units B = 81^k, bracket Q = 25^l by a B / phaseDen ≤ Q ≤ b B / phaseDen.
private meta def down (a q : ℕ) := a*q/phaseDen
private meta def up (b q : ℕ) := b*q/phaseDen+1

private meta def windows (a b i j : ℕ) : List Span :=
  let p := 3^i
  let q := 5^j
  let lo := p + up b q
  let row := min stop (min (3*p) (p + down a (5*q)))
  let col := min stop (min (down a (5*q)) (down a q + 3*p))
  (if j%2 ≠ 0 ∧ lo < row then [(lo,row)] else []) ++
    (if i%4 ≠ 0 ∧ lo < col then [(lo,col)] else [])

-- A hint names only the two exponents. Its order and completeness are
-- immaterial to soundness, since every decoded window is checked.
private meta def hinted (a b : ℕ) (keys : List ℕ) : List Span :=
  keys.flatMap fun key => windows a b (key/32) (key%32)

private lemma bracket {B Q a b : ℕ} (lo : a*B ≤ phaseDen*Q) (hi : phaseDen*Q ≤ b*B) (q : ℕ) :
    down a q * B ≤ Q*q ∧ Q*q ≤ up b q * B := by
  have h₁ := Nat.div_mul_le_self (a*q) phaseDen
  have h₂ : b*q ≤ (b*q/phaseDen+1)*phaseDen := by unfold phaseDen; omega
  unfold down up
  constructor
  · apply Nat.le_of_mul_le_mul_right (c:=phaseDen) _ (by decide)
    nlinarith only [Nat.mul_le_mul_right B h₁,Nat.mul_le_mul_right q lo]
  · apply Nat.le_of_mul_le_mul_right (c:=phaseDen) _ (by decide)
    nlinarith only [Nat.mul_le_mul_right B h₂,Nat.mul_le_mul_right q hi]

private lemma window_safe {k l a b i j : ℕ} {s : Span}
    (bound : a*81^k ≤ phaseDen*25^l) (bound' : phaseDen*25^l ≤ b*81^k)
    (hs : s ∈ windows a b i j) {n : ℕ} (hn : s.1*81^k ≤ n) (hn' : n < s.2*81^k) :
    jointCost n = 0 := by
  let B := 81^k
  let Q := 25^l
  let p := 3^i
  let q := 5^j
  have Pdef : 3^(4*k+i) = p*B := by dsimp [p,B]; rw [pow_add,pow_mul]; ring
  have Qdef : 5^(2*l+j) = Q*q := by dsimp [q,Q]; rw [pow_add,pow_mul]; rfl
  obtain ⟨qlo,qhi⟩ := bracket bound bound' q
  obtain ⟨qlo',_⟩ := bracket bound bound' (5*q)
  change down a q * B ≤ Q*q at qlo
  change Q*q ≤ up b q * B at qhi
  have low : ∀ {z}, (p+up b q)*B ≤ z → p*B+Q*q ≤ z := by
    intro z hz; rw [Nat.add_mul] at hz; omega
  unfold windows at hs
  simp only [List.mem_append] at hs
  rcases hs with row | col
  · split at row <;> simp_all only [List.mem_cons,List.not_mem_nil,or_false]
    rename_i guard
    subst s
    obtain ⟨odd,_⟩ := guard
    have lower := low hn
    have upper := hn'
    change n < min stop (min (3*p) (p+down a (5*q))) * B at upper
    have hP := upper.trans_le (Nat.mul_le_mul_right B
      ((min_le_right ..).trans (min_le_left ..)))
    have hQ := upper.trans_le (Nat.mul_le_mul_right B
      ((min_le_right ..).trans (min_le_right ..)))
    rw [Nat.add_mul] at hQ
    have lp := Nat.log_eq_of_pow_le_of_lt_pow (b:=3) (Pdef ▸ (by omega : p*B≤n))
      (by rw [pow_succ',Pdef]; simpa only [Nat.mul_assoc] using hP)
    have lq := Nat.log_eq_of_pow_le_of_lt_pow (b:=5)
      (by rw [Qdef,Pdef]; omega : 5^(2*l+j) ≤ n-3^(4*k+i))
      (by rw [pow_succ',Qdef,Pdef]; change down a (5*q)*B ≤ Q*(5*q) at qlo'
          rw [show Q*(5*q)=5*(Q*q) by ring] at qlo'; omega)
    simp only [jointCost,lp,lq,ite_eq_right (by omega : (2*l+j)%2 ≠ 0)]
  · split at col <;> simp_all only [List.mem_cons,List.not_mem_nil,or_false]
    rename_i guard
    subst s
    obtain ⟨survives,_⟩ := guard
    have lower := low hn
    have upper := hn'
    change n < min stop (min (down a (5*q)) (down a q + 3*p)) * B at upper
    have hQ := upper.trans_le (Nat.mul_le_mul_right B
      ((min_le_right ..).trans (min_le_left ..)))
    have hP := upper.trans_le (Nat.mul_le_mul_right B
      ((min_le_right ..).trans (min_le_right ..)))
    rw [Nat.add_mul,Nat.mul_assoc] at hP
    change down a (5*q)*B ≤ Q*(5*q) at qlo'
    rw [show Q*(5*q)=5*(Q*q) by ring] at qlo'
    have lq := Nat.log_eq_of_pow_le_of_lt_pow (b:=5) (Qdef ▸ (by omega : Q*q≤n))
      (by rw [pow_succ',Qdef]; omega)
    have lp := Nat.log_eq_of_pow_le_of_lt_pow (b:=3)
      (by rw [Pdef,Qdef]; omega : 3^(4*k+i) ≤ n-5^(2*l+j))
      (by rw [pow_succ',Pdef,Qdef]; omega)
    simp [jointCost,columnCost,lq,lp,survives]

private def charge (N : ℕ) := ∑ n ∈ range N, jointCost n

private lemma extend {s t c : ℕ} (h : s ≤ t) (hc : ∀ n, s ≤ n → n < t → jointCost n ≤ c) :
    charge t ≤ charge s + (t-s)*c := by
  unfold charge
  conv_lhs => rw [show t=s+(t-s) by omega,sum_range_add]
  gcongr
  simpa using sum_le_sum (s:=range (t-s)) (fun i hi => hc (s+i) (by omega)
    (by have := mem_range.mp hi; omega))

private lemma grow {s t : ℕ} (h : s ≤ t) : charge t ≤ charge s + (t-s) := by
  simpa using extend (c:=1) h (fun _ _ _ => by unfold jointCost columnCost; split_ifs <;> decide)

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
    (safe : ∀ s ∈ xs, ∀ n, s.1*B ≤ n → n < s.2*B → jointCost n = 0)
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
    obtain ⟨key,_,mem⟩ := List.mem_flatMap.mp hs
    exact window_safe lo hi mem h₁ h₂
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
      for (lo,hi) in windows a b i j do
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

/-- Every ordinary prefix of length at least 81⁵ has simultaneous first-precision
failure frequency at most 143881/250000, including an unfinished final shell. -/
theorem joint_cost_bound {N : ℕ} (large : 3486784401 ≤ N) :
    250000 * (∑ n ∈ range N, jointCost n) ≤ 143881 * N := by
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
      ≤ 143881/250000 := by
  change asymptoticDiscrepancy (alpha 3 * alpha 5) ≤ _
  apply le_of_forall_pos_le_add
  intro ε ep
  apply limsup_le_of_le (isCoboundedUnder_le_of_le _ (fun N => (radix_discrepancy_bounds 2 _ N).1))
  filter_upwards [joint_prefix_discrepancy ep,eventually_ge_atTop 3486784401] with N uniform hN
  have count : 250000 * (∑ n ∈ range N, (jointCost n : ℝ)) ≤ 143881 * N := by
    exact_mod_cast joint_cost_bound hN
  have pos : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  refine uniform.trans (add_le_add_left ?_ ε)
  apply (min_le_left ..).trans
  rw [div_le_iff₀ pos]
  linarith

end Ordinary
end NormalityChecker.ProductThreeFive
