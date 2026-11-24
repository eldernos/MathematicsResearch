module

public import NormalityChecker.DiscrepancyChecker

/-! An ordinary-prefix bound using only the two first-precision tests. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

def failsFiveThirteen (n : ℕ) : Prop :=
  CellProfile.coordinate 5 1 n ∈ ({2,3}:Finset ℕ) ∧
  CellProfile.coordinate 13 1 n ∈ ({10,11,12}:Finset ℕ)

instance (n : ℕ) : Decidable (failsFiveThirteen n) := inferInstanceAs (Decidable (_ ∧ _))

def countJointFiveThirteen (N : ℕ) := ((range N).filter failsFiveThirteen).card

private theorem bands {n : ℕ} (h : failsFiveThirteen n) :
    2*5^(Nat.log 5 n)≤n ∧ n<4*5^(Nat.log 5 n) ∧
    10*13^(Nat.log 13 n)≤n ∧ n<13*13^(Nat.log 13 n) := by
  simp only [failsFiveThirteen,CellProfile.coordinate,Nat.div_one,mem_insert,mem_singleton] at h
  have p : 0<5^(Nat.log 5 n) := by positivity
  have q : 0<13^(Nat.log 13 n) := by positivity
  exact ⟨(Nat.le_div_iff_mul_le p).mp (by omega),(Nat.div_lt_iff_lt_mul p).mp (by omega),
    (Nat.le_div_iff_mul_le q).mp (by omega),(Nat.div_lt_iff_lt_mul q).mp (by omega)⟩

private theorem in_band {x p u v a j : ℕ} (hp : 0<p) (hx : u*p^a≤x ∧ x<v*p^a)
    (below : j=0 ∨ v*p^(j-1)≤x) (upper : x<u*p^(j+1)) :
    u*p^j≤x ∧ x<v*p^j := by
  have same : a=j := by
    rcases lt_trichotomy a j with lt|eq|gt
    · rcases below with z|le
      · omega
      · have h := Nat.mul_le_mul_left v (Nat.pow_le_pow_right hp (by omega : a≤j-1))
        omega
    · exact eq
    · have h := Nat.mul_le_mul_left u (Nat.pow_le_pow_right hp (by omega : j+1≤a))
      omega
  simpa only [same] using hx

private theorem last_three {n : ℕ} (fail : failsFiveThirteen n) (late : 2197≤n) :
    1000*countJointFiveThirteen (n+1) ≤ 234*(n+1) := by
  let j := Nat.log 5 n-3
  let k := Nat.log 13 n-2
  let A := 5^j
  let B := 13^k
  have jbig := Nat.le_log_of_pow_le (b:=5) (x:=3) (y:=n) (by decide) (by omega)
  have kbig := Nat.le_log_of_pow_le (b:=13) (x:=2) (y:=n) (by decide) (by omega)
  have eq5 : Nat.log 5 n=j+3 := by dsimp [j]; omega
  have eq13 : Nat.log 13 n=k+2 := by dsimp [k]; omega
  obtain ⟨l5,r5,l13,r13⟩ := bands fail
  rw [eq5,pow_add] at l5 r5
  rw [eq13,pow_add] at l13 r13
  change 2*(A*125)≤n at l5
  change n<4*(A*125) at r5
  change 10*(B*169)≤n at l13
  change n<13*(B*169) at r13
  let old := range B
  let first := Ico (max (2*A) (10*B)) (min (4*A) (13*B))
  let second := Ico (max (10*A) (130*B)) (min (20*A) (169*B))
  let last := Ico (max (250*A) (1690*B)) (n+1)
  have cover : (range (n+1)).filter failsFiveThirteen ⊆ ((old ∪ first) ∪ second) ∪ last := by
    intro x hx
    obtain ⟨within,bad⟩ := mem_filter.mp hx
    have xn := mem_range.mp within
    obtain ⟨lo,hi,low,high⟩ := bands bad
    let e := Nat.log 13 x
    change 10*13^e≤x at low
    change x<13*13^e at high
    by_cases past : e<k
    · have h := Nat.pow_le_pow_right (by decide : 0<13) (by omega : e+1≤k)
      rw [pow_succ'] at h
      exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_range.mpr (high.trans_le h))))
    have ee : e≤k+2 := by
      by_contra! future
      have h := Nat.pow_le_pow_right (by decide : 0<13) future
      have h' : B*2197≤13^e := by
        change 13^(k+3)≤13^e at h; rwa [pow_add] at h
      omega
    simp only [mem_union,old,first,second,last,mem_range,mem_Ico,lt_min_iff]
    rcases (by omega : e=k ∨ e=k+1 ∨ e=k+2) with h|h|h
    · rw [h] at low high
      change 10*B≤x at low; change x<13*B at high
      have below : j=0 ∨ 4*5^(j-1)≤x := by
        by_cases z : j=0
        · exact Or.inl z
        · have hA : A=5^(j-1)*5 := by dsimp [A]; rw [← pow_succ]; congr 1; omega
          exact Or.inr (by omega)
      have band := in_band (j:=j) (by decide : 0<5) ⟨lo,hi⟩ below
        (by rw [pow_succ]; change x<2*(A*5); omega)
      change 2*A≤x ∧ x<4*A at band; omega
    · rw [h,pow_succ] at low high
      change 10*(B*13)≤x at low; change x<13*(B*13) at high
      have band := in_band (j:=j+1) (by decide : 0<5) ⟨lo,hi⟩
        (Or.inr (by simp only [Nat.add_sub_cancel]; change 4*A≤x; omega))
        (by rw [show j+1+1=j+2 by omega,pow_add]; change x<2*(A*25); omega)
      rw [pow_succ] at band; change 2*(A*5)≤x ∧ x<4*(A*5) at band; omega
    · rw [h,pow_add] at low high
      change 10*(B*169)≤x at low
      have band := in_band (j:=j+3) (by decide : 0<5) ⟨lo,hi⟩
        (Or.inr (by rw [show j+3-1=j+2 by omega,pow_add]; change 4*(A*25)≤x; omega))
        (by rw [show j+3+1=j+4 by omega,pow_add]; change x<2*(A*625); omega)
      rw [pow_add] at band; change 2*(A*125)≤x ∧ x<4*(A*125) at band; omega
  have counts := (card_le_card cover).trans (card_union_le ..)
  have two := card_union_le (old ∪ first) second
  have one := card_union_le old first
  simp only [old,first,second,last,card_range,Nat.card_Ico] at *
  change 1000*((range (n+1)).filter failsFiveThirteen).card≤_
  omega

/-- At the first precision alone the fraction simultaneously failing is at most
0.234 up to a fixed initial cost, at every integer cutoff. -/
theorem joint_five_thirteen_count (N : ℕ) :
    1000*countJointFiveThirteen N≤234*N+2197000 := by
  induction N with
  | zero => simp [countJointFiveThirteen]
  | succ n ih =>
    by_cases good : failsFiveThirteen n
    · by_cases late : 2197≤n
      · exact (last_three good late).trans (by omega)
      · have h : countJointFiveThirteen (n+1)≤n+1 := (card_filter_le ..).trans_eq (card_range _)
        omega
    · have unchanged : countJointFiveThirteen (n+1)=countJointFiveThirteen n := by simp [countJointFiveThirteen,range_add_one,filter_insert,good]
      rw [unchanged]; omega

/-- The bound uses the two level-one tests only, including the partial final scale. -/
theorem first_precision_joint_discrepancy :
    limsup (radixDiscrepancy 2 (powerValue 2 1 {2,5,13})) atTop ≤ 234/1000 := by
  let A : Finset ℕ := {2,5,13}
  let J : Finset ℕ := {5,13}
  apply discrepancy_of_joint_failures A J (fun _ => 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  intro ε pos
  have erased5 : A.erase 5={2,13} := by decide
  have erased13 : A.erase 13={2,5} := by decide
  have eq (n : ℕ) : (∀ p∈J, CellProfile.coordinate p (p^0) n∈failedCells 2 1 p 0 (A.erase p)) ↔
      failsFiveThirteen n := by
    simp [J,erased5,erased13,
      five_thirteen_first_failures.1,five_thirteen_first_failures.2,failsFiveThirteen]
  obtain ⟨N₀,high⟩ := exists_nat_gt (2197/ε)
  filter_upwards [eventually_ge_atTop N₀] with N late
  simp_rw [eq]; rw [← sum_filter]; simp only [sum_const,nsmul_eq_mul,mul_one]
  change (countJointFiveThirteen N:ℝ) ≤ _
  have budget : (2197:ℝ)≤ε*N := by
    have h := high.le.trans (Nat.cast_le.mpr late)
    linarith only [(div_le_iff₀ pos).mp h]
  have h : (1000:ℝ)*countJointFiveThirteen N≤234*N+2197000 := by exact_mod_cast joint_five_thirteen_count N
  linarith only [budget,h]

end NormalityChecker.LocalizedSupport
