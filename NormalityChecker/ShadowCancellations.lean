module

public import NormalityChecker.AdjacentShadow
public import Mathlib.Algebra.Polynomial.Roots

/-! A polynomial obstruction to simultaneous cancellation at a fixed gap. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.ShadowCancellations

def residue (p n : ℕ) := binomialPrefix p n (2*n-p)
def term (p n : ℕ) : ZMod p := n.choose (2*n-p+1)

private lemma unit {p v : ℕ} (hv : 0<v) (lt : v<p) : (v:ZMod p)≠0 :=
  mt (ZMod.natCast_eq_zero_iff v p).mp (Nat.not_dvd_of_pos_of_lt hv lt)

private lemma term_ne {n p : ℕ} (hp : p.Prime) (lo : n<p) (hi : p≤2*n) : term p n≠0 := by
  apply mt (ZMod.natCast_eq_zero_iff ..).mp; intro dvd
  have fac := Nat.choose_mul_factorial_mul_factorial (show 2*n-p+1≤n by omega)
  have hfac : p∣n.factorial := by rw [← fac]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left dvd _) _
  exact lo.not_ge ((Nat.Prime.dvd_factorial hp).mp hfac)

/-- Pascal's rule and the ratio of two successive binomial coefficients on the diagonal. -/
theorem residue_step {n p : ℕ} (pr : p.Prime) (lo : n+1<p) (hi : p≤2*n) :
    2*residue p (n+1)=4*residue p n+3*term p n ∧
    (2*(2*(n:ZMod p)+3))*term p (n+1) = -((n:ZMod p)+1)*term p n := by
  let : Fact p.Prime := ⟨pr⟩
  let d := 2*n-p
  have dl : d+1≤n := by dsimp [d]; omega
  have off : d+p=2*n := Nat.sub_add_cancel hi
  have rel := congrArg (fun a : ℕ => (a:ZMod p)) off
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self,add_zero] at rel
  have succ := congrArg (fun a : ℕ => (a:ZMod p)) (Nat.choose_succ_right_eq n (d+1))
  push_cast [Nat.cast_sub dl] at succ
  have next := congrArg (fun a : ℕ => (a:ZMod p)) (Nat.add_one_mul_choose_eq n (d+2))
  push_cast at next
  have nz : ((n:ZMod p)+1)≠0 := by simpa using unit (Nat.zero_lt_succ n) lo
  have ratio : 2*(n.choose (d+2):ZMod p) = -(n.choose (d+1):ZMod p) := by
    apply mul_right_cancel₀ nz
    linear_combination succ - ((n.choose (d+2):ZMod p)+(n.choose (d+1):ZMod p))*rel
  unfold residue term; rw [show 2*(n+1)-p=d+2 by dsimp [d]; omega]
  change _=4*binomialPrefix p n d+3*(n.choose (d+1):ZMod p) ∧ _= -_*(n.choose (d+1):ZMod p)
  constructor
  · rw [pascal_prefix p n (d+1),show binomialPrefix p n (d+1)=binomialPrefix p n d+(n.choose (d+1):ZMod p) from sum_range_succ ..]
    linear_combination ratio
  · linear_combination -2*next + ((n:ZMod p)+1)*ratio - 2*((n+1).choose (d+2+1):ZMod p)*rel

variable (p : ℕ)
private noncomputable def factor (j : ℕ) : (ZMod p)[X] := C 2*(C 2*(X+C (j:ZMod p))+C 3)
private noncomputable def numerator : ℕ → (ZMod p)[X]
  | 0 => 1
  | j+1 => -(X+C (j:ZMod p)+1)*numerator j
private noncomputable def obstruction : ℕ → (ZMod p)[X]
  | 0 => 0
  | j+1 => factor p j*(C 2*obstruction j+C 3*numerator p j)
private def common (n : ℕ) : ℕ → ZMod p
  | 0 => 1
  | j+1 => (2*(2*((n:ZMod p)+j)+3))*common n j

private lemma obstruction_identity {n h : ℕ} (pr : p.Prime) (lo : n+h<p) (hi : p≤2*n) (zero : residue p n=0) :
    common p n h*term p (n+h)=(numerator p h).eval (n:ZMod p)*term p n ∧
    2*common p n h*residue p (n+h)=(obstruction p h).eval (n:ZMod p)*term p n := by
  induction h with
  | zero => simp [common,numerator,obstruction,zero]
  | succ j ih =>
    obtain ⟨step₁,step₂⟩ := residue_step (n:=n+j) pr (by omega) (by omega)
    obtain ⟨old₁,old₂⟩ := ih (by omega)
    simp only [Nat.cast_add] at step₂
    simp only [common,numerator,obstruction,factor,eval_neg,eval_add,eval_mul,eval_X,eval_C,eval_one]
    constructor
    · linear_combination common p n j * step₂ - ((n:ZMod p)+j+1)*old₁
    · linear_combination (2*(2*((n:ZMod p)+j)+3))*(common p n j*step₁+2*old₂+3*old₁)

private lemma degrees (h : ℕ) : (numerator p h).natDegree≤h ∧ (obstruction p h).natDegree≤h := by
  induction h with
  | zero => simp [numerator,obstruction]
  | succ j ih =>
    have lin : (X+C (j:ZMod p)).natDegree≤1 := natDegree_add_le_of_degree_le natDegree_X_le (by simp)
    have f : (factor p j).natDegree≤1 := by unfold factor; apply (natDegree_C_mul_le ..).trans; apply natDegree_add_le_of_degree_le ((natDegree_C_mul_le ..).trans lin) (by simp)
    constructor
    · rw [numerator]; exact natDegree_mul_le_of_le (show (-(X+C (j:ZMod p)+1)).natDegree≤1 by rw [natDegree_neg]; exact natDegree_add_le_of_degree_le lin (by simp)) ih.1 |>.trans (by omega)
    · rw [obstruction]; exact natDegree_mul_le_of_le f (natDegree_add_le_of_degree_le ((natDegree_C_mul_le ..).trans ih.2) ((natDegree_C_mul_le ..).trans ih.1)) |>.trans (by omega)

private lemma obstruction_ne {h : ℕ} (pr : p.Prime) (big : 3<p) (pos : 0<h) (short : 2*h<p) : obstruction p h≠0 := by
  let : Fact p.Prime := ⟨pr⟩
  have two : (2:ZMod p)≠0 := by exact_mod_cast unit (by decide : 0<2) (by omega : 2<p)
  have three : (3:ZMod p)≠0 := by exact_mod_cast unit (by decide : 0<3) big
  have vanish (j : ℕ) : (numerator p (j+1)).eval (-1)=0 := by induction j with | zero => simp [numerator] | succ j ih => rw [numerator,eval_mul,ih,mul_zero]
  have val : (obstruction p h).eval (-1)≠0 := by
    induction h with
    | zero => omega
    | succ j ih =>
      have f : (factor p j).eval (-1)≠0 := by
        have v := unit (p:=p) (show 0<2*j+1 by omega) (by omega : 2*j+1<p)
        push_cast at v; simp only [factor,eval_mul,eval_C,eval_add,eval_X]; apply mul_ne_zero two; convert v using 1; ring
      rw [obstruction,eval_mul]; apply mul_ne_zero f; rcases j with _|j
      · simpa [obstruction,numerator] using three
      · simp only [eval_add,eval_mul,eval_C,vanish,mul_zero,add_zero]; exact mul_ne_zero two (ih (by omega) (by omega))
  intro z; apply val; simp [z]

/-- At most `h` positions can lose the same prime both at `n` and `n+h`. -/
theorem paired_cancellations {p h : ℕ} (pr : p.Prime) (big : 3<p) (pos : 0<h) (short : 2*h<p) :
    ((range p).filter (fun n => n+h<p ∧ p≤2*n ∧ ¬p∣(logShadow n n).den ∧ ¬p∣(logShadow (n+h) (n+h)).den)).card≤h := by
  classical
  let : Fact p.Prime := ⟨pr⟩
  let U := (range p).filter (fun n => n+h<p ∧ p≤2*n ∧ ¬p∣(logShadow n n).den ∧ ¬p∣(logShadow (n+h) (n+h)).den)
  let W := obstruction p h
  have root {n : ℕ} (hn : n∈U) : W.eval (n:ZMod p)=0 := by
    obtain ⟨_,lo,hi,a,b⟩ := mem_filter.mp hn
    have z : residue p n=0 := not_not.mp (fun ne => a ((logShadow_binomial_prime pr (by omega) hi).mpr ne))
    have z' : residue p (n+h)=0 := not_not.mp (fun ne => b ((logShadow_binomial_prime pr lo (by omega)).mpr ne))
    have id := (obstruction_identity p pr lo hi z).2; rw [z',mul_zero] at id
    exact (mul_eq_zero.mp id.symm).resolve_right (term_ne pr (by omega) hi)
  have inj : Set.InjOn (fun n : ℕ => (n:ZMod p)) (U:Set ℕ) := by
    intro a ha b hb eqn; have r := congrArg ZMod.val eqn
    simpa [ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp ha).1),ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp hb).1)] using r
  change U.card≤h
  rw [← card_image_of_injOn inj]
  apply (Polynomial.card_le_degree_of_subset_roots (p:=W) ?_).trans (degrees p h).2
  intro x hx; obtain ⟨n,hn,rfl⟩ := mem_image.mp (Finset.mem_val.mp hx)
  exact (Polynomial.mem_roots (obstruction_ne p pr big pos short)).mpr (root hn)

/-- Indices `ceil(p/2) ≤ n < p` where the corrected model loses this prime. -/
def cancellations (p : ℕ) := (range p).filter (fun n => p≤2*n ∧ ¬p∣(logShadow n n).den)

/-- Count one first failure per block of `H+1` indices. Every further failure
has a predecessor at some positive distance at most `H`. -/
theorem window_cancellations {p H A T : ℕ} (pr : p.Prime) (big : 3<p) (short : 2*H<p)
    (E : Finset ℕ) (cancel : E⊆cancellations p) (window : E⊆Ico A (A+T)) :
    E.card ≤ T/(H+1)+1+H^2 := by
  classical
  let B := E.filter (fun n => ∀ m∈E,(m-A)/(H+1)=(n-A)/(H+1) → n≤m)
  let P := fun h => (range p).filter (fun n => n+h<p ∧ p≤2*n ∧ ¬p∣(logShadow n n).den ∧ ¬p∣(logShadow (n+h) (n+h)).den)
  let U := fun j => (P (j+1)).image (·+(j+1))
  have first : B.card ≤ T/(H+1)+1 := by
    rw [← card_range (T/(H+1)+1)]; apply card_le_card_of_injOn (fun n => (n-A)/(H+1))
    · intro n hn; apply mem_range.mpr; have bound := mem_Ico.mp (window (mem_filter.mp hn).1)
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n-A≤T))
    · intro a ha b hb eqn; obtain ⟨am,al⟩ := mem_filter.mp ha; obtain ⟨bm,bl⟩ := mem_filter.mp hb
      exact le_antisymm (al b bm eqn.symm) (bl a am eqn)
  have cover : E⊆B∪(range H).biUnion U := by
    intro n hn; by_cases h : n∈B; exact mem_union_left _ h
    have no : ¬∀ m∈E,(m-A)/(H+1)=(n-A)/(H+1) → n≤m := fun prop => h (mem_filter.mpr ⟨hn,prop⟩)
    push Not at no; obtain ⟨m,hm,eqn,lt⟩ := no
    have bound := Nat.lt_mul_div_succ (n-A) (Nat.zero_lt_succ H)
    rw [← eqn,Nat.mul_succ] at bound
    have base := Nat.mul_div_le (m-A) (H+1)
    change n-A < (H+1)*((m-A)/(H+1))+(H+1) at bound
    have := (mem_Ico.mp (window hm)).1
    have diff : n-m-1<H := by omega
    have id : m+(n-m-1+1)=n := by omega
    obtain ⟨nl,_,nz⟩ := mem_filter.mp (cancel hn); obtain ⟨ml,mh,mz⟩ := mem_filter.mp (cancel hm)
    exact mem_union_right _ (mem_biUnion.mpr ⟨n-m-1,mem_range.mpr diff,mem_image.mpr ⟨m,mem_filter.mpr ⟨ml,by rw [id]; exact ⟨mem_range.mp nl,mh,mz,nz⟩⟩,id⟩⟩)
  have each (j : ℕ) (hj : j∈range H) : (U j).card≤H := by
    have h := mem_range.mp hj
    exact card_image_le.trans ((paired_cancellations (h:=j+1) pr big (by omega) (by omega)).trans h)
  have total := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add first ((card_biUnion_le ..).trans (sum_le_sum each))))
  simpa [sq] using total

theorem cancellation_count {p H : ℕ} (pr : p.Prime) (big : 3<p) (short : 2*H<p) :
    (cancellations p).card ≤ p/(H+1)+1+H^2 :=
  window_cancellations (A:=0) pr big short _ Subset.rfl (by simp [cancellations])

end NormalityChecker.ShadowCancellations
