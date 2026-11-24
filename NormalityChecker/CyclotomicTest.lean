module

public import NormalityChecker.CyclotomicClassification
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section
open Finset Polynomial
namespace NormalityChecker

/-- Multiplicative order by bounded search and fast modular exponentiation. -/
def residueOrder (b p : ℕ) : ℕ :=
  let s := (Ico 1 p).filter fun e => b.powMod e p=1
  if h : s.Nonempty then s.min' h else 0

theorem residueOrder_eq {b p : ℕ} [Fact p.Prime] (hbc : b.Coprime p) :
    residueOrder b p = orderOf (b:ZMod p) := by
  let d := orderOf (b:ZMod p)
  let hp := Fact.out (p:=p.Prime)
  have hdvd := ZMod.orderOf_dvd_card_sub_one ((ZMod.isUnit_iff_coprime b p).mpr hbc).ne_zero
  have hp' : 0<p-1 := Nat.sub_pos_of_lt hp.one_lt
  have hd := Nat.pos_of_dvd_of_pos hdvd hp'
  have he (e : ℕ) : b.powMod e p=1 ↔ (b:ZMod p)^e=1 := by
    rw [Nat.powMod_def,← Nat.cast_pow, ← Nat.cast_one (R:=ZMod p),ZMod.natCast_eq_natCast_iff]
    change _ ↔ _=1%p; rw [Nat.mod_eq_of_lt hp.one_lt]
  let s := (Ico 1 p).filter fun e => b.powMod e p=1
  have hm : d∈s := mem_filter.mpr ⟨mem_Ico.mpr ⟨hd,(Nat.le_of_dvd hp' hdvd).trans_lt (Nat.sub_lt hp.pos (by decide))⟩,
    (he d).mpr (pow_orderOf_eq_one _)⟩
  have hs : s.Nonempty := ⟨d,hm⟩
  change (if H : s.Nonempty then s.min' H else 0)=d
  rw [dite_eq_left hs]
  have hn := mem_filter.mp (s.min'_mem hs)
  exact le_antisymm (s.min'_le d hm) (Nat.le_of_dvd (mem_Ico.mp hn.1).1 (orderOf_dvd_of_pow_eq_one ((he _).mp hn.2)))

namespace CyclicPolynomial

/-- Coefficient vector of a sparse polynomial reduced modulo X^d-1. -/
def collect {ι : Type*} (d : ℕ) (M : Finset ι) (coeff : ι → ℚ) (expo : ι → ℕ) : Vector ℚ d :=
  Vector.ofFn fun r => ∑ m ∈ M, if expo m % d = r.val then coeff m else 0

/-- Multiplication by X^e-1 with cyclic indices. -/
def difference {d : ℕ} (e : ℕ) (v : Vector ℚ d) : Vector ℚ d :=
  Vector.ofFn fun r => v[(r.val+d-e)%d]'(Nat.mod_lt _ (Nat.zero_lt_of_lt r.isLt)) - v[r.val]

private noncomputable def repr {d : ℕ} (v : Vector ℚ d) : ℚ[X] :=
  ∑ r : Fin d, C v[r.val]*X^r.val

private lemma repr_coeff {d : ℕ} (v : Vector ℚ d) (n : ℕ) :
    (repr v).coeff n = if h : n<d then v[n] else 0 := by
  classical
  simp only [repr,finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  split_ifs with h
  · let r : Fin d := ⟨n,h⟩
    rw [sum_eq_single r]
    · simp [r]
    · intro a _ ha; have : a.val≠n := fun e => ha (Fin.ext e)
      simp [Ne.symm this]
    · simp
  · apply sum_eq_zero; intro a _; have : a.val≠n := by have := a.isLt; omega
    simp [Ne.symm this]

private lemma repr_small {d : ℕ} (hd : 0<d) (v : Vector ℚ d) : (repr v).natDegree<d := by
  have H : (repr v).natDegree≤d-1 := natDegree_le_iff_coeff_eq_zero.mpr (fun n hn => by
    rw [repr_coeff,dite_eq_right (by omega)])
  omega

private lemma pow_residue {R : Type*} [Monoid R] {x : R} {d : ℕ} (hx : x^d=1) (n : ℕ) :
    x^(n%d) = x^n := by
  conv_rhs => rw [← Nat.mod_add_div n d,pow_add,pow_mul,hx,one_pow,mul_one]

private lemma eval_collect {ι R : Type*} [CommRing R] (F : ℚ[X] →+* R) {d : ℕ}
    (hd : 0<d) (hx : (F X)^d=1) (M : Finset ι) (c : ι → ℚ) (e : ι → ℕ) :
    F (repr (collect d M c e)) = F (∑ m∈M, C (c m)*X^(e m)) := by
  classical
  simp only [repr,collect,Vector.getElem_ofFn,map_sum,map_mul,map_pow,sum_mul]
  rw [sum_comm]; apply sum_congr rfl; intro m _
  let r : Fin d := ⟨e m%d,Nat.mod_lt _ hd⟩
  rw [sum_eq_single r]
  · simp [r,pow_residue hx]
  · intro a _ ha
    have H : e m%d≠a.val := fun h => ha (Fin.ext h.symm)
    simp [H]
  · simp

private lemma eval_difference {R : Type*} [CommRing R] (F : ℚ[X] →+* R) {d e : ℕ}
    (he : e<d) (hx : (F X)^d=1) (v : Vector ℚ d) :
    F (repr (difference e v)) = F (repr v) * ((F X)^e-1) := by
  classical
  let I (r : Fin d) := v[r.val]
  have H := eval_collect F (Nat.zero_lt_of_lt he) hx (univ : Finset (Fin d)) I (fun r => r.val+e)
  have entries (r : Fin d) : (collect d univ I (fun a : Fin d => a.val+e))[r.val] =
      v[(r.val+d-e)%d]'(Nat.mod_lt _ (Nat.zero_lt_of_lt he)) := by
    let a : Fin d := ⟨(r.val+d-e)%d,Nat.mod_lt _ (Nat.zero_lt_of_lt he)⟩
    have idx (i : Fin d) : (i.val+e)%d=r.val ↔ i=a := by
      have h1 : r.val<d := r.isLt
      have h2 := i.isLt
      have h3 : r.val+d-e+e=r.val+d := by omega
      have move (x : ℕ) (h : x<2*d) : x%d=if x<d then x else x-d := by
        split_ifs with g
        · exact Nat.mod_eq_of_lt g
        · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      rw [move _ (by omega)]
      rw [Fin.ext_iff]
      change _ ↔ i.val=(r.val+d-e)%d
      rw [move _ (by omega)]; split_ifs <;> omega
    simp only [collect,Vector.getElem_ofFn,idx]; simp [a,I]
  have eqn : repr (difference e v) = repr (collect d univ I (fun r : Fin d => r.val+e))-repr v := by
    simp only [repr,← sum_sub_distrib]; apply sum_congr rfl; intro r _
    simp [difference,entries,map_sub,sub_mul]
  rw [eqn,map_sub,H]
  simp only [repr,map_sum,map_mul,map_pow,pow_add,mul_sub_one, sum_mul,I]
  simp_rw [mul_assoc]

/-- Fold the proper-divisor properExponents, storing the length-d row after each step. -/
def sieve {d : ℕ} (v : Vector ℚ d) (ds : List ℕ) : Vector ℚ d :=
  ds.foldl (fun row e => difference e row) v

private lemma eval_sieve {R : Type*} [CommRing R] (F : ℚ[X] →+* R) {d : ℕ}
    (hx : (F X)^d=1) (ds : List ℕ) (hl : ∀ e∈ds,e<d) (v : Vector ℚ d) :
    F (repr (sieve v ds)) = F (repr v) * (ds.map (fun e => (F X)^e-1)).prod := by
  induction ds generalizing v with
  | nil => simp [sieve]
  | cons e ds ih =>
    change F (repr (sieve (difference e v) ds))=_
    rw [ih (fun _ he => hl _ (by simp [he])),eval_difference F (hl _ (by simp)) hx]
    simp [mul_assoc]

def properExponents (d : ℕ) := (List.range d).filter fun e => decide (e ∣ d)

private lemma factors_mem {d e : ℕ} : e∈properExponents d ↔ e∈d.properDivisors := by
  simp [properExponents,Nat.mem_properDivisors,and_comm]

/-- Test divisibility of the sparse input polynomial by the d-th cyclotomic polynomial. -/
def vanishes (d : ℕ) (M : Finset ℕ) (c : ℕ → ℚ) : Bool :=
  let row := sieve (collect d M c id) (properExponents d)
  decide (∀ r : Fin d, row[r.val]=0)

theorem vanishes_iff {d : ℕ} (hd : 0<d) (M : Finset ℕ) (c : ℕ → ℚ) :
    vanishes d M c = true ↔ cyclotomic d ℚ ∣ ∑ m∈M, C (c m)*X^m := by
  classical
  let P : ℚ[X] := ∑ m∈M, C (c m)*X^m
  let ds := d.properDivisors
  let mask : ℚ[X] := ∏ e∈ds, (X^e-1)
  let row := sieve (collect d M c id) (properExponents d)
  let Q : ℚ[X] := X^d-1
  let F := AdjoinRoot.mk Q
  have hx : (F X)^d=1 := by
    have H := AdjoinRoot.mk_self (f:=Q); change F (X^d-1)=0 at H
    exact sub_eq_zero.mp (by simpa using H)
  have eval : F (repr row)= F (P*mask) := by
    rw [map_mul]
    dsimp only [row, mask]; rw [eval_sieve F hx,eval_collect F hd hx]
    · congr 1
      simp only [map_prod,map_sub,map_pow,map_one]
      have He : (properExponents d).toFinset=ds := by ext e; rw [List.mem_toFinset]; exact factors_mem
      rw [← He]; exact (List.prod_toFinset _ (List.Nodup.filter _ List.nodup_range)).symm
    · intro e he; exact (Nat.mem_properDivisors.mp (factors_mem.mp he)).2
  have vanish : vanishes d M c=true ↔ Q ∣ P*mask := by
    change decide (∀ r : Fin d, row[r.val]=0)=true ↔ _
    rw [decide_eq_true_eq, ← AdjoinRoot.mk_eq_zero,← eval]
    constructor
    · intro H; simp [repr,H]
    · intro H r
      have Hz := Polynomial.eq_zero_of_dvd_of_natDegree_lt ((AdjoinRoot.mk_eq_zero).mp H)
        (show (repr row).natDegree<Q.natDegree by change _ < (X^d-C (1:ℚ)).natDegree; rw [natDegree_X_pow_sub_C]; exact repr_small hd row)
      simpa [repr_coeff,r.isLt] using congrArg (fun f : ℚ[X] => f.coeff r.val) Hz
  rw [vanish]
  have factor : Q = cyclotomic d ℚ * ∏ e∈ds, cyclotomic e ℚ := by
    have H := prod_cyclotomic_eq_X_pow_sub_one hd ℚ
    rw [← Nat.cons_self_properDivisors hd.ne',Finset.prod_cons] at H
    exact H.symm
  constructor
  · intro H
    let ζ := Complex.exp (2*Real.pi*Complex.I/d)
    have hζ := Complex.isPrimitiveRoot_exp d hd.ne'
    let ev := aeval ζ (R:=ℚ)
    have root : ev Q=0 := by simp [ev,Q,hζ.pow_eq_one,ζ]
    have hz : ev (P*mask)=0 := by obtain ⟨v,hv⟩ := H; rw [hv,map_mul,root,zero_mul]
    rw [map_mul] at hz
    have hm : ev mask≠0 := by
      dsimp only [mask]; rw [map_prod]; apply Finset.prod_ne_zero_iff.mpr
      intro e he; rw [map_sub,map_pow,map_one]; dsimp only [ev]; rw [aeval_X]
      exact sub_ne_zero.mpr (fun hh => (not_le_of_gt (Nat.mem_properDivisors.mp he).2)
        (Nat.le_of_dvd (Nat.pos_of_mem_properDivisors he) ((hζ.pow_eq_one_iff_dvd e).mp hh)))
    have : NeZero (d:ℚ) := ⟨by exact_mod_cast hd.ne'⟩
    rw [hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hd)]
    exact minpoly.dvd _ _ ((mul_eq_zero.mp hz).resolve_right hm)
  · intro H
    rw [factor]
    exact mul_dvd_mul H (Finset.prod_dvd_prod_of_dvd _ _ (fun e _ => cyclotomic.dvd_X_pow_sub_one e ℚ))

end CyclicPolynomial

/-- All failed cells, directly inspectable with exact rational arithmetic. -/
def resonanceWitnesses (b p S : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) : Finset ℕ :=
  (Ico S (p*S)).filter fun u => CyclicPolynomial.vanishes (residueOrder b p) M (cellWeight p u a)

theorem resonanceWitnesses_eq {b p : ℕ} [Fact p.Prime] (hbc : b.Coprime p)
    (S : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) :
    resonanceWitnesses b p S M a = resonantCells b p S M a := by
  classical
  have hp := Fact.out (p:=p.Prime)
  have hd := Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one ((ZMod.isUnit_iff_coprime b p).mpr hbc).ne_zero)
    (Nat.sub_pos_of_lt hp.one_lt)
  ext u; rw [resonanceWitnesses,resonantCells,mem_filter,mem_filter,residueOrder_eq hbc]
  exact and_congr_right (fun _ => CyclicPolynomial.vanishes_iff hd M (cellWeight p u a))

/-- Exact Boolean checker on the admissible parameter domain of the correctness theorem. -/
def cyclotomicNormalTest (b p : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) : Bool :=
  decide (resonanceWitnesses b p (max 1 (M.sup id)) M a = ∅)

theorem cyclotomicNormalTest_correct {b p : ℕ} [Fact p.Prime] (hb : 1<b) (ho : Odd p)
    (hbc : b.Coprime p) (M : Finset ℕ) (a : ℕ → ℚ) (hm : ∀ m∈M,0<m) :
    cyclotomicNormalTest b p M a=true ↔ NormalIn b (radixSum b p M a) := by
  let S := max 1 (M.sup id)
  rw [cyclotomic_normal_iff hb ho hbc (S:=S) (by dsimp [S]; omega) M a (fun m h => ⟨hm m h,
    (Finset.le_sup (f:=id) h).trans (le_max_right ..)⟩)]
  simp only [cyclotomicNormalTest,decide_eq_true_eq,resonanceWitnesses_eq hbc,resonantCells,filter_eq_empty_iff,S]

end NormalityChecker
