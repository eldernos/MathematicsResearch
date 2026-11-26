module

public import NormalityChecker.StrideDenominatorRate
public import Mathlib.Algebra.Polynomial.Roots

/-! Value multiplicities of the prime-to-`p` part of the two-stride logarithm prefix. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.StrideResidueReturns

private noncomputable def factors {K : Type*} [Field K] (s : Finset ℕ) (v : ℕ → K) : K[X] :=
  ∏ i ∈ s, (X + C (v i))

private lemma eval_factors {K : Type*} [Field K] (s : Finset ℕ) (v : ℕ → K) (x : K) :
    (factors s v).eval x = ∏ i ∈ s, (x + v i) := by
  change (evalRingHom x) (∏ i ∈ s, (X+C (v i))) = _
  simp [map_prod]

private lemma degree_factors {K : Type*} [Field K] (s : Finset ℕ) (v : ℕ → K) :
    (factors s v).natDegree ≤ s.card := by
  apply (natDegree_prod_le s _).trans
  simp

/-- A weighted sum of distinct simple fractions takes any prescribed value at
most as often as there are poles, provided one residue survives. -/
theorem simple_fraction_fiber {K : Type*} [Field K] (s : Finset ℕ) (v a : ℕ → K)
    (distinct : Set.InjOn v (s : Set ℕ)) {i : ℕ} (hi : i ∈ s) (alive : a i ≠ 0)
    (c : K) (E : Finset K) (regular : ∀ x ∈ E, ∀ j ∈ s, x+v j ≠ 0)
    (value : ∀ x ∈ E, ∑ j ∈ s, a j/(x+v j) = c) : E.card ≤ s.card := by
  classical
  let P : K[X] := (∑ j ∈ s, C (a j)*factors (s.erase j) v) - C c * factors s v
  have evalP (x : K) : P.eval x =
      (∑ j ∈ s, a j * ∏ l ∈ s.erase j, (x+v l)) - c * ∏ l ∈ s, (x+v l) := by
    simp [P, eval_finsetSum, eval_factors]
  have nz : P ≠ 0 := by
    intro zero
    have h := evalP (-v i)
    rw [zero, eval_zero, prod_eq_zero hi (neg_add_cancel _), mul_zero, sub_zero,
      sum_eq_single_of_mem i hi] at h
    · apply (mul_ne_zero alive (prod_ne_zero_iff.mpr ?_)) h.symm
      intro l hl eqn
      have e : v l = v i := by linear_combination eqn
      exact (ne_of_mem_erase hl) (distinct (mem_of_mem_erase hl) hi e)
    · intro j hj ne
      rw [prod_eq_zero (mem_erase.mpr ⟨ne.symm,hi⟩) (neg_add_cancel _), mul_zero]
  apply (card_le_degree_of_subset_roots (p:=P) ?_).trans
  · dsimp only [P]
    apply (natDegree_sub_le ..).trans
    apply max_le _ ((natDegree_C_mul_le ..).trans (degree_factors ..))
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_le ..).trans ((degree_factors ..).trans (card_le_card (erase_subset ..)))
  · intro x hx
    apply (mem_roots nz).mpr
    rw [IsRoot, evalP,sub_eq_zero,← value x hx,sum_mul]
    apply sum_congr rfl
    intro j hj
    rw [←prod_erase_mul s (fun l => x+v l) hj]
    field_simp [regular x hx j hj]

/-- A periodically weighted binary prefix in the field. Its inverse convention
omits precisely the indices divisible by the selected prime. -/
def regularPart {p : ℕ} [Fact p.Prime] (w : ℕ → ZMod p) (N : ℕ) : ZMod p :=
  ∑ j ∈ range N, (2 : ZMod p)^(N-(j+1)) * w (j+1) / (j+1 : ℕ)

private lemma jump {p : ℕ} [Fact p.Prime] (w : ℕ → ZMod p) (N h : ℕ) :
    regularPart w (N+h) = 2^h * regularPart w N +
      ∑ i ∈ range h, 2^(h-(i+1)) * w (N+i+1) / (N+i+1 : ℕ) := by
  simp only [regularPart, sum_range_add, mul_sum]
  apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intro i hi
  · have bound := mem_range.mp hi
    rw [show N+h-(i+1) = h+(N-(i+1)) by omega, pow_add]; ring
  · rw [show N+h-(N+i+1) = h-(i+1) by omega]

private lemma inj_lifts {p h : ℕ} [Fact p.Prime] (short : h ≤ p) :
    Set.InjOn (fun i : ℕ => (i : ZMod p)) (range h : Finset ℕ) := by
  intro i hi j hj eqn
  have eqv := congrArg ZMod.val eqn
  simpa [ZMod.val_natCast_of_lt ((mem_range.mp hi).trans_le short),
    ZMod.val_natCast_of_lt ((mem_range.mp hj).trans_le short)] using eqv

/-- In a single residue class of the coefficient period, at most h positions
in a prime block have any given ordered pair of regular residues at distance h.
The numerator condition excludes gaps consisting entirely of zero coefficients. -/
theorem regular_pairs {p m A h a : ℕ} [Fact p.Prime] (big : 2 < p) (short : h < p)
    (w : ℕ → ZMod p) (period : ∀ j, w j = w (j%m))
    (alive : ∃ i ∈ range h, w (a+i+1) ≠ 0) (r t : ZMod p)
    (E : Finset ℕ) (starts : ∀ n ∈ E, n+h < p ∧ (A*p+n)%m = a ∧
      regularPart w (A*p+n) = r ∧ regularPart w (A*p+n+h) = t) : E.card ≤ h := by
  classical
  let lift : ℕ → ZMod p := fun n => (n : ZMod p) + 1
  let coeff : ℕ → ZMod p := fun i => 2^(h-(i+1))*w (a+i+1)
  have base (n : ℕ) : ((A*p+n : ℕ) : ZMod p) = n := by simp
  have reg {n i : ℕ} (hn : n+h < p) (hi : i ∈ range h) : lift n+(i : ZMod p) ≠ 0 := by
    have bnd := mem_range.mp hi
    have nz : ((n+1+i : ℕ) : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    simpa [lift] using nz
  have sums {n : ℕ} (hn : n∈E) :
      ∑ i ∈ range h, coeff i / (lift n+(i:ZMod p)) = t-2^h*r := by
    obtain ⟨_,phase,first,last⟩ := starts n hn
    have eqn := jump w (A*p+n) h
    rw [first,last] at eqn
    rw [eq_sub_iff_add_eq,eqn,add_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    have same : w (A*p+n+i+1) = w (a+i+1) := by
      rw [period (A*p+n+i+1),period (a+i+1)]
      congr 1
      have congruence : A*p+n ≡ a [MOD m] := by simp [Nat.ModEq, ←phase]
      exact (congruence.add_right i).add_right 1
    rw [same]
    simp [lift,coeff,add_assoc,add_comm,add_left_comm]
  obtain ⟨j,hj,nz⟩ := alive
  have two : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) big)
  have inject : Set.InjOn lift (E : Set ℕ) := by
    intro n hn k hk eqn
    apply inj_lifts (p:=p) (h:=p) le_rfl
      (mem_range.mpr (show n<p by have := (starts n hn).1; omega))
      (mem_range.mpr (show k<p by have := (starts k hk).1; omega))
    exact add_right_cancel eqn
  rw [←card_image_of_injOn inject]
  simpa only [card_range] using simple_fraction_fiber (range h) (fun i => (i:ZMod p)) coeff
    (inj_lifts short.le) hj (mul_ne_zero (pow_ne_zero _ two) nz) (t-2^h*r) (E.image lift)
    (fun x hx => by obtain ⟨n,hn,rfl⟩ := mem_image.mp hx; exact fun _ hi => reg (starts n hn).1 hi)
    (fun x hx => by obtain ⟨n,hn,rfl⟩ := mem_image.mp hx; exact sums hn)

/-- From fixed-gap collisions to the number of hits in an arbitrary short interval. -/
theorem window_of_pairs {A T H : ℕ} (E : Finset ℕ) (window : E ⊆ Ico A (A+T))
    (pairs : ∀ h, 0 < h → h ≤ H → (E.filter (fun n => n+h ∈ E)).card ≤ h) :
    E.card ≤ T/(H+1)+1+H^2 := by
  classical
  let B := E.filter (fun n => ∀ m∈E,(m-A)/(H+1)=(n-A)/(H+1) → n≤m)
  let P := fun h => E.filter (fun n => n+h ∈ E)
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
    exact mem_union_right _ (mem_biUnion.mpr ⟨n-m-1,mem_range.mpr diff,
      mem_image.mpr ⟨m,mem_filter.mpr ⟨hm, by simpa only [id] using hn⟩, id⟩⟩)
  have each (j : ℕ) (hj : j∈range H) : (U j).card≤H := by
    have h := mem_range.mp hj
    exact card_image_le.trans ((pairs (j+1) (by omega) (by omega)).trans (by omega))
  have total := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add first ((card_biUnion_le ..).trans (sum_le_sum each))))
  simpa [sq] using total


/-- Anti-concentration in each phase class of a periodically weighted prefix.
Different multiples of p may lie before the observation window. -/
theorem regular_window {p m A a H D T : ℕ} [Fact p.Prime] (big : 2 < p) (short : H < p)
    (w : ℕ → ZMod p) (period : ∀ j, w j = w (j%m))
    (active : ∃ i ∈ range m, w (a+i+1) ≠ 0)
    (t : ZMod p) (E : Finset ℕ) (window : E ⊆ Ico D (D+T))
    (starts : ∀ n ∈ E, n < p ∧ (A*p+n)%m = a ∧ regularPart w (A*p+n) = t) :
    E.card ≤ T/(H+1)+1+H^2 := by
  classical
  apply window_of_pairs E window
  intro h pos small
  by_cases hm : m ≤ h
  · obtain ⟨i,hi,wi⟩ := active
    apply regular_pairs (A:=A) (a:=a) big (small.trans_lt short) w period
      ⟨i, mem_range.mpr ((mem_range.mp hi).trans_le hm), wi⟩ t t
    intro n hn
    obtain ⟨lo,hi⟩ := mem_filter.mp hn
    obtain ⟨_,phase,atStart⟩ := starts n lo
    obtain ⟨en,_,atEnd⟩ := starts (n+h) hi
    exact ⟨en,phase,atStart,by simpa [Nat.add_assoc] using atEnd⟩
  · have empty : E.filter (fun n => n+h∈E) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨lo,hi⟩ := mem_filter.mp hn
      have same : A*p+n+h ≡ A*p+n [MOD m] := by
        change (A*p+n+h)%m = (A*p+n)%m
        rw [Nat.add_assoc, (starts (n+h) hi).2.1, (starts n lo).2.1]
      have cancel : h ≡ 0 [MOD m] := Nat.ModEq.add_left_cancel' (A*p+n) (by simpa only [add_zero] using same)
      have dvd := Nat.modEq_zero_iff_dvd.mp cancel
      exact hm (Nat.le_of_dvd pos dvd)
    simp [empty]

/-- The prime-free part of the actual shifted two-stride logarithm prefix. -/
def logarithmDigit (p : ℕ) [Fact p.Prime] (N : ℕ) : ZMod p :=
  regularPart (fun j => (StrideDenominatorRate.weight j : ZMod p)) N

/-- The two rational parts of the actual prefix, separated according to whether
the binary-exponent index is a multiple of p. -/
def siftedRaw (p : ℕ) (poles : Bool) : ℕ → ℚ
  | 0 => 0
  | n+1 => 2*siftedRaw p poles n + if decide (p ∣ n+1) = poles
      then (StrideDenominatorRate.weight (n+1) : ℚ)/(n+1) else 0

theorem actual_split (p n : ℕ) :
    twoStridePrefix n = siftedRaw p false n + siftedRaw p true n := by
  induction n with
  | zero => simp [twoStridePrefix,stridedPrefix,siftedRaw]
  | succ n ih =>
    rw [StrideDenominatorRate.step,ih]
    by_cases h : p ∣ n+1 <;> simp [siftedRaw,h] <;> ring

/-- A common numerator and an invertible denominator simultaneously represent
the rational prime-free sum and its finite-field value. -/
theorem actual_regular_digit (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ D : ℕ, ∃ B : ℤ, (D : ZMod p) ≠ 0 ∧
      (D : ℚ)*siftedRaw p false n = B ∧ (D : ZMod p)*logarithmDigit p n = B := by
  induction n with
  | zero => exact ⟨1,0,by simp,by simp [siftedRaw],by simp [logarithmDigit,regularPart]⟩
  | succ n ih =>
    obtain ⟨D,B,unit,rational,residue⟩ := ih
    have st := jump (p:=p) (fun j => (StrideDenominatorRate.weight j : ZMod p)) n 1
    simp only [sum_range_one,pow_one,zero_add,add_zero,Nat.sub_self,pow_zero,one_mul] at st
    change logarithmDigit p (n+1) = 2*logarithmDigit p n +
      (StrideDenominatorRate.weight (n+1) : ZMod p)/((n+1:ℕ) : ZMod p) at st
    by_cases hit : p ∣ n+1
    · have z : ((n+1:ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr hit
      refine ⟨D,2*B,unit,?_,?_⟩
      · simp only [siftedRaw,hit,decide_true,ite_false,Bool.true_eq_false,add_zero,Int.cast_mul,Int.cast_ofNat]
        linear_combination 2*rational
      · rw [st,z,div_zero,add_zero,Int.cast_mul,Int.cast_ofNat]
        linear_combination 2*residue
    · let W := StrideDenominatorRate.weight (n+1)
      have un : ((n+1:ℕ) : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hit
      have qn : ((n:ℚ)+1) ≠ 0 := by positivity
      refine ⟨D*(n+1), 2*B*(n+1 : ℕ)+D*W, by simpa only [Nat.cast_mul] using mul_ne_zero unit un, ?_, ?_⟩
      · simp only [siftedRaw,hit,decide_false,ite_true,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
          Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,Int.cast_one]
        dsimp [W]
        field_simp [qn]
        linear_combination 2*((n:ℚ)+1)*rational
      · rw [st]
        push_cast at un ⊢
        dsimp [W]
        field_simp [un]
        linear_combination 2*((n:ZMod p)+1)*residue

private lemma weight_period (j : ℕ) :
    StrideDenominatorRate.weight j = StrideDenominatorRate.weight (j%6) := by
  simp only [StrideDenominatorRate.weight]
  have d2 : 2 ∣ j%6 ↔ 2 ∣ j := by omega
  have d3 : 3 ∣ j%6 ↔ 3 ∣ j := by omega
  have d6 : 6 ∣ j%6 ↔ 6 ∣ j := by omega
  simp only [d2,d3,d6]

/-- Any given residue occurs at most six times the one-phase bound in T positions
of any p-block of the actual two-stride p-regular digits. -/
theorem logarithm_window {p A D T H : ℕ} [Fact p.Prime] (big : 3<p) (short : H<p)
    (target : ZMod p) (E : Finset ℕ) (window : E⊆Ico D (D+T))
    (hits : ∀ n ∈ E, n<p ∧ logarithmDigit p (A*p+n)=target) :
    E.card ≤ 6*(T/(H+1)+1+H^2) := by
  classical
  let E' := fun a : ℕ => E.filter (fun n => (A*p+n)%6=a)
  have cover : E ⊆ (range 6).biUnion E' := by
    intro n hn
    exact mem_biUnion.mpr ⟨_,mem_range.mpr (Nat.mod_lt _ (by decide)),mem_filter.mpr ⟨hn,rfl⟩⟩
  refine (card_le_card cover).trans (card_biUnion_le.trans ?_)
  have bound (a : ℕ) (ha : a∈range 6) : (E' a).card ≤ T/(H+1)+1+H^2 := by
    have al := mem_range.mp ha
    let w := fun j : ℕ => (StrideDenominatorRate.weight j : ZMod p)
    have active : ∃ i ∈ range 6, w (a+i+1) ≠ 0 := by
      refine ⟨5-a,mem_range.mpr (by omega),?_⟩
      rw [show a+(5-a)+1=6 by omega]
      norm_num [w,StrideDenominatorRate.weight]
    apply regular_window (A:=A) (a:=a) (by omega) short w
      (fun j => congrArg (fun z : ℤ => (z : ZMod p)) (weight_period j)) active target
      (E' a) ((filter_subset ..).trans window)
    intro n hn
    obtain ⟨he,ph⟩ := mem_filter.mp hn
    exact ⟨(hits n he).1,ph,(hits n he).2⟩
  simpa [mul_comm] using sum_le_sum bound

end NormalityChecker.StrideResidueReturns
