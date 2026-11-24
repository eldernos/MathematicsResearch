module

public import NormalityChecker.ArithmeticCertificate
public import NormalityChecker.FirstFrequency
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Nat.Fib.Zeckendorf

/-! Nearest-integer escape from the least Zeckendorf summand. -/
@[expose] public section
open Finset Real Filter
open scoped goldenRatio Topology
namespace NormalityChecker

private lemma digits_envelope (N : ℕ) (digit : ℕ → ℝ) (bits : ∀ j, 0≤digit j ∧ digit j≤1) :
    -1≤∑ j∈range N,digit j*ψ^j ∧ ∑ j∈range N,digit j*ψ^j≤φ := by
  induction N generalizing digit with
  | zero => simp [goldenRatio_pos.le]
  | succ N ih =>
    obtain ⟨l,h⟩ := ih (fun j => digit (j+1)) (fun j => bits _)
    rw [sum_range_succ']; simp only [pow_zero,mul_one,pow_succ,← mul_assoc,← sum_mul]
    have left := mul_le_mul_of_nonpos_right h goldenConj_neg.le
    have right := mul_le_mul_of_nonpos_right l goldenConj_neg.le
    rw [goldenRatio_mul_goldenConj] at left
    constructor <;> linarith [(bits 0).1,(bits 0).2,goldenRatio_add_goldenConj]

private lemma envelope_finset (S : Finset ℕ) : -1≤∑ j∈S,ψ^j ∧ ∑ j∈S,ψ^j≤φ := by
  let N := S.sup id + 1
  have sub : S⊆range N := fun j h => mem_range.mpr (Nat.lt_succ_of_le (le_sup (f:=id) h))
  let d (j : ℕ) : ℝ := if j∈S then 1 else 0
  have H := digits_envelope N d (fun j => by dsimp [d]; split <;> norm_num)
  have e : ∑ j∈range N,d j*ψ^j = ∑ j∈S,ψ^j := by
    simp only [d,ite_mul,one_mul,zero_mul,← sum_filter]
    congr 1; ext j; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => sub h)
  rwa [e] at H

/-- The error in the Fibonacci representation before reduction modulo one. -/
theorem golden_fibonacci_identity (S : Finset ℕ) :
    ((∑ i∈S,Nat.fib (i+1):ℕ):ℝ)-φ*((∑ i∈S,Nat.fib i:ℕ):ℝ)=∑ i∈S,ψ^i := by
  push_cast; rw [mul_sum,← sum_sub_distrib]; exact sum_congr rfl (fun i _ => fib_succ_sub_goldenRatio_mul_fib i)

private theorem golden_signed_error (S : Finset ℕ) {k : ℕ} (mem : k∈S)
    (gap : ∀ j∈S,j≠k → k+2≤j) :
    ∃ u : ℝ, (φ⁻¹≤u ∧ u≤φ) ∧
      ((∑ i∈S,Nat.fib (i+1):ℕ):ℝ)-φ*((∑ i∈S,Nat.fib i:ℕ):ℝ)=ψ^k*u := by
  let R := S.erase k
  let U := R.image (fun j => j-(k+2))
  let T := ∑ i∈U,ψ^i
  have er : ∑ j∈R,ψ^j = ψ^(k+2)*T := by
    dsimp [T,U]; rw [sum_image,mul_sum]
    · apply sum_congr rfl; intro i hi; rw [← pow_add]; congr 1; have g := gap i (mem_erase.mp hi).2 (mem_erase.mp hi).1; omega
    · intro i hi j hj H; dsimp at H; have := gap i (mem_erase.mp hi).2 (mem_erase.mp hi).1; have := gap j (mem_erase.mp hj).2 (mem_erase.mp hj).1; omega
  let M := ∑ i∈S,Nat.fib i
  let z : ℤ := ((∑ i∈S,Nat.fib (i+1):ℕ):ℤ)
  let y := φ*(M:ℝ)
  have ident : (z:ℝ)-y=ψ^k*(1+ψ^2*T) := by
    simp only [z,y,Int.cast_natCast]
    dsimp only [M]
    rw [golden_fibonacci_identity,← sum_erase_add _ _ mem,show ∑ j∈S.erase k,ψ^j=ψ^(k+2)*T from er,pow_add]; ring
  obtain ⟨tl,tu⟩ := envelope_finset U
  change -1≤T at tl; change T≤φ at tu
  have scale : φ⁻¹ ≤ 1+ψ^2*T ∧ 1+ψ^2*T≤φ := by
    rw [inv_goldenRatio]; have lo := mul_le_mul_of_nonneg_left tl (sq_nonneg ψ)
    have hi := mul_le_mul_of_nonneg_left tu (sq_nonneg ψ)
    have eqn : ψ^2*φ= -ψ := by rw [sq,mul_assoc,goldenConj_mul_goldenRatio]; ring
    rw [eqn] at hi; constructor <;> nlinarith [goldenConj_sq,goldenRatio_add_goldenConj]
  exact ⟨_,scale,ident⟩

/-- For a representation whose first occupied index is `k` and whose next
index is at least `k+2`, give two-sided distance bounds including the wrap at `k=2`. -/
theorem golden_least_bounds (S : Finset ℕ) {k : ℕ} (hk : 2≤k) (mem : k∈S)
    (gap : ∀ j∈S,j≠k → k+2≤j) :
    let q := φ⁻¹
    q^(k+1) ≤ turnDistance (φ*(∑ i∈S,Nat.fib i:ℕ)) ∧
    turnDistance (φ*(∑ i∈S,Nat.fib i:ℕ)) ≤ q^k*φ := by
  let q := φ⁻¹
  have qp : 0<q := inv_pos.mpr goldenRatio_pos
  have ql : q<1 := inv_lt_one_of_one_lt₀ one_lt_goldenRatio
  have qψ : q = -ψ := inv_goldenRatio
  let M := ∑ i∈S,Nat.fib i
  let z : ℤ := ((∑ i∈S,Nat.fib (i+1):ℕ):ℤ)
  let y := φ*(M:ℝ)
  obtain ⟨u,scale,ident⟩ := golden_signed_error S mem gap
  change (z:ℝ)-y=ψ^k*u at ident
  have absid : |y-z|=q^k*(u) := by
    rw [abs_sub_comm,ident,abs_mul,abs_pow,abs_of_neg goldenConj_neg,← qψ,abs_of_nonneg (qp.le.trans scale.1)]
  have band : q^(k+1)≤|y-z| ∧ |y-z|≤q^k*φ := by rw [absid,pow_succ]; exact ⟨by gcongr; exact scale.1,by gcongr; exact scale.2⟩
  have fold : q^k*φ+q^(k+1)≤1 := by
    have mq := pow_le_pow_of_le_one qp.le ql.le hk
    rw [pow_succ]; calc q^k*φ+q^k*q = q^k*(φ+q) := by ring
                        _ ≤ q^2*(φ+q) := by gcongr
                        _ ≤ 1 := by rw [qψ]; nlinarith [goldenConj_sq,goldenConj_mul_goldenRatio,mul_self_nonneg ψ,goldenConj_neg,show ψ^2*φ= -ψ by rw [sq,mul_assoc,goldenConj_mul_goldenRatio]; ring,show ψ^3=2*ψ+1 by rw [pow_succ,goldenConj_sq]; nlinarith [goldenConj_sq],goldenRatio_lt_two,one_lt_goldenRatio]
  refine ⟨?_,(round_le y z).trans band.2⟩
  change _≤|y-(round y:ℤ)|; by_cases eqn : round y=z
  · simpa only [eqn] using band.1
  · have sep := Int.one_le_abs (sub_ne_zero.mpr eqn)
    have realSep : (1:ℝ)≤|(round y:ℝ)-(z:ℝ)| := by exact_mod_cast sep
    have tri := abs_sub_le (round y:ℝ) y z; rw [abs_sub_comm (round y:ℝ) y] at tri; linarith [band.2]

/-- Binary (or other fixed-radix) normality transfers among these three quadratic values. -/
theorem golden_normal_equivalences {b : ℕ} (hb : 2≤b) :
    (NormalIn b φ ↔ NormalIn b (√5)) ∧ (NormalIn b φ ↔ NormalIn b (1/√5)) := by
  have t := normal_add_rat_iff hb (√5) 1
  have f := normal_mul_nat_iff hb (by decide : 0<2) φ
  have e : (2:ℝ)*φ=√5+(1:ℚ) := by dsimp [goldenRatio]; push_cast; ring
  norm_cast at e; push_cast at f t; rw [show (2:ℝ)*φ=√5+1 by simpa using e] at f
  have first := f.symm.trans t
  have h := normal_mul_nat_iff hb (by decide : 0<5) (1/√5); push_cast at h
  rw [show (5:ℝ)*(1/√5)=√5 by field_simp; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]] at h
  exact ⟨first,first.trans h⟩

lemma zeckendorf_nonempty {M : ℕ} (hM : 0<M) : M.zeckendorf.toFinset.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr; intro e
  have l := (List.toFinset_eq_empty_iff _).mp e
  have h := Nat.sum_zeckendorf_fib M; simp [l] at h; omega

/-- Smallest occupied Fibonacci index, with value zero for the empty representation. -/
def leastFibIndex (M : ℕ) := if h : 0<M then M.zeckendorf.toFinset.min' (zeckendorf_nonempty h) else 0

private lemma pairwise_gap {l : List ℕ} (h : l.Pairwise (fun a b => b+2≤a))
    {j k : ℕ} (hj : j∈l) (hk : k∈l) (ne : j≠k) : j+2≤k ∨ k+2≤j := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    obtain ⟨first,rest⟩ := List.pairwise_cons.mp h
    by_cases ej : j=a
    · subst j; exact Or.inr (first _ ((List.mem_cons.mp hk).resolve_left (Ne.symm ne)))
    have jmem := (List.mem_cons.mp hj).resolve_left ej
    rcases List.mem_cons.mp hk with rfl|kmem
    · exact Or.inl (first _ jmem)
    · exact ih rest jmem kmem

private theorem zeckendorf_data {M : ℕ} (hm : 0<M) :
    let S := M.zeckendorf.toFinset
    let k := leastFibIndex M
    2≤k ∧ k∈S ∧ (∀ j∈S,j≠k → k+2≤j) ∧ ∑ i∈S,Nat.fib i=M := by
  let : Trans (fun a b : ℕ => b+2≤a) (fun a b : ℕ => b+2≤a) (fun a b : ℕ => b+2≤a) := ⟨by omega⟩
  let l := M.zeckendorf
  let k := leastFibIndex M
  have chain : (l++[0]).IsChain (fun a b => b+2≤a) := Nat.isZeckendorfRep_zeckendorf M
  obtain ⟨pw,_,last⟩ := List.pairwise_append.mp chain.pairwise
  have nd : l.Nodup := pw.imp (by intros; omega)
  have km : k∈l.toFinset := by dsimp only [k,leastFibIndex]; rw [dite_eq_left hm]; apply min'_mem
  have kl := List.mem_toFinset.mp km
  have ge := last k kl 0 (by simp)
  refine ⟨by omega,km,?_,(List.sum_toFinset Nat.fib nd).trans (Nat.sum_zeckendorf_fib M)⟩
  intro j hj ne
  have mn := min'_le l.toFinset j hj
  have idk : k=l.toFinset.min' (zeckendorf_nonempty hm) := dite_eq_left hm
  have sep := pairwise_gap pw (List.mem_toFinset.mp hj) kl ne
  omega

/-- Canonical Zeckendorf form of the distance bound, for every positive integer. -/
theorem golden_zeckendorf_bounds {M : ℕ} (hm : 0<M) :
    φ⁻¹^(leastFibIndex M+1) ≤ turnDistance ((M:ℝ)*φ) ∧
    turnDistance ((M:ℝ)*φ) ≤ φ⁻¹^(leastFibIndex M)*φ := by
  obtain ⟨hk,mem,gap,total⟩ := zeckendorf_data hm
  simpa only [total,mul_comm] using golden_least_bounds _ hk mem gap

/-- The integer part is determined by shifting all occupied Fibonacci indices
and subtracting one exactly when the least index is even. -/
theorem golden_floor_zeckendorf {M : ℕ} (hm : 0<M) :
    ⌊(M:ℝ)*φ⌋ = ((∑ j∈M.zeckendorf.toFinset,Nat.fib (j+1):ℕ):ℤ) -
      (if Even (leastFibIndex M) then 1 else 0) := by
  obtain ⟨hk,mem,gap,total⟩ := zeckendorf_data hm
  obtain ⟨u,hu,id⟩ := golden_signed_error _ mem gap
  rw [total,mul_comm φ] at id
  let k := leastFibIndex M
  let z : ℤ := ((∑ j∈M.zeckendorf.toFinset,Nat.fib (j+1):ℕ):ℤ)
  change (z:ℝ)-(M:ℝ)*φ=ψ^k*u at id
  change ⌊(M:ℝ)*φ⌋=z-(if Even k then 1 else 0)
  have up : 0<u := (inv_pos.mpr goldenRatio_pos).trans_le hu.1
  have q := inv_lt_one_of_one_lt₀ one_lt_goldenRatio
  have band : |(z:ℝ)-(M:ℝ)*φ|<1 := by
    rw [id,abs_mul,abs_pow,abs_of_neg goldenConj_neg,← inv_goldenRatio,abs_of_pos up]
    calc φ⁻¹^k*u ≤ φ⁻¹^2*φ := mul_le_mul (pow_le_pow_of_le_one (inv_pos.mpr goldenRatio_pos).le q.le hk) hu.2 up.le (by positivity [goldenRatio_pos])
         _ = φ⁻¹ := by field_simp [goldenRatio_pos.ne']
         _ < 1 := q
  have bounds := abs_lt.mp band
  split_ifs with ev
  · have hp := mul_pos (ev.pow_pos (ne_of_lt goldenConj_neg)) up
    apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith
  · have hp := mul_neg_of_neg_of_pos ((Nat.not_even_iff_odd.mp ev).pow_neg goldenConj_neg) up
    simp only [sub_zero]; apply Int.floor_eq_iff.mpr; constructor <;> linarith

/-- Frequency of powers of two whose canonical representation uses an index at most `K`. -/
noncomputable def smallFibFrequency (K N : ℕ) : ℝ := ((range N).filter (fun n => leastFibIndex (2^n)≤K)).card / (N:ℝ)

/-- A fixed Fibonacci index cutoff occurs with positive lower density precisely
when the binary orbit of the golden ratio has discrepancy strictly below one. -/
theorem golden_discrepancy_iff_small_index : asymptoticDiscrepancy φ<1 ↔
    ∃ K : ℕ, ∃ η : ℝ, 0<η ∧ ∀ᶠ N in atTop, η≤smallFibFrequency K N := by
  rw [discrepancy_lt_one_iff_transitions]
  let q := φ⁻¹
  have qp : 0<q := inv_pos.mpr goldenRatio_pos
  have ql : q<1 := inv_lt_one_of_one_lt₀ one_lt_goldenRatio
  have band (n : ℕ) := golden_zeckendorf_bounds (M:=2^n) (by positivity)
  simp only [Nat.cast_pow,Nat.cast_ofNat,turnDistance,abs_sub_round_eq_min] at band
  change ∀ n, q^(leastFibIndex (2^n)+1) ≤ min (shift 2 φ n) (1-shift 2 φ n) ∧
    min (shift 2 φ n) (1-shift 2 φ n) ≤ q^(leastFibIndex (2^n))*φ at band
  constructor
  · intro h; obtain ⟨K,hK⟩ := exists_pow_lt_of_lt_one (show 0<1/4/φ by positivity) ql
    have ev := eventually_lt_of_lt_liminf (half_lt_self h : transitionDensity φ/2<transitionDensity φ)
      (isBoundedUnder_of_eventually_ge (.of_forall fun N => (frequency_bounds (shift 2 φ) (1/4) (3/4) N).1))
    refine ⟨K,_,half_pos h,?_⟩; filter_upwards [ev] with N hN; apply hN.le.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N); apply Nat.cast_le.mpr; apply card_le_card
    intro n hn; obtain ⟨mem,lo,hi⟩ := mem_filter.mp hn; apply mem_filter.mpr; refine ⟨mem,?_⟩
    by_contra! large
    have po := pow_le_pow_of_le_one qp.le ql.le large.le
    have md : (1:ℝ)/4≤min (shift 2 φ n) (1-shift 2 φ n) := le_min lo (by linarith)
    have v := md.trans (band n).2
    exact (not_lt_of_ge v) ((mul_le_mul_of_nonneg_right po goldenRatio_pos.le).trans_lt ((lt_div_iff₀ goldenRatio_pos).mp hK))
  · rintro ⟨K,η,ep,ev⟩
    obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one (pow_pos qp (K+1)) (by norm_num : (1/2:ℝ)<1)
    have small := (tendsto_const_div_atTop_nhds_zero_nat (m:ℝ)).eventually_lt_const (half_pos ep)
    have pos : 0<η/(2*((m:ℝ)+1)) := by positivity
    apply pos.trans_le; apply le_liminf_of_le (isCoboundedUnder_ge_of_le _ (fun N => (frequency_bounds (shift 2 φ) (1/4) (3/4) N).2))
    filter_upwards [ev,small] with N hN hmN
    have fr : smallFibFrequency K N ≤ frequency (shift 2 φ) ((1/2)^m/4) (1-(1/2)^m/4) N := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N); apply Nat.cast_le.mpr; apply card_le_card
      intro n hn; obtain ⟨mem,idx⟩ := mem_filter.mp hn
      have g := (pow_le_pow_of_le_one qp.le ql.le (Nat.succ_le_succ idx)).trans (band n).1
      change q^(K+1) ≤ _ at g
      rcases le_min_iff.mp g with ⟨l,r⟩
      exact mem_filter.mpr ⟨mem,by linarith [pow_pos (by norm_num : (0:ℝ)<1/2) m],by linarith [pow_pos (by norm_num : (0:ℝ)<1/2) m]⟩
    have obs := (hN.trans fr).trans (interior_frequency_le_transitions φ N m)
    change _ ≤ transitionFrequency φ N
    rw [div_le_iff₀ (by positivity)]; nlinarith

end NormalityChecker
