module

public import NormalityChecker.LocalizedFive

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedFive

def Supported (m : ℕ) : Prop := ∃ a j : ℕ, m = 2^a * 5^j

open Classical in
noncomputable def term (i : ℕ) : ℝ :=
  if Supported (i+1) then (1/2:ℝ)^(i+1)/(i+1) else 0

/-- The logarithmic series restricted to indices with prime factors in `{2,5}`. -/
noncomputable def value : ℝ := ∑' i : ℕ, term i

private lemma term_bounds (i : ℕ) : 0 ≤ term i ∧ term i ≤ (1/2:ℝ)^(i+1)/(i+1) := by
  unfold term; split_ifs <;> constructor <;> first | positivity | rfl

private lemma summable_term : Summable term :=
  Summable.of_nonneg_of_le (fun i => (term_bounds i).1) (fun i => (term_bounds i).2) hasSum_logTwo.summable

private def index (v : ℕ × ℕ) := 2^v.2 * 5^v.1

private lemma index_injective : Function.Injective index := by
  rintro ⟨j,a⟩ ⟨l,b⟩ he
  change 2^a*5^j = 2^b*5^l at he
  have val (v w : ℕ) : (2^v*5^w).factorization 5 = w := by
    rw [Nat.factorization_mul (by positivity) (by positivity),Finsupp.add_apply,
      Nat.factorization_pow_self (by decide : Nat.Prime 5),Nat.factorization_eq_zero_of_not_dvd
      (fun h => (by decide : ¬5∣2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow h)),zero_add]
  have eqj := congrArg (fun n : ℕ => n.factorization 5) he
  simp only [val] at eqj; subst l
  have eqab := Nat.eq_of_mul_eq_mul_right (by positivity : 0<5^j) he
  exact Prod.ext rfl (Nat.pow_right_injective (by decide : 2≤2) eqab)

/-- Literal double-series statement, reindexed by unique factorization. -/
theorem value_eq_series : value = ∑' j : ℕ, ∑' a : ℕ,
    1 / ((2:ℝ)^a*5^j * 2^(2^a*5^j : ℕ)) := by
  classical
  let g (v : ℕ × ℕ) := index v - 1
  have pos (v : ℕ × ℕ) : 0 < index v := by dsimp [index]; positivity
  have inj : Function.Injective g := by
    intro v w he; apply index_injective; dsimp [g] at he; have := pos v; have := pos w; omega
  have H : HasSum (term ∘ g) value := (inj.hasSum_iff (fun i hi => by
    have h : ¬ Supported (i+1) := by
      rintro ⟨a,j,he⟩; apply hi; exact ⟨(j,a),by change 2^a*5^j-1=i; omega⟩
    simp [term,h])).mpr summable_term.hasSum
  have summand (v : ℕ × ℕ) : (term ∘ g) v = 1 / ((2:ℝ)^v.2*5^v.1 * 2^(index v)) := by
    have hs : Supported (index v) := ⟨v.2,v.1,rfl⟩
    simp only [Function.comp_apply,term,g,Nat.sub_add_cancel (pos v),hs,ite_true]
    rw [← Nat.cast_one (R:=ℝ),← Nat.cast_add,Nat.sub_add_cancel (pos v),Nat.cast_one,one_div_pow]
    dsimp [index]; push_cast; ring
  rw [← H.tsum_eq, H.summable.tsum_prod']
  · exact tsum_congr fun j => tsum_congr fun a => summand (j,a)
  · exact fun i => H.summable.prod_factor i

private lemma truncate (n : ℕ) :
    (shiftedPrefix n:ℝ) = 2^n * (∑ i ∈ range n, term i) := by
  classical
  let rect := (range (Nat.log 5 n+1)) ×ˢ (range (Nat.log 2 n+1))
  let allowed := rect.filter (fun v => index v ≤ n)
  have pos (v : ℕ × ℕ) : 0 < index v := by dsimp [index]; positivity
  have mem (v : ℕ × ℕ) (hv : index v ≤ n) : v ∈ allowed := by
    have hj := (Nat.le_mul_of_pos_left (5^v.1) (by positivity : 0<2^v.2)).trans hv
    have ha := (Nat.le_mul_of_pos_right (2^v.2) (by positivity : 0<5^v.1)).trans hv
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by have := Nat.le_log_of_pow_le (by decide : 1<5) hj; omega),
      mem_range.mpr (by have := Nat.le_log_of_pow_le (by decide : 1<2) ha; omega)⟩,hv⟩
  have eqn : allowed.image (fun v => index v - 1) = (range n).filter (fun i => Supported (i+1)) := by
    ext i; constructor
    · intro hi; obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
      have h := (mem_filter.mp hv).2
      exact mem_filter.mpr ⟨mem_range.mpr (by have := pos v; omega),v.2,v.1, Nat.sub_add_cancel (pos v)⟩
    · intro hi; obtain ⟨ha,a,j,hj⟩ := mem_filter.mp hi
      have he : index (j,a) = i+1 := hj.symm
      exact mem_image.mpr ⟨(j,a),mem _ (by have := mem_range.mp ha; omega),by omega⟩
  have sumform : ∑ i ∈ range n, term i = ∑ v ∈ allowed, (1/2:ℝ)^(index v)/(index v) := by
    simp only [term,← sum_filter,← eqn]
    rw [sum_image]; swap
    · intro a _ b _ he; change index a - 1 = index b - 1 at he; apply index_injective; have := pos a; have := pos b; omega
    apply sum_congr rfl; intro v _; rw [Nat.sub_add_cancel (pos v)]
    rw [← Nat.cast_one (R:=ℝ),← Nat.cast_add,Nat.sub_add_cancel (pos v)]
  rw [sumform,mul_sum,sum_filter]; unfold shiftedPrefix
  push_cast; rw [sum_product]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro a _
  simp only [index,apply_ite,Rat.cast_zero,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  by_cases h : 2^a*5^j ≤ n
  · simp only [h,ite_true]; push_cast; rw [one_div_pow,pow_sub₀ _ (by norm_num) h]; field_simp
  · simp [h]

/-- The omitted positive tail is dominated by the ordinary logarithm tail at the same shift. -/
theorem shift_error (n : ℕ) :
    0 ≤ (2:ℝ)^n*value-shiftedPrefix n ∧ (2:ℝ)^n*value-shiftedPrefix n ≤ 1/(n+1:ℝ) := by
  let f (i : ℕ) := (1/2:ℝ)^(i+1)/(i+1)
  have eqLog : 2^n * ∑ i ∈ range n, f i = (logPrefix n:ℝ) := by
    induction n with
    | zero => simp [logPrefix]
    | succ n ih =>
      rw [sum_range_succ,mul_add,pow_succ',mul_assoc,ih]
      simp [logPrefix,f,pow_succ',mul_div_assoc',← mul_assoc]; field_simp
  have H : value = (∑ i ∈ range n, term i) + ∑' i, term (i+n) := summable_term.sum_add_tsum_nat_add n |>.symm
  have H' : Real.log 2 = (∑ i ∈ range n, f i) + ∑' i, f (i+n) :=
    hasSum_logTwo.tsum_eq ▸ (hasSum_logTwo.summable.sum_add_tsum_nat_add n).symm
  have cmp := ((summable_nat_add_iff n).mpr summable_term).tsum_le_tsum
    (fun i => (term_bounds (i+n)).2) ((summable_nat_add_iff n).mpr hasSum_logTwo.summable)
  rw [truncate,H,mul_add,add_sub_cancel_left]
  refine ⟨mul_nonneg (by positivity) (tsum_nonneg fun i => (term_bounds _).1),?_⟩
  apply (mul_le_mul_of_nonneg_left cmp (by positivity : 0≤(2:ℝ)^n)).trans
  have h := (logTwo_tail_bounds n).2
  rw [H',mul_add,eqLog,add_sub_cancel_left] at h; exact h

/-- On an interval with no new supported index the rational prefix evolves by doubling alone. -/
theorem prefix_orbit {s i : ℕ} (clean : ∀ m, s < m → m ≤ s+i → ¬Supported m) :
    (shiftedPrefix (s+i):ℝ) = (2:ℝ)^i*shiftedPrefix s := by
  rw [truncate,truncate,sum_range_add]
  have hz : ∑ j ∈ range i, term (s+j) = 0 := by
    apply sum_eq_zero; intro j hj; simp [term,clean (s+j+1) (by omega) (by have := mem_range.mp hj; omega)]
  rw [hz,add_zero,pow_add]; ring

/-- Once all inserted dyadic denominators have cleared, the whole reduced denominator
is a power of five dividing the largest available power. -/
theorem clean_denominator (n : ℕ) (clean : ∀ a j : ℕ, 2^a*5^j ≤ n → 2^a*5^j+a ≤ n) :
    (shiftedPrefix n).den ∣ 5^(Nat.log 5 n) := by
  let k := Nat.log 5 n
  let scaled := ∑ j ∈ range (k+1), ∑ a ∈ range (Nat.log 2 n+1),
    if 2^a*5^j ≤ n then 2^(n-(2^a*5^j+a))*5^(k-j) else 0
  apply (reduced_info (S:=scaled) (pow_pos (by decide : 0<5) k) _).1
  dsimp [scaled,shiftedPrefix]; simp only [Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,mul_sum]
  apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro a _
  by_cases h : 2^a*5^j ≤ n
  · simp only [h,ite_true,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_div_assoc']
    rw [eq_div_iff (by positivity)]
    have e := congrArg (fun t : ℕ => (2:ℚ)^t) (show n-(2^a*5^j+a)+a=n-2^a*5^j by have := clean a j h; omega)
    have d := congrArg (fun t : ℕ => (5:ℚ)^t) (Nat.sub_add_cancel (show j ≤ k by have := mem_range.mp hj; omega))
    simp only [pow_add] at e d
    linear_combination 5^(k-j)*5^j*e + 2^(n-2^a*5^j)*d
  · simp [h]

end NormalityChecker.LocalizedFive
