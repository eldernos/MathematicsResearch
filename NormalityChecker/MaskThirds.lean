module

public import NormalityChecker.MaskGrid
public import NormalityChecker.SharpDiscrepancy

/-! Exact discrepancy 2/3 for two rational-polynomial families on full supports. -/
@[expose] public section
open Finset Filter Polynomial
open scoped Topology
namespace NormalityChecker.PolynomialMasks

def Third (y : ℚ) : Prop := ∃ z : ℤ, 3*y=z ∧ ¬3∣z

private theorem third_shift {y : ℚ} (model : Third y) (i : ℕ) :
    ∃ z : ℤ, (1/3:ℝ) ≤ (2:ℝ)^i*y-z ∧ (2:ℝ)^i*y-z ≤ 2/3 := by
  obtain ⟨m,hm,unit⟩ := model
  let v : ℤ := 2^i*m
  have h3 : Prime (3:ℤ) := by norm_num
  have nonzero : ¬3∣v := by
    intro h
    rcases h3.dvd_mul.mp h with hit|hit
    · exact (by decide : ¬(3:ℤ)∣2) (h3.dvd_of_dvd_pow hit)
    · exact unit hit
  have rem := Int.emod_add_mul_ediv v 3
  have lo := Int.emod_nonneg v (by decide : (3:ℤ)≠0)
  have hi := Int.emod_lt_of_pos v (by decide : (0:ℤ)<3)
  have nz := mt Int.dvd_of_emod_eq_zero nonzero
  have rr : 1≤v%3 ∧ v%3≤2 := by omega
  have split : (v%3:ℤ)+3*(v/3)=v := rem
  have realSplit : ((v%3:ℤ):ℝ)+3*((v/3:ℤ):ℝ)=v := by exact_mod_cast split
  have scaled : (v:ℝ)=3*((2:ℝ)^i*y) := by
    have hr : 3*(y:ℝ)=m := by exact_mod_cast hm
    dsimp [v]; push_cast; rw [← hr]; ring
  refine ⟨v/3, ?_⟩
  have r₁ : (1:ℝ)≤(v%3:ℤ) := by exact_mod_cast rr.1
  have r₂ : ((v%3:ℤ):ℝ)≤2 := by exact_mod_cast rr.2
  constructor <;> linarith

/-- Binary shifts near the two nonzero thirds on clean blocks have limiting
discrepancy 2/3. The sharp binary transition inequality supplies the upper bound. -/
theorem thirds_discrepancy {S : Finset ℕ} {a : ℕ → ℚ} (growth : PolyGrowth a)
    (supp : ∀ m, m∉Nat.factoredNumbers S → a m=0)
    (thirds : ∀ᶠ k : ℕ in atTop, ∀ n, Clean S k n → Third (pre 2 a n)) :
    Tendsto (radixDiscrepancy 2 (series 2 a)) atTop (𝓝 (2/3)) := by
  classical
  let x := series 2 a
  have near {δ : ℝ} (pos : 0<δ) (small : δ≤1/12) :
      Tendsto (frequency (shift 2 x) (1/3-δ) (2/3+δ)) atTop (𝓝 1) := by
    let hit (n : ℕ) := 1/3-δ≤shift 2 x n ∧ shift 2 x n<2/3+δ
    have H := exceptional_frequency S (fun n => ¬hit n) (by
      filter_upwards [thirds,clean_approx (by decide : 2≤2) growth supp pos] with k model close n hn i hi
      obtain ⟨z,lo,up⟩ := third_shift (model n hn) i
      have err := abs_lt.mp (close n hn i hi)
      change -δ < (2:ℝ)^(n+i)*x-(2:ℝ)^i*(pre 2 a n:ℝ) ∧ (2:ℝ)^(n+i)*x-(2:ℝ)^i*(pre 2 a n:ℝ)<δ at err
      have lower : 1/3-δ ≤ (2:ℝ)^(n+i)*x-z := by linarith [err.1]
      have upper : (2:ℝ)^(n+i)*x-z < 2/3+δ := by linarith [err.2]
      apply not_not_intro
      dsimp [hit,shift]
      norm_num only [Nat.cast_ofNat] at *
      rw [← Int.fract_sub_intCast _ z,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]
      exact ⟨lower,upper⟩)
    have lim := tendsto_const_nhds (x:=(1:ℝ)) |>.sub H
    rw [sub_zero] at lim
    apply lim.congr'
    filter_upwards [eventually_gt_atTop 0] with N hn
    have sz := card_filter_add_card_filter_not (s:=range N) hit
    rw [card_range] at sz
    change 1-(((range N).filter (fun n => ¬hit n)).card:ℝ)/N=(((range N).filter hit).card:ℝ)/N
    have np : (N:ℝ)≠0 := by exact_mod_cast hn.ne'
    have realSz : (((range N).filter hit).card:ℝ)+(((range N).filter (fun n => ¬hit n)).card:ℝ)=N := by exact_mod_cast sz
    field_simp [np]; linarith
  have transF : Tendsto (transitionFrequency x) atTop (𝓝 1) := by
    convert near (by norm_num : (0:ℝ)<1/12) le_rfl using 1; norm_num [transitionFrequency]
  have upper := sharp_asymptotic_discrepancy x
  change limsup (radixDiscrepancy 2 x) atTop ≤ max (2/3) (1-liminf (transitionFrequency x) atTop) at upper
  rw [transF.liminf_eq,sub_self,max_eq_left (by norm_num)] at upper
  rw [tendsto_order]; constructor
  · intro y hy
    let δ := min (1/12:ℝ) ((2/3-y)/4)
    have dp : 0<δ := lt_min (by norm_num) (by linarith)
    have small : δ≤1/12 := min_le_left ..
    have tiny : δ≤(2/3-y)/4 := min_le_right ..
    filter_upwards [(tendsto_order.mp (near dp small)).1 _ (by linarith : 1-δ<1)] with N observed
    have I := interval_le_radix (b:=2) (N:=N) x (by linarith : 0≤1/3-δ)
      (by linarith : 1/3-δ<2/3+δ) (by linarith)
    have := (le_abs_self _).trans I
    change frequency (shift 2 x) _ _ N > 1-δ at observed
    change y<radixDiscrepancy 2 x N
    linarith
  · intro z hz
    exact eventually_lt_of_limsup_lt (upper.trans_lt hz)
      (isBoundedUnder_of_eventually_le (.of_forall fun N => (radix_discrepancy_bounds 2 x N).2))

private theorem singleton_smooth {p m : ℕ} (hp : p.Prime) :
    m ∈ Nat.factoredNumbers {p} ↔ ∃ j : ℕ, m=p^j := by
  constructor
  · intro hm
    let e := Nat.equivProdNatFactoredNumbers (s:=∅) hp (by simp)
    obtain ⟨⟨j,v⟩,hit⟩ := e.surjective ⟨m,hm⟩
    have eqn := congrArg Subtype.val hit
    change p^j*(v:ℕ)=m at eqn
    have one : (v:ℕ)=1 := by simpa using v.property
    exact ⟨j,by simpa [one] using eqn.symm⟩
  · rintro ⟨j,rfl⟩; simpa using Nat.pow_mul_mem_factoredNumbers (s:=∅) hp j (by simp : 1∈Nat.factoredNumbers ∅)

/-- The full ternary support with polynomial X²/3 and denominator m. -/
theorem ternary_linear_thirds :
    Tendsto (radixDiscrepancy 2 (maskedValue 2 {3} (fun _ => true) (C (1/3)*X^2) 1)) atTop (𝓝 (2/3)) := by
  let a := weights {3} (fun _ => true) (C (1/3)*X^2) 1
  apply thirds_discrepancy (weights_growth ..) (weights_supported _ _ _ _)
  filter_upwards with k n hn
  have pos := (pow_pos (by decide : 0<2) k).trans_le hn.start
  let v (m : ℕ) : ℤ := if m∈Nat.factoredNumbers {3} then (2:ℤ)^(n-m)*m else 0
  have total : 3*pre 2 a n = ((∑ m∈range (n+1),v m : ℤ):ℚ) := by
    simp only [pre,mul_sum,Int.cast_sum]; apply sum_congr rfl; intro m _
    by_cases sm : m∈Nat.factoredNumbers {3}
    · simp [a,weights,v,sm]; field_simp [sm.1]
    · simp [a,weights,v,sm]
  refine ⟨_,total,?_⟩
  have mem : 1∈range (n+1) := by simp; omega
  rw [← add_sum_erase _ _ mem]
  have other : (3:ℤ)∣∑ m ∈ (range (n+1)).erase 1,v m := by
    apply Finset.dvd_sum; intro m hm
    by_cases sm : m∈Nat.factoredNumbers {3}
    · obtain ⟨j,rfl⟩ := (singleton_smooth (by decide : Nat.Prime 3)).mp sm
      have ne := (mem_erase.mp hm).1
      cases j with
      | zero => simp at ne
      | succ j => dsimp [v]; rw [ite_eq_left sm]; exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
    · simp [v,sm]
  have first : v 1 = (2:ℤ)^(n-1) := by simp [v,((singleton_smooth (by decide : Nat.Prime 3)).mpr ⟨0,rfl⟩ : 1∈Nat.factoredNumbers {3})]
  rw [first]; intro divides
  have d := (dvd_add_left other).mp divides
  exact (by decide : ¬(3:ℤ)∣2) ((by norm_num : Prime (3:ℤ)).dvd_of_dvd_pow d)


private def depth (j : ℕ) := 2^j+j

private theorem depth_mono : Monotone depth := fun i j h =>
  Nat.add_le_add (Nat.pow_le_pow_right (by decide) h) h

private def numerator (j : ℕ) : ℤ := ∑ r ∈ range (j+1), (2:ℤ)^(depth j-depth r)

private theorem numerator_step (j : ℕ) :
    numerator (j+1) = (2:ℤ)^(2^j+1)*numerator j+1 := by
  have step : depth (j+1)=depth j+(2^j+1) := by simp [depth,pow_succ]; omega
  unfold numerator; rw [sum_range_succ,mul_sum]
  simp only [Nat.sub_self,pow_zero]; congr 1
  apply sum_congr rfl; intro r hr
  rw [← pow_add,step]
  have dr : depth r ≤ depth j := depth_mono (mem_range_succ_iff.mp hr)
  rw [Nat.add_comm (depth j), Nat.add_sub_assoc dr]

private theorem numerator_mod (j : ℕ) : (numerator (j+1) : ZMod 3)=2 := by
  induction j with
  | zero => decide +kernel
  | succ j ih =>
    rw [numerator_step (j+1)]; push_cast; rw [ih]
    have sq : (2:ZMod 3)^2=1 := by decide
    rw [pow_succ, pow_succ (2:ℕ), Nat.mul_comm _ 2, pow_mul, sq,one_pow]; decide

/-- The full dyadic support, weighted by 1/(3m), also has discrepancy 2/3.
At the common binary depth 2ʲ+j the numerator is 2 modulo 3 for every j≥1. -/
theorem dyadic_reciprocal_thirds :
    Tendsto (radixDiscrepancy 2 (maskedValue 2 {2} (fun _ => true) (C (1/3)) 1)) atTop (𝓝 (2/3)) := by
  let a := weights {2} (fun _ => true) (C (1/3)) 1
  apply thirds_discrepancy (weights_growth ..) (weights_supported _ _ _ _)
  have big (k : ℕ) (hk : 4≤k) : 2*(k+1) ≤ 2^k := by
    induction k,hk using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  filter_upwards [eventually_ge_atTop 4] with k hk n hn
  let J := Nat.log 2 n
  let B := 2^k
  have pos := (pow_pos (by decide : 0<2) k).trans_le hn.start
  have left : 2^J≤n := Nat.pow_log_le_self 2 pos.ne'
  have bound : n ≤ 2^(2*(k+1)) := by
    apply (Nat.le_add_right n B).trans (hn.bound.trans_eq _)
    rw [Nat.mul_add, Nat.mul_one,pow_add,Nat.mul_comm 2 k,pow_mul]; ring
  have eps : J≤B := ((pow_right_strictMono₀ (by decide : 1<2)).le_iff_le.mp (left.trans bound)).trans (big k hk)
  have smooth (j : ℕ) : 2^j ∈ Nat.factoredNumbers {2} :=
    (singleton_smooth Nat.prime_two).mpr ⟨j,rfl⟩
  have old := hn.old (2^J) (smooth J) (by have := pow_pos (by decide : 0<2) k; omega)
  have late : depth J ≤ n := by change 2^J+J ≤ n; change 2^J+B ≤ n at old; omega
  let I := (range (n+1)).filter (fun m => m∈Nat.factoredNumbers {2})
  have eqset : I = (range (J+1)).image (fun j => 2^j) := by
    ext m; simp only [I, mem_filter,mem_range_succ_iff,mem_image]
    constructor
    · rintro ⟨le,sm⟩; obtain ⟨j,rfl⟩ := (singleton_smooth Nat.prime_two).mp sm
      exact ⟨j,Nat.le_log_of_pow_le (by decide) le,rfl⟩
    · rintro ⟨j,hj,rfl⟩; exact ⟨(Nat.pow_le_pow_right (by decide) hj).trans left,smooth j⟩
  let z := (2:ℤ)^(n-depth J)*numerator J
  have total : 3*pre 2 a n=(z:ℚ) := by
    let f (m : ℕ) := (2:ℚ)^(n-m)/(m:ℚ)
    have eqn : 3*pre 2 a n = ∑ m∈I, f m := by
      rw [pre,mul_sum]; dsimp only [I]; rw [sum_filter]
      apply sum_congr rfl; intro m _; by_cases sm : m∈Nat.factoredNumbers {2}
      · simp [a,weights,f,sm]; ring
      · simp [a,weights,sm]
    rw [eqn,eqset,sum_image (fun i _ j _ h => (pow_right_strictMono₀ (by decide : 1<2)).injective h)]
    simp only [z,numerator,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_sum,mul_sum]
    apply sum_congr rfl; intro j hj
    have dj := depth_mono (mem_range_succ_iff.mp hj)
    have nj : depth j ≤ n := dj.trans late
    dsimp [f]; push_cast
    rw [← pow_add, show n-depth J+(depth J-depth j)=n-depth j by omega]
    rw [div_eq_iff (by positivity),← pow_add]; congr 1; dsimp [depth] at nj ⊢; omega
  refine ⟨z,total,?_⟩
  have nonzero : ¬(3:ℤ)∣numerator J := by
    cases J with
    | zero => decide +kernel
    | succ j =>
      intro div; have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr div
      rw [numerator_mod j] at h; contradiction
  intro div
  rcases (by norm_num : Prime (3:ℤ)).dvd_mul.mp div with h|h
  · exact (by decide : ¬(3:ℤ)∣2) ((by norm_num : Prime (3:ℤ)).dvd_of_dvd_pow h)
  · exact nonzero h

end NormalityChecker.PolynomialMasks
