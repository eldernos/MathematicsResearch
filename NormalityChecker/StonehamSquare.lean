module

public import NormalityChecker.ArithmeticCertificate
public import NormalityChecker.PrimeCancellation
public import Mathlib.Analysis.Normed.Group.Tannery

/-! The true shifted prefixes and exact denominator profile of the binary Stoneham square. -/
@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker.StonehamSquare

/-- Exponents are indexed from zero, so the first insertion of the square is at six. -/
def location (v : ℕ × ℕ) := 3^(v.1+1) + 3^(v.2+1)
def degree (v : ℕ × ℕ) := (v.1+1) + (v.2+1)
def active (n : ℕ) := ((range (Nat.log 3 n)) ×ˢ (range (Nat.log 3 n))).filter
  (fun v => location v ≤ n)

lemma mem_active {n : ℕ} {v : ℕ × ℕ} : v ∈ active n ↔ location v ≤ n := by
  refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,h⟩⟩
  · exact mem_range.mpr (Nat.le_log_of_pow_le (by decide) ((Nat.le_add_right ..).trans h))
  · exact mem_range.mpr (Nat.le_log_of_pow_le (by decide) ((Nat.le_add_left ..).trans h))

/-- The reduced denominator of this rational measures the retained ternary power. -/
def pre (n : ℕ) : ℚ := ∑ v ∈ active n, (2:ℚ)^(n-location v)/(3:ℚ)^(degree v)

noncomputable def alpha : ℝ :=
  ∑' j : ℕ, 1 / ((3:ℝ)^(j+1)*(2:ℝ)^(3^(j+1):ℕ))

/-- The error is the actual shifted tail of the square, summed over ordered pairs. -/
theorem shifted_tail : Tendsto (fun n : ℕ => (2:ℝ)^n * alpha^2 - (pre n:ℝ)) atTop (𝓝 0) := by
  let a (j : ℕ) := 1 / ((3:ℝ)^(j+1)*(2:ℝ)^(3^(j+1):ℕ))
  let c (j : ℕ) := (1/3:ℝ)^(j+1)
  have cp (j : ℕ) : 0 ≤ c j := by dsimp [c]; positivity
  have ap (j : ℕ) : 0 ≤ a j := by dsimp [a]; positivity
  have major (j : ℕ) : a j ≤ c j := by
    dsimp [a,c]
    rw [one_div_pow, ← div_div]
    exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  have sc : Summable c := (summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num))
  have sa := sc.of_nonneg_of_le ap major
  have sp := sa.mul_of_nonneg sa ap ap
  have prod : alpha^2 = ∑' v : ℕ × ℕ, a v.1 * a v.2 := by
    rw [pow_two]; exact sa.tsum_mul_tsum sa sp
  let tail (n : ℕ) (v : ℕ × ℕ) := if location v ≤ n then 0 else
    (2:ℝ)^n * (a v.1 * a v.2)
  have form (n : ℕ) (v : ℕ × ℕ) :
      (2:ℝ)^n * (a v.1 * a v.2) = (2:ℝ)^n / ((3:ℝ)^degree v * (2:ℝ)^location v) := by
    simp [a,degree,location,pow_add]; ring
  have dom (n : ℕ) (v : ℕ × ℕ) : ‖tail n v‖ ≤ c v.1 * c v.2 := by
    dsimp only [tail]
    split_ifs with incl
    · simpa using mul_nonneg (cp _) (cp _)
    · rw [form,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have pow : (2:ℝ)^n ≤ 2^location v := pow_le_pow_right₀ (by norm_num) (by omega)
      dsimp [c]
      rw [one_div_pow,one_div_pow,div_le_iff₀ (by positivity)]
      apply pow.trans_eq
      rw [degree,pow_add]
      field_simp
      simp [pow_add,mul_assoc]
  have decay := tendsto_tsum_of_dominated_convergence (g:=fun _ : ℕ × ℕ => (0:ℝ))
    (sc.mul_of_nonneg sc cp cp) (f:=tail) (fun v => tendsto_const_nhds.congr'
      ((eventually_ge_atTop (location v)).mono fun n hn => by simp [tail,hn])) (.of_forall dom)
  simp only [tsum_zero] at decay
  apply decay.congr
  intro n
  change (∑' v, tail n v) = _
  have spl (v : ℕ × ℕ) : (2:ℝ)^n*(a v.1*a v.2) = tail n v +
      (if v ∈ active n then (2:ℝ)^(n-location v)/(3:ℝ)^(degree v) else 0) := by
    dsimp only [tail]
    by_cases incl : location v ≤ n
    · simp only [mem_active,incl,ite_true,zero_add,form,pow_sub₀ _ (by norm_num : (2:ℝ) ≠ 0) incl]
      ring
    · simp [mem_active,incl]
  have fin : Summable (fun v : ℕ × ℕ => if v ∈ active n then
      (2:ℝ)^(n-location v)/(3:ℝ)^(degree v) else 0) :=
    summable_of_ne_finset_zero (s:=active n) (fun _ h => by simp [h])
  have eqn := (Summable.of_norm_bounded (sc.mul_of_nonneg sc cp cp) (dom n)).tsum_add fin
  simp_rw [← spl] at eqn
  have finiteEq : (∑' v, if v ∈ active n then (2:ℝ)^(n-location v)/(3:ℝ)^degree v else 0)
      = ∑ v ∈ active n, (2:ℝ)^(n-location v)/(3:ℝ)^degree v := by
    rw [tsum_eq_sum (s:=active n) (fun _ h => by simp [h])]
    exact sum_congr rfl (fun v hv => ite_eq_left hv)
  rw [tsum_mul_left, ← prod, finiteEq] at eqn
  simp only [pre,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  rw [eqn]
  simp

theorem follows {n i : ℕ} (free : ∀ v, n < location v → n+i < location v) :
    pre (n+i) = (2:ℚ)^i * pre n := by
  have same : active (n+i) = active n := by
    ext v; rw [mem_active,mem_active]; constructor
    · intro h; exact le_of_not_gt (fun gt => (free v gt).not_ge h)
    · omega
  simp only [pre,same,mul_sum]
  apply sum_congr rfl; intro v hv
  have lo := mem_active.mp hv
  rw [show n+i-location v = i+(n-location v) by omega,pow_add,mul_div_assoc]

def numerator (n D : ℕ) := ∑ v ∈ active n, 2^(n-location v)*3^(D-degree v)

lemma scaled_pre {n D : ℕ} (cap : ∀ v ∈ active n, degree v ≤ D) :
    pre n = (numerator n D : ℚ) / 3^D := by
  rw [eq_div_iff (by positivity)]
  simp only [pre,numerator,sum_mul,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply sum_congr rfl; intro v hv
  rw [pow_sub₀ _ (by norm_num : (3:ℚ) ≠ 0) (cap v hv)]
  ring

private lemma six_dvd (v : ℕ × ℕ) : 6 ∣ location v := by
  have pow (j : ℕ) : 3^(j+1) % 6 = 3 := by
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ (3:ℕ) (j+1),Nat.mul_mod,ih]
  simp [Nat.dvd_iff_mod_eq_zero,location,Nat.add_mod,pow]

private lemma timing {m n : ℕ} (v : ℕ × ℕ) (active : location v ≤ n)
    (order : (2:ZMod m)^6=1) : (2:ZMod m)^(n-location v) = 2^n := by
  obtain ⟨t,ht⟩ := six_dvd v
  have unit : (2:ZMod m)^location v=1 := by rw [ht,pow_mul,order,one_pow]
  calc _ = (2:ZMod m)^(n-location v)*2^location v := by rw [unit,mul_one]
       _ = _ := by rw [← pow_add,Nat.sub_add_cancel active]

def layer (n D : ℕ) := (active n).filter (fun v => degree v = D)

private lemma residue_three {n D : ℕ} (cap : ∀ v ∈ active n, degree v ≤ D) :
    (numerator n D : ZMod 3) = 2^n * (layer n D).card := by
  simp only [numerator,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show ((layer n D).card:ZMod 3) = ∑ v ∈ active n, if degree v=D then 1 else 0 by simp [layer],mul_sum]
  apply sum_congr rfl; intro v h
  rw [timing v (mem_active.mp h) (by decide)]
  by_cases eq : degree v=D
  · simp [eq]
  · simp [eq,zero_pow (by have := cap v h; omega : D-degree v ≠ 0),show (3:ZMod 3)=0 by decide]

private lemma residue_nine {n D : ℕ} (pos : 0<D) (cap : ∀ v ∈ active n, degree v ≤ D) :
    (numerator n D : ZMod 9) = 2^n * ((layer n D).card + 3*(layer n (D-1)).card) := by
  simp only [numerator,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have cards (j : ℕ) : ((layer n j).card:ZMod 9) = ∑ v ∈ active n, if degree v=j then 1 else 0 := by simp [layer]
  rw [cards,cards,mul_sum,← sum_add_distrib,mul_sum]
  apply sum_congr rfl; intro v h
  rw [timing v (mem_active.mp h) (by decide)]
  have le := cap v h
  by_cases eq : degree v=D
  · simp [eq,show D≠D-1 by omega]
  by_cases next : degree v=D-1
  · simp [next,show D-(D-1)=1 by omega,show D-1≠D by omega]
  · have low : 2 ≤ D-degree v := by omega
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le low
    simp [eq,next,he,pow_add,show (3:ZMod 9)^2=0 by decide]

private lemma exact_den {n D : ℕ} (cap : ∀ v ∈ active n, degree v ≤ D)
    (unit : ¬3∣numerator n D) : (pre n).den = 3^D := by
  have cop := (Nat.prime_three.coprime_iff_not_dvd.mpr unit).symm.pow_right D
  rw [scaled_pre cap]
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat,Int.cast_pow,Int.cast_ofNat] using (Rat.den_div_eq_of_coprime (a:=(numerator n D:ℕ)) (b:=((3^D:ℕ):ℤ))
    (by positivity) (by simpa using cop))

private lemma den_of_layer {n D : ℕ} (cap : ∀ v ∈ active n, degree v ≤ D)
    (unit : ((layer n D).card:ZMod 3) ≠ 0) : (pre n).den = 3^D := by
  apply exact_den cap
  intro dvd
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr dvd
  rw [residue_three cap] at hz
  exact (mul_ne_zero (pow_ne_zero _ (by decide : (2:ZMod 3)≠0)) unit) hz

private lemma den_of_first_loss {n D : ℕ} (dp : 0 < D) (cap : ∀ v ∈ active n, degree v ≤ D)
    (top : (layer n D).card = 3) (next : (layer n (D-1)).card = 4) : (pre n).den = 3^(D-1) := by
  let a := numerator n D
  have dvd : 3 ∣ a := (ZMod.natCast_eq_zero_iff ..).mp (by rw [show (a:ZMod 3) = _ from residue_three cap, top]; change (2:ZMod 3)^n * 3 = 0; rw [show (3:ZMod 3)=0 by decide,mul_zero])
  obtain ⟨v,hv⟩ := dvd
  have unit : ¬3∣v := by
    intro h
    have dvd9 : 9 ∣ a := hv ▸ (Nat.mul_dvd_mul_left 3 h)
    have hz := (ZMod.natCast_eq_zero_iff ..).mpr dvd9
    change (numerator n D:ZMod 9) = 0 at hz
    rw [residue_nine dp cap,top,next] at hz
    have bu := ((ZMod.isUnit_iff_coprime 2 9).mpr (by decide)).pow n
    have clear := bu.mul_right_inj.mp (hz.trans (mul_zero _).symm)
    exact (by decide : (3+3*4:ZMod 9)≠0) clear
  have eqn : pre n = (v:ℚ)/3^(D-1) := by
    rw [scaled_pre cap]
    change (a:ℚ)/3^D=_
    rw [hv,Nat.cast_mul,Nat.cast_ofNat,pow_sub₀ _ (by norm_num) dp,pow_one]
    ring
  rw [eqn]
  have cop := (Nat.prime_three.coprime_iff_not_dvd.mpr unit).symm.pow_right (D-1)
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat,Int.cast_pow,Int.cast_ofNat] using (Rat.den_div_eq_of_coprime (a:=(v:ℤ)) (b:=((3^(D-1):ℕ):ℤ)) (by positivity) (by simpa using cop))

/-- On scale `k+4`, the old square of exponents is full. Each new arm has
one maximal coordinate. The parameter `m` is the last zero-based arm index. -/
private def shape (k m : ℕ) (v : ℕ × ℕ) : Prop :=
  v.1 ≤ k+3 ∧ v.2 ≤ k+3 ∧ (v.1 = k+3 → v.2 ≤ m) ∧ (v.2 = k+3 → v.1 ≤ m)

private lemma outer {k n : ℕ} (hi : n < 3^(k+5)) {v : ℕ × ℕ} (hv : v ∈ active n) :
    v.1 ≤ k+3 ∧ v.2 ≤ k+3 := by
  have h := (mem_active.mp hv).trans_lt hi
  have left := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp ((Nat.le_add_right ..).trans_lt h)
  have right := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp ((Nat.le_add_left ..).trans_lt h)
  omega

private lemma arm_cap {k m n : ℕ} (hi : n < 3^(k+5)) (cut : n < 3^(k+4)+3^(m+2))
    {v : ℕ × ℕ} (hv : v ∈ active n) : shape k m v := by
  obtain ⟨a,b⟩ := outer hi hv
  have h := (mem_active.mp hv).trans_lt cut
  dsimp [location] at h
  refine ⟨a,b,?_,?_⟩
  · intro eq; rw [eq,Nat.add_lt_add_iff_left] at h
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp h; omega
  · intro eq; rw [eq, Nat.add_comm _ (3^(k+3+1)),Nat.add_lt_add_iff_left] at h
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp h; omega

private lemma old_mem {k n i j : ℕ} (lo : 3^(k+4) ≤ n) (hi : i ≤ k+2) (hj : j ≤ k+2) :
    (i,j) ∈ active n := by
  apply mem_active.mpr
  have a : 3^(i+1) ≤ 3^(k+3) := Nat.pow_le_pow_right (by decide) (by omega)
  have b : 3^(j+1) ≤ 3^(k+3) := Nat.pow_le_pow_right (by decide) (by omega)
  change 3^(i+1)+3^(j+1) ≤ n
  rw [pow_succ (3:ℕ) (k+3)] at lo
  omega

private lemma shape_mem {k m n : ℕ} (lo : 3^(k+4)+3^(m+1) ≤ n) {v : ℕ × ℕ}
    (hv : shape k m v) : v ∈ active n := by
  obtain ⟨a,b,left,right⟩ := hv
  rcases v with ⟨i,j⟩
  dsimp only at *
  by_cases eq : i=k+3
  · apply mem_active.mpr; change 3^(i+1)+3^(j+1) ≤ n
    rw [eq]
    exact (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ (left eq))) _).trans lo
  by_cases eq' : j=k+3
  · apply mem_active.mpr; change 3^(i+1)+3^(j+1) ≤ n
    rw [eq',add_comm]
    exact (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ (right eq'))) _).trans lo
  exact old_mem ((Nat.le_add_right ..).trans lo) (by omega) (by omega)

private lemma layer_on_window {k m n D : ℕ} {U : Finset (ℕ × ℕ)}
    (incl : ∀ v ∈ active n, shape k m v) (full : ∀ v, shape k m v → v ∈ active n)
    (eqn : ∀ i j : ℕ, (shape k m (i,j) ∧ degree (i,j)=D) ↔ (i,j) ∈ U) :
    layer n D = U := by
  ext ⟨i,j⟩
  rw [layer,mem_filter,← eqn]
  exact and_congr_left fun _ => ⟨incl _,full _⟩

/-- All four intervals include the left endpoint. The exponent labels in this
statement use `k+4` for the logarithmic scale, hence cover every scale from 4 on. -/
theorem exact_profile (k n : ℕ) (lo : 3^(k+4) ≤ n) (hi : n < 3^(k+5)) :
    (pre n).den =
      if n < 3^(k+4)+3^(k+2) then 3^(2*k+6)
      else if n < 3^(k+4)+3^(k+3) then 3^(2*k+5)
      else if n < 2*3^(k+4) then 3^(2*k+7)
      else 3^(2*k+8) := by
  split_ifs with first second third
  · have incl := fun v (h : v ∈ active n) => arm_cap (m:=k) hi first h
    have cap (v : ℕ × ℕ) (h : v ∈ active n) : degree v ≤ 2*k+6 := by
      obtain ⟨a,b,c,d⟩ := incl v h; dsimp [degree]; omega
    apply den_of_layer cap
    have top : layer n (2*k+6) = {(k+2,k+2)} := by
      ext ⟨i,j⟩
      change ((i,j) ∈ (active n).filter (fun v => degree v = 2*k+6)) ↔ _
      rw [mem_filter,mem_singleton,Prod.mk.injEq]
      dsimp only [degree]
      constructor
      · rintro ⟨h,e⟩; obtain ⟨a,b,c,d⟩ := incl (i,j) h; dsimp only at *; omega
      · rintro ⟨rfl,rfl⟩; exact ⟨old_mem lo le_rfl le_rfl,by omega⟩
    simp [top]
  · have incl := fun v (h : v ∈ active n) => arm_cap (m:=k+1) hi second h
    have full := fun v => shape_mem (k:=k) (m:=k+1) (n:=n) (le_of_not_gt first) (v:=v)
    have cap (v : ℕ × ℕ) (h : v ∈ active n) : degree v ≤ 2*k+6 := by
      obtain ⟨a,b,c,d⟩ := incl v h; dsimp [degree]; omega
    let top : Finset (ℕ × ℕ) := {(k+2,k+2),(k+3,k+1),(k+1,k+3)}
    let next : Finset (ℕ × ℕ) := {(k+2,k+1),(k+1,k+2),(k+3,k),(k,k+3)}
    have ht : layer n (2*k+6) = top := layer_on_window incl full (by
      intro i j; simp only [shape,degree,top,mem_insert,mem_singleton,Prod.mk.injEq]; omega)
    have hn : layer n (2*k+6-1) = next := layer_on_window incl full (by
      intro i j; simp only [shape,degree,next,mem_insert,mem_singleton,Prod.mk.injEq]; omega)
    apply den_of_first_loss (D:=2*k+6) (by omega) cap
    · rw [ht]; simp [top]
    · rw [hn]; simp [next]
  · have bound : n < 3^(k+4) + 3^(k+4) := by omega
    have incl := fun v (h : v ∈ active n) => arm_cap (m:=k+2) hi bound h
    have full := fun v => shape_mem (k:=k) (m:=k+2) (n:=n) (le_of_not_gt second) (v:=v)
    have cap (v : ℕ × ℕ) (h : v ∈ active n) : degree v ≤ 2*k+7 := by
      obtain ⟨a,b,c,d⟩ := incl v h; dsimp [degree]; omega
    have ht : layer n (2*k+7) = {(k+3,k+2),(k+2,k+3)} := layer_on_window incl full (by
      intro i j; simp only [shape,degree,mem_insert,mem_singleton,Prod.mk.injEq]; omega)
    apply den_of_layer cap
    rw [ht]; simp; decide
  · have incl (v : ℕ × ℕ) (h : v ∈ active n) : shape k (k+3) v :=
      ⟨(outer hi h).1,(outer hi h).2,fun _ => (outer hi h).2,fun _ => (outer hi h).1⟩
    have bound : 3^(k+4)+3^(k+4) ≤ n := by omega
    have full := fun v => shape_mem (k:=k) (m:=k+3) (n:=n) bound (v:=v)
    have cap (v : ℕ × ℕ) (h : v ∈ active n) : degree v ≤ 2*k+8 := by
      obtain ⟨a,b⟩ := outer hi h; dsimp [degree]; omega
    have ht : layer n (2*k+8) = {(k+3,k+3)} := layer_on_window incl full (by
      intro i j; simp only [shape,degree,mem_singleton,Prod.mk.injEq]; omega)
    apply den_of_layer cap
    simp [ht]

/-- The second interval on the third scale is a genuine small-scale exception. -/
theorem third_scale_exception : (pre 30).den=9 ∧ (pre 35).den=9 ∧ (pre 36).den=243 := by
  decide +kernel

/-- Exact initial denominator profile, including every digit in the exceptional
third scale and the empty prefixes before the first insertion. -/
theorem initial_profile : ∀ n : Fin 81, (pre n.val).den =
    if n.val < 6 then 1 else if n.val < 12 then 9 else if n.val < 18 then 27
    else if n.val < 30 then 81 else if n.val < 36 then 9 else if n.val < 54 then 243 else 729 := by
  decide +kernel

/-- The reduced prefix denominators grow quadratically at every late digit. -/
theorem quadratic_denominator {n : ℕ} (large : 81 ≤ n) :
    n^2 < 243*(pre n).den ∧ (pre n).den ≤ n^2 := by
  have big : 4 ≤ Nat.log 3 n := Nat.le_log_of_pow_le (by decide) large
  let k := Nat.log 3 n - 4
  have eqn : k+4 = Nat.log 3 n := Nat.sub_add_cancel big
  have lo : 3^(k+4) ≤ n := by rw [eqn]; exact Nat.pow_log_le_self _ (by omega)
  have hi : n < 3^(k+5) := by rw [show k+5=Nat.log 3 n+1 by omega]; exact Nat.lt_pow_succ_log_self (by decide) _
  have pf := exact_profile k n lo hi
  have lower : 3^(2*k+5) ≤ (pre n).den := by
    rw [pf]; split_ifs <;> apply Nat.pow_le_pow_right (by decide) <;> omega
  have upper : (pre n).den ≤ 3^(2*k+8) := by
    rw [pf]; split_ifs <;> apply Nat.pow_le_pow_right (by decide) <;> omega
  constructor
  · calc n^2 < (3^(k+5))^2 := Nat.pow_lt_pow_left hi (by decide)
         _ = 243*3^(2*k+5) := by
           rw [← pow_mul,show (k+5)*2=5+(2*k+5) by omega,pow_add]; rfl
         _ ≤ _ := Nat.mul_le_mul_left _ lower
  · apply upper.trans
    rw [show 2*k+8=(k+4)*2 by omega,pow_mul]
    exact Nat.pow_le_pow_left lo _

private lemma den_range {n : ℕ} (np : 0<n) (big : 4 ≤ Nat.log 3 n) :
    ∃ e, (pre n).den=3^e ∧ Nat.log 3 n ≤ e ∧ e ≤ 2*Nat.log 3 n := by
  let k := Nat.log 3 n - 4
  have eqn : k+4 = Nat.log 3 n := Nat.sub_add_cancel big
  have pf := exact_profile k n (by rw [eqn]; exact Nat.pow_log_le_self _ np.ne') (by
    rw [show k+5=Nat.log 3 n+1 by omega]; exact Nat.lt_pow_succ_log_self (by decide) _)
  split_ifs at pf <;> exact ⟨_,pf,by omega,by omega⟩

/-- The square of the Stoneham series starting at exponent one is binary normal. -/
theorem binary_normal : NormalIn 2 (alpha^2) := by
  apply normal_of_arithmetic_certificate (c:=3) (B:=3) (L:=3) (by decide) (by decide)
    (by decide) _ pre shifted_tail (fixed_support_orbit_estimate (by decide) (by decide) (by decide)) 6
  intro u hu M η pos
  have dec := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<3)).const_mul 32
  simp only [mul_zero] at dec
  filter_upwards [eventually_ge_atTop (max M 4), dec.eventually_le_const pos] with k hk small
  let B := 3^k
  let S := ((range (2*(k+1))) ×ˢ (range (2*(k+1)))).image location
  let E := insertionBlocks S B (u*B)
  have kp : 1 ≤ k := by omega
  have bp : 0<B := pow_pos (by decide) _
  have cnt : S.card ≤ (2*(k+1))^2 := by simpa [S,pow_two] using
    (card_image_le (s:=(range (2*(k+1))) ×ˢ (range (2*(k+1)))) (f:=location))
  have exp : ((9:ℕ)^(k+1)) = 3^(2*(k+1)) := by rw [pow_mul]; rfl
  have cover (v : ℕ × ℕ) (h : location v < 9^(k+1)) : location v ∈ S := by
    rw [exp] at h
    have a := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp ((Nat.le_add_right ..).trans_lt h)
    have b := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp ((Nat.le_add_left ..).trans_lt h)
    exact mem_image.mpr ⟨v,mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,rfl⟩
  refine ⟨E,?_,?_⟩
  · have bound := (card_insertionBlocks S B (u*B)).trans (Nat.mul_le_mul_left 2 cnt)
    have kr : (1:ℝ) ≤ k := by exact_mod_cast kp
    have price : (E.card:ℝ) ≤ 32*(k:ℝ)^2 := by
      have bd : (E.card:ℝ) ≤ 2*(2*((k:ℝ)+1))^2 := by exact_mod_cast bound
      exact bd.trans (by nlinarith [sq_nonneg ((k:ℝ)-1)])
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at small
    exact price.trans small
  · intro l hl good
    let n := (u*B+l)*B
    have un : 1 ≤ u := (mem_Ico.mp hu).1
    have uu : u < 9 := (mem_Ico.mp hu).2
    have lo : 3^(2*k) ≤ n := by
      rw [Nat.mul_comm 2 k,pow_mul,pow_two]
      apply Nat.mul_le_mul_right
      exact (Nat.le_mul_of_pos_left B un).trans (Nat.le_add_right ..)
    have hi : n+B ≤ 9^(k+1) := by
      have eqn : B*B = 9^k := by rw [← mul_pow]; rfl
      calc n+B = (u*B+l+1)*B := by dsimp [n]; ring
           _ ≤ ((u+1)*B)*B := by apply Nat.mul_le_mul_right; rw [Nat.add_mul,one_mul]; change l<B at hl; omega
           _ = (u+1)*(B*B) := Nat.mul_assoc ..
           _ ≤ 9*(B*B) := Nat.mul_le_mul_right _ uu
           _ = _ := by rw [eqn,pow_succ']
    have kj := Nat.le_log_of_pow_le (by decide : 1<3) lo
    have np := (pow_pos (by decide : 0<3) _).trans_le lo
    have top : Nat.log 3 n < 2*(k+1) := Nat.log_lt_of_lt_pow np.ne' (by rw [← exp]; omega)
    obtain ⟨e,den,low,up⟩ := den_range np (by omega)
    change M ≤ (pre n).den ∧ _ ∧ _ ∧ _
    refine ⟨den ▸ ((by omega : M ≤ e).trans (Nat.lt_pow_self (by decide : 1<3)).le),
      ⟨e,den ▸ dvd_rfl⟩,?_,?_⟩
    · change (pre n).den ≤ (3^k)^6
      rw [den,← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · intro i hi'
      change pre (n+i) = (2:ℚ)^i*pre n
      apply follows
      intro v gt
      by_contra! inc
      have ne := insertionBlocks_free bp good (cover v (by change i<B at hi'; omega)) (by
        rw [Nat.add_mul,one_mul]
        change location v < n+B
        change i<B at hi'
        omega)
      change location v + B ≤ n at ne
      omega

end NormalityChecker.StonehamSquare
