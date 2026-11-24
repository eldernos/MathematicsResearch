module

public import NormalityChecker.ProductThreeFivePrefix
public import NormalityChecker.ProductThreeFiveStatements
public import NormalityChecker.PrimeCancellation

/-! Exact top-row and top-column tests for the binary product prefix. -/
@[expose] public section
open Finset
namespace NormalityChecker.ProductThreeFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Numerator on the common denominator 3^K 5^L, where K and L are the
integer logarithms of the digit position. This includes every ordered pair. -/
def commonNum (n : ℕ) : ℕ := ∑ v ∈ active n,
  2^(n-location v) * 3^(Nat.log 3 n-(v.1+1)) * 5^(Nat.log 5 n-(v.2+1))

theorem commonNum_eq (n : ℕ) :
    (commonNum n : ℚ) = pre n * (3:ℚ)^Nat.log 3 n * (5:ℚ)^Nat.log 5 n := by
  rw [commonNum,pre,sum_mul,sum_mul,Nat.cast_sum]
  apply sum_congr rfl
  intro v hv
  obtain ⟨hi,hj⟩ := mem_product.mp (mem_filter.mp hv).1
  have h₃ := Nat.sub_add_cancel (mem_range.mp hi : v.1+1 ≤ Nat.log 3 n)
  have h₅ := Nat.sub_add_cancel (mem_range.mp hj : v.2+1 ≤ Nat.log 5 n)
  simp only [weightDen,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp
  rw [← h₃, ← h₅]
  simp only [Nat.add_sub_cancel,pow_add,pow_succ]
  ring

/-- To any prescribed ternary precision, sum only the active rows within
that many layers of the top. No hypothesis on the opposite endpoints is needed. -/
theorem ternary_layers (n h : ℕ) :
    (commonNum n : ZMod (3^h)) =
      ∑ v ∈ (active n).filter (fun v => Nat.log 3 n-(v.1+1)<h),
        ((2^(n-location v)*3^(Nat.log 3 n-(v.1+1))*5^(Nat.log 5 n-(v.2+1)):ℕ) : ZMod (3^h)) := by
  rw [commonNum,Nat.cast_sum]
  symm
  apply sum_subset (filter_subset ..)
  intro v hv missing
  have le : h ≤ Nat.log 3 n-(v.1+1) := by
    simpa only [mem_filter,hv,true_and,not_lt] using missing
  exact (ZMod.natCast_eq_zero_iff ..).mpr
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow 3 le) _) _)

/-- The analogous quinary test uses only the top active columns. -/
theorem quinary_layers (n h : ℕ) :
    (commonNum n : ZMod (5^h)) =
      ∑ v ∈ (active n).filter (fun v => Nat.log 5 n-(v.2+1)<h),
        ((2^(n-location v)*3^(Nat.log 3 n-(v.1+1))*5^(Nat.log 5 n-(v.2+1)):ℕ) : ZMod (5^h)) := by
  rw [commonNum,Nat.cast_sum]
  symm
  apply sum_subset (filter_subset ..)
  intro v hv missing
  have le : h ≤ Nat.log 5 n-(v.2+1) := by
    simpa only [mem_filter,hv,true_and,not_lt] using missing
  exact (ZMod.natCast_eq_zero_iff ..).mpr (dvd_mul_of_dvd_right (pow_dvd_pow 5 le) _)

private def rowTerm (j : ℕ) : ZMod 3 := ((5:ZMod 3)^(j+1)*2^(5^(j+1):ℕ))⁻¹
private def colTerm (i : ℕ) : ZMod 5 := ((3:ZMod 5)^(i+1)*2^(3^(i+1):ℕ))⁻¹

private lemma row_period (j : ℕ) : rowTerm (j+2) = rowTerm j := by
  unfold rowTerm
  rw [show j+2+1=j+1+2 by omega,pow_add (5:ZMod 3) _ 2,pow_add (5:ℕ) _ 2,
    Nat.mul_comm (5^(j+1)),pow_mul,
    show (5:ZMod 3)^2=1 by decide, mul_one,
    show (2:ZMod 3)^(5^2:ℕ)=2 by decide]

private lemma col_period (i : ℕ) : colTerm (i+4) = colTerm i := by
  unfold colTerm
  rw [show i+4+1=i+1+4 by omega,pow_add (3:ZMod 5) _ 4,pow_add (3:ℕ) _ 4,
    Nat.mul_comm (3^(i+1)),pow_mul,
    show (3:ZMod 5)^4=1 by decide, mul_one,
    show (2:ZMod 5)^(3^4:ℕ)=2 by decide]

private lemma row_sum (m : ℕ) :
    ∑ j ∈ range m, rowTerm j = (if m%2=0 then 0 else 1) := by
  have step (m : ℕ) : rowTerm m = rowTerm (m%2) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases h : m<2
      · rw [Nat.mod_eq_of_lt h]
      · obtain ⟨a,rfl⟩ : ∃ a, m=a+2 := ⟨m-2,by omega⟩
        rw [row_period,ih a (by omega)]; simp
  have v0 : rowTerm 0 = 1 := ZMod.inv_eq_of_mul_eq_one _ _ _ (by decide)
  have v1 : rowTerm 1 = 2 := ZMod.inv_eq_of_mul_eq_one _ _ _ (by decide)
  induction m with
  | zero => decide
  | succ m ih =>
    rw [sum_range_succ,ih,step]
    have h : m%2<2 := Nat.mod_lt _ (by decide)
    interval_cases e : m%2 <;> simp [Nat.add_mod m 1 2,e,v0,v1]
    decide

/-- Prefix sums of the four quinary column residues, indexed modulo four. -/
def colWeight (r : ℕ) : ℕ := if r%4=0 then 0 else if r%4=1 then 4 else if r%4=2 then 1 else 2

private lemma col_sum (m : ℕ) :
    ∑ i ∈ range m, colTerm i = colWeight m := by
  have step (m : ℕ) : colTerm m = colTerm (m%4) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases h : m<4
      · rw [Nat.mod_eq_of_lt h]
      · obtain ⟨a,rfl⟩ : ∃ a, m=a+4 := ⟨m-4,by omega⟩
        rw [col_period,ih a (by omega)]; simp
  have v0 : colTerm 0 = 4 := ZMod.inv_eq_of_mul_eq_one _ _ _ (by decide)
  have v1 : colTerm 1 = 2 := ZMod.inv_eq_of_mul_eq_one _ _ _ (by decide)
  have v2 : colTerm 2 = 1 := ZMod.inv_eq_of_mul_eq_one _ _ _ (by decide)
  have v3 : colTerm 3 = 3 := ZMod.inv_eq_of_mul_eq_one _ _ _ (by decide)
  induction m with
  | zero => decide
  | succ m ih =>
    rw [sum_range_succ,ih,step]
    have h : m%4<4 := Nat.mod_lt _ (by decide)
    unfold colWeight
    interval_cases e : m%4 <;> simp [Nat.add_mod m 1 4,e,v0,v1,v2,v3] <;> decide

private lemma row_slice {n k : ℕ} (hk : k+1=Nat.log 3 n) :
    (active n).filter (fun v => v.1=k) =
      (range (Nat.log 5 (n-3^(k+1)))).image (fun j => (k,j)) := by
  have p : 3^(k+1) ≤ n := by
    rw [hk]; apply Nat.pow_log_le_self; rintro rfl; simp at hk
  ext ⟨i,j⟩
  simp only [mem_filter,mem_active,location,mem_image,mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨j,Nat.le_log_of_pow_le (by decide) (by omega : 5^(j+1)≤n-3^(i+1)),rfl,rfl⟩
  · rintro ⟨j',hj,rfl,rfl⟩
    have pos : 0<n-3^(k+1) := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hj
    have h := (Nat.pow_le_pow_right (by decide : 0<5) hj).trans (Nat.pow_log_le_self 5 pos.ne')
    exact ⟨by omega,rfl⟩

private lemma col_slice {n l : ℕ} (hl : l+1=Nat.log 5 n) :
    (active n).filter (fun v => v.2=l) =
      (range (Nat.log 3 (n-5^(l+1)))).image (fun i => (i,l)) := by
  have q : 5^(l+1) ≤ n := by
    rw [hl]; apply Nat.pow_log_le_self; rintro rfl; simp at hl
  ext ⟨i,j⟩
  simp only [mem_filter,mem_active,location,mem_image,mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨i,Nat.le_log_of_pow_le (by decide) (by omega : 3^(i+1)≤n-5^(j+1)),rfl,rfl⟩
  · rintro ⟨i',hi,rfl,rfl⟩
    have pos : 0<n-5^(l+1) := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hi
    have h := (Nat.pow_le_pow_right (by decide : 0<3) hi).trans (Nat.pow_log_le_self 3 pos.ne')
    exact ⟨by omega,rfl⟩

private lemma sub_decompose {u v n : ℕ} (h : u+v ≤ n) : n-u=n-(u+v)+v := by omega

/-- After removing a unit, the ternary residue counts the active top row
modulo two. Its endpoint depends on n minus the current power of three. -/
theorem ternary_residue {n k : ℕ} (hk : k+1=Nat.log 3 n) :
    (commonNum n : ZMod 3) =
      2^(n-3^(k+1)) * 5^(Nat.log 5 n) *
      (if Nat.log 5 (n-3^(k+1))%2=0 then 0 else 1) := by
  rw [← row_sum, mul_sum, ← sum_image (f:=fun v : ℕ × ℕ =>
    (2:ZMod 3)^(n-3^(k+1))*5^(Nat.log 5 n)*rowTerm v.2) (fun a _ b _ (h : (k,a)=(k,b)) => congrArg Prod.snd h),
      ← row_slice hk, sum_filter,commonNum,Nat.cast_sum]
  apply sum_congr rfl
  intro v hv
  have inds := mem_product.mp (mem_filter.mp hv).1
  have loc := mem_active.mp hv
  change 3^(v.1+1)+5^(v.2+1) ≤ n at loc
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,← hk]
  split_ifs with eq
  · have h₅ := Nat.sub_add_cancel (mem_range.mp inds.2 : v.2+1 ≤ Nat.log 5 n)
    rw [eq] at loc
    simp only [eq,Nat.sub_self,pow_zero,mul_one,rowTerm]
    have h₂ : n-3^(k+1) = n-location v+5^(v.2+1) := by
      simp only [location,eq]
      exact sub_decompose loc
    have fac : (5:ZMod 3)^Nat.log 5 n =
        5^(Nat.log 5 n-(v.2+1))*5^(v.2+1) := by rw [← pow_add,h₅]
    rw [h₂,pow_add (2:ZMod 3) _ (5^(v.2+1)),fac]
    field_simp [show (2:ZMod 3) ≠ 0 by decide, show (5:ZMod 3) ≠ 0 by decide]
  · have h := mem_range.mp inds.1
    have diff : k+1-(v.1+1) ≠ 0 := by omega
    simp only [show (3:ZMod 3)=0 by decide,zero_pow diff,mul_zero,zero_mul]

/-- The quinary residue on the active top column is a unit times the
four-entry table 0, 4, 1, 2 indexed by the column length modulo four. -/
theorem quinary_residue {n l : ℕ} (hl : l+1=Nat.log 5 n) :
    (commonNum n : ZMod 5) =
      2^(n-5^(l+1)) * 3^(Nat.log 3 n) *
      colWeight (Nat.log 3 (n-5^(l+1))) := by
  rw [← col_sum, mul_sum, ← sum_image (f:=fun v : ℕ × ℕ =>
    (2:ZMod 5)^(n-5^(l+1))*3^(Nat.log 3 n)*colTerm v.1) (fun a _ b _ (h : (a,l)=(b,l)) => congrArg Prod.fst h),
      ← col_slice hl, sum_filter,commonNum,Nat.cast_sum]
  apply sum_congr rfl
  intro v hv
  have inds := mem_product.mp (mem_filter.mp hv).1
  have loc := mem_active.mp hv
  change 3^(v.1+1)+5^(v.2+1) ≤ n at loc
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,← hl]
  split_ifs with eq
  · have h₃ := Nat.sub_add_cancel (mem_range.mp inds.1 : v.1+1 ≤ Nat.log 3 n)
    rw [eq] at loc
    simp only [eq,Nat.sub_self,pow_zero,mul_one,colTerm]
    have h₂ : n-5^(l+1) = n-location v+3^(v.1+1) := by
      simp only [location,eq]
      rw [Nat.add_comm (3^(v.1+1)) (5^(l+1))] at loc ⊢
      exact sub_decompose loc
    have fac : (3:ZMod 5)^Nat.log 3 n =
        3^(Nat.log 3 n-(v.1+1))*3^(v.1+1) := by rw [← pow_add,h₃]
    rw [h₂,pow_add (2:ZMod 5) _ (3^(v.1+1)),fac]
    field_simp [show (2:ZMod 5) ≠ 0 by decide, show (3:ZMod 5) ≠ 0 by decide]
  · have h := mem_range.mp inds.2
    have diff : l+1-(v.2+1) ≠ 0 := by omega
    simp only [show (5:ZMod 5)=0 by decide,zero_pow diff,mul_zero]

/-- A positive top power of three survives in the reduced denominator precisely
when its row contains an odd number of active terms. -/
theorem ternary_survival_iff {n k : ℕ} (hk : k+1=Nat.log 3 n) :
    3^(k+1) ∣ (pre n).den ↔ Nat.log 5 (n-3^(k+1))%2 ≠ 0 := by
  have H := top_power_iff (S:=commonNum n) (x:=pre n) (a:=k+1) Nat.prime_three (by omega)
    (C:=5^Nat.log 5 n)
    (fun h => (by decide : ¬3 ∣ 5) (Nat.prime_three.dvd_of_dvd_pow h)) (by positivity)
    (by simpa [hk,mul_assoc,mul_comm,mul_left_comm] using commonNum_eq n)
  rw [H,← ZMod.natCast_eq_zero_iff,ternary_residue hk]
  split_ifs <;> simp_all [show (2:ZMod 3)≠0 by decide,show (5:ZMod 3)≠0 by decide]

/-- The full top power of five survives exactly at column lengths outside the
zero class modulo four. The first three nonzero residues are 4, 1, 2. -/
theorem quinary_survival_iff {n l : ℕ} (hl : l+1=Nat.log 5 n) :
    5^(l+1) ∣ (pre n).den ↔ Nat.log 3 (n-5^(l+1))%4 ≠ 0 := by
  have prime : Nat.Prime 5 := by decide
  have H := top_power_iff (S:=commonNum n) (x:=pre n) (a:=l+1) prime (by omega)
    (C:=3^Nat.log 3 n)
    (fun h => (by decide : ¬5 ∣ 3) (prime.dvd_of_dvd_pow h)) (by positivity)
    (by simpa [hl,mul_assoc,mul_comm,mul_left_comm] using commonNum_eq n)
  rw [H,← ZMod.natCast_eq_zero_iff,quinary_residue hl]
  unfold colWeight
  split_ifs <;> simp_all [show (2:ZMod 5)≠0 by decide, show (3:ZMod 5)≠0 by decide,
    show (4:ZMod 5)≠0 by decide]

theorem mixedPrefix_eq (n : ℕ) : StonehamStatements.mixedPrefix n = pre n := by
  rw [pre,active,sum_filter,sum_product]; rfl

/-- Check the two exact endpoint tests against a separately stated prefix. -/
theorem mixed_prefix_residues : StonehamStatements.MixedPrefixResidues := by
  intro n hn
  have hk := Nat.le_log_of_pow_le (b:=3) (x:=1) (by decide) (by simpa using (by omega : 3≤n))
  have hl := Nat.le_log_of_pow_le (b:=5) (x:=1) (by decide) (by simpa using hn)
  obtain ⟨k,hK⟩ : ∃ k, Nat.log 3 n=k+1 := ⟨Nat.log 3 n-1,by omega⟩
  obtain ⟨l,hL⟩ : ∃ l, Nat.log 5 n=l+1 := ⟨Nat.log 5 n-1,by omega⟩
  dsimp only
  rw [mixedPrefix_eq,hK,hL]
  exact ⟨ternary_survival_iff hK.symm,quinary_survival_iff hL.symm⟩

end NormalityChecker.ProductThreeFive
