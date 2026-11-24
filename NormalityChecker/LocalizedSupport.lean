module

public import NormalityChecker.FourierTest
public import NormalityChecker.PrimeCancellation
public import Mathlib.NumberTheory.SmoothNumbers

/-! Prefixes of the logarithm restricted to a finite prime support. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

def indices (S : Finset ℕ) (n : ℕ) := (range (n+1)).filter (· ∈ Nat.factoredNumbers S)

@[simp] lemma mem_indices {S n m} : m ∈ indices S n ↔ m ≤ n ∧ m ∈ Nat.factoredNumbers S := by
  simp [indices]

def weight (b m : ℕ) : ℚ := 1 / ((m:ℚ)*(b:ℚ)^m)
def partialSum (b : ℕ) (S : Finset ℕ) (n : ℕ) := ∑ m ∈ indices S n, weight b m
def shifted (b : ℕ) (S : Finset ℕ) (n : ℕ) := (b:ℚ)^n * partialSum b S n

noncomputable def term (b : ℕ) (S : Finset ℕ) (i : ℕ) : ℝ :=
  if i+1 ∈ Nat.factoredNumbers S then 1 / (((i:ℝ)+1)*(b:ℝ)^(i+1)) else 0
noncomputable def value (b : ℕ) (S : Finset ℕ) := ∑' i, term b S i

lemma sum_layers {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hs : p ∉ S) (n k : ℕ)
    (hi : n < p^(k+1)) {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ m ∈ indices (insert p S) n, f m = ∑ j ∈ range (k+1),
      ∑ r ∈ indices S (n/p^j), f (p^j*r) := by
  classical
  rw [sum_sigma']
  symm
  apply sum_nbij' (fun x : Σ _ : ℕ, ℕ => p^x.1*x.2)
    (fun m => ⟨m.factorization p, (m.primeFactorsList.filter (· ∈ S)).prod⟩)
  · intro x hx
    obtain ⟨_,hr⟩ := mem_sigma.mp hx
    obtain ⟨hr,hsr⟩ := mem_indices.mp hr
    exact mem_indices.mpr ⟨by simpa [mul_comm] using (Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mp hr,
      Nat.pow_mul_mem_factoredNumbers hp _ hsr⟩
  · intro m hm
    obtain ⟨hm,hms⟩ := mem_indices.mp hm
    let e := Nat.equivProdNatFactoredNumbers hp hs
    let x := e.symm ⟨m,hms⟩
    have he : p^x.1*x.2.val = m := congrArg Subtype.val (e.apply_symm_apply ⟨m,hms⟩)
    apply mem_sigma.mpr
    change x.1 ∈ range (k+1) ∧ x.2.val ∈ indices S (n/p^x.1)
    exact ⟨mem_range.mpr ((Nat.pow_lt_pow_iff_right hp.one_lt).mp
      ((Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero x.2.property.1)).trans_lt (he ▸ hm.trans_lt hi))),
      mem_indices.mpr ⟨(Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mpr (by rw [mul_comm,he]; exact hm),x.2.property⟩⟩
  · intro x hx
    have hr := (mem_indices.mp (mem_sigma.mp hx).2).2
    have H := (Nat.equivProdNatFactoredNumbers hp hs).symm_apply_apply (x.1,⟨x.2,hr⟩)
    exact congrArg (fun z : ℕ × Nat.factoredNumbers S => (⟨z.1,z.2.val⟩ : Σ _ : ℕ, ℕ)) H
  · intro m hm
    exact congrArg Subtype.val ((Nat.equivProdNatFactoredNumbers hp hs).apply_symm_apply ⟨m,(mem_indices.mp hm).2⟩)
  · intros; rfl

lemma orbit {b S s i} (free : ∀ m, s<m → m≤s+i → m ∉ Nat.factoredNumbers S) :
    shifted b S (s+i) = (b:ℚ)^i*shifted b S s := by
  have e : indices S (s+i) = indices S s := by
    ext m; simp only [mem_indices]; constructor
    · rintro ⟨hm,hs⟩; exact ⟨le_of_not_gt (fun h => free m h hm hs),hs⟩
    · rintro ⟨hm,hs⟩; exact ⟨by omega,hs⟩
  simp only [shifted,partialSum,e,pow_add]; ring

private lemma truncate (b S n) : (partialSum b S n : ℝ) = ∑ i ∈ range n, term b S i := by
  simp only [partialSum,indices,sum_filter,Rat.cast_sum]
  rw [sum_range_succ']
  have hz : 0 ∉ Nat.factoredNumbers S := fun h => h.1 rfl
  simp [hz,term,weight,apply_ite]
private lemma term_bound (b : ℕ) (S : Finset ℕ) (i : ℕ) : 0≤term b S i ∧ term b S i ≤ 1 / (((i:ℝ)+1)*(b:ℝ)^(i+1)) := by
  unfold term; split_ifs <;> constructor <;> first | positivity | rfl

lemma summable_term (b : ℕ) (S : Finset ℕ) (hb : 2 ≤ b) : Summable (term b S) := by
  apply Summable.of_nonneg_of_le (fun i => (term_bound b S i).1) _ hasSum_logTwo.summable
  intro i; apply (term_bound b S i).2.trans
  rw [one_div_pow,div_div]; apply one_div_le_one_div_of_le (by positivity)
  rw [mul_comm]; gcongr
  exact_mod_cast hb

/-- The shifted omitted tail is bounded uniformly by `1/(n+1)`. -/
theorem shift_error (b : ℕ) (S : Finset ℕ) (hb : 2 ≤ b) (n : ℕ) : 0 ≤ (b:ℝ)^n*value b S - shifted b S n ∧
    (b:ℝ)^n*value b S - shifted b S n ≤ 1/((n:ℝ)+1) := by
  have hbpos : (0:ℝ)<b := by exact_mod_cast (show 0<b by have := hb; omega)
  have split := (summable_term b S hb).sum_add_tsum_nat_add n
  have e : (b:ℝ)^n*value b S - shifted b S n = ∑' i, (b:ℝ)^n*term b S (i+n) := by
    simp only [shifted,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,truncate,value,← split,tsum_mul_left]; ring
  rw [e]; refine ⟨tsum_nonneg (fun i => mul_nonneg (by positivity) (term_bound b S _).1),?_⟩
  let c := (1/2:ℝ)/(n+1)
  have hg := (summable_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).mul_left c
  apply (((summable_nat_add_iff n).mpr (summable_term b S hb)).mul_left ((b:ℝ)^n)).tsum_le_tsum (g:=fun i => c*(1/2:ℝ)^i) _ hg |>.trans
  · rw [tsum_mul_left,tsum_geometric_two]; dsimp [c]; apply le_of_eq; ring
  · intro i; apply (mul_le_mul_of_nonneg_left (term_bound b S _).2 (by positivity)).trans
    have cancel : (b:ℝ)^n * (1 / (((i+n:ℕ):ℝ)+1) / (b:ℝ)^(i+n+1)) = 1/((((i+n:ℕ):ℝ)+1)*(b:ℝ)^(i+1)) := by
      rw [show i+n+1=i+1+n by omega,pow_add]; field_simp
    rw [← div_div,cancel]; dsimp [c]; rw [one_div_pow]
    calc _ ≤ 1 / (((n:ℝ)+1)*2^(i+1)) := by
           apply one_div_le_one_div_of_le (by positivity); push_cast; gcongr <;> first | exact_mod_cast hb | linarith
         _ = _ := by rw [pow_succ]; field_simp


end NormalityChecker.LocalizedSupport
