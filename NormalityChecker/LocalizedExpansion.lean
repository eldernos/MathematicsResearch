module

public import NormalityChecker.LocalizedLayers
public import NormalityChecker.FourierTest

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.Localized
variable (d : Parameters)

def Supported (m : ℕ) := ∃ v, index d v = m

lemma index_injective : Function.Injective (index d) := by
  rintro ⟨a,j⟩ ⟨c,l⟩ h
  have e : weight d (a,j) = weight d (c,l) := by simp only [weight,h]
  have hnorm := congrArg (padicNorm d.p) e
  rw [norm_weight,norm_weight] at hnorm
  have hj : j=l := (pow_right_injective₀ (by exact_mod_cast d.hp.pos : (0:ℚ)<d.p) (by exact_mod_cast d.hp.ne_one)) hnorm
  subst l
  have hac := Nat.eq_of_mul_eq_mul_right (pow_pos d.hp.pos j) h
  exact Prod.ext (Nat.pow_right_injective d.hq hac) rfl

open Classical in
noncomputable def term (i : ℕ) : ℝ :=
  if Supported d (i+1) then 1 / (((i:ℝ)+1)*(d.b:ℝ)^(i+1)) else 0

noncomputable def value := ∑' i : ℕ, term d i

private lemma term_bound (i : ℕ) : 0≤term d i ∧ term d i ≤ 1 / (((i:ℝ)+1)*(d.b:ℝ)^(i+1)) := by
  unfold term; split_ifs <;> constructor <;> first | positivity | rfl

private lemma summable_term : Summable (term d) := by
  apply Summable.of_nonneg_of_le (fun i => (term_bound d i).1) _ hasSum_logTwo.summable
  intro i; apply (term_bound d i).2.trans
  rw [one_div_pow,div_div]; apply one_div_le_one_div_of_le (by positivity)
  rw [mul_comm]; gcongr
  exact_mod_cast d.hb

lemma value_eq_series : value d = ∑' j : ℕ, ∑' a : ℕ,
    1 / ((d.q:ℝ)^a*d.p^j*(d.b:ℝ)^(d.q^a*d.p^j : ℕ)) := by
  classical
  let g (v : ℕ × ℕ) := index d (v.2,v.1) - 1
  have inj : Function.Injective g := by
    intro v w h
    have e : index d (v.2,v.1) = index d (w.2,w.1) := by
      dsimp [g] at h; have := index_pos d (v.2,v.1); have := index_pos d (w.2,w.1); omega
    have eqn := index_injective d e; exact Prod.ext (congrArg Prod.snd eqn) (congrArg Prod.fst eqn)
  have H : HasSum (term d ∘ g) (value d) := (inj.hasSum_iff (fun i hi => by
    have h : ¬ Supported d (i+1) := by
      rintro ⟨v,hv⟩; apply hi; exact ⟨(v.2,v.1),by simp [g,hv]⟩
    simp [term,h])).mpr (summable_term d).hasSum
  rw [← H.tsum_eq,H.summable.tsum_prod' (fun i => H.summable.prod_factor i)]
  apply tsum_congr; intro j; apply tsum_congr; intro a
  have e : g (j,a)+1 = index d (a,j) := Nat.sub_add_cancel (index_pos d _)
  have er : (g (j,a):ℝ)+1 = index d (a,j) := by exact_mod_cast e
  have hs : Supported d (index d (a,j)) := ⟨_,rfl⟩
  simp only [Function.comp_apply,term,e,er,hs,ite_true]
  simp [index]

private lemma truncate (n : ℕ) : (unshifted d n:ℝ) = ∑ i ∈ range n, term d i := by
  classical
  let g (v : ℕ × ℕ) := index d v - 1
  have e : (allowed d n).image g = (range n).filter (fun i => Supported d (i+1)) := by
    ext i; constructor
    · rintro hi; obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
      have h := (mem_allowed d).mp hv; have := index_pos d v
      exact mem_filter.mpr ⟨mem_range.mpr (by dsimp [g]; omega),⟨v,by dsimp [g]; omega⟩⟩
    · intro hi; obtain ⟨hr,v,hv⟩ := mem_filter.mp hi
      exact mem_image.mpr ⟨v,(mem_allowed d).mpr (by rw [hv]; exact mem_range.mp hr),by simp [g,hv]⟩
  simp only [term,← sum_filter,← e,unshifted,Rat.cast_sum]
  rw [sum_image]; swap
  · intro v _ w _ he; apply index_injective d; dsimp [g] at he; have := index_pos d v; have := index_pos d w; omega
  apply sum_congr rfl; intro v _
  have eqn : g v+1 = index d v := Nat.sub_add_cancel (index_pos d v)
  have er : (g v:ℝ)+1 = index d v := by exact_mod_cast eqn
  simp [weight,eqn,er]

/-- The shifted omitted tail is bounded uniformly by `1/(n+1)`. -/
theorem shift_error (n : ℕ) : 0 ≤ (d.b:ℝ)^n*value d - shifted d n ∧
    (d.b:ℝ)^n*value d - shifted d n ≤ 1/((n:ℝ)+1) := by
  have hb : (0:ℝ)<d.b := by exact_mod_cast (show 0<d.b by have := d.hb; omega)
  have split := (summable_term d).sum_add_tsum_nat_add n
  have e : (d.b:ℝ)^n*value d - shifted d n = ∑' i, (d.b:ℝ)^n*term d (i+n) := by
    simp only [shifted,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,truncate,value,← split,tsum_mul_left]; ring
  rw [e]; refine ⟨tsum_nonneg (fun i => mul_nonneg (by positivity) (term_bound d _).1),?_⟩
  let c := (1/2:ℝ)/(n+1)
  have hg := (summable_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).mul_left c
  apply (((summable_nat_add_iff n).mpr (summable_term d)).mul_left ((d.b:ℝ)^n)).tsum_le_tsum (g:=fun i => c*(1/2:ℝ)^i) _ hg |>.trans
  · rw [tsum_mul_left,tsum_geometric_two]; dsimp [c]; apply le_of_eq; ring
  · intro i; apply (mul_le_mul_of_nonneg_left (term_bound d _).2 (by positivity)).trans
    have cancel : (d.b:ℝ)^n * (1 / (((i+n:ℕ):ℝ)+1) / (d.b:ℝ)^(i+n+1)) = 1/((((i+n:ℕ):ℝ)+1)*(d.b:ℝ)^(i+1)) := by
      rw [show i+n+1=i+1+n by omega,pow_add]; field_simp
    rw [← div_div,cancel]; dsimp [c]; rw [one_div_pow]
    calc _ ≤ 1 / (((n:ℝ)+1)*2^(i+1)) := by
           apply one_div_le_one_div_of_le (by positivity); push_cast; gcongr <;> first | exact_mod_cast d.hb | linarith
         _ = _ := by rw [pow_succ]; field_simp

/-- On a stretch without an insertion the shifted rational prefix follows the base orbit exactly. -/
theorem prefix_orbit {s i : ℕ} (free : ∀ m, s<m → m≤s+i → ¬Supported d m) :
    shifted d (s+i) = (d.b:ℚ)^i * shifted d s := by
  have e : allowed d (s+i) = allowed d s := by
    ext v; rw [mem_allowed,mem_allowed]; constructor
    · intro h; by_contra! hh; exact free _ hh h ⟨v,rfl⟩
    · omega
  simp only [shifted,unshifted,e,pow_add]; ring

end NormalityChecker.Localized
