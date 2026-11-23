module

public import NormalityChecker.ResonantDensity
public import NormalityChecker.Resonance
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section
open Filter Finset
open scoped Topology
namespace NormalityChecker

/-- Lifting the minus-one congruence for any odd c, including composite moduli. -/
theorem odd_radix_lift {c : ℕ} (hc : Odd c) {X : ℤ} (h : (c:ℤ) ∣ X+1) (j : ℕ) :
    (c:ℤ)^(j+1) ∣ X^(c^j)+1 := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    let Y := X^(c^j)
    have hd : (c:ℤ) ∣ Y-(-1) := (dvd_pow_self _ (Nat.succ_ne_zero j)).trans (by simpa [Y] using ih)
    have hs := dvd_geom_sum₂_self (n:=c) hd
    have ih' : (c:ℤ)^(j+1) ∣ Y-(-1) := by simpa [Y] using ih
    have H := mul_dvd_mul hs ih'
    rw [pow_succ c j,pow_mul]
    change (c:ℤ)^(j+1+1) ∣ Y^c+1
    simpa only [pow_succ' (c:ℤ) (j+1), ← sub_neg_eq_add, geom_sum₂_mul,hc.neg_one_pow] using H

noncomputable def radixComponent (b c m : ℕ) : ℝ :=
  ∑' j : ℕ, (1/(b:ℝ))^(m*c^j) / ((m:ℝ)*(c:ℝ)^j)

private noncomputable def pair (b c m l j : ℕ) : ℝ :=
  ((1/(b:ℝ))^(m*c^j)+(1/(b:ℝ))^(l*c^j))/(c:ℝ)^j

private lemma pair_majorant {b c m l : ℕ} (hb : 2≤b) (hc : 1<c) (hm : 0<m) (hml : m≤l)
    (n J i : ℕ) (hn : n≤c^J) :
    (b:ℝ)^n*pair b c m l (i+J) ≤ (2/(c:ℝ)^J)*(1/(c:ℝ))^i := by
  have hb' : (1:ℝ)≤b := by exact_mod_cast (show 1≤b by omega)
  have H : ∀ a : ℕ, 0<a → (b:ℝ)^n*(1/(b:ℝ))^(a*c^(i+J)) ≤ 1 := by
    intro a ha
    rw [one_div_pow,mul_one_div,div_le_one (by positivity)]
    apply pow_le_pow_right₀ hb'
    exact (hn.trans (Nat.pow_le_pow_right (by omega) (by omega : J ≤ i+J))).trans (Nat.le_mul_of_pos_left _ ha)
  unfold pair
  calc
    _ = ((b:ℝ)^n*(1/(b:ℝ))^(m*c^(i+J))+(b:ℝ)^n*(1/(b:ℝ))^(l*c^(i+J)))/(c:ℝ)^(i+J) := by ring
    _ ≤ 2/(c:ℝ)^(i+J) := div_le_div_of_nonneg_right (by linarith [H m hm,H l (hm.trans_le hml)]) (by positivity)
    _ = _ := by rw [pow_add,one_div_pow]; ring

private lemma pair_sums {b c m l : ℕ} (hb : 2≤b) (hc : 1<c) (hm : 0<m) (hml : m≤l) :
    HasSum (pair b c m l) ((m:ℝ)*radixComponent b c m+(l:ℝ)*radixComponent b c l) := by
  have hc' : (1:ℝ)<c := by exact_mod_cast hc
  have geom := summable_geometric_of_lt_one (by positivity : 0≤1/(c:ℝ)) ((div_lt_one (by positivity)).mpr hc')
  have hp : Summable (pair b c m l) := .of_nonneg_of_le (fun _ => by unfold pair; positivity)
    (fun i => by simpa using pair_majorant hb hc hm hml 0 0 i (by simp)) (by simpa using geom.mul_left 2)
  let f (a j : ℕ) := (1/(b:ℝ))^(a*c^j)/(c:ℝ)^j
  have e (j : ℕ) : pair b c m l j = f m j+f l j := by dsimp [pair,f]; ring
  have hf : Summable (f m) := .of_nonneg_of_le (fun _ => by dsimp [f]; positivity)
    (fun i => by rw [e]; exact le_add_of_nonneg_right (by dsimp [f]; positivity)) hp
  have hg : Summable (f l) := .of_nonneg_of_le (fun _ => by dsimp [f]; positivity)
    (fun i => by rw [e]; exact le_add_of_nonneg_left (by dsimp [f]; positivity)) hp
  have he (a : ℕ) (ha : 0<a) : (a:ℝ)*radixComponent b c a = ∑' j, f a j := by
    rw [radixComponent, ← tsum_mul_left]; apply tsum_congr; intro j; dsimp [f]; field_simp
  rw [he m hm,he l (hm.trans_le hml)]
  exact (hf.hasSum.add hg.hasSum).congr_fun (fun j => e j)

private lemma shifted_pair_int {b c m l : ℕ} (hb : 2≤b) (hc : Odd c) (hml : m<l)
    (hr : c ∣ b^(l-m)+1) (n j : ℕ) (hn : l*c^j≤n) :
    ∃ z : ℤ, (b:ℝ)^n*pair b c m l j=z := by
  have hd := (pow_dvd_pow (c:ℤ) (Nat.le_succ j)).trans
    (odd_radix_lift hc (X:=(b:ℤ)^(l-m)) (by exact_mod_cast hr) j)
  obtain ⟨z,hz⟩ := hd
  have hz' : (b:ℝ)^((l-m)*c^j)+1=(c:ℝ)^j*z := by rw [pow_mul]; exact_mod_cast hz
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨(b:ℤ)^d*z,?_⟩
  have he : l*c^j=m*c^j+(l-m)*c^j := by rw [← Nat.add_mul,Nat.add_sub_of_le hml.le]
  unfold pair
  rw [pow_add,one_div_pow,one_div_pow,he,pow_add]
  have hc0 : c ≠ 0 := by rintro rfl; exact (by decide : ¬ Odd (0:ℕ)) hc
  push_cast; field_simp [hc0]
  exact hz'

/-- On the resonance intervals the shifted sum exceeds an integer by a strictly
positive amount bounded uniformly by 2/((c-1)c^k). -/
theorem radix_pair_tail {b c m l : ℕ} (hb : 2≤b) (hc : 1<c) (hodd : Odd c)
    (hm : 0<m) (hml : m<l) (hr : c ∣ b^(l-m)+1) {k n : ℕ}
    (hlo : l*c^k≤n) (hhi : n≤c^(k+1)) :
    ∃ z : ℤ, 0 < (b:ℝ)^n*((m:ℝ)*radixComponent b c m+(l:ℝ)*radixComponent b c l)-z ∧
      (b:ℝ)^n*((m:ℝ)*radixComponent b c m+(l:ℝ)*radixComponent b c l)-z ≤ (2/((c:ℝ)-1))/(c:ℝ)^k := by
  have J (j : ℕ) (hj : j∈range (k+1)) := shifted_pair_int hb hodd hml hr n j
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0<c) (by simpa using mem_range.mp hj : j≤k))).trans hlo)
  choose z hz using J
  let Z := ∑ j ∈ (range (k+1)).attach, z j.val j.property
  have HZ : ∑ j ∈ range (k+1), (b:ℝ)^n*pair b c m l j = Z := by
    simp only [Z,Int.cast_sum,← hz]; exact (sum_attach _ _).symm
  have hs := (pair_sums hb hc hm hml.le).mul_left ((b:ℝ)^n)
  let t (i : ℕ) := (b:ℝ)^n*pair b c m l (i+(k+1))
  have ht : Summable t := (summable_nat_add_iff _).mpr hs.summable
  have he := hs.summable.sum_add_tsum_nat_add (k+1)
  rw [HZ,hs.tsum_eq] at he
  refine ⟨Z,?_⟩
  rw [← he, add_sub_cancel_left]
  have hc' : (1:ℝ)<c := by exact_mod_cast hc
  have hp (i : ℕ) : 0 < t i := by dsimp [t,pair]; positivity
  refine ⟨ht.tsum_pos (fun i => (hp i).le) 0 (hp 0),?_⟩
  have h1 : 1/(c:ℝ)<1 := (div_lt_one (by positivity)).mpr hc'
  calc
    _ ≤ ∑' i : ℕ, (2/(c:ℝ)^(k+1))*(1/(c:ℝ))^i := ht.tsum_le_tsum
      (fun i => pair_majorant hb hc hm hml.le n (k+1) i hhi)
      ((summable_geometric_of_lt_one (by positivity) h1).mul_left _)
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (by positivity) h1,pow_succ]; field_simp

/-- Quantitative abnormality for every fixed all-zero block. -/
theorem radix_pair_zero_limsup {b c m l : ℕ} (hb : 2≤b) (hc : 1<c) (hodd : Odd c)
    (hm : 0<m) (hml : m<l) (hlc : l<c) (hr : c ∣ b^(l-m)+1) (r : ℕ) :
    ((c:ℝ)-l)/(c-1) ≤ limsup (frequency
      (shift b ((m:ℝ)*radixComponent b c m+(l:ℝ)*radixComponent b c l)) 0 (1/(b:ℝ)^r)) atTop := by
  apply geometric_cells_limsup hc (hm.trans hml) hlc
  have hc' : (1:ℝ)<c := by exact_mod_cast hc
  have ht : Tendsto (fun k : ℕ => (2/((c:ℝ)-1))/(c:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=2/((c:ℝ)-1))).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hc'))
  filter_upwards [ht.eventually_lt_const (by positivity : (0:ℝ)<1/(b:ℝ)^r)] with k hk n hn hn'
  obtain ⟨z,hz,hz'⟩ := radix_pair_tail hb hc hodd hm hml hr hn hn'.le
  have hle : 1/(b:ℝ)^r ≤ 1 := (div_le_one (by positivity)).mpr
    (one_le_pow₀ (by exact_mod_cast (show 1≤b by omega)))
  unfold shift
  have H (v : ℝ) : Int.fract v = Int.fract (v-z) := by simp
  rw [H]
  rw [Int.fract_eq_self.mpr ⟨hz.le,((hz'.trans_lt hk).trans_le hle)⟩]
  exact ⟨hz.le,hz'.trans_lt hk⟩

theorem radix_pair_not_normal {b c m l : ℕ} (hb : 2≤b) (hc : 1<c) (hodd : Odd c)
    (hm : 0<m) (hml : m<l) (hlc : l<c) (hr : c ∣ b^(l-m)+1) :
    ¬ NormalIn b ((m:ℝ)*radixComponent b c m+(l:ℝ)*radixComponent b c l) := by
  intro hn
  have hc' : (1:ℝ)<c := by exact_mod_cast hc
  have hl' : (l:ℝ)<c := by exact_mod_cast hlc
  have hb' : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have H := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb')).eventually_lt_const
    (div_pos (sub_pos.mpr hl') (sub_pos.mpr hc'))
  obtain ⟨r,hr₀,hsmall⟩ := (H.and (eventually_gt_atTop 0)).exists
  have hfreq := hn.2 r 0 hsmall (pow_pos (by omega) _)
  have hl := radix_pair_zero_limsup hb hc hodd hm hml hlc hr r
  simp only [Nat.cast_zero,zero_div,zero_add] at hfreq
  rw [hfreq.limsup_eq] at hl
  exact (by simpa [one_div] using hr₀ : 1/(b:ℝ)^r < ((c:ℝ)-l)/(c-1)).not_ge hl

theorem radix_pair_irrational {b c m l : ℕ} (hb : 2≤b) (hc : 1<c) (hodd : Odd c)
    (hm : 0<m) (hml : m<l) (hlc : l<c) (hr : c ∣ b^(l-m)+1) :
    Irrational ((m:ℝ)*radixComponent b c m+(l:ℝ)*radixComponent b c l) := by
  rintro ⟨q,hq⟩
  have hc' : (1:ℝ)<c := by exact_mod_cast hc
  have hd : (0:ℝ)<q.den := by exact_mod_cast q.pos
  have ht : Tendsto (fun k : ℕ => (2/((c:ℝ)-1))/(c:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=2/((c:ℝ)-1))).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hc'))
  obtain ⟨k,hk⟩ := (ht.eventually_lt_const (by positivity : (0:ℝ)<1/q.den)).exists
  let n := l*c^k
  obtain ⟨z,hz,hz'⟩ := radix_pair_tail hb hc hodd hm hml hr (k:=k) (n:=n) le_rfl
    (by rw [pow_succ']; exact Nat.mul_le_mul_right _ hlc.le)
  rw [← hq] at hz hz'
  let w : ℤ := (b:ℤ)^n*q.num - z*q.den
  have he : (w:ℝ) = ((b:ℝ)^n*(q:ℝ)-z)*q.den := by
    rw [Rat.cast_def]; dsimp [w]; push_cast; field_simp
  have hp : (0:ℤ)<w := by exact_mod_cast (he.symm ▸ mul_pos hz hd : (0:ℝ)<w)
  have hlt : (w:ℝ)<1 := by
    rw [he]; exact (lt_div_iff₀ hd).mp (hz'.trans_lt hk)
  have hw : w<(1:ℤ) := by exact_mod_cast hlt
  omega

/-- The odd part obtained by removing at most one factor of two from y²+1. -/
def oddSquareDivisor (y : ℕ) := if Even y then y^2+1 else (y^2+1)/2

theorem oddSquareDivisor_spec (y : ℕ) :
    Odd (oddSquareDivisor y) ∧ oddSquareDivisor y ∣ y^2+1 ∧ y^2+1 ≤ 2*oddSquareDivisor y := by
  rcases Nat.even_or_odd y with he | ho
  · rw [oddSquareDivisor,ite_eq_left he]
    obtain ⟨t,rfl⟩ := he
    refine ⟨⟨2*t^2,by ring⟩,dvd_rfl,by omega⟩
  · rw [oddSquareDivisor,ite_eq_right (Nat.not_even_iff_odd.mpr ho)]
    obtain ⟨t,rfl⟩ := ho
    have he : (2*t+1)^2+1=2*(2*t*(t+1)+1) := by ring
    rw [he,Nat.mul_div_cancel_left _ (by decide : 0<2)]
    exact ⟨⟨t*(t+1),by ring⟩,dvd_mul_left _ _,le_rfl⟩

theorem all_base_resonance (b : ℕ) (hb : 2≤b) :
    let c := oddSquareDivisor b
    ¬ NormalIn b (radixComponent b c 1 + 3*radixComponent b c 3) := by
  obtain ⟨ho,hd,hle⟩ := oddSquareDivisor_spec b
  have hc : 3 < oddSquareDivisor b := by
    by_cases h : b=2
    · subst b; decide
    · have h' : 3≤b := by omega
      nlinarith [Nat.pow_le_pow_left h' 2]
  simpa using radix_pair_not_normal (b:=b) (c:=oddSquareDivisor b) (m:=1) (l:=3) hb (by omega) ho
    (by decide) (by decide) hc hd

/-- In every radix, a single irrational resonant pair can exceed a prescribed
threshold below one for the upper frequency of *every* fixed zero block. -/
theorem severe_resonance (b : ℕ) (hb : 2≤b) (η : ℝ) (hη : η<1) :
    ∃ d : ℕ, 0<d ∧
      let l := 2*d+1
      let c := oddSquareDivisor (b^d)
      let x := radixComponent b c 1+(l:ℝ)*radixComponent b c l
      Irrational x ∧ ¬ NormalIn b x ∧ ∀ r : ℕ, η < limsup (frequency (shift b x) 0 (1/(b:ℝ)^r)) atTop := by
  let e := min (1-η) 1
  have he : 0<e := lt_min (sub_pos.mpr hη) zero_lt_one
  obtain ⟨d,hd⟩ := exists_nat_gt (max 2 (2/e))
  have hd₂ : (2:ℝ)<d := (le_max_left ..).trans_lt hd
  have hde : 2/e < d := (le_max_right ..).trans_lt hd
  have hd₀ : 0<d := by exact_mod_cast (zero_lt_two.trans hd₂)
  let l := 2*d+1
  let c := oddSquareDivisor (b^d)
  obtain ⟨ho,hdvd,hle⟩ := oddSquareDivisor_spec (b^d)
  have hpow : (b^d)^2=b^(2*d) := by rw [← pow_mul,Nat.mul_comm]
  rw [hpow] at hdvd hle
  have hbase := (Nat.two_mul_sq_add_one_le_two_pow_two_mul d).trans (Nat.pow_le_pow_left hb (2*d))
  have hsq : d^2+1 ≤ c := by change _ ≤ 2*c at hle; omega
  have hdl : l<c := by
    have hd₃ : 3≤d := by exact_mod_cast hd₂
    dsimp [l]; nlinarith [Nat.mul_le_mul_right d hd₃]
  have hc : 1<c := by dsimp [l] at hdl; omega
  have hml : 1<l := by dsimp [l]; omega
  have hr : c ∣ b^(l-1)+1 := by simpa [l] using hdvd
  have hratio : η < ((c:ℝ)-l)/(c-1) := by
    have he' := (div_lt_iff₀ he).mp hde
    have heη : e ≤ 1-η := min_le_left ..
    have hc' : (1:ℝ)<c := by exact_mod_cast hc
    have hs' : (d:ℝ)^2+1 ≤ c := by exact_mod_cast hsq
    rw [lt_div_iff₀ (sub_pos.mpr hc')]
    dsimp [l]; push_cast
    nlinarith [mul_lt_mul_of_pos_left he' (by positivity : (0:ℝ)<d),
      mul_le_mul_of_nonneg_left (show (d:ℝ)^2 ≤ c-1 by linarith) he.le,
      mul_le_mul_of_nonneg_right heη (sub_pos.mpr hc').le]
  refine ⟨d,hd₀,?_,?_,?_⟩
  · simpa [c,l] using radix_pair_irrational hb hc ho (by decide : 0<1) hml hdl hr
  · simpa [c,l] using radix_pair_not_normal hb hc ho (by decide : 0<1) hml hdl hr
  · intro r; simpa [c,l] using hratio.trans_le (radix_pair_zero_limsup hb hc ho (by decide : 0<1) hml hdl hr r)

theorem binary_zero_block_limsup (r : ℕ) :
    1/2 ≤ limsup (frequency (shift 2 (component 1+2*component 2)) 0 (1/(2:ℝ)^r)) atTop := by
  have H := radix_pair_zero_limsup (b:=2) (c:=3) (m:=1) (l:=2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  norm_num [radixComponent,component] at H ⊢
  exact H

end NormalityChecker
