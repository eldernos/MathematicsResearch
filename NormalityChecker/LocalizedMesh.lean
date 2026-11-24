module

public import NormalityChecker.LocalizedLayers
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.Localized
variable (d : Parameters)

private lemma log_ratio_irrational : Irrational (Real.log d.p / Real.log d.q) := by
  have hp : 0 < Real.log d.p := Real.log_pos (by exact_mod_cast d.hp.one_lt)
  have hq : 0 < Real.log d.q := Real.log_pos (by exact_mod_cast (show 1<d.q from d.hq))
  rintro ⟨r,hr⟩
  have hd : (0:ℝ)<r.den := by exact_mod_cast r.pos
  rw [Rat.cast_def] at hr
  have eqn := (div_eq_div_iff hd.ne' hq.ne').mp hr
  have hn : 0 ≤ r.num := by
    by_contra! h
    have := mul_neg_of_neg_of_pos (by exact_mod_cast h : (r.num:ℝ)<0) hq
    linarith [mul_pos hp hd]
  let m := r.num.toNat
  have hm : (m:ℝ) = (r.num:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  have e : (d.q:ℝ)^m = (d.p:ℝ)^r.den := by
    have hqpos : (0:ℝ)<d.q := by exact_mod_cast (show 0<d.q by have := d.hq; omega)
    have hppos : (0:ℝ)<d.p := by exact_mod_cast d.hp.pos
    apply Real.log_injOn_pos (pow_pos hqpos m) (pow_pos hppos r.den)
    simpa [Real.log_pow,hm,mul_comm] using eqn
  have en : d.q^m = d.p^r.den := by exact_mod_cast e
  exact prime_not_dvd_cofactor d (d.hp.dvd_of_dvd_pow (en ▸ dvd_pow_self d.p r.pos.ne'))

/-- Every open interval above one contains a threshold `q^a / p^i` with both
exponents natural. This uses the forward orbit of an irrational rotation. -/
theorem threshold_between {x y : ℝ} (hx : 1≤x) (hxy : x<y) :
    ∃ a i : ℕ, x < (d.q:ℝ)^a/(d.p:ℝ)^i ∧ (d.q:ℝ)^a/(d.p:ℝ)^i < y := by
  let Q := Real.log d.q
  let P := Real.log d.p
  have hQ : 0<Q := Real.log_pos (by exact_mod_cast (show 1<d.q from d.hq))
  have hP : 0<P := Real.log_pos (by exact_mod_cast d.hp.one_lt)
  let : Fact (0<Q) := ⟨hQ⟩
  have dense : DenseRange (fun i : ℕ => i • ((-P:ℝ) : AddCircle Q)) :=
    denseRange_zsmul_iff_nsmul.mp (AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa [neg_div] using (log_ratio_irrational d).neg))
  let I := Set.Ioo (Real.log x) (Real.log y)
  have ho : IsOpen ((fun z : ℝ => (z : AddCircle Q)) '' I) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hx' : 0<x := by linarith
  obtain ⟨i,z,hz,he⟩ := dense.exists_mem_open ho ((Set.nonempty_Ioo.mpr (Real.log_lt_log hx' hxy)).image _)
  rw [← AddCircle.coe_nsmul] at he
  obtain ⟨a,ha⟩ := QuotientAddGroup.eq_iff_sub_mem.mp he
  change a • Q = z - i • (-P) at ha
  simp only [zsmul_eq_mul,nsmul_eq_mul,mul_neg,sub_neg_eq_add] at ha
  have hz' : Real.log x < z ∧ z < Real.log y := hz
  have ha' : 0 ≤ a := by
    by_contra! h
    have := mul_neg_of_neg_of_pos (by exact_mod_cast h : (a:ℝ)<0) hQ
    linarith [Real.log_nonneg hx,mul_nonneg (Nat.cast_nonneg i) hP.le]
  lift a to ℕ using ha' with a
  have ep : 0 < (d.p:ℝ) := by exact_mod_cast d.hp.pos
  have eq : 0 < (d.q:ℝ) := by exact_mod_cast (show 0<d.q by have := d.hq; omega)
  have l : Real.log ((d.q:ℝ)^a/(d.p:ℝ)^i) = z := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    dsimp [P,Q] at ha; push_cast at ha; linarith
  refine ⟨a,i,(Real.log_lt_log_iff hx' (by positivity)).mp ?_,(Real.log_lt_log_iff (by positivity) (hx'.trans hxy)).mp ?_⟩ <;> rw [l] <;> tauto

/-- Uniform finite precision: the top `J+1` layers meet every subinterval of
width at least `ε` in a unit cell. `J` is independent of the large scale. -/
theorem threshold_mesh (u : ℕ) (hu : 1≤u) {ε : ℝ} (hε : 0<ε) :
    ∃ J : ℕ, ∀ x y : ℝ, u≤x → y≤u+1 → x+ε≤y →
      ∃ a i : ℕ, i≤J ∧ x < (d.q:ℝ)^a/(d.p:ℝ)^i ∧ (d.q:ℝ)^a/(d.p:ℝ)^i < y := by
  obtain ⟨M,hM⟩ := exists_nat_gt (2/ε)
  have hM' : 0<(M:ℝ) := lt_trans (by positivity) hM
  have small := (div_lt_iff₀ hε).mp hM
  have cut (r : ℕ) := threshold_between d (x:=(u:ℝ)+r/M) (y:=(u:ℝ)+(r+1)/M)
    ((show (1:ℝ) ≤ u by exact_mod_cast hu).trans (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg r) hM'.le)))
    (by gcongr; linarith)
  choose a i hi using cut
  refine ⟨(range (M+2)).sup i,fun x y hx hy hxy => ?_⟩
  let v := (x-u)*M
  have h0 : 0≤v := mul_nonneg (sub_nonneg.mpr hx) hM'.le
  let r := ⌊v⌋₊+1
  have hr : (r:ℝ) ≤ v+1 := by dsimp [r]; push_cast; linarith [Nat.floor_le h0]
  have hv : v < (r:ℝ) := by simpa [r] using Nat.lt_floor_add_one v
  have hm : v ≤ M := by dsimp [v]; nlinarith [mul_le_mul_of_nonneg_right (show x-(u:ℝ)≤1 by linarith) hM'.le]
  have hr' : r≤M+1 := by exact_mod_cast (show (r:ℝ)≤M+1 by linarith)
  refine ⟨a r,i r,le_sup (mem_range.mpr (show r<M+2 by omega)),lt_trans ?_ (hi r).1,lt_of_lt_of_le (hi r).2 ?_⟩
  · apply (sub_lt_iff_lt_add'.mp ((lt_div_iff₀ hM').mpr hv))
  · apply le_sub_iff_add_le'.mp
    apply (div_le_iff₀ hM').mpr
    dsimp [v] at hr; nlinarith [mul_le_mul_of_nonneg_right hxy hM'.le]

/-- On each unit cell of the normalized scale, any two exceptional positions are
less than `ε p^k` apart. This includes cutoffs inside the exceptional region. -/
lemma exceptional_diameter_of_mesh (u : ℕ) (hu : 1≤u) {ε : ℝ} {J : ℕ}
    (H : ∀ x y : ℝ, u≤x → y≤u+1 → x+ε≤y → ∃ a i : ℕ, i≤J ∧ x < (d.q:ℝ)^a/(d.p:ℝ)^i ∧ (d.q:ℝ)^a/(d.p:ℝ)^i < y) :
    ∀ k ≥ J, ∀ s t : ℕ, u*d.p^k ≤ s → t ≤ (u+1)*d.p^k →
      padicNorm d.p (shifted d s) < (d.p:ℚ)^(k-J) →
      padicNorm d.p (shifted d t) < (d.p:ℚ)^(k-J) → (t:ℝ)-s < ε*(d.p:ℝ)^k := by
  intro k hk s t hs ht hbad₁ hbad₂
  by_contra! wide
  let S := (d.p:ℝ)^k
  have hS : 0<S := pow_pos (by exact_mod_cast d.hp.pos) _
  have hs' : (u:ℝ)*S ≤ s := by dsimp [S]; exact_mod_cast hs
  have ht' : (t:ℝ)≤(u+1)*S := by dsimp [S]; exact_mod_cast ht
  obtain ⟨a,i,hi,h₁,h₂⟩ := H ((s:ℝ)/S) ((t:ℝ)/S) ((le_div_iff₀ hS).mpr hs')
    ((div_le_iff₀ hS).mpr ht') (by rw [← le_sub_iff_add_le',← sub_div,le_div_iff₀ hS]; exact wide)
  have inv : (d.p:ℝ)^i * (d.p:ℝ)^(k-i) = S := by rw [← pow_add,Nat.add_sub_of_le (hi.trans hk)]
  have hi' : 0<(d.p:ℝ)^i := pow_pos (by exact_mod_cast d.hp.pos) _
  have e : ((index d (a,k-i):ℕ):ℝ) = ((d.q:ℝ)^a/(d.p:ℝ)^i)*S := by
    simp only [index,Nat.cast_mul,Nat.cast_pow]; rw [← inv]; field_simp
  have h₁' : s < index d (a,k-i) := by exact_mod_cast (show (s:ℝ) < (index d (a,k-i):ℝ) by rw [e]; exact (div_lt_iff₀ hS).mp h₁)
  have h₂' : index d (a,k-i) ≤ t := by exact_mod_cast (show (index d (a,k-i):ℝ) ≤ t by rw [e]; exact ((lt_div_iff₀ hS).mp h₂).le)
  have ratio : t ≤ d.q*s := calc
    t ≤ (u+1)*d.p^k := ht
    _ ≤ (d.q*u)*d.p^k := Nat.mul_le_mul_right _ (by nlinarith [Nat.mul_le_mul_right u d.hq])
    _ ≤ d.q*s := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hs
  have sep := separated_prefixes d h₁' h₂' ratio
  have pw : (d.p:ℚ)^(k-J) ≤ (d.p:ℚ)^(k-i) := pow_le_pow_right₀ (by exact_mod_cast d.hp.one_le) (by omega)
  exact (not_lt_of_ge (pw.trans sep)) (max_lt hbad₁ hbad₂)

theorem exceptional_diameter (u : ℕ) (hu : 1≤u) {ε : ℝ} (hε : 0<ε) :
    ∃ J : ℕ, ∀ k ≥ J, ∀ s t : ℕ, u*d.p^k ≤ s → t ≤ (u+1)*d.p^k →
      padicNorm d.p (shifted d s) < (d.p:ℚ)^(k-J) →
      padicNorm d.p (shifted d t) < (d.p:ℚ)^(k-J) → (t:ℝ)-s < ε*(d.p:ℝ)^k := by
  obtain ⟨J,H⟩ := threshold_mesh d u hu hε
  exact ⟨J,exceptional_diameter_of_mesh d u hu H⟩

/-- A set of integer starts of diameter at most `w` has at most `w+1` members. -/
lemma card_of_diameter (A : Finset ℕ) {w : ℝ} (hw : 0≤w)
    (diam : ∀ s∈A, ∀ t∈A, (t:ℝ)-s ≤ w) : (A.card:ℝ) ≤ w+1 := by
  rcases A.eq_empty_or_nonempty with rfl | hn
  · simp; linarith
  let l := A.min' hn
  let r := A.max' hn
  have h := diam l (A.min'_mem hn) r (A.max'_mem hn)
  have sub : A ⊆ Icc l r := fun i hi => mem_Icc.mpr ⟨A.min'_le _ hi,A.le_max' _ hi⟩
  have le := card_le_card sub
  rw [Nat.card_Icc] at le
  have hl : l ≤ r := A.min'_le _ (A.max'_mem hn)
  have le' : (A.card:ℝ) ≤ (r:ℝ)+1-l := by exact_mod_cast (show (A.card:ℤ)≤(r:ℤ)+1-l by omega)
  linarith

private lemma norm_le_prime_part (x : ℚ) : padicNorm d.p x ≤ (d.p:ℚ)^(x.den.factorization d.p) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  have hc := congrArg (padicNorm d.p) (Rat.den_mul_eq_num x)
  rw [padicNorm.mul,padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast x.den_ne_zero),padicValRat.of_nat,
    zpow_neg,zpow_natCast,inv_mul_eq_div] at hc
  have hpos : 0 < (d.p:ℚ) := by exact_mod_cast d.hp.pos
  rw [Nat.factorization_def _ d.hp]
  simpa using (div_le_iff₀ (pow_pos hpos _)).mp (hc.trans_le (padicNorm.of_int x.num))

/-- For every exceptional fraction `ε`, all sufficiently large loss thresholds `L`
have exceptional fraction at most `ε` on all sufficiently late prime-power shells.
The denominator is the reduced denominator at *every* digit position. -/
theorem severe_loss_rare {ε : ℝ} (hε : 0<ε) : ∀ᶠ L : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
    (((Ico (d.p^k) (d.p^(k+1))).filter (fun n => (shifted d n).den.factorization d.p ≤ k-L)).card : ℝ)
      ≤ ε*((d.p:ℝ)-1)*d.p^k := by
  classical
  let U := Ico 1 d.p
  let δ := ε/2
  have hδ : 0<δ := half_pos hε
  have H (u : ℕ) (hu : u∈U) := exceptional_diameter d u (mem_Ico.mp hu).1 hδ
  choose! cut hcut using H
  filter_upwards [eventually_gt_atTop (U.sup cut)] with L hL
  have grow := tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast d.hp.one_lt : (1:ℝ)<d.p)
  filter_upwards [eventually_ge_atTop L,grow.eventually_ge_atTop (1/δ)] with k hk size
  let S := d.p^k
  have hS : 0<S := pow_pos d.hp.pos _
  have hSr : (S:ℝ)=(d.p:ℝ)^k := by simp [S]
  let bad (n : ℕ) := (shifted d n).den.factorization d.p ≤ k-L
  let cell (u : ℕ) := (Ico (u*S) ((u+1)*S)).filter bad
  have per (u : ℕ) (hu : u∈U) : ((cell u).card:ℝ) ≤ ε*S := by
    have hJ := (le_sup hu : cut u ≤ U.sup cut).trans_lt hL
    have low {n : ℕ} (hn : bad n) : padicNorm d.p (shifted d n) < (d.p:ℚ)^(k-cut u) :=
      (norm_le_prime_part d _).trans_lt (pow_lt_pow_right₀ (by exact_mod_cast d.hp.one_lt) (by dsimp [bad] at hn; omega))
    have hc := card_of_diameter (cell u) (w:=δ*S) (by positivity) (fun s hs t ht => by
      obtain ⟨hi,hs'⟩ := mem_filter.mp hs; obtain ⟨hj,ht'⟩ := mem_filter.mp ht
      rw [hSr]; exact (hcut u hu k (by omega) s t (mem_Ico.mp hi).1 (mem_Ico.mp hj).2.le (low hs') (low ht')).le)
    have one : 1≤(S:ℝ)*δ := (div_le_iff₀ hδ).mp (hSr ▸ size)
    dsimp [δ] at hc one; linarith
  have cover : (Ico (d.p^k) (d.p^(k+1))).filter bad ⊆ U.biUnion cell := by
    intro n hn; obtain ⟨hn,hb⟩ := mem_filter.mp hn
    obtain ⟨lo,hi⟩ := mem_Ico.mp hn
    have hu₀ : 1≤n/S := (Nat.le_div_iff_mul_le hS).mpr (by simpa [S] using lo)
    have hu₁ : n/S<d.p := (Nat.div_lt_iff_lt_mul hS).mpr (by simpa [S,pow_succ'] using hi)
    exact mem_biUnion.mpr ⟨n/S,mem_Ico.mpr ⟨hu₀,hu₁⟩,mem_filter.mpr ⟨mem_Ico.mpr
      ⟨Nat.div_mul_le_self ..,by simpa [mul_comm] using Nat.lt_mul_div_succ n hS⟩,hb⟩⟩
  have total := (card_le_card cover).trans (card_biUnion_le ..)
  calc _ ≤ ∑ u ∈ U, ((cell u).card:ℝ) := by exact_mod_cast total
       _ ≤ ∑ _u ∈ U, ε*(S:ℝ) := sum_le_sum per
       _ = _ := by simp [U,Nat.cast_sub d.hp.one_le,hSr]; ring

end NormalityChecker.Localized
