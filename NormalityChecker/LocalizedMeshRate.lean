module

public import NormalityChecker.LocalizedMesh
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! An effective threshold mesh for two multiplicatively independent integers. -/
@[expose] public section
namespace NormalityChecker.Localized

/-- On a bounded positive interval, a logarithmic separation has a lower bound
from the distance of the endpoints. -/
private lemma log_gap {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y-x ≤ y*(Real.log y - Real.log x) := by
  have hy := hx.trans_le hxy
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  have H := mul_le_mul_of_nonneg_right h hy.le
  field_simp at H; nlinarith

/-- One positive return of the irrational rotation with explicit upper and lower
step sizes. The lower bound uses only that distinct positive integers differ by one. -/
theorem mesh_return {p q : ℕ} (hp : 2≤p) (hq : 2≤q) (cop : p.Coprime q)
    {M : ℕ} (hM : 0<M) : ∃ i a : ℕ, 0 < i ∧ i ≤ M ∧
      1 ≤ ((q:ℝ)*p^M)*|i*Real.log p-a*Real.log q| ∧
      |i*Real.log p-a*Real.log q| ≤ Real.log q/(M+1) := by
  let P := Real.log (p:ℝ); let Q := Real.log (q:ℝ)
  have hP : 0<P := Real.log_pos (by exact_mod_cast hp)
  have hQ : 0<Q := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨a,i,hi,hiM,near⟩ := Real.exists_int_int_abs_mul_sub_le (P/Q) hM
  have hsmall : (1:ℝ)/(M+1) < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast (by omega : 1<M+1)
  have ha : 0 ≤ a := by
    by_contra! hn
    have ha' : (a:ℝ) ≤ -1 := by exact_mod_cast (by omega : a ≤ -1)
    have h0 := mul_nonneg (by exact_mod_cast hi.le : (0:ℝ) ≤ i) (div_nonneg hP.le hQ.le)
    have := (le_abs_self _).trans_lt (near.trans_lt hsmall); linarith
  lift a to ℕ using ha; lift i to ℕ using hi.le
  have hi' : 0 < i := by exact_mod_cast hi
  have hiM' : i ≤ M := by exact_mod_cast hiM
  refine ⟨i,a,hi',hiM',?_,?_⟩
  all_goals
    have near' : |(i:ℝ)*P-(a:ℝ)*Q| ≤ Q/(M+1) := by
      have H := mul_le_mul_of_nonneg_right near hQ.le
      rw [← abs_of_pos hQ,← abs_mul] at H
      simp only [Int.cast_natCast,abs_of_pos hQ] at H
      convert H using 1 <;> congr 1 <;> field_simp
  · have pp : 0<(p:ℝ) := by exact_mod_cast (by omega : 0<p)
    have qq : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
    let A := p^i; let B := q^a
    have hab : A ≠ B := by
      intro h
      have cp := (cop.pow_left i).pow_right a
      change A.Coprime B at cp; rw [h] at cp
      have : A=1 := h.trans (by simpa using cp)
      exact (one_lt_pow₀ hp hi'.ne').ne' this
    have hA : (0:ℝ)<A := by exact_mod_cast pow_pos (by omega : 0<p) i
    have hB : (0:ℝ)<B := by exact_mod_cast pow_pos (by omega : 0<q) a
    have la : Real.log (A:ℝ) = i*P := by simp [A,P,Real.log_pow]
    have lb : Real.log (B:ℝ) = a*Q := by simp [B,Q,Real.log_pow]
    have hiQ : |(i:ℝ)*P-(a:ℝ)*Q| ≤ Q := near'.trans ((div_le_self hQ.le (by linarith [Nat.cast_nonneg (α:=ℝ) M] : (1:ℝ) ≤ M+1)))
    have boundA : (A:ℝ) ≤ (p:ℝ)^M := by exact_mod_cast Nat.pow_le_pow_right (by omega : 0<p) hiM'
    have boundB : (B:ℝ) ≤ q*A := by
      apply (Real.log_le_log_iff hB (mul_pos qq hA)).mp
      rw [Real.log_mul qq.ne' hA.ne',lb,la]; linarith [(abs_le.mp hiQ).1]
    have maxB : max (A:ℝ) B ≤ q*(p:ℝ)^M := max_le
      (boundA.trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast (by omega : 1 ≤ q))))
      (boundB.trans (mul_le_mul_of_nonneg_left boundA qq.le))
    change 1 ≤ ((q:ℝ)*p^M)*|i*P-a*Q|
    apply le_trans _ (mul_le_mul_of_nonneg_right maxB (abs_nonneg _))
    rcases lt_or_gt_of_ne hab with ab|ba
    · have le : (A:ℝ)+1 ≤ B := by exact_mod_cast ab
      have h := log_gap hA (by linarith : (A:ℝ)≤B); rw [la,lb] at h
      rw [max_eq_right (by linarith),abs_of_nonpos (by rw [← la,← lb]; exact sub_nonpos.mpr (Real.log_le_log hA (by linarith)))]
      linarith
    · have le : (B:ℝ)+1 ≤ A := by exact_mod_cast ba
      have h := log_gap hB (by linarith : (B:ℝ)≤A); rw [la,lb] at h
      rw [max_eq_left (by linarith),abs_of_nonneg (by rw [← la,← lb]; exact sub_nonneg.mpr (Real.log_le_log hB (by linarith)))]
      linarith
  · exact near'

private lemma rotation_grid {Q z step : ℝ} (hQ : 0<Q) (hz : 0≤z) (hstep : step ≠ 0) :
    ∃ h l : ℕ, (l:ℝ)*|step| ≤ Q ∧ |h*Q+l*step-z| ≤ |step| := by
  let h := ⌊z/Q⌋₊
  have base : (h:ℝ)*Q ≤ z := (le_div_iff₀ hQ).mp (Nat.floor_le (div_nonneg hz hQ.le))
  have top : z < ((h:ℝ)+1)*Q := (div_lt_iff₀ hQ).mp (Nat.lt_floor_add_one _)
  have approx {s y : ℝ} (hs : 0<s) (hy : 0≤y) :
      let l := ⌊y/s⌋₊; (l:ℝ)*s ≤ y ∧ y < ((l:ℝ)+1)*s :=
    ⟨(le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hy hs.le)),
     (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one _)⟩
  rcases lt_or_gt_of_ne hstep with neg|pos
  · let y := ((h:ℝ)+1)*Q-z
    let l := ⌊y/(-step)⌋₊
    have H := approx (neg_pos.mpr neg) (by dsimp [y]; linarith : 0≤y)
    change (l:ℝ)*(-step) ≤ y ∧ y < ((l:ℝ)+1)*(-step) at H
    refine ⟨h+1,l,?_,?_⟩ <;> rw [abs_of_neg neg] <;> dsimp [y] at H
    · linarith
    · push_cast; apply abs_le.mpr; constructor <;> linarith
  · let y := z-(h:ℝ)*Q
    let l := ⌊y/step⌋₊
    have H := approx pos (sub_nonneg.mpr base)
    change (l:ℝ)*step ≤ y ∧ y < ((l:ℝ)+1)*step at H
    refine ⟨h,l,?_,?_⟩ <;> rw [abs_of_pos pos] <;> dsimp [y] at H
    · linarith
    · apply abs_le.mpr; constructor <;> linarith

/-- A threshold occurs in every interval of width `3 U log(q)/(M+1)` in
`[1,U]`, using a layer at most `M*q^2*p^M`. All exponents are natural. -/
theorem effective_threshold_mesh {p q : ℕ} (hp : 2≤p) (hq : 2≤q) (cop : p.Coprime q)
    {M : ℕ} (hM : 0<M) {x y U : ℝ} (hx : 1≤x) (hy : y≤U) (hU : 0<U)
    (wide : x + 3*U*Real.log q/(M+1) ≤ y) :
    ∃ a i : ℕ, i ≤ M*q^2*p^M ∧ x < (q:ℝ)^a/(p:ℝ)^i ∧ (q:ℝ)^a/(p:ℝ)^i < y := by
  obtain ⟨i,a,_,hiM,separation,near⟩ := mesh_return hp hq cop hM
  let Q := Real.log (q:ℝ); let P := Real.log (p:ℝ)
  let step := a*Q-i*P
  have hQ : 0<Q := Real.log_pos (by exact_mod_cast hq)
  have hM' : (0:ℝ)<M+1 := by positivity
  have s : |step| = |i*P-a*Q| := abs_sub_comm ..
  have hstep : step ≠ 0 := by intro h; rw [← s,h,abs_zero,mul_zero] at separation; norm_num at separation
  have delta := div_pos hQ hM'
  change |i*P-a*Q| ≤ Q/(M+1) at near
  have hwide : 3*U*(Q/(M+1)) ≤ y-x := by rw [← mul_div_assoc]; dsimp [Q]; linarith
  have hxpos : 0<x := by linarith
  have hxy : x<y := by nlinarith [mul_pos hU delta]
  have hypos := hxpos.trans hxy
  have gap := log_gap hxpos hxy.le
  have logs := Real.log_lt_log hxpos hxy
  have halfwidth : 2*(Q/(M+1)) < Real.log y - Real.log x := by
    have H := mul_le_mul_of_nonneg_right hy (sub_nonneg.mpr logs.le)
    have := mul_pos hU delta
    apply lt_of_mul_lt_mul_left (a:=U) _ hU.le; nlinarith only [gap,hwide,H,this]
  let z := (Real.log x + Real.log y)/2
  obtain ⟨h,l,len,close⟩ := rotation_grid hQ (by dsimp [z]; linarith [Real.log_nonneg hx] : 0≤z) hstep
  have budget : (l:ℝ) ≤ q^2*(p:ℝ)^M := by
    have H := mul_le_mul_of_nonneg_left separation (Nat.cast_nonneg (α:=ℝ) l)
    rw [← s] at H
    have H' := mul_le_mul_of_nonneg_right len (show (0:ℝ)≤q*p^M by positivity)
    have qlog := Real.log_le_self (Nat.cast_nonneg (α:=ℝ) q)
    have cap := mul_le_mul_of_nonneg_right qlog (show (0:ℝ)≤q*p^M by positivity)
    dsimp [Q] at H'; nlinarith only [H,H',cap]
  have limit : l ≤ q^2*p^M := by exact_mod_cast budget
  refine ⟨h+l*a,l*i,(Nat.mul_le_mul limit hiM).trans_eq (by ring),?_⟩
  have pp : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have qq : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have val : Real.log ((q:ℝ)^(h+l*a)/(p:ℝ)^(l*i)) = h*Q+l*step := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow]; push_cast; dsimp [step,P,Q]; ring
  rw [← Real.log_lt_log_iff hxpos (by positivity), ← Real.log_lt_log_iff (by positivity) hypos,val]
  rw [s,abs_le] at close; dsimp only [z] at close; constructor <;> linarith

end NormalityChecker.Localized
