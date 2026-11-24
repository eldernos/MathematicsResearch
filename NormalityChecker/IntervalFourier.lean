module

public import NormalityChecker.LocalizedMesh
public import NormalityChecker.FourierTest

/-! A finite smoothing bound for interval counts, using squared geometric sums on a grid. -/
@[expose] public section
open Finset
open scoped ComplexConjugate
namespace NormalityChecker.IntervalFourier

private lemma phase_pow (x : ℝ) (r : ℕ) : phase x ^ r = phase (r*x) := by
  induction r with
  | zero => simp [phase]
  | succ r ih => rw [pow_succ,ih,← phase_add]; congr 1; push_cast; ring

private lemma phase_conj (x : ℝ) : conj (phase x) = phase (-x) := by
  simp [phase,← Complex.exp_conj,map_ofNat]

private noncomputable def kernel (H : ℕ) (x : ℝ) := ‖∑ r ∈ range H, phase x ^ r‖^2

private lemma kernel_expand (H : ℕ) (x : ℝ) : (kernel H x : ℂ) =
    ∑ r ∈ range H, ∑ s ∈ range H, phase (((r:ℝ)-s)*x) := by
  unfold kernel; rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj,map_sum,sum_mul]
  apply sum_congr rfl; intro r _; rw [mul_sum]; apply sum_congr rfl; intro s _
  rw [phase_pow,phase_pow,phase_conj,← phase_add]; congr 1; ring

private lemma grid_phase {H : ℕ} [NeZero H] (z : ZMod H) (x : ℝ) (r s : ℕ) :
    phase (((r:ℝ)-s)*(x-z.val/H)) = phase (((r:ℝ)-s)*x)*ZMod.stdAddChar (((s:ZMod H)-(r:ZMod H))*z) := by
  have h := ZMod.stdAddChar_coe (N:=H) (((s:ℤ)-r)*z.val)
  push_cast at h; rw [ZMod.natCast_zmod_val] at h; rw [h]; unfold phase; push_cast; rw [← Complex.exp_add]; congr 1; ring

private lemma kernel_total {H : ℕ} [NeZero H] (x : ℝ) :
    ∑ z : ZMod H, kernel H (x-z.val/H) = (H:ℝ)^2 := by
  have orth (r s : ℕ) (hr : r<H) (hs : s<H) : ∑ z : ZMod H, ZMod.stdAddChar (((s:ZMod H)-(r:ZMod H))*z) =
      if s=r then (H:ℂ) else 0 := by
    split_ifs with e
    · simp [e,ZMod.card]
    · apply AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar H _)
      intro h; apply e; have h' := congrArg ZMod.val (sub_eq_zero.mp h)
      simpa [ZMod.val_natCast,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hs] using h'
  apply Complex.ofReal_injective
  push_cast; simp_rw [kernel_expand,grid_phase]
  rw [sum_comm]
  calc _ = ∑ r ∈ range H, ∑ s ∈ range H, phase (((r:ℝ)-s)*x)*(if s=r then (H:ℂ) else 0) := by
           apply sum_congr rfl; intro r hr; rw [sum_comm]; apply sum_congr rfl; intro s hs
           rw [← mul_sum,orth r s (mem_range.mp hr) (mem_range.mp hs)]
       _ = _ := by simp +contextual [mul_ite,phase,pow_two]

private lemma kernel_count {H T : ℕ} [NeZero H] (u : ℕ → ℝ) (z : ZMod H) {E : ℝ} (hE : 0≤E)
    (fourier : ∀ h : ℤ, h ≠ 0 → h.natAbs < H → ‖∑ n ∈ range T, phase (h*u n)‖ ≤ E) :
    ∑ n ∈ range T, kernel H (u n-z.val/H) ≤ H*T+(H:ℝ)^2*E := by
  have terms (r : ℕ) (hr : r∈range H) (s : ℕ) (hs : s∈range H) :
      ‖∑ n ∈ range T, phase (((r:ℝ)-s)*(u n-z.val/H))‖ ≤ (if s=r then (T:ℝ) else 0)+E := by
    by_cases e : s=r
    · simp [e,phase,hE]
    · simp only [ite_eq_right e,zero_add]; simp_rw [grid_phase]; rw [← sum_mul,norm_mul,show ‖ZMod.stdAddChar (((s:ZMod H)-(r:ZMod H))*z)‖ = 1 from Circle.norm_coe _,mul_one]
      convert fourier ((r:ℤ)-s) (by omega) (by have := mem_range.mp hr; have := mem_range.mp hs; omega) using 2
      push_cast; rfl
  have eqn : ((∑ n ∈ range T, kernel H (u n-z.val/H):ℝ):ℂ) = ∑ r ∈ range H, ∑ s ∈ range H,
      ∑ n ∈ range T, phase (((r:ℝ)-s)*(u n-z.val/H)) := by
    push_cast; simp_rw [kernel_expand]; rw [sum_comm]; apply sum_congr rfl; intro _ _; rw [sum_comm]
  have bound := (norm_sum_le ..).trans (sum_le_sum (fun r hr => (norm_sum_le ..).trans (sum_le_sum (terms r hr))))
  rw [← eqn,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _)] at bound
  simpa +contextual [sum_add_distrib,pow_two,mul_add,mul_assoc] using bound

private lemma chord {x δ : ℝ} (hδ : 0<δ) (lo : δ ≤ |x|) (hi : |x| ≤ 1-δ) :
    4*δ ≤ ‖phase x - 1‖ := by
  have bound {y : ℝ} (yl : δ ≤ y) (yh : y ≤ 1-δ) : 2*δ ≤ Real.sin (Real.pi*y) := by
    by_cases mid : y ≤ 1/2
    · have H := Real.mul_le_sin (mul_nonneg Real.pi_pos.le (hδ.le.trans yl))
        (show Real.pi*y≤Real.pi/2 by linarith [mul_le_mul_of_nonneg_left mid Real.pi_pos.le])
      field_simp [Real.pi_ne_zero] at H; nlinarith [mul_le_mul_of_nonneg_left yl Real.pi_pos.le,Real.pi_pos]
    · rw [← Real.sin_pi_sub]; have H := Real.mul_le_sin (x:=Real.pi-Real.pi*y)
            (by nlinarith [mul_le_mul_of_nonneg_left yh Real.pi_pos.le,mul_pos Real.pi_pos hδ])
            (by nlinarith [mul_lt_mul_of_pos_left (lt_of_not_ge mid) Real.pi_pos])
      field_simp [Real.pi_ne_zero] at H
      rw [show Real.pi-Real.pi*y=Real.pi*(1-y) by ring]; linarith
  have eqn : phase x = Complex.exp (Complex.I*((2*Real.pi*x:ℝ):ℂ)) := by unfold phase; push_cast; congr 1; ring
  rw [eqn,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,show 2*Real.pi*x/2=Real.pi*x by ring]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have H := bound lo hi
  rcases le_or_gt 0 x with pos|neg
  · rw [abs_of_nonneg pos] at H; linarith [le_abs_self (Real.sin (Real.pi*x))]
  · rw [abs_of_neg neg,mul_neg,Real.sin_neg] at H; linarith [neg_le_abs (Real.sin (Real.pi*x))]

private lemma kernel_far {H : ℕ} {δ x : ℝ} (hδ : 0<δ) (lo : δ ≤ |x|) (hi : |x| ≤ 1-δ) :
    kernel H x ≤ (1/δ)^2 := by
  have h := chord hδ lo hi
  let A := ‖∑ r ∈ range H, phase x^r‖
  have ga : A*‖phase x-1‖ ≤ 2 := by
    dsimp [A]; rw [← norm_mul,geom_sum_mul]; simpa [norm_pow,norm_phase,one_add_one_eq_two] using norm_sub_le (phase x^H) 1
  have le : A ≤ 1/δ := (le_div_iff₀ hδ).mpr (by nlinarith [mul_le_mul_of_nonneg_left h (show 0≤A from norm_nonneg _),mul_nonneg (show 0≤A from norm_nonneg _) hδ.le])
  exact pow_le_pow_left₀ (norm_nonneg _) le _

private noncomputable def nodes (H : ℕ) [NeZero H] (a c : ℝ) : Finset (ZMod H) :=
  univ.filter fun z => a ≤ (z.val:ℝ)/H ∧ (z.val:ℝ)/H ≤ c

private lemma node_count {H : ℕ} [NeZero H] {a c : ℝ} (le : a ≤ c) :
    ((nodes H a c).card:ℝ) ≤ (c-a)*H+1 := by
  have pos : (0:ℝ)<H := by exact_mod_cast NeZero.pos H
  rw [← card_image_of_injective _ (ZMod.val_injective H)]
  apply Localized.card_of_diameter _ (mul_nonneg (sub_nonneg.mpr le) pos.le)
  intro i hi j hj
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hi; obtain ⟨y,hy,rfl⟩ := mem_image.mp hj
  have l := (le_div_iff₀ pos).mp (mem_filter.mp hx).2.1
  have r := (div_le_iff₀ pos).mp (mem_filter.mp hy).2.2
  linarith

noncomputable def count (u : ℕ → ℝ) (a c : ℝ) (T : ℕ) : ℕ :=
  ((range T).filter (fun n => a ≤ u n ∧ u n < c)).card

private noncomputable def error (H T : ℕ) (δ E : ℝ) := T*(4*δ+3/H+(1/δ)^2/H)+H*E

private lemma count_upper {H T : ℕ} [NeZero H] (u : ℕ → ℝ) {a c δ E : ℝ} (hac : a≤c)
    (ha : 0≤a) (hc : c≤1) (hδ : 0<δ) (hE : 0≤E)
    (fourier : ∀ h : ℤ, h ≠ 0 → h.natAbs < H → ‖∑ n ∈ range T, phase (h*u n)‖ ≤ E) :
    (count u a c T:ℝ) ≤ T*(c-a)+error H T δ E := by
  classical
  let G := nodes H (a-δ) (c+δ) ∪ nodes H 0 δ ∪ nodes H (1-δ) 1
  have pos : (0:ℝ)<H := by exact_mod_cast NeZero.pos H
  have card : (G.card:ℝ) ≤ ((c-a)+4*δ)*H+3 := by
    have le := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _ :
      _ ≤ (nodes H (a-δ) (c+δ)).card + (nodes H 0 δ).card + (nodes H (1-δ) 1).card)
    change (G.card:ℕ) ≤ _ at le
    have hs : (G.card:ℝ) ≤ ((nodes H (a-δ) (c+δ)).card:ℝ) + (nodes H 0 δ).card + (nodes H (1-δ) 1).card := by exact_mod_cast le
    linarith [node_count (H:=H) (a:=a-δ) (c:=c+δ) (by linarith),node_count (H:=H) hδ.le,
      node_count (H:=H) (a:=1-δ) (c:=1) (by linarith)]
  have card' : G.card ≤ H := by simpa [ZMod.card] using (card_le_card (subset_univ G))
  have nonneg (x : ℝ) : 0 ≤ kernel H x := sq_nonneg _
  have single (n : ℕ) : (if a≤u n ∧ u n<c then (H:ℝ)^2 else 0) ≤
      (∑ z ∈ G, kernel H (u n-z.val/H)) + H*(1/δ)^2 := by
    split_ifs with h
    · have far (z : ZMod H) (hz : z ∉ G) : kernel H (u n-z.val/H) ≤ (1/δ)^2 := by
        simp only [G,mem_union,nodes,mem_filter,mem_univ,true_and,not_or] at hz
        have z0 : 0 ≤ (z.val:ℝ)/H := by positivity
        have z1 : (z.val:ℝ)/H ≤ 1 := (div_le_one pos).mpr (by exact_mod_cast (ZMod.val_lt z).le)
        have l : δ < (z.val:ℝ)/H := lt_of_not_ge (fun he => hz.1.2 ⟨z0,he⟩)
        have r : (z.val:ℝ)/H < 1-δ := lt_of_not_ge (fun he => hz.2 ⟨he,z1⟩)
        apply kernel_far hδ _ (abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩)
        rcases lt_or_ge ((z.val:ℝ)/H) (a-δ) with left|right
        · exact le_trans (by linarith [h.1]) (le_abs_self _)
        · have gt : c+δ < (z.val:ℝ)/H := lt_of_not_ge (fun he => hz.1.1 ⟨right,he⟩)
          exact le_trans (by linarith [h.2]) (neg_le_abs _)
      rw [← kernel_total (H:=H) (u n),← sum_sdiff (s₁:=G) (s₂:=univ) (subset_univ _)]
      have F := sum_le_sum (s:=univ \ G) (fun z hz => far z (mem_sdiff.mp hz).2)
      have size : (univ \ G).card ≤ H := by simpa [ZMod.card] using card_le_card (sdiff_subset (s:=univ) (t:=G))
      simp only [sum_const,nsmul_eq_mul] at F
      linarith [mul_le_mul_of_nonneg_right (by exact_mod_cast size : ((univ \ G).card:ℝ)≤H) (sq_nonneg (1/δ))]
    · positivity [sum_nonneg (fun z (_ : z ∈ G) => nonneg (u n-z.val/H))]
  have all := sum_le_sum (s:=range T) (fun n _ => single n)
  rw [← sum_filter,sum_add_distrib,sum_comm] at all
  simp only [sum_const,nsmul_eq_mul,card_range] at all
  have sums := sum_le_sum (s:=G) (fun z _ => kernel_count u z hE fourier)
  simp only [sum_const,nsmul_eq_mul] at sums
  change (count u a c T:ℝ)*H^2 ≤ _ at all
  have ht : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_right card (show (0:ℝ) ≤ H*T by positivity)
  have h2 := mul_le_mul_of_nonneg_right (by exact_mod_cast card' : (G.card:ℝ) ≤ H) (show 0≤(H:ℝ)^2*E by positivity)
  apply le_of_mul_le_mul_right (a:=(H:ℝ)^2) _ (by positivity)
  calc _ ≤ ((c-a+4*δ)*H+3)*(H*T) + H*((H:ℝ)^2*E) + T*(H*(1/δ)^2) := by nlinarith only [all,sums,h1,h2]
       _ = _ := by unfold error; field_simp; ring

/-- Interval-count error from finitely many Fourier sums. `E` bounds the
unnormalized sums at every nonzero frequency of absolute value less than `H`. -/
theorem interval_count_bound {H T : ℕ} [NeZero H] (u : ℕ → ℝ) {a c δ E : ℝ}
    (hu : ∀ n, 0≤u n ∧ u n<1) (ha : 0≤a) (hac : a≤c) (hc : c≤1) (hδ : 0<δ) (hE : 0≤E)
    (fourier : ∀ h : ℤ, h ≠ 0 → h.natAbs < H → ‖∑ n ∈ range T, phase (h*u n)‖ ≤ E) :
    |(count u a c T:ℝ)-T*(c-a)| ≤ 2*(T*(4*δ+3/H+(1/δ)^2/H)+H*E) := by
  have h1 := count_upper u hac ha hc hδ hE fourier
  have h2 := count_upper u ha le_rfl (hac.trans hc) hδ hE fourier
  have h3 := count_upper u hc (ha.trans hac) le_rfl hδ hE fourier
  have partition : count u 0 a T + count u a c T + count u c 1 T = T := by
    classical
    have each (n : ℕ) : (if 0≤u n ∧ u n<a then 1 else 0 : ℕ) + (if a≤u n ∧ u n<c then 1 else 0) +
        (if c≤u n ∧ u n<1 then 1 else 0) = 1 := by
      have := hu n; split_ifs <;> first | rfl | exfalso; grind
    simpa [count,sum_add_distrib,← sum_filter] using sum_congr (s₁:=range T) rfl (fun i _ => each i)
  have total : (count u 0 a T:ℝ) + count u a c T + count u c 1 T = T := by exact_mod_cast partition
  have pos : 0 ≤ error H T δ E := by unfold error; positivity
  change _ ≤ 2*error H T δ E; apply abs_le.mpr; constructor <;> linarith

end NormalityChecker.IntervalFourier
