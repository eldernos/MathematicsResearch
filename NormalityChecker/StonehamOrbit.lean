module

public import NormalityChecker.StonehamOrder
public import NormalityChecker.Correlations
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section
open Finset Filter
open scoped Topology ComplexConjugate
namespace NormalityChecker

private noncomputable def orbitSum {q : ℕ} [NeZero q] (b T : ℕ) (z : ZMod q) : ℂ :=
  ∑ i ∈ range T, ZMod.stdAddChar ((b:ZMod q)^i*z)

/-- Orthogonality over all additive frequencies for distinct points of the orbit. -/
private lemma orbit_energy {q : ℕ} [NeZero q] (b T : ℕ) (hT : T ≤ orderOf (b:ZMod q)) :
    ∑ z : ZMod q, ‖orbitSum b T z‖^2 = (T:ℝ)*q := by
  classical
  have orth (x : ZMod q) : ∑ z : ZMod q, ZMod.stdAddChar (x*z) = if x=0 then (q:ℂ) else 0 := by
    split_ifs with h
    · simp [h, ZMod.card]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)
  have conjχ (x : ZMod q) : conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]; rfl
  have row (i : ℕ) (hi : i∈range T) :
      ∑ j ∈ range T, ∑ z : ZMod q, ZMod.stdAddChar (((b:ZMod q)^i-(b:ZMod q)^j)*z) = q := by
    simp_rw [orth, sub_eq_zero]
    have eqn (j : ℕ) (hj : j∈range T) : (b:ZMod q)^i = (b:ZMod q)^j ↔ i=j :=
      ⟨fun e => pow_injOn_Iio_orderOf ((mem_range.mp hi).trans_le hT) ((mem_range.mp hj).trans_le hT) e,
       fun e => e ▸ rfl⟩
    rw [sum_congr rfl (fun j hj => if_congr (eqn j hj) rfl rfl)]
    simp [hi]
  have energy : ∑ z : ZMod q, orbitSum b T z * conj (orbitSum b T z) = (T:ℂ)*q := by
    simp only [orbitSum,map_sum,sum_mul,mul_sum,conjχ,← AddChar.map_add_eq_mul,← sub_eq_add_neg,← sub_mul]
    rw [sum_comm]
    simp_rw [sum_comm (s:=univ) (t:=range T)]
    rw [sum_comm, sum_congr rfl row]; simp
  simpa [Complex.mul_conj,Complex.normSq_eq_norm_sq,← Complex.ofReal_pow, ← Complex.ofReal_sum] using congrArg Complex.re energy

private lemma orbit_shift {q : ℕ} [NeZero q] (b T j : ℕ) (z : ZMod q) :
    ‖orbitSum b T z - orbitSum b T ((b:ZMod q)^j*z)‖ ≤ 2*j := by
  let f (i : ℕ) := ZMod.stdAddChar ((b:ZMod q)^i*z)
  have e := congrArg (fun t : ℕ => ∑ i ∈ range t, f i) (Nat.add_comm T j)
  simp only [sum_range_add] at e
  have norm (n : ℕ) : ‖∑ i ∈ range j, f (n+i)‖ ≤ j := by
    simpa only [show ∀ i, ‖f i‖ = 1 from fun _ => Circle.norm_coe _, sum_const,card_range,
      nsmul_eq_mul,mul_one] using norm_sum_le (range j) (fun i => f (n+i))
  have eqn : orbitSum b T z - orbitSum b T ((b:ZMod q)^j*z) =
      (∑ i ∈ range j, f (0+i)) - ∑ i ∈ range j, f (T+i) := by
    simp only [zero_add]
    have h : orbitSum b T ((b:ZMod q)^j*z) = ∑ i ∈ range T, f (j+i) := by
      simp [orbitSum,f,pow_add,mul_left_comm,mul_assoc]
    rw [h]; change (∑ i ∈ range T, f i) - _ = _
    linear_combination e
  rw [eqn]
  linarith [norm_sub_le (∑ i ∈ range j, f (0+i)) (∑ i ∈ range j, f (T+i)),norm 0,norm T]

private lemma short_orbit {q H : ℕ} [NeZero q] (b T : ℕ) (z : ZMod q) (hT : T≤orderOf (b:ZMod q))
    (hTq : T≤q) (hH : 0<H) {δ : ℝ} (hδ : 0<δ) (hlarge : 1 ≤ H*δ^2)
    (hinj : Set.InjOn (fun j : ℕ => (b:ZMod q)^j*z) (range H)) :
    ‖orbitSum b T z‖ ≤ δ*q + 2*H := by
  classical
  have htotal : ∑ j ∈ range H, ‖orbitSum b T ((b:ZMod q)^j*z)‖^2 ≤ (T:ℝ)*q := by
    rw [← orbit_energy (q:=q) b T hT]
    exact sum_le_sum_of_injOn (fun j => (b:ZMod q)^j*z) hinj (by simp)
      (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  obtain ⟨j,hj,hsmall⟩ : ∃ j∈range H, ‖orbitSum b T ((b:ZMod q)^j*z)‖ ≤ δ*q := by
    by_contra! h
    have hsum := sum_lt_sum_of_nonempty (show (range H).Nonempty from ⟨0,mem_range.mpr hH⟩)
      (fun j hj => (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr (h j hj))
    simp only [sum_const,card_range,nsmul_eq_mul] at hsum
    have hqT : (T:ℝ) ≤ q := by exact_mod_cast hTq
    nlinarith [mul_le_mul_of_nonneg_right hlarge (sq_nonneg (q:ℝ)),
      mul_le_mul_of_nonneg_right hqT (Nat.cast_nonneg (α:=ℝ) q)]
  have ht := norm_add_le (orbitSum b T z - orbitSum b T ((b:ZMod q)^j*z)) (orbitSum b T ((b:ZMod q)^j*z))
  rw [sub_add_cancel] at ht
  have hj' : (j:ℝ) ≤ H := by exact_mod_cast (mem_range.mp hj).le
  linarith [orbit_shift b T j z]

/-- Uniform cancellation through any prefix of length at most c^k. The starting
numerator may vary with the scale, provided it is coprime to c. -/
theorem stoneham_orbit_small {b c : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c)
    (hbc : b.Coprime c) (h : ℤ) (hh : h≠0) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ A : ℕ, A.Coprime c → ∀ T ≤ c^k,
      ‖∑ i ∈ range T, phase ((h:ℝ)*A*(b:ℝ)^i/(c:ℝ)^k)‖ ≤ ε*(c:ℝ)^k := by
  classical
  let : NeZero c := ⟨by omega⟩
  let C := b^c.totient-1
  have hC : 0<C := Nat.sub_pos_of_lt (one_lt_pow₀ hb (Nat.totient_pos.mpr (by omega)).ne')
  let δ := ε/(2*C)
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨H,hH⟩ := exists_nat_gt (1/δ^2)
  have hH' : 0<H := by exact_mod_cast (lt_trans (by positivity : 0<1/δ^2) hH)
  have hlarge := ((div_lt_iff₀ (by positivity)).mp hH).le
  have grow : Tendsto (fun k : ℕ => c^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hc
  have distinct (i j : ℕ) : ∀ᶠ k : ℕ in atTop,
      (b:ZMod (c^k))^i*h = (b:ZMod (c^k))^j*h → i=j := by
    let x := (b:ℤ)^j*h-(b:ℤ)^i*h
    filter_upwards [grow.eventually_gt_atTop x.natAbs] with k hk e
    have hd : ((c^k:ℕ):ℤ) ∣ x := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
      (by push_cast; exact e : (((b:ℤ)^i*h:ℤ):ZMod (c^k)) = (((b:ℤ)^j*h:ℤ):ZMod (c^k)))
    have hx : x=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hk)
    apply pow_right_injective₀ (by exact_mod_cast (show 0<b by omega) : (0:ℤ)<b)
      (by exact_mod_cast (show b≠1 by omega))
    exact mul_right_cancel₀ hh (sub_eq_zero.mp hx).symm
  have dists := (eventually_all_finset (range H)).mpr (fun i _ =>
    (eventually_all_finset (range H)).mpr (fun j _ => distinct i j))
  have grow' : Tendsto (fun k : ℕ => (c:ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hc)
  filter_upwards [dists,grow'.eventually_ge_atTop (2*H/δ)] with k hd hq
  let q := c^k
  let t := orderOf (b:ZMod q)
  have hq' : 2*(H:ℝ) ≤ δ*q := by
    rw [div_le_iff₀ hδ] at hq
    simpa [q,mul_comm] using hq
  have segment (w : ZMod q) (hw : IsUnit w) (T : ℕ) (hT : T≤t) (hTq : T≤q) :
      ‖orbitSum b T ((h:ZMod q)*w)‖ ≤ 2*δ*q := by
    have hi : Set.InjOn (fun j : ℕ => (b:ZMod q)^j*((h:ZMod q)*w)) (range H) := by
      intro i hi j hj e
      simp only [← mul_assoc] at e
      exact hd i hi j hj (hw.mul_right_cancel e)
    linarith [short_orbit b T _ hT hTq hH' hδ hlarge hi]
  have blocks (d : ℕ) (T : ℕ) (hT : T≤d*t) (hTq : T≤q) (w : ZMod q) (hw : IsUnit w) :
      ‖orbitSum b T ((h:ZMod q)*w)‖ ≤ d*(2*δ*q) := by
    induction d generalizing T w with
    | zero => simp_all [orbitSum]
    | succ d ih =>
      let L := min T t
      have hL : L≤T := min_le_left ..
      have hd' : T-L ≤ d*t := by dsimp [L]; rw [Nat.succ_mul] at hT; omega
      have hu := ((ZMod.isUnit_iff_coprime b q).mpr (hbc.pow_right k)).pow L
      have split : orbitSum b T ((h:ZMod q)*w) =
          orbitSum b L ((h:ZMod q)*w) + orbitSum b (T-L) ((h:ZMod q)*((b:ZMod q)^L*w)) := by
        unfold orbitSum
        conv_lhs => rw [← Nat.add_sub_of_le hL, sum_range_add]
        simp [pow_add,mul_assoc,mul_left_comm,mul_comm]
      rw [split]
      have h₁ := segment w hw L (min_le_right ..) (hL.trans hTq)
      have h₂ := ih (T-L) hd' (by omega) _ (hu.mul hw)
      have ht := (norm_add_le _ _).trans (add_le_add h₁ h₂)
      push_cast; linarith
  intro A hA T hT
  have H' := blocks C T (hT.trans (stoneham_order_bound hb hc ho hbc k)) hT (A:ZMod q)
    ((ZMod.isUnit_iff_coprime A q).mpr (hA.pow_right k))
  have eqn (i : ℕ) : ZMod.stdAddChar ((b:ZMod q)^i*((h:ZMod q)*(A:ZMod q))) =
      phase ((h:ℝ)*A*(b:ℝ)^i/(c:ℝ)^k) := by
    have E := ZMod.stdAddChar_coe (N:=q) ((b:ℤ)^i*(h*A))
    push_cast at E
    rw [E, phase]; congr 1; dsimp [q]; push_cast; ring
  simp only [orbitSum,eqn] at H'
  have he : (C:ℝ)*(2*δ*q) = ε*(c:ℝ)^k := by dsimp [δ,q]; push_cast; field_simp
  exact H'.trans_eq he

end NormalityChecker
