module

public import NormalityChecker.QuadraticOrbitModel
public import NormalityChecker.SupportDiscrepancy
public import Mathlib.Data.Nat.Factorization.Induction

/-! Uniform interval counts on every partial lower half and on every partial
upper half whose actual reduced denominator exceeds the prescribed cutoff. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.QuadraticOrbit

/-- Errors are measured relative to the half-shell length, including for a
partial last block of length zero. The same threshold works for all intervals. -/
def GoodHalves (b : ℕ) (x : ℝ) (q : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ᶠ r : ℕ in atTop, ∀ u : ℕ,
    (u = 2 ∨ (u = 3 ∧ M ≤ q r)) → ∀ T ≤ 2^r, ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 →
    ‖∑ i ∈ range T, Localized.centered (shift b x) a c (u*2^r+i)‖ ≤ ε*(2:ℝ)^r

private theorem prime_support_shift {b D : ℕ} (hb : 0 < b) (hd : 0 < D) :
    ∃ s a d : ℕ, 0 < a ∧ 0 < d ∧ b.Coprime d ∧ b^s*d = D*a := by
  induction D using induction_on_primes with
  | zero => omega
  | one => exact ⟨0,1,1,by decide,by decide,by simp,by simp⟩
  | prime_mul p n hp ih =>
    obtain ⟨s,a,d,ha,hd',cop,eqn⟩ := ih (Nat.pos_of_mul_pos_left hd)
    by_cases divides : p ∣ b
    · obtain ⟨t,ht⟩ := divides
      have tp : 0 < t := Nat.pos_of_mul_pos_left (ht ▸ hb)
      refine ⟨s+1,t*a,d,by positivity,hd',cop,?_⟩
      rw [pow_succ',Nat.mul_assoc,eqn]
      nth_rw 1 [ht]
      ring
    · refine ⟨s,a,p*d,ha,Nat.mul_pos hp.pos hd',(hp.coprime_iff_not_dvd.mpr divides).symm.mul_right cop,?_⟩
      linear_combination (norm := ring) p*eqn

private theorem shifted_window (f : ℕ → ℂ) (unit : ∀ n, ‖f n‖ ≤ 1) (s n T : ℕ) :
    ‖∑ i ∈ range T, f (n+i)‖ ≤ ‖∑ i ∈ range T, f (n+i+s)‖ + 2*s := by
  have eqn : (∑ i ∈ range T, f (n+i)) + (∑ i ∈ range s, f (n+T+i)) =
      (∑ i ∈ range s, f (n+i)) + ∑ i ∈ range T, f (n+i+s) := by
    have h := congrArg (fun z => ∑ i ∈ range z, f (n+i)) (Nat.add_comm T s)
    simp only [sum_range_add] at h
    simpa only [Nat.add_assoc,Nat.add_comm s] using h
  have small (m : ℕ) : ‖∑ i ∈ range s, f (m+i)‖ ≤ s :=
    (norm_sum_le ..).trans ((sum_le_sum (fun i _ => unit (m+i))).trans_eq (by simp))
  have H := norm_sub_le ((∑ i ∈ range s, f (n+i)) + ∑ i ∈ range T, f (n+i+s)) (∑ i ∈ range s, f (n+T+i))
  conv_lhs at H => rw [← eqn,add_sub_cancel_right]
  linarith only [H, norm_add_le (∑ i ∈ range s, f (n+i)) (∑ i ∈ range T, f (n+i+s)),small n,small (n+T)]

/-- Multiply the true model by a fixed nonzero rational supported away from
the radix in its denominator. This permits a direct interval estimate. -/
theorem scaled_good_halves {b : ℕ} (hb : 3 ≤ b) (odd : Odd b) (A B C : ℤ)
    (nz : A ≠ 0) (z : ℚ) (hz : z ≠ 0) (cop : b.Coprime z.den) :
    GoodHalves b ((z:ℝ)*value b A B C) (upperDen b A B C) := by
  let P := model b A B C
  let R (n : ℕ) := z*P n
  let d := z.den
  let G := z⁻¹.den
  have dp : 0 < d := z.pos
  have gp : 0 < G := z⁻¹.pos
  have recover (n : ℕ) : (P n).den ≤ G*(R n).den := by
    apply Nat.le_of_dvd (Nat.mul_pos gp (R n).pos)
    simpa only [R, inv_mul_cancel_left₀ hz] using Rat.mul_den_dvd z⁻¹ (R n)
  have tail := (shifted_tail (by omega : 2 ≤ b) A B C).const_mul (z:ℝ)
  have tr : Tendsto (fun n => (b:ℝ)^n*((z:ℝ)*value b A B C) - (R n:ℝ)) atTop (𝓝 0) := by
    simpa only [R,P,Rat.cast_mul,mul_zero,mul_sub,mul_left_comm (z:ℝ)] using tail
  intro ε ep
  obtain ⟨M,N,block⟩ := smooth_interval_block (d:=8)
    (fixed_support_orbit_estimate (by omega : 1<b) (by dsimp [d] at *; omega : 1<2*d)
      (odd.coprime_two_right.mul_right cop)) _ R tr (half_pos ep)
  refine ⟨G*M,?_⟩
  have splitGrow : Tendsto (fun r : ℕ => r/2) atTop atTop :=
    tendsto_atTop.mpr (fun k => (eventually_ge_atTop (2*k)).mono (fun r hr => by omega))
  have powGrow := (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < 2)).comp splitGrow
  have err := ((tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)).const_mul 40).comp splitGrow
  rw [mul_zero] at err
  filter_upwards [eventually_ge_atTop 6, powGrow.eventually_ge_atTop (max d (max N (2*A.natAbs*(G*M)))),
    err.eventually_le_const (half_pos ep)] with r hr large price u hu T hT a c ha hac hc
  let j := r/2
  let B₀ := 2^j
  let L := 2^(r-j)
  let Q := 2^r
  have jp : 3 ≤ j := by dsimp [j]; omega
  have bp : 0 < B₀ := pow_pos (by decide) _
  have qpos : 0 < Q := pow_pos (by decide) _
  have mass : L*B₀ = Q := by dsimp [L,B₀,Q]; rw [← pow_add,Nat.sub_add_cancel (by dsimp [j]; omega)]
  have bl : B₀ ≤ L := Nat.pow_le_pow_right (by decide) (by dsimp [j]; omega)
  change max d (max N (2*A.natAbs*(G*M))) ≤ B₀ at large
  have qbig : B₀ ≤ Q := Nat.pow_le_pow_right (by decide) (by dsimp [j]; omega)
  have hlow := (le_max_right N (2*A.natAbs*(G*M))).trans ((le_max_right ..).trans (large.trans qbig))
  have hlate := (le_max_left N (2*A.natAbs*(G*M))).trans ((le_max_right ..).trans (large.trans qbig))
  let V := ((range (r+2)) ×ˢ range (r+2)).image (fun v => ParameterTwoSquare.location v.1 v.2)
  let E := insertionBlocks V B₀ (u*L)
  have card : E.card ≤ 2*(r+2)^2 := (card_insertionBlocks ..).trans
    (Nat.mul_le_mul_left _ (by simpa [V,pow_two] using
      (card_image_le (s:=(range (r+2)) ×ˢ range (r+2)) (f:=fun v => ParameterTwoSquare.location v.1 v.2))))
  have charge : (E.card+1:ℝ)*B₀ ≤ (ε/2)*Q := by
    have hsize : (r:ℝ)+2 ≤ 3*j := by exact_mod_cast (by dsimp [j]; omega : r+2 ≤ 3*j)
    have ej : (E.card:ℝ) ≤ 2*((r:ℝ)+2)^2 := by exact_mod_cast card
    have hjr : (1:ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
    have cost : (E.card+1:ℝ) ≤ 40*(j:ℝ)^2 := by
      nlinarith only [ej, pow_le_pow_left₀ (by positivity) hsize 2, one_le_pow₀ hjr (n:=2)]
    change 40*((j:ℝ)^2/(2:ℝ)^j) ≤ ε/2 at price
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)] at price
    have cr : (E.card+1:ℝ) ≤ ε/2*L := (cost.trans price).trans (by
      apply mul_le_mul_of_nonneg_left _ (half_pos ep).le; exact_mod_cast bl)
    calc _ ≤ (ε/2*L)*B₀ := by gcongr
         _ = _ := by rw [mul_assoc,← Nat.cast_mul,mass]
  let x := (z:ℝ)*value b A B C
  let f := Localized.centered (shift b x) a c
  have whole := prefix_block_bound (s:=u*Q) f (Localized.centered_norm _ ha hac hc) bp
    (L:=L) (T:=T) (mass.symm ▸ hT) E (half_pos ep).le
  have full := whole (fun l hl clean => by
    let n := u*Q+l*B₀
    have grid : (u*L+l)*B₀ = n := by dsimp [n]; rw [Nat.add_mul,Nat.mul_assoc,mass]
    have endpoint : n+B₀ ≤ (u+1)*Q := calc
      n+B₀ = u*Q+(l+1)*B₀ := by dsimp [n]; ring
      _ ≤ u*Q+L*B₀ := Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) _
      _ = _ := by rw [mass]; ring
    have ulo : 2 ≤ u := by rcases hu with h|⟨h,_⟩ <;> omega
    have uhi : u ≤ 3 := by rcases hu with h|⟨h,_⟩ <;> omega
    have lo : 2^(r+1) ≤ n := by rw [pow_succ']; exact (Nat.mul_le_mul_right Q ulo).trans (Nat.le_add_right ..)
    have top : n+B₀ ≤ 2^(r+2) := by
      rw [pow_add,Nat.mul_comm]; exact endpoint.trans (Nat.mul_le_mul_right Q (by omega))
    have hi : n < 2^(r+2) := by omega
    have profile := shell_den hb odd (by omega) lo hi A B C nz
    have high : (R n).den ∣ d*2^(2*r) :=
      (Rat.mul_den_dvd z (P n)).trans (Nat.mul_dvd_mul_left d profile.1)
    have enough : G*M ≤ (P n).den := by
      rcases hu with rfl|⟨rfl,good⟩
      · have early : n < 3*2^r := by change n+B₀ ≤ 3*Q at endpoint; omega
        have h := profile.2 early; rw [two_mul r,pow_add,pow_succ] at h
        change Q*Q ≤ A.natAbs*(P n).den*(Q*2) at h
        have small : Q ≤ 2*A.natAbs*(P n).den := Nat.le_of_mul_le_mul_right
          (h.trans_eq (by ring)) qpos
        exact Nat.le_of_mul_le_mul_left (hlow.trans small) (by have := Int.natAbs_pos.mpr nz; positivity)
      · have inhalf : l*B₀ < Q := by rw [← mass]; exact Nat.mul_lt_mul_of_pos_right hl bp
        exact (upper_den_constant odd hb (by omega) A B C nz inhalf).symm ▸ good
    apply block B₀ n (hlate.trans ((Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ r)).trans lo))
      (Nat.le_of_mul_le_mul_left (enough.trans (recover n)) gp) _ _ _ a c ha hac hc
    · exact ⟨2*r,high.trans (by
        rw [mul_pow,Nat.mul_comm]; apply Nat.mul_dvd_mul_left
        simpa only [pow_one] using (pow_dvd_pow d (show 1 ≤ 2*r by omega)))⟩
    · apply (Nat.le_of_dvd (Nat.mul_pos dp (by positivity)) high).trans
      calc d*2^(2*r) ≤ B₀*2^(2*r) := Nat.mul_le_mul_right _ ((le_max_left ..).trans large)
           _ = 2^(j+2*r) := (pow_add ..).symm
           _ ≤ B₀^8 := by dsimp only [B₀]; rw [← pow_mul]; apply Nat.pow_le_pow_right (by decide); dsimp [j]; omega
    · intro i ii
      have hin : n+i < 2^(r+2) := by omega
      have logn := Nat.log_eq_of_pow_le_of_lt_pow lo hi
      have same := Nat.log_eq_of_pow_le_of_lt_pow (lo.trans (Nat.le_add_right n i)) hin
      have free (v w : ℕ) (newer : n < ParameterTwoSquare.location v w) :
          n+i < ParameterTwoSquare.location v w := by
        by_contra! ins
        have win := ins.trans_lt hin
        have a₁ := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp ((Nat.le_add_right ..).trans_lt win)
        have a₂ := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp ((Nat.le_add_left ..).trans_lt win)
        have hit : ParameterTwoSquare.location v w ∈ V := mem_image.mpr
          ⟨(v,w),mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,rfl⟩
        have out := insertionBlocks_free bp clean hit (by rw [Nat.add_mul,one_mul,grid]; omega)
        rw [grid] at out; omega
      dsimp only [R,P]; rw [follows (by omega) A B C (same.trans logn.symm) free]; ring)
  rw [← Nat.cast_mul,mass] at full
  change ‖∑ i ∈ range T, f (u*Q+i)‖ ≤ ε*(2:ℝ)^r
  have qr : (Q:ℝ) = (2:ℝ)^r := by simp [Q]
  rw [← qr]; linarith only [full,charge]

/-- Counts for the original rational quadratic, allowing arbitrary prime
divisors of its coefficient denominator. Dropping a fixed shift costs at most
two endpoint segments. -/
theorem rational_good_halves {b D : ℕ} (hb : 3 ≤ b) (odd : Odd b) (hd : 0 < D)
    (A B C : ℤ) (nz : A ≠ 0) :
    GoodHalves b (value b A B C / D) (upperDen b A B C) := by
  obtain ⟨s,a,d,ha,hd',cop,eqn⟩ := prime_support_shift (by omega : 0 < b) hd
  let z := (a:ℚ)/d
  have zd : z.den ∣ d := by
    simpa [z,div_eq_mul_inv,Rat.inv_natCast_den_of_pos hd'] using Rat.mul_den_dvd (a:ℚ) (d:ℚ)⁻¹
  have zn : z ≠ 0 := div_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hd'.ne')
  have ratio : (b:ℝ)^s / D = (z:ℝ) := by
    dsimp [z]; push_cast; rw [div_eq_div_iff (by positivity) (by positivity)]
    exact_mod_cast (eqn.trans (Nat.mul_comm ..))
  let x := value b A B C / D
  have translated (n : ℕ) : shift b x (n+s) = shift b ((z:ℝ)*value b A B C) n := by
    dsimp only [shift,x]; rw [← ratio,pow_add]; congr 1; ring
  intro ε ep
  obtain ⟨M,good⟩ := scaled_good_halves hb odd A B C nz z zn (cop.of_dvd_right zd) (ε/2) (half_pos ep)
  have grow := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually_ge_atTop (4*s/ε)
  refine ⟨M,?_⟩
  filter_upwards [good,grow] with r g large u hu T ht α γ hα hαγ hγ
  let f := Localized.centered (shift b x) α γ
  have cost := shifted_window f (Localized.centered_norm _ hα hαγ hγ) s (u*2^r) T
  have eqf (i : ℕ) : f (u*2^r+i+s) =
      Localized.centered (shift b ((z:ℝ)*value b A B C)) α γ (u*2^r+i) := by
    simp only [f,Localized.centered,translated]
  simp_rw [eqf] at cost
  exact cost.trans (by linarith only [g u hu T ht α γ hα hαγ hγ, (div_le_iff₀ ep).mp large])

end NormalityChecker.QuadraticOrbit
