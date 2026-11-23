module

public import NormalityChecker.StonehamOrbit
public import NormalityChecker.GeneralResonance
public import NormalityChecker.Dilation
public import NormalityChecker.ScaleTransfer

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

private noncomputable def weightedTerm (b c m j : ℕ) : ℝ :=
  (1/(b:ℝ))^(m*c^j)/(c:ℝ)^j

private lemma weighted_majorant {b c m J n : ℕ} (hb : 1<b) (hc : 1<c) (hn : n≤m*c^J) (i : ℕ) :
    (b:ℝ)^n * weightedTerm b c m (i+J) ≤ (1/(c:ℝ)^J)*(1/(c:ℝ))^i := by
  have h₁ : n≤m*c^(i+J) := hn.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  have h₂ : (b:ℝ)^n ≤ (b:ℝ)^(m*c^(i+J)) := pow_le_pow_right₀ (by exact_mod_cast hb.le) h₁
  have he : (b:ℝ)^n*(1/(b:ℝ))^(m*c^(i+J)) ≤ 1 := by
    rw [one_div_pow,mul_one_div,div_le_one (by positivity)]; exact h₂
  unfold weightedTerm
  rw [← mul_div_assoc]
  apply (div_le_div_of_nonneg_right he (by positivity)).trans_eq
  rw [pow_add,one_div_pow]; ring

private lemma weighted_sums {b c m : ℕ} (hb : 1<b) (hc : 1<c) (hm : 0<m) :
    HasSum (weightedTerm b c m) ((m:ℝ)*radixComponent b c m) := by
  have hsmall : 1/(c:ℝ)<1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast hc)
  have hs : Summable (weightedTerm b c m) := .of_nonneg_of_le
    (fun i => by unfold weightedTerm; positivity)
    (fun i => by simpa using weighted_majorant (m:=m) (J:=0) hb hc (n:=0) (Nat.zero_le _) i)
    (summable_geometric_of_lt_one (by positivity) hsmall)
  rw [radixComponent, ← tsum_mul_left]
  convert hs.hasSum using 1
  apply tsum_congr; intro i; unfold weightedTerm; field_simp

private lemma weighted_prefix {b c : ℕ} (hb : 1<b) (hc : 1<c) (hbc : b.Coprime c)
    (m k n : ℕ) (hn : m*c^k≤n) : ∃ A : ℕ, A.Coprime c ∧
      (b:ℝ)^n * (∑ j ∈ range (k+1), weightedTerm b c m j) = A/(c:ℝ)^k := by
  have term (j : ℕ) (hj : m*c^j≤n) :
      (b:ℝ)^n*weightedTerm b c m j = (b:ℝ)^(n-m*c^j)/(c:ℝ)^j := by
    unfold weightedTerm
    conv_lhs => rw [← Nat.add_sub_of_le hj,pow_add,one_div_pow]
    field_simp
  induction k with
  | zero =>
    refine ⟨b^(n-m),hbc.pow_left _,?_⟩
    simpa using term 0 hn
  | succ k ih =>
    obtain ⟨A,hA,he⟩ := ih ((Nat.mul_le_mul_left m (Nat.pow_le_pow_right (by omega) k.le_succ)).trans hn)
    let d := n-m*c^(k+1)
    refine ⟨b^d+c*A,(Nat.coprime_add_mul_left_left ..).mpr (hbc.pow_left d),?_⟩
    rw [sum_range_succ,mul_add,he,term _ hn,pow_succ (c:ℝ)]
    dsimp [d]; push_cast; field_simp; ring

/-- At the left endpoint of each cell the finite prefix has a unit numerator.
The same numerator generates the orbit up to the next insertion. -/
private lemma weighted_cell {b c m : ℕ} (hb : 1<b) (hc : 1<c) (hm : 0<m) (hbc : b.Coprime c)
    {u : ℕ} (hu : u ∈ Ico m (c*m)) (k : ℕ) :
    ∃ A : ℕ, A.Coprime c ∧ ∀ i < c^k,
      |(b:ℝ)^(u*c^k+i)*((m:ℝ)*radixComponent b c m)- A*(b:ℝ)^i/(c:ℝ)^k| ≤
        (1/((c:ℝ)-1))/(c:ℝ)^k := by
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hu
  obtain ⟨A,hA,he⟩ := weighted_prefix hb hc hbc m k (u*c^k) (Nat.mul_le_mul_right _ hlo)
  refine ⟨A,hA,fun i hi => ?_⟩
  let n := u*c^k+i
  have hn : n ≤ m*c^(k+1) := by dsimp [n]; rw [pow_succ]; nlinarith [Nat.mul_le_mul_right (c^k) (Nat.succ_le_of_lt hhi)]
  have hp : (∑ j ∈ range (k+1), (b:ℝ)^n*weightedTerm b c m j) = A*(b:ℝ)^i/(c:ℝ)^k := by
    rw [← mul_sum]; dsimp [n]; rw [pow_add]; linear_combination (b:ℝ)^i*he
  have hs := (weighted_sums hb hc hm).mul_left ((b:ℝ)^n)
  let t (j : ℕ) := (b:ℝ)^n * weightedTerm b c m (j+(k+1))
  have ht : Summable t := (summable_nat_add_iff _).mpr hs.summable
  have eqn := hs.summable.sum_add_tsum_nat_add (k+1)
  rw [hp,hs.tsum_eq] at eqn
  change |(b:ℝ)^n*_ - _| ≤ _
  rw [← eqn,add_sub_cancel_left,abs_of_nonneg (tsum_nonneg (fun j => by unfold weightedTerm; positivity))]
  have hsmall : 1/(c:ℝ)<1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast hc)
  calc
    _ ≤ ∑' j : ℕ, (1/(c:ℝ)^(k+1))*(1/(c:ℝ))^j := ht.tsum_le_tsum
      (fun j => weighted_majorant hb hc hn j) ((summable_geometric_of_lt_one (by positivity) hsmall).mul_left _)
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (by positivity) hsmall,pow_succ]; field_simp

private theorem weighted_fourier {b c m : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c)
    (hbc : b.Coprime c) (hm : 0<m) (h : ℤ) (hh : h≠0) :
    Tendsto (mean (fun n => phase (h*((b:ℝ)^n*((m:ℝ)*radixComponent b c m))))) atTop (𝓝 0) := by
  apply mean_zero_of_radix_cells (c:=c) hc hm
  intro u hu ε hε
  let C := 2*Real.pi*|(h:ℝ)| *(1/((c:ℝ)-1))
  have err : Tendsto (fun k : ℕ => C/(c:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=C)).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hc : (1:ℝ)<c)))
  filter_upwards [stoneham_orbit_small hb hc ho hbc h hh (ε/2) (half_pos hε),
    err.eventually_lt_const (half_pos hε)] with k H hsmall T hT
  obtain ⟨A,hA,happrox⟩ := weighted_cell hb hc hm hbc hu k
  let f (i : ℕ) := phase (h*((b:ℝ)^(u*c^k+i)*((m:ℝ)*radixComponent b c m)))
  let g (i : ℕ) := phase ((h:ℝ)*A*(b:ℝ)^i/(c:ℝ)^k)
  have point (i : ℕ) (hi : i∈range T) : ‖f i-g i‖ ≤ ε/2 := by
    apply (phase_sub_le _ _).trans
    rw [show (h:ℝ)*A*(b:ℝ)^i/(c:ℝ)^k = h*(A*(b:ℝ)^i/(c:ℝ)^k) by ring, ← mul_sub,abs_mul,← mul_assoc]
    apply (mul_le_mul_of_nonneg_left (happrox i ((mem_range.mp hi).trans_le hT)) (by positivity)).trans
    simpa [C,mul_div_assoc] using hsmall.le
  have diff : ‖(∑ i ∈ range T, f i) - ∑ i ∈ range T, g i‖ ≤ (ε/2)*(c:ℝ)^k := by
    rw [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans ((sum_le_sum point).trans ?_)
    simp only [sum_const,card_range,nsmul_eq_mul]; rw [mul_comm]; gcongr; exact_mod_cast hT
  have tri := norm_add_le ((∑ i ∈ range T, f i) - ∑ i ∈ range T, g i) (∑ i ∈ range T, g i)
  rw [sub_add_cancel] at tri
  have model : ‖∑ i ∈ range T, g i‖ ≤ ε/2*(c:ℝ)^k := H A hA T hT
  change ‖∑ i ∈ range T, f i‖ ≤ _
  linarith

/-- Stoneham normality for the weighted components, including odd composite c. -/
theorem weighted_radixComponent_normal {b c m : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c)
    (hbc : b.Coprime c) (hm : 0<m) : NormalIn b ((m:ℝ)*radixComponent b c m) :=
  normal_of_fourier hb _ (weighted_fourier hb hc ho hbc hm)

theorem radixComponent_normal {b c m : ℕ} (hb : 1<b) (hc : 1<c) (ho : Odd c)
    (hbc : b.Coprime c) (hm : 0<m) : NormalIn b (radixComponent b c m) := by
  apply normal_of_dilated_fourier hb _ m hm
  simpa only [mul_left_comm (m:ℝ)] using weighted_fourier hb hc ho hbc hm

theorem weighted_radixComponent_pos {b c m : ℕ} (hb : 1<b) (hc : 1<c) (hm : 0<m) :
    0 < (m:ℝ)*radixComponent b c m := by
  have hs := weighted_sums hb hc hm
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun i => by unfold weightedTerm; positivity) 0 (by unfold weightedTerm; positivity)

/-- In every integer radix there are two positive, individually normal explicit
components whose irrational sum exceeds the specified upper frequency for every
fixed zero block. The same pair works for all block lengths. -/
theorem severe_normal_summands (b : ℕ) (hb : 2≤b) (η : ℝ) (hη : η<1) :
    ∃ d : ℕ, 0<d ∧
      let l := 2*d+1
      let c := oddSquareDivisor (b^d)
      let x := radixComponent b c 1
      let y := (l:ℝ)*radixComponent b c l
      0<x ∧ 0<y ∧ NormalIn b x ∧ NormalIn b y ∧ Irrational (x+y) ∧
        ¬ NormalIn b (x+y) ∧ ∀ r : ℕ, η < limsup (frequency (shift b (x+y)) 0 (1/(b:ℝ)^r)) atTop := by
  obtain ⟨d,hd,H⟩ := severe_resonance b hb η hη
  let c := oddSquareDivisor (b^d)
  obtain ⟨ho,hdvd,hle⟩ := oddSquareDivisor_spec (b^d)
  have hpow : 2 ≤ b^d := hb.trans (Nat.le_self_pow hd.ne' _)
  have hc : 1<c := by change (b^d)^2+1 ≤ 2*c at hle; nlinarith [Nat.pow_le_pow_left hpow 2]
  have hbc : b.Coprime c := Nat.Coprime.of_dvd
    ((dvd_pow_self b hd.ne').trans (dvd_pow_self (b^d) (by decide : 2≠0))) hdvd (by simp)
  refine ⟨d,hd,?_,weighted_radixComponent_pos hb hc (by omega),?_,
    weighted_radixComponent_normal hb hc ho hbc (by omega),H⟩
  · simpa using weighted_radixComponent_pos (m:=1) hb hc (by decide)
  · exact radixComponent_normal hb hc ho hbc (by decide)

end NormalityChecker
