module

public import NormalityChecker.SignedPhases

/-! A signed normality test on any eventual power cycle modulo a coefficient period. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- A forward traversal of `L` powers, with the newest amplitude having weight one. -/
def phaseWindow {d : ℕ} (p : ℕ) (H : ZMod d → ℚ) : ℕ → ZMod d → ℚ
  | 0, _ => 0
  | L+1, z => (p:ℚ)^L*H (z*p)+phaseWindow p H L (z*p)

private lemma window_step {d : ℕ} (p : ℕ) (H : ZMod d → ℚ) (L j : ℕ) :
    phaseWindow p H L ((p:ZMod d)^(j+1))-p*phaseWindow p H L ((p:ZMod d)^j) =
      H ((p:ZMod d)^(j+L+1))-(p:ℚ)^L*H ((p:ZMod d)^(j+1)) := by
  induction L generalizing j with
  | zero => simp [phaseWindow]
  | succ L ih =>
    simp only [phaseWindow,← pow_succ]; have h := ih (j+1)
    rw [show j+(L+1)+1=(j+1)+L+1 by omega,pow_succ (p:ℚ)]; linear_combination h

/-- A cycle witness exists even when `p` shares factors with the coefficient period. -/
theorem exists_power_cycle (p d : ℕ) [NeZero d] : ∃ J L : ℕ, 0<L ∧ (p:ZMod d)^(J+L)=(p:ZMod d)^J := by
  obtain ⟨i,j,h,e⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f:=fun j : ℕ => (p:ZMod d)^j) (fun _ => Set.mem_univ _)
  exact ⟨i,j-i,by omega,by simpa only [Nat.add_sub_cancel' h.le] using e.symm⟩

private lemma cycle_test {α : Type*} [Monoid α] {g : α} {J L : ℕ} (pos : 0<L)
    (cycle : g^(J+L)=g^J) (f : α → ℚ) :
    (∀ᶠ j in atTop, f (g^j)≠0) ↔ ∀ i : Fin L, f (g^(J+i.val))≠0 := by
  have rep (i t : ℕ) : g^(J+i+t*L)=g^(J+i) := by
    induction t with
    | zero => simp
    | succ t ih => rw [show J+i+(t+1)*L=(J+L)+(i+t*L) by ring,pow_add,cycle,← pow_add,← Nat.add_assoc,ih]
  constructor
  · intro ev i; obtain ⟨K,allK⟩ := eventually_atTop.mp ev
    rw [← rep i K]; exact allK _ (by have := Nat.le_mul_of_pos_right K pos; omega)
  · intro h; filter_upwards [eventually_ge_atTop J] with n hn
    let m := n-J
    have e : n=J+m%L+(m/L)*L := by have := Nat.mod_add_div m L; dsimp [m] at *; rw [Nat.mul_comm L] at this; omega
    rw [e,rep]; exact h ⟨_,Nat.mod_lt _ pos⟩

/-- Rational sequences agreeing up to scaling after a finite prefix have sums
related by the same scaling and an explicitly rational translation. -/
private lemma affine_tail (f g : ℕ → ℚ) (D : ℤ) (summ : Summable (fun j => (f j:ℝ)))
    (ev : ∀ᶠ j in atTop,g j=D*f j) : ∃ r : ℚ, (∑' j,(g j:ℝ))=(D:ℝ)*(∑' j,(f j:ℝ))+r := by
  obtain ⟨J,same⟩ := eventually_atTop.mp ev
  have eqR (j : ℕ) (h : J≤j) : (g j:ℝ)=(D:ℝ)*(f j:ℝ) := by exact_mod_cast same j h
  have sm := (summable_congr_atTop (Filter.eventually_atTop.mpr ⟨J,fun j h => (eqR j h).symm⟩)).mp (summ.mul_left (D:ℝ))
  refine ⟨∑ j∈range J,(g j-D*f j),?_⟩
  rw [← sm.sum_add_tsum_nat_add J,← summ.sum_add_tsum_nat_add J]; push_cast
  simp_rw [eqR _ (Nat.le_add_left J _),tsum_mul_left]; rw [sum_sub_distrib,← mul_sum]; ring

/-- Complete test at order one. `J,L` can be any certified preperiod and cycle length. -/
theorem periodic_normal_iff_phases {b p d J L : ℕ} [NeZero d] (hb : 2≤b) (hp : p.Prime)
    (cop : b.Coprime p) (lp : 0<L) (cycle : (p:ZMod d)^(J+L)=(p:ZMod d)^J) (A : ZMod d → ℚ) :
    NormalIn b (∑' n : ℕ,(A ((n:ZMod d)+1):ℝ)/(p:ℝ)^(Nat.log p (n+1))/(b:ℝ)^(n+1)) ↔
      ∀ i : Fin L, phaseWindow p (periodicAntidifference b d A) L ((p:ZMod d)^(J+i.val))≠0 := by
  let H := periodicAntidifference b d A
  let W := phaseWindow p H L
  let D := ∏ z : ZMod d, (W z).den
  have dp : 0<D := prod_pos (fun z _ => (W z).pos)
  let I (z : ZMod d) : ℤ := (W z).num*(D/(W z).den:ℕ)
  have clear (z : ZMod d) : (I z:ℚ)=(D:ℚ)*W z := by
    have dvd : (W z).den∣D := dvd_prod_of_mem _ (mem_univ z)
    have id := (W z).mul_den_eq_num
    have ht : ((D/(W z).den:ℕ):ℚ)*(W z).den=D := by exact_mod_cast Nat.div_mul_cancel dvd
    change (((W z).num*(((D/(W z).den:ℕ):ℤ)):ℤ):ℚ)=_
    rw [Int.cast_mul,Int.cast_natCast,← id]; linear_combination (W z)*ht
  let c (j : ℕ) := I ((p:ZMod d)^j)
  let E := (D:ℤ)*(1-(p:ℤ)^L)
  have en : E≠0 := mul_ne_zero (by exact_mod_cast dp.ne') (sub_ne_zero.mpr (one_lt_pow₀ (by exact_mod_cast hp.one_lt : 1<(p:ℤ)) lp.ne').ne)
  let f (j : ℕ) : ℚ := H ((p:ZMod d)^j)/(p:ℚ)^j/(b:ℚ)^(p^j)
  let g (j : ℕ) := SignedPhases.coeff p c j/(b:ℚ)^(p^j)
  obtain ⟨step,summ,_⟩ := periodic_data hb A
  have sm : Summable (fun j => (f j:ℝ)) := by
    apply Summable.of_norm_bounded (summ.comp_injective (Nat.pow_right_injective hp.two_le)).norm
    intro j; simp only [f,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Real.norm_eq_abs,Function.comp_apply,abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [Nat.cast_pow]; apply div_le_self (abs_nonneg _); rw [abs_pow,abs_of_nonneg (Nat.cast_nonneg p)]; exact one_le_pow₀ (by exact_mod_cast hp.one_le)
  have eqn : ∀ᶠ j in atTop,g j=E*f j := by
    filter_upwards [eventually_ge_atTop (J+1)] with j h
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
    have cc : (p:ZMod d)^(t+L+1)=(p:ZMod d)^(t+1) := by
      rw [show t+L+1=(J+L)+(t+1-J) by omega,pow_add,cycle,← pow_add]; congr 1; omega
    have win := window_step p H L t; rw [cc] at win
    dsimp only [g,f,SignedPhases.coeff,SignedPhases.jump,c,E]; push_cast; rw [clear,clear]; dsimp only [W]
    simp only [Nat.succ_eq_add_one]
    linear_combination ((D:ℚ)/(p:ℚ)^(t+1)/(b:ℚ)^(p^(t+1)))*win
  obtain ⟨r,aff⟩ := affine_tail f g E sm eqn
  have ae : SignedPhases.value b p c=(E:ℝ)*(∑' j,(f j:ℝ))+r := by simpa [SignedPhases.value,g] using aff
  have cap (j : ℕ) : (c j).natAbs≤∑ z : ZMod d,(I z).natAbs := single_le_sum (f:=fun z => (I z).natAbs) (fun z _ => Nat.zero_le _) (mem_univ ((p:ZMod d)^j))
  have sc := SignedPhases.normal_iff_eventually_nonzero hb hp cop c cap
  rw [ae,normal_add_rat_iff hb,normal_mul_int_iff hb en] at sc
  have nz (j : ℕ) : c j≠0 ↔ W ((p:ZMod d)^j)≠0 := by
    have v := clear ((p:ZMod d)^j); change (c j:ℚ)=_ at v
    have dz : (D:ℚ)≠0 := by exact_mod_cast dp.ne'
    simpa only [ne_eq,Int.cast_eq_zero,mul_eq_zero,or_iff_right dz] using not_congr (congrArg (·=(0:ℚ)) v).to_iff
  have right := sc.trans ((Filter.eventually_congr (.of_forall nz)).trans (cycle_test lp cycle W))
  have ident := dense_boundary_identity (s:=1) (b:=b) hp.two_le (fun n => A n) (fun n => H n) step summ
  let z : ℤ := 1-(p:ℤ)
  let a : ℚ := (p:ℚ)*H 1/b
  have transform : (∑' n : ℕ,(A ((n:ZMod d)+1):ℝ)/(p:ℝ)^(Nat.log p (n+1))/(b:ℝ)^(n+1)) =
        (z:ℝ)*(∑' j,(f j:ℝ))+a := by simpa [f,z,a,add_comm] using ident
  rw [transform,normal_add_rat_iff hb,normal_mul_int_iff hb (show z≠0 by dsimp [z]; exact sub_ne_zero.mpr (by exact_mod_cast hp.one_lt.ne : (1:ℤ)≠p))]; exact right

/-- Period-four dense coefficients, in residue order `0,1,2,3`. -/
def signedFour : ZMod 4 → ℚ := fun z => match z.val with
  | 0 => -1/2
  | 1 => 1
  | 2 => 3/2
  | _ => -3

/-- One recurring phase is exactly zero in this dense binary expansion. -/
theorem signed_four_nonnormal : ¬ NormalIn 2
    (∑' n : ℕ,(signedFour ((n:ZMod 4)+1):ℝ)/(3:ℝ)^(Nat.log 3 (n+1))/(2:ℝ)^(n+1)) := by
  have h := periodic_normal_iff_phases (b:=2) (p:=3) (J:=0) (L:=2) (by decide)
    (by decide) (by decide) (by decide) (by decide : (3:ZMod 4)^(0+2)=(3:ZMod 4)^0) signedFour
  intro n; exact (h.mp n (1:Fin 2)) (by decide +kernel)

end NormalityChecker
