module

public import NormalityChecker.QuadraticOrbitTransfer

/-! The clipped weights of the upper dyadic half-shells and their maximum. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.QuadraticOrbit

def OnPlateau (r n : ℕ) : Prop := 3*2^r ≤ n ∧ n < 4*2^r

instance (r n : ℕ) : Decidable (OnPlateau r n) := inferInstanceAs (Decidable (_ ∧ _))

def plateauLength (r N : ℕ) := min N (4*2^r) - 3*2^r

noncomputable def plateauWeight (r N : ℕ) : ℝ := (plateauLength r N : ℝ)/N

/-- At each cutoff only finitely many terms can be nonzero. -/
noncomputable def plateauEnvelope (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ r : ℕ, plateauWeight r N * F r

theorem plateauWeight_bounds (r N : ℕ) : 0 ≤ plateauWeight r N ∧ plateauWeight r N ≤ 1/4 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),?_⟩
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [plateauWeight]
  · rw [plateauWeight,div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)]
    have h : 4*plateauLength r N ≤ N := by dsimp [plateauLength]; omega
    have t : 4*(plateauLength r N:ℝ) ≤ N := by exact_mod_cast h
    linarith

theorem plateauWeight_endpoint (r : ℕ) : plateauWeight r (4*2^r) = 1/4 := by
  have h : plateauLength r (4*2^r) = 2^r := by dsimp [plateauLength]; omega
  rw [plateauWeight,h]; push_cast; field_simp

private theorem product_le {F : ℕ → ℝ} (bd : ∀ r, F r ≤ 1) (r N : ℕ) :
    plateauWeight r N * F r ≤ 1/4 := by
  have h := plateauWeight_bounds r N
  exact (mul_le_of_le_one_right h.1 (bd r)).trans h.2

theorem le_plateauEnvelope {F : ℕ → ℝ} (bd : ∀ r, F r ≤ 1) (r N : ℕ) :
    plateauWeight r N * F r ≤ plateauEnvelope F N :=
  le_ciSup (f:=fun j => plateauWeight j N * F j) ⟨1/4,by rintro _ ⟨j,rfl⟩; exact product_le bd j N⟩ r

theorem plateauEnvelope_bounds {F : ℕ → ℝ} (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (N : ℕ) :
    0 ≤ plateauEnvelope F N ∧ plateauEnvelope F N ≤ 1/4 :=
  ⟨(mul_nonneg (plateauWeight_bounds 0 N).1 (hF 0).1).trans
    (le_plateauEnvelope (fun r => (hF r).2) 0 N),ciSup_le (fun r => product_le (fun j => (hF j).2) r N)⟩

/-- The peak at the right endpoint of each plateau gives the exact limsup
of the maximum, even if positive orbit factors occur extremely sparsely. -/
theorem plateauEnvelope_limsup {F : ℕ → ℝ} (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) :
    limsup (plateauEnvelope F) atTop = (1/4)*limsup F atTop := by
  have lo := isCoboundedUnder_le_of_le atTop (f:=F) (x:=0) (fun r => (hF r).1)
  have hi := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall fun r => (hF r).2)
  have ebd := plateauEnvelope_bounds hF
  have elo := isCoboundedUnder_le_of_le atTop (f:=plateauEnvelope F) (x:=0) (fun N => (ebd N).1)
  have ehi := isBoundedUnder_of_eventually_le (f:=atTop) (.of_forall fun N => (ebd N).2)
  have nn : 0 ≤ limsup F atTop := le_limsup_of_frequently_le
    (Eventually.frequently (.of_forall fun r => (hF r).1)) hi
  apply le_antisymm
  · apply (limsup_le_iff' elo ehi).mpr
    intro v hv
    have vp : 0 < v := by linarith
    obtain ⟨K,late⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt
      (by linarith : limsup F atTop < 4*v) hi)
    filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat ((2:ℝ)^K)).eventually_le_const vp]
      with N old
    apply ciSup_le; intro r
    by_cases hr : K ≤ r
    · exact (mul_le_mul (plateauWeight_bounds r N).2 (late r hr).le (hF r).1 (by norm_num)).trans_eq (by ring)
    · have len : plateauLength r N ≤ 2^K := by
        have pow := Nat.pow_le_pow_right (by decide : 0<2) (le_of_not_ge hr)
        dsimp [plateauLength]; omega
      exact (mul_le_of_le_one_right (plateauWeight_bounds r N).1 (hF r).2).trans
        ((div_le_div_of_nonneg_right (by exact_mod_cast len : (plateauLength r N:ℝ) ≤ (2:ℝ)^K) (Nat.cast_nonneg N)).trans old)
  · apply (le_limsup_iff elo ehi).mpr
    intro v hv
    have freq := frequently_lt_of_lt_limsup lo (by linarith : 4*v < limsup F atTop)
    rw [frequently_atTop] at freq ⊢
    intro K
    obtain ⟨r,hr,good⟩ := freq K
    have h := le_plateauEnvelope (fun j => (hF j).2) r (4*2^r)
    rw [plateauWeight_endpoint] at h
    exact ⟨4*2^r,by have := Nat.lt_two_pow_self (n:=r); omega,by linarith⟩

/-- All but one plateau meeting the recent part of a prefix have small
factor. The discarded positions form an initial segment of relative size at most ε. -/
theorem isolated_plateau {q : ℕ → ℕ} {F : ℕ → ℝ} (sep : Separated q)
    (decay : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ r ≥ 1, M ≤ q r → F r ≤ ε)
    {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ E j : ℕ, 1 ≤ j ∧ (E:ℝ) ≤ ε*N ∧
      ∀ i n : ℕ, E ≤ n → n < N → OnPlateau i n → i ≠ j → F i ≤ ε := by
  obtain ⟨M,regular⟩ := decay ε ep
  obtain ⟨H,hH⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually_ge_atTop (2/ε)).exists
  obtain ⟨K,uniq⟩ := eventually_atTop.mp (sep M H)
  filter_upwards [eventually_ge_atTop (2^(K+H+1))] with N huge
  let t := Nat.log 2 N-H
  have late := Nat.le_log_of_pow_le (by decide : 1<2) huge
  have eqn : t+H=Nat.log 2 N := by dsimp [t]; omega
  have tk : K ≤ t := by dsimp [t]; omega
  have tp : 1 ≤ t := by dsimp [t]; omega
  have pos := (pow_pos (by decide : 0<2) _).trans_le huge
  have low : 2^(t+H) ≤ N := by rw [eqn]; exact Nat.pow_log_le_self _ pos.ne'
  have high : N < 2^(t+H+1) := by rw [eqn]; exact Nat.lt_pow_succ_log_self (by decide) _
  have early : ((2^(t+1):ℕ):ℝ) ≤ ε*N := by
    have l : (2:ℝ)^t*2^H ≤ N := by exact_mod_cast (show 2^t*2^H ≤ N by rwa [←pow_add])
    push_cast; rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left ((div_le_iff₀ ep).mp hH) (by positivity : 0 ≤ (2:ℝ)^t),
                    mul_le_mul_of_nonneg_left l ep.le]
  have recent {i n : ℕ} (h : 2^(t+1) ≤ n) (hn : n < N) (hit : OnPlateau i n) :
      i ∈ Ico t (t+H) := by
    obtain ⟨left,right⟩ := hit
    have h₁ : 2^(t+1) < 2^(i+2) := by rw [pow_add (2:ℕ) i 2]; omega
    have h₂ : 2^(i+1) < 2^(t+H+1) := by rw [pow_succ']; omega
    have i₁ := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h₁
    have i₂ := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h₂
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  by_cases ex : ∃ j ∈ Ico t (t+H), q j < M
  · obtain ⟨j,hj,small⟩ := ex
    refine ⟨_,j,tp.trans (mem_Ico.mp hj).1,early,fun i n hn hn' hit ne => ?_⟩
    have hi := recent hn hn' hit
    exact regular i (tp.trans (mem_Ico.mp hi).1) (by
      by_contra! bad; exact ne (uniq t tk i hi j hj bad small))
  · push Not at ex
    exact ⟨_,t,tp,early,fun i n h hn hit _ => regular i
      (tp.trans (mem_Ico.mp (recent h hn hit)).1) (ex i (recent h hn hit))⟩

/-- Subtract one from the usual dyadic shell index, as in the quadratic model. -/
def shellIndex (n : ℕ) := Nat.log 2 n - 1

theorem cell_index {r u i : ℕ} (hu : u = 2 ∨ u = 3) (hi : i < 2^r) :
    shellIndex (u*2^r+i) = r := by
  have right : 2^(r+2) = 4*2^r := by rw [pow_add]; ring
  have k : Nat.log 2 (u*2^r+i) = r+1 := Nat.log_eq_of_pow_le_of_lt_pow
    (by rw [pow_succ']; rcases hu with rfl|rfl <;> omega)
    (by rw [right]; rcases hu with rfl|rfl <;> omega)
  simp [shellIndex,k]

theorem index_of_onPlateau {i n : ℕ} (h : OnPlateau i n) : shellIndex n = i := by
  obtain ⟨lo,hi⟩ := h
  simpa only [Nat.add_sub_of_le lo] using
    (cell_index (r:=i) (u:=3) (i:=n-3*2^i) (Or.inr rfl) (by omega))

/-- A scalar value carried by each plateau and zero elsewhere. -/
noncomputable def plateauProfile (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if OnPlateau (shellIndex n) n then f (shellIndex n) else 0

private theorem plateauFilter (r N : ℕ) :
    (range N).filter (OnPlateau r) = Ico (3*2^r) (min N (4*2^r)) := by
  ext n; simp only [mem_filter,mem_range,OnPlateau,mem_Ico,lt_min_iff]; tauto

theorem sum_single_plateau (j N : ℕ) (v : ℝ) :
    (∑ n ∈ range N, if OnPlateau j n then v else 0) = plateauLength j N*v := by
  rw [← sum_filter,plateauFilter]; simp [plateauLength]

theorem profile_mass_error {F f : ℕ → ℝ} (bd : ∀ i, F i ≤ 1) (dom : ∀ i, |f i| ≤ F i)
    {N E j : ℕ} {ε : ℝ} (he : 0 ≤ ε)
    (onlyOne : ∀ i n : ℕ, E ≤ n → n < N → OnPlateau i n → i ≠ j → F i ≤ ε) :
    |∑ n ∈ range N, plateauProfile f n - plateauLength j N*f j| ≤ E+ε*N := by
  rw [← sum_single_plateau,← sum_sub_distrib]
  have bound (n : ℕ) (hn : n ∈ range N) :
      |plateauProfile f n - (if OnPlateau j n then f j else 0)| ≤
        (if n < E then 1 else 0) + ε := by
    by_cases hj : OnPlateau j n
    · simp [plateauProfile,index_of_onPlateau hj,hj]; split <;> linarith
    · rw [ite_eq_right hj,sub_zero,plateauProfile]
      split_ifs with h small small
      · linarith [(dom _).trans (bd (shellIndex n))]
      · simpa using (dom _).trans (onlyOne _ n (by omega) (mem_range.mp hn) h (by rintro eq; exact hj (eq ▸ h)))
      · simp; linarith
      · simpa using he
  have H := (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum bound)
  simp only [sum_add_distrib,← sum_filter,sum_const,card_range,nsmul_eq_mul,mul_one] at H
  have cnt : ((range N).filter (·<E)).card ≤ E := (card_le_card (t:=range E)
    (fun n hn => mem_range.mpr (mem_filter.mp hn).2)).trans_eq (card_range E)
  linarith only [H,Nat.cast_le (α:=ℝ).mpr cnt,mul_comm (N:ℝ) ε]

theorem envelope_excess {F : ℕ → ℝ} (bd : ∀ i, 0 ≤ F i ∧ F i ≤ 1)
    {N E j : ℕ} {ε : ℝ} (he : 0 ≤ ε) (hn : 0 < N) (cost : (E:ℝ) ≤ ε*N)
    (onlyOne : ∀ i n : ℕ, E ≤ n → n < N → OnPlateau i n → i ≠ j → F i ≤ ε) :
    plateauEnvelope F N ≤ plateauWeight j N*F j + ε := by
  apply ciSup_le; intro i
  have nn := mul_nonneg (plateauWeight_bounds j N).1 (bd j).1
  by_cases eqn : i = j
  · subst i; linarith
  by_cases small : F i ≤ ε
  · have wt := (plateauWeight_bounds i N).2
    have h := mul_le_mul_of_nonneg_right (show plateauWeight i N ≤ 1 by linarith) (bd i).1
    linarith
  · have cnt : ((range N).filter (OnPlateau i)).card ≤ E := by
      apply (card_le_card (t:=range E) _).trans_eq (card_range E)
      intro n hn'; obtain ⟨hN,hit⟩ := mem_filter.mp hn'
      exact mem_range.mpr (lt_of_not_ge (fun h => small (onlyOne i n h (mem_range.mp hN) hit eqn)))
    rw [plateauFilter,Nat.card_Ico] at cnt
    have w : plateauWeight i N ≤ ε := (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ)<N)).mpr
      ((Nat.cast_le (α:=ℝ).mpr cnt).trans cost)
    exact (mul_le_of_le_one_right (plateauWeight_bounds i N).1 (bd i).2).trans (by linarith)

end NormalityChecker.QuadraticOrbit
