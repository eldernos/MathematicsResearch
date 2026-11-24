module

public import NormalityChecker.CellProfile
public import NormalityChecker.SupportDiscrepancy

/-! Finite modular certificates for upper bounds on extreme interval discrepancy. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

def failedCells (b s p ell : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Ico (p^ell) (p*p^ell)).filter (fun u => powerCellResidue s p ell S (inverseLift b p ell ell) u=0)

def discrepancyCertificate (b s p ell : ℕ) (S : Finset ℕ) : ℚ :=
  CellProfile.bound p (p^ell) (failedCells b s p ell S)

/-- A zero at higher precision also vanishes after reduction to a divisor. -/
private lemma represents_zero_reduces {m n : ℕ} (dvd : m∣n) {x : ℚ} {z : ZMod m}
    (fine : Represents x (0:ZMod n)) (coarse : Represents x z) : z=0 := by
  obtain ⟨a,d,hd,realFine,modFine⟩ := fine
  obtain ⟨v,e,he,realCoarse,modCoarse⟩ := coarse
  let φ := ZMod.castHom dvd (ZMod m)
  have unit : IsUnit (d:ZMod m) := by simpa [φ] using hd.map φ
  have zero : (a:ZMod m)=0 := by simpa [φ] using congrArg φ modFine.symm
  have cross : (d:ℚ)*v=e*a := by linear_combination (e:ℚ)*realFine-(d:ℚ)*realCoarse
  have natCross : d*v=e*a := by exact_mod_cast cross
  have smallCross : (d:ZMod m)*v=e*a := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod m) natCross
  apply he.mul_right_inj.mp; rw [modCoarse,mul_zero]; apply unit.mul_right_inj.mp
  rw [smallCross,zero,mul_zero,mul_zero]

/-- Raising the precision can only remove normalized positions from the failed set. -/
theorem failed_cell_refines {b s p ell u : ℕ} {S : Finset ℕ} (hs : 0<s) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (fail : u∈failedCells b s p (ell+1) S) :
    u/p∈failedCells b s p ell S := by
  obtain ⟨inside,zero⟩ := mem_filter.mp fail
  obtain ⟨lo,hi⟩ := mem_Ico.mp inside
  let k := 2*(ell+1)
  let n := u*p^(ell+1)
  have dk : k-(ell+1)=ell+1 := by dsimp [k]; omega
  have dk' : k-ell=ell+1+1 := by dsimp [k]; omega
  have fine : n/p^(k-(ell+1))=u := by simp [n,dk,Nat.mul_div_cancel _ (pow_pos hp.pos _)]
  have coarse : n/p^(k-ell)=u/p := by
    rw [dk',pow_succ,← Nat.div_div_eq_div_mul]; simp [n,Nat.mul_div_cancel _ (pow_pos hp.pos _)]
  have bound : n<p^(k+1) := by
    calc n < (p*p^(ell+1))*p^(ell+1) := Nat.mul_lt_mul_of_pos_right hi (pow_pos hp.pos _)
         _ = p^(k+1) := by rw [← pow_succ',← pow_add]; congr 1; dsimp [k]; omega
  have f := power_prefix_residue hs hp outside cop (k:=k) (by dsimp [k]; omega : ell+1+(ell+1)≤k) bound (canonical_lift_fixed hp cop (ell+1))
  have g := power_prefix_residue hs hp outside cop (k:=k) (by dsimp [k]; omega : ell+ell≤k) bound (canonical_lift_fixed hp cop ell)
  rw [fine,zero] at f; rw [coarse] at g
  refine mem_filter.mpr ⟨mem_Ico.mpr ⟨(Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [pow_succ] using lo),
    (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_succ,mul_assoc] using hi)⟩,?_⟩
  exact represents_zero_reduces (pow_dvd_pow p (Nat.le_succ _)) f g

private lemma support_modulus {b p : ℕ} (A : Finset ℕ) (primes : ∀ r∈A,r.Prime)
    (pp : p.Prime) (mem : p∈A) (cop : b.Coprime p) :
    ∃ c : ℕ, 1<c ∧ b.Coprime c ∧ ∀ r∈A,r∣b*c := by
  let U := A.filter (fun r => ¬r∣b)
  let c := ∏ r∈U,r
  have dvd (r : ℕ) (hr : r∈U) : r∣c := dvd_prod_of_mem id hr
  have pos : 0<c := prod_pos (fun r hr => (primes r (mem_filter.mp hr).1).pos)
  have high := Nat.le_of_dvd pos (dvd p (mem_filter.mpr ⟨mem,pp.coprime_iff_not_dvd.mp cop.symm⟩))
  refine ⟨c,pp.one_lt.trans_le high,Nat.Coprime.prod_right (fun r hr => ((primes r (mem_filter.mp hr).1).coprime_iff_not_dvd.mpr (mem_filter.mp hr).2).symm),?_⟩
  intro r hr; by_cases h : r∣b
  · exact h.trans (dvd_mul_right ..)
  · exact (dvd r (mem_filter.mpr ⟨hr,h⟩)).trans (dvd_mul_left ..)

/-- Any covering set of failed grid cells is allowed. Successful cells yield
large reduced denominators at every sufficiently late scale. -/
theorem discrepancy_of_cell_cover {b s p ell : ℕ} {S : Finset ℕ} (hb : 2≤b) (hs : 0<s)
    (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime)
    (Z : Finset ℕ) (cover : failedCells b s p ell S ⊆ Z) (grid : Z⊆Ico (p^ell) (p*p^ell)) :
    limsup (radixDiscrepancy b (powerValue b s (insert p S))) atTop ≤ (CellProfile.bound p (p^ell) Z:ℝ) := by
  let A := insert p S
  obtain ⟨c,hc,bc,supp⟩ := support_modulus A (fun r hr => by rcases mem_insert.mp hr with rfl|h; exacts [hp,primes r h]) hp (mem_insert_self ..) cop
  let u := CellProfile.coordinate p (p^ell)
  apply discrepancy_of_survival A hb hc bc hs supp (fun n => decide (u n∈Z))
  · intro M
    let K := 2*ell+M
    filter_upwards [eventually_ge_atTop (p^K)] with n stable ok
    let k := Nat.log p n
    have hk : K≤k := Nat.le_log_of_pow_le hp.one_lt stable
    have np : 0<n := (pow_pos hp.pos K).trans_le stable
    have left := Nat.pow_log_le_self p np.ne'
    have right := Nat.lt_pow_succ_log_self hp.one_lt n
    have coord : u n=n/p^(k-ell) := by simp [u,CellProfile.coordinate,Nat.log_div_base_pow,k]
    have ke : ell≤k := by dsimp [K] at hk; omega
    have split : p^ell*p^(k-ell)=p^k := by rw [← pow_add]; congr 1; omega
    have inside : u n∈Ico (p^ell) (p*p^ell) := by
      rw [coord,mem_Ico,Nat.le_div_iff_mul_le (pow_pos hp.pos _),Nat.div_lt_iff_lt_mul (pow_pos hp.pos _),mul_assoc,split,← pow_succ']; exact ⟨left,right⟩
    have nz : powerCellResidue s p ell S (inverseLift b p ell ell) (u n)≠0 := fun h => by
      have mem := cover (show u n∈failedCells b s p ell S from mem_filter.mpr ⟨inside,h⟩); simp [mem] at ok
    rw [coord] at nz
    have den := cell_power_denominator hs hp outside cop (k:=k) (by dsimp [K] at hk; omega : ell+ell≤k) right (canonical_lift_fixed hp cop ell) nz
    have ex : k≤k*s := by simpa using Nat.mul_le_mul_left k hs
    have exp : M≤k*s-ell := by dsimp [K] at hk; omega
    exact (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt (n:=M))).trans ((Nat.pow_le_pow_right hp.pos exp).trans (Nat.le_of_dvd (Rat.pos _) den))
  · apply Eventually.of_forall; intro N
    have H := Rat.cast_le (K:=ℝ) |>.mpr (CellProfile.count_bound hp.one_lt (pow_pos hp.pos ell) Z grid N)
    simpa [u,apply_ite] using H

/-- Soundness of the executable rational discrepancy checker at a single precision. -/
theorem discrepancy_le_certificate {b s p : ℕ} {S : Finset ℕ} (hb : 2≤b) (hs : 0<s)
    (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime) (ell : ℕ) :
    limsup (radixDiscrepancy b (powerValue b s (insert p S))) atTop ≤ (discrepancyCertificate b s p ell S:ℝ) :=
  discrepancy_of_cell_cover hb hs hp outside cop primes _ (Subset.rfl) (filter_subset ..)

/-- Arbitrarily small bad mass suffices, even when no finite test is zero. The
worst-prefix fraction is at most `p` times the full-scale bad fraction. -/
theorem normal_of_shrinking_cells {b s p : ℕ} {S : Finset ℕ} (hb : 2≤b) (hs : 0<s)
    (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime)
    (shrink : ∀ ε : ℚ, 0<ε → ∃ ell : ℕ, ((failedCells b s p ell S).card:ℚ) ≤ ε*p^ell) :
    NormalIn b (powerValue b s (insert p S)) := by
  apply normal_of_radix_limsup_zero hb; apply le_of_forall_pos_le_add; intro ε pos
  obtain ⟨δ,hδ,small⟩ := exists_rat_btwn (show (0:ℝ)<ε/2 by positivity)
  obtain ⟨ell,tiny⟩ := shrink δ (by exact_mod_cast hδ)
  let Z := failedCells b s p ell S
  have cert : CellProfile.bound p (p^ell) Z ≤ 2*δ := by
    apply max'_le _ _ _; intro r hr; rcases mem_insert.mp hr with rfl|hm
    · have : (0:ℚ)<δ := by exact_mod_cast hδ
      positivity
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hm
    have high : (p^ell:ℕ)≤v := (mem_Icc.mp hv).1
    have vp : (0:ℚ)<v := by exact_mod_cast (pow_pos hp.pos ell).trans_le high
    apply (div_le_iff₀ vp).mpr
    have one : (1:ℚ)≤(p:ℚ)-1 := by
      have h : (2:ℚ)≤p := by exact_mod_cast hp.two_le
      linarith
    have t := div_le_self (Nat.cast_nonneg Z.card : (0:ℚ)≤Z.card) one
    have count : (CellProfile.mass Z v:ℚ)≤Z.card := by exact_mod_cast card_filter_le Z _
    have large : (p:ℚ)^ell≤v := by exact_mod_cast high
    have q := mul_le_mul_of_nonneg_left large (show (0:ℚ)≤δ by exact_mod_cast hδ.le)
    change (Z.card:ℚ)≤_ at tiny; linarith only [q,count,tiny,t]
  have fin := (discrepancy_le_certificate hb hs hp outside cop primes ell).trans (by exact_mod_cast cert : (discrepancyCertificate b s p ell S:ℝ)≤2*(δ:ℝ))
  linarith

private lemma indices_one (S : Finset ℕ) : indices S 1={1} := by
  ext i; simp only [mem_indices,mem_singleton]; constructor
  · rintro ⟨le,mem⟩; have h := mem.1; omega
  · rintro rfl; simp [Nat.factoredNumbers]; exact fun q h e => (h.ne_one e).elim

private lemma first_cell_unit {b p s : ℕ} (hp : p.Prime) (cop : b.Coprime p) (S : Finset ℕ) :
    powerCellResidue s p 0 S (inverseLift b p 0 0) 1≠0 := by
  have unit := (ZMod.isUnit_iff_coprime b (p^(0+1))).mpr (cop.pow_right _)
  let : NeZero (p^(0+1)) := ⟨(pow_pos hp.pos _).ne'⟩
  have h : ((b:ZMod (p^(0+1)))⁻¹)≠0 := by
    intro zero; obtain ⟨v,hv⟩ := unit; rw [← hv,ZMod.inv_coe_unit] at zero
    have mul := congrArg ((v:ZMod (p^(0+1))) * ·) zero
    simp at mul
    have nz : (1:ZMod (p^(0+1))) ≠0 := by have : Fact (1<p^(0+1)) := ⟨by simpa using hp.one_lt⟩; exact one_ne_zero
    exact nz mul
  simpa [powerCellResidue,indices_one,inverseLift] using h

/-- Every scale has a passing cell `[1,2)`, independently of the other primes. -/
theorem discrepancy_le_of_support_prime {b s p : ℕ} {S : Finset ℕ} (hb : 2≤b) (hs : 0<s)
    (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime) :
    limsup (radixDiscrepancy b (powerValue b s (insert p S))) atTop ≤ 1-1/((p:ℝ)-1) := by
  let Z := Ico 2 p
  have cover : failedCells b s p 0 S⊆Z := by
    intro u hu; obtain ⟨hg,zero⟩ := mem_filter.mp hu
    simp only [pow_zero,mul_one,mem_Ico] at hg; apply mem_Ico.mpr; refine ⟨?_,hg.2⟩
    by_contra! fail; have e : u=1 := by omega
    exact first_cell_unit (s:=s) hp cop S (e ▸ zero)
  have H := discrepancy_of_cell_cover hb hs hp outside cop primes Z cover (by simp [Z]; grind)
  have val : CellProfile.bound p 1 Z≤1-1/((p:ℚ)-1) := by
    have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
    have two : (2:ℚ)≤p := by exact_mod_cast hp.two_le
    apply max'_le _ _ _; intro r hr; rcases mem_insert.mp hr with rfl|hm
    · have := (div_le_one (by linarith : 0<(p:ℚ)-1)).mpr (show 1≤(p:ℚ)-1 by linarith); linarith
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hm; simp only [mul_one,mem_Icc] at hv
    have vp : (0:ℚ)<v := by exact_mod_cast hv.1
    have zc : Z.card=p-2 := Nat.card_Ico ..
    have vc : CellProfile.mass Z v=v-2 := by
      have e : Z.filter (·<v)=Ico 2 v := by ext i; simp [Z]; omega
      rw [CellProfile.mass,e,Nat.card_Ico]
    unfold CellProfile.score; rw [zc,vc,Nat.cast_sub hp.two_le]; apply (div_le_iff₀ vp).mpr
    by_cases big : 2≤v
    · rw [Nat.cast_sub big]; field_simp [(sub_pos.mpr pp).ne']; push_cast; nlinarith [show (v:ℚ)≤p by exact_mod_cast hv.2]
    · have e : v=1 := by omega
      subst v; simp; field_simp [(sub_pos.mpr pp).ne']; ring_nf; norm_num
  exact H.trans (by simpa using (Rat.cast_le (K:=ℝ)).mpr val)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- Successive precisions show the cost of incomplete scales. `ell=L-1`.
At the first precision the complete-scale fraction is only `1/4`. -/
theorem base_seven_certificate_values :
    discrepancyCertificate 7 1 5 0 {2,3}=5/12 ∧
    discrepancyCertificate 7 1 5 1 {2,3}=1/4 ∧
    discrepancyCertificate 7 1 5 2 {2,3}=0 := by decide +kernel

end NormalityChecker.LocalizedSupport
