module

public import NormalityChecker.DeepCancellation

/-! A finite-scale lower bound dual to the modular discrepancy certificate. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

private def deepPositions (b p : ℕ) (S : Finset ℕ) (N : ℕ) :=
  (range N).filter (fun n => n∈failedCells b 1 p (Nat.log p n) S)

/-- Apart from at most one initial observation, the inherited carry in a finite
certificate is already present among the actual deep failures of earlier scales. -/
private lemma carry_le_deep {b p : ℕ} {S : Finset ℕ} (hp : p.Prime) (outside : p∉S) (cop : b.Coprime p)
    (k v : ℕ) (lo : p^k≤v) :
    ((failedCells b 1 p k S).card:ℝ)/(p-1)+CellProfile.mass (failedCells b 1 p k S) v ≤
      (deepPositions b p S v).card+1 := by
  let Z := fun j => failedCells b 1 p j S
  let F := deepPositions b p S
  have reg {j n : ℕ} (h : n∈Z j) : p^j≤n ∧ n<p^(j+1) := by simpa [pow_succ'] using mem_Ico.mp (mem_filter.mp h).1
  have adds (j u : ℕ) (low : p^j≤u) : (F (p^j)).card+CellProfile.mass (Z j) u≤(F u).card := by
    let E := (Z j).filter (·<u)
    have dis : Disjoint (F (p^j)) E := disjoint_left.mpr (fun n h₁ h₂ => (mem_range.mp (mem_filter.mp h₁).1).not_ge (reg (mem_filter.mp h₂).1).1)
    rw [show CellProfile.mass (Z j) u=E.card from rfl,← card_union_of_disjoint dis]; apply card_le_card
    intro n hn; rcases mem_union.mp hn with h|h
    · obtain ⟨r,m⟩ := mem_filter.mp h; exact mem_filter.mpr ⟨range_mono low r,m⟩
    · obtain ⟨m,r⟩ := mem_filter.mp h; refine mem_filter.mpr ⟨mem_range.mpr r,?_⟩
      rwa [Nat.log_eq_of_pow_le_of_lt_pow (reg m).1 (reg m).2]
  have parent (j : ℕ) : (Z (j+1)).card≤(Z j).card*p := by
    rw [← card_range p,← card_product]
    apply card_le_card_of_injOn (fun n => (n/p,n%p)) (fun n h => mem_product.mpr ⟨failed_cell_refines (by decide) hp outside cop h,mem_range.mpr (Nat.mod_lt _ hp.pos)⟩)
    intro n _ m _ e; change (n/p,n%p)=(m/p,m%p) at e
    obtain ⟨a,b⟩ := Prod.mk.inj e
    calc n = p*(n/p)+n%p := (Nat.div_add_mod n p).symm
         _ = p*(m/p)+m%p := by rw [a,b]
         _ = m := Nat.div_add_mod m p
  have pp : 0<(p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have budget (j : ℕ) : ((Z j).card:ℝ)≤((F (p^j)).card+1)*((p:ℝ)-1) := by
    induction j with
    | zero =>
      have le := card_le_card (filter_subset (fun u => powerCellResidue 1 p 0 S (inverseLift b p 0 0) u=0) (Ico (p^0) (p*p^0)))
      change (Z 0).card≤_ at le; simp only [Nat.card_Ico,pow_zero,mul_one] at le
      have rc : ((Z 0).card:ℝ)≤p-1 := by exact_mod_cast (Nat.cast_le (α:=ℝ)).mpr le |>.trans_eq (Nat.cast_sub hp.one_le)
      exact rc.trans (le_mul_of_one_le_left pp.le (by linarith [Nat.cast_nonneg (α:=ℝ) (F (p^0)).card]))
    | succ j ih =>
      have add := adds j (p^(j+1)) (Nat.pow_le_pow_right hp.pos (Nat.le_succ _))
      rw [CellProfile.mass,filter_true_of_mem (fun n h => (reg h).2)] at add
      have c : ((F (p^j)).card:ℝ)+(Z j).card≤(F (p^(j+1))).card := by exact_mod_cast add
      have m := mul_le_mul_of_nonneg_right c pp.le
      have par : ((Z (j+1)).card:ℝ)≤(Z j).card*(p:ℝ) := by exact_mod_cast parent j
      nlinarith only [par,m,ih]
  have dk := (div_le_iff₀ pp).mpr (budget k)
  have add : ((F (p^k)).card:ℝ)+CellProfile.mass (Z k) v≤(F v).card := by exact_mod_cast adds k v lo
  change ((Z k).card:ℝ)/_+CellProfile.mass (Z k) v≤(F v).card+1; linarith

/-- For logarithmic order one and a single off-base prime, the computable
upper bounds converge to the actual asymptotic interval discrepancy. -/
theorem certificate_tendsTo_discrepancy {b p : ℕ} {S : Finset ℕ} (hb : 2≤b) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime) (base : ∀ r∈S,r∣b) :
    Tendsto (fun k : ℕ => (discrepancyCertificate b 1 p k S:ℝ)) atTop
      (𝓝 (limsup (radixDiscrepancy b (value b (insert p S))) atTop)) := by
  let A := insert p S
  let x := value b A
  let d := limsup (radixDiscrepancy b x) atTop
  have gd := radix_discrepancy_bounds b x
  have lower (k : ℕ) : d≤(discrepancyCertificate b 1 p k S:ℝ) := by
    simpa only [value_one] using discrepancy_le_certificate hb (by decide : 0<1) hp outside cop primes k
  have posD : 0≤d := le_limsup_of_le (isBoundedUnder_of_eventually_le (.of_forall fun n => (gd n).2)) (fun y h => by obtain ⟨n,hn⟩ := h.exists; exact (gd n).1.trans hn)
  rw [Metric.tendsto_atTop]; intro ε he
  let δ := min (ε/8) (1/2)
  have dp : 0<δ := lt_min (by positivity) (by norm_num)
  have small : δ≤1 := (min_le_right ..).trans (by norm_num)
  obtain ⟨K,tail⟩ := eventually_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const dp)
  have Dcut := eventually_lt_of_limsup_lt (show d<d+δ by linarith) (isBoundedUnder_of_eventually_le (.of_forall fun n => (gd n).2))
  obtain ⟨V,large⟩ := eventually_atTop.mp Dcut
  let r := A.card+1
  let C := (2*(p:ℝ)+1)^r
  have pp : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have price := ((tendsto_pow_const_div_const_pow_of_one_lt r pp).const_mul C).eventually_lt_const (show C*0<δ by simpa using dp)
  have G : Tendsto (fun k : ℕ => p^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hp.one_lt
  have early := ((tendsto_const_div_atTop_nhds_zero_nat ((K:ℝ)+1)).comp G).eventually_lt_const dp
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (((eventually_ge_atTop 1).and (G.eventually_ge_atTop V)).and (price.and early))
  refine ⟨J,fun k hk => ?_⟩
  obtain ⟨⟨one,vlow⟩,pr,sm⟩ := hJ k hk
  let D := p*(k+1)
  have size : p^(k+1)≤2^D := by dsimp [D]; rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
  have dk : (D:ℝ)+1≤(2*p+1)*k := by
    dsimp [D]; push_cast; have kr : (1:ℝ)≤k := by exact_mod_cast one
    nlinarith [mul_nonneg (by positivity : 0≤(p:ℝ)) (sub_nonneg.mpr kr)]
  have bd : (D:ℝ)*(D+1)^A.card≤C*(k:ℝ)^r := by
    calc _ ≤ ((D:ℝ)+1)^r := by dsimp [r]; rw [pow_succ']; gcongr; linarith
         _ ≤ ((2*p+1)*k:ℝ)^r := pow_le_pow_left₀ (by positivity) dk r
         _ = _ := mul_pow ..
  have pk : 0<(p:ℝ)^k := by positivity
  rw [← mul_div_assoc,div_lt_iff₀ pk] at pr
  change (K+1:ℝ)/(p^k:ℕ)<δ at sm; rw [Nat.cast_pow,div_lt_iff₀ pk] at sm
  let Z := failedCells b 1 p k S
  have upper : (discrepancyCertificate b 1 p k S:ℝ)≤d+4*δ := by
    let U := insert (0:ℚ) ((Icc (p^k) (p*p^k)).image (CellProfile.score p Z))
    suffices each : ∀ z∈U,(z:ℝ)≤d+4*δ from each _ (max'_mem U (insert_nonempty ..))
    intro z hz; rcases mem_insert.mp hz with rfl|hz
    · rw [Rat.cast_zero]; positivity
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    obtain ⟨lo,hi⟩ := mem_Icc.mp hv; rw [← pow_succ'] at hi
    let F := deepPositions b p S v
    have obs := deep_count_bound hb hp outside cop base (hi.trans size) small F (range K)
      (filter_subset ..) (fun _ h => (mem_filter.mp h).2) (fun n _ h => tail n (by simpa using h))
    have carr := carry_le_deep hp outside cop k v lo
    have vp : (0:ℝ)<v := by exact_mod_cast (pow_pos hp.pos _).trans_le lo
    have hfreq := le_csSup (s:={z | ∃ a c : ℝ, 0≤a ∧ a<c ∧ c≤1 ∧ z=|frequency (shift b x) a c v-(c-a)|})
      (a:=|frequency (shift b x) 0 δ v-(δ-0)|) (show BddAbove _ from ⟨1,by rintro _ ⟨a,c,ha,lt,hc,rfl⟩; have f := frequency_bounds (shift b x) a c v; rw [abs_le]; constructor <;> linarith [f.1,f.2]⟩) ⟨0,δ,le_rfl,dp,small,rfl⟩
    change _≤radixDiscrepancy b x v at hfreq
    have fr := (abs_le.mp (hfreq.trans (large v (vlow.trans lo)).le)).2
    have fcost := mul_le_mul_of_nonneg_left fr vp.le
    have dv : (p:ℝ)^k≤v := by exact_mod_cast lo
    have rel := mul_le_mul_of_nonneg_left dv dp.le
    change ((CellProfile.score p Z v:ℚ):ℝ)≤_; unfold CellProfile.score; push_cast; apply (div_le_iff₀ vp).mpr
    simp only [card_range] at obs
    change (F.card:ℝ)≤K+(D:ℝ)*(D+1)^A.card+v*frequency (shift b x) 0 δ v at obs
    change ((Z.card:ℝ)/_)+_≤(F.card:ℝ)+1 at carr
    nlinarith only [carr,obs,bd,sm,pr,fcost,rel]
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (lower k))]; change _-d<ε
  have hδ := min_le_left (ε/8) (1/2:ℝ); change δ≤_ at hδ; linarith

end NormalityChecker.LocalizedSupport
