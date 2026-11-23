module

public import NormalityChecker.Distribution

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- The observed position lies within ε of an integer translate of one of the centers. -/
def nearResidues (C : Finset ℝ) (ε y : ℝ) : Prop :=
  ∃ t ∈ C, ∃ z : ℤ, |y-(t+z)| < ε

open Classical in
noncomputable def concentrationFrequency (b : ℕ) (x : ℝ) (C : Finset ℝ) (ε : ℝ) (N : ℕ) : ℝ :=
  ((range N).filter (fun n => nearResidues C ε ((b:ℝ)^n*x))).card / (N:ℝ)

/-- Positive upper density near a fixed finite set modulo one, at every radius,
is incompatible with normality. The approximations may approach from either side. -/
theorem not_normal_of_concentration {b : ℕ} {x η : ℝ} {C : Finset ℝ} (hη : 0<η)
    (H : ∀ ε : ℝ, 0<ε → ∃ᶠ N in atTop, η ≤ concentrationFrequency b x C ε N) :
    ¬ NormalIn b x := by
  classical
  intro h
  have U := (normalIn_iff_uniform h.1 x).mp h
  let ε := η/(4*((C.card:ℝ)+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  let W (n : ℕ) (t : ℝ) := (⌊(b:ℝ)^n*x-(t-ε)⌋:ℝ) - ⌊(b:ℝ)^n*x-(t+ε)⌋
  have hw (n : ℕ) (t : ℝ) : 0 ≤ W n t := by
    apply sub_nonneg.mpr; exact_mod_cast Int.floor_mono (by linarith : (b:ℝ)^n*x-(t+ε) ≤ (b:ℝ)^n*x-(t-ε))
  have hw1 {n : ℕ} {t : ℝ} {z : ℤ} (hz : |(b:ℝ)^n*x-(t+z)| < ε) : 1 ≤ W n t := by
    obtain ⟨hl,hu⟩ := abs_lt.mp hz
    have hl' := Int.le_floor.mpr (by linarith : (z:ℝ) ≤ (b:ℝ)^n*x-(t-ε))
    have hu' := Int.floor_lt.mpr (by linarith : (b:ℝ)^n*x-(t+ε) < z)
    dsimp [W]; exact_mod_cast (show (1:ℤ) ≤ ⌊(b:ℝ)^n*x-(t-ε)⌋ - ⌊(b:ℝ)^n*x-(t+ε)⌋ by omega)
  have hdom (N : ℕ) : concentrationFrequency b x C ε N ≤
      ∑ t ∈ C, (N:ℝ)⁻¹ * ∑ n ∈ range N, W n t := by
    rw [← mul_sum,sum_comm, concentrationFrequency, div_eq_inv_mul, card_filter]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum; intro n _
    by_cases hp : nearResidues C ε ((b:ℝ)^n*x)
    · simp only [hp,ite_true]
      obtain ⟨t,ht,z,hz⟩ := hp
      exact (hw1 hz).trans (single_le_sum (fun i _ => hw n i) ht)
    · simpa [hp] using sum_nonneg (fun t (_ : t ∈ C) => hw n t)
  have ht := tendsto_finsetSum C (fun t _ => U (t-ε) (t+ε))
  have he : (∑ t ∈ C, ((t+ε)-(t-ε))) < η := by
    simp only [show ∀ t : ℝ, t+ε-(t-ε)=2*ε by intro; ring,sum_const,nsmul_eq_mul]
    dsimp [ε]; field_simp; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) C.card) hη.le]
  apply H ε hε
  filter_upwards [ht.eventually_lt_const he] with N hN
  exact ((hdom N).trans_lt hN).not_ge

open Classical in
/-- An expansion whose arithmetic prefixes hit finitely many residues with positive
upper density and whose shifted remainders tend to zero is nonnormal. -/
theorem not_normal_of_prefix_hits {b : ℕ} {x η : ℝ} {P : ℕ → ℝ} {C : Finset ℝ}
    (hη : 0<η) (herror : Tendsto (fun n => (b:ℝ)^n*x-P n) atTop (𝓝 0))
    (hcount : ∃ᶠ N in atTop, η ≤
      ((range N).filter (fun i => ∃ t ∈ C, ∃ z : ℤ, P i=t+z)).card/(N:ℝ)) :
    ¬ NormalIn b x := by
  classical
  apply not_normal_of_concentration (C:=C) (η:=η/2) (half_pos hη)
  intro ε hε
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp herror) ε hε
  have small := (tendsto_const_div_atTop_nhds_zero_nat (K:ℝ)).eventually_lt_const (half_pos hη)
  apply (hcount.and_eventually (small.and (eventually_gt_atTop 0))).mono
  rintro N ⟨hN,hsmall,hpos⟩
  let near := (range N).filter (fun i => nearResidues C ε ((b:ℝ)^i*x))
  let hit := (range N).filter (fun i => ∃ t ∈ C, ∃ z : ℤ, P i=t+z)
  have hsub : hit ⊆ range K ∪ near := by
    intro i hi
    obtain ⟨hiN,t,ht,z,hz⟩ := mem_filter.mp hi
    by_cases hiK : i<K
    · exact mem_union_left _ (mem_range.mpr hiK)
    · refine mem_union_right _ (mem_filter.mpr ⟨hiN,t,ht,z,?_⟩)
      simpa [Real.dist_eq,hz] using hK i (by omega)
  have HH := (card_le_card hsub).trans (Finset.card_union_le ..)
  rw [card_range] at HH
  have HH' : (hit.card:ℝ) ≤ K+(near.card:ℝ) := by exact_mod_cast HH
  change η≤(hit.card:ℝ)/N at hN
  change η/2≤(near.card:ℝ)/N
  have hn : (0:ℝ)<N := by exact_mod_cast hpos
  rw [le_div_iff₀ hn] at hN ⊢
  rw [div_lt_iff₀ hn] at hsmall
  linarith

/-- A fixed rational grid contains y up to tolerance ε whenever Dy is within Dε of an integer. -/
private lemma near_grid {D : ℕ} (hD : 0<D) {y ε : ℝ} {z : ℤ}
    (hz : |(D:ℝ)*y-z| < D*ε) :
    nearResidues ((range D).image (fun a : ℕ => (a:ℝ)/D)) ε y := by
  classical
  have hd : (0:ℤ)<D := by exact_mod_cast hD
  let r := (z%(D:ℤ)).toNat
  have hr : (r:ℤ) = z%D := Int.toNat_of_nonneg (Int.emod_nonneg _ hd.ne')
  have hrD : r<D := by exact_mod_cast (hr ▸ Int.emod_lt_of_pos z hd : (r:ℤ)<D)
  refine ⟨(r:ℝ)/D,mem_image.mpr ⟨r,mem_range.mpr hrD,rfl⟩,z/(D:ℤ), ?_⟩
  have he : (r:ℝ) + (D:ℝ)*((z/(D:ℤ):ℤ):ℝ) = z := by
    exact_mod_cast (hr ▸ Int.emod_add_mul_ediv z D : (r:ℤ)+(D:ℤ)*(z/D)=z)
  have hd' : (0:ℝ)<D := by exact_mod_cast hD
  apply (mul_lt_mul_iff_right₀ hd').mp
  have e : (D:ℝ)*(y-((r:ℝ)/D+↑(z/(D:ℤ)))) = D*y-z := by
    rw [mul_sub,mul_add, show (D:ℝ)*((r:ℝ)/D)=r by field_simp]; linarith
  rw [← e,abs_mul,abs_of_pos hd'] at hz
  exact hz

/-- Integers on every position of one proportional cell give a finite-grid
obstruction for the original number before clearing its rational coefficients. -/
theorem not_normal_of_grid_cell {b D u : ℕ} {x B : ℝ} (hD : 0<D)
    (H : ∀ k i : ℕ, i<3^k → ∃ z : ℤ,
      |(D:ℝ)*((b:ℝ)^(u*3^k+i+1)*x)-z| ≤ B/(3:ℝ)^k) : ¬ NormalIn b x := by
  classical
  let C := (range D).image (fun a : ℕ => (a:ℝ)/D)
  apply not_normal_of_concentration (C:=C) (η:=1/((u:ℝ)+2)) (by positivity)
  intro ε hε
  have lim : Tendsto (fun k : ℕ => B/(3:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=B)).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3)))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (lim.eventually_lt_const (show 0<(D:ℝ)*ε by positivity))
  rw [frequently_atTop]
  intro M
  obtain ⟨j,hj⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(3:ℕ))).eventually_ge_atTop M)
  let k := max K j
  let q := 3^k
  let N := (u+1)*q+1
  have hq : 0<q := pow_pos (by decide) _
  have hqM : M≤q := hj _ (le_max_right ..)
  have hN : 0<N := Nat.succ_pos _
  have hqN : q≤N := (Nat.le_mul_of_pos_left q (Nat.succ_pos u)).trans (Nat.le_succ _)
  refine ⟨N,hqM.trans hqN,?_⟩
  have hsub : Ico (u*q+1) N ⊆ (range N).filter (fun n => nearResidues C ε ((b:ℝ)^n*x)) := by
    intro n hn; obtain ⟨hl,hu⟩ := mem_Ico.mp hn
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hl
    have hi : i<q := by dsimp [N] at hu; rw [Nat.add_mul] at hu; omega
    obtain ⟨z,hz⟩ := H k i hi
    apply mem_filter.mpr; refine ⟨mem_range.mpr hu,?_⟩
    exact near_grid hD (z:=z) (by simpa [Nat.add_right_comm] using hz.trans_lt (hK k (le_max_left ..)))
  have hc := card_le_card hsub
  rw [Nat.card_Ico,show N-(u*q+1)=q by dsimp [N]; rw [Nat.add_mul]; omega] at hc
  rw [concentrationFrequency,div_le_div_iff₀ (by positivity) (by exact_mod_cast hN)]
  have hnq : N ≤ (u+2)*q := by dsimp [N]; rw [Nat.add_mul,Nat.add_mul]; omega
  have hc' := Nat.mul_le_mul_left (u+2) hc
  simpa [mul_comm] using (show (N:ℝ) ≤ ((u:ℝ)+2)*((#((range N).filter (fun n => nearResidues C ε ((b:ℝ)^n*x)))):ℝ) by exact_mod_cast hnq.trans hc')

end NormalityChecker
