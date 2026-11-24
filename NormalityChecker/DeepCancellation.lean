module

public import NormalityChecker.DiscrepancyChecker

/-! Growing-precision tests on the actual integer mesh of a geometric scale. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

/-- When all other primes divide the radix, a zero at the current scale's
full mesh yields an integer shifted prefix once the radix factors have cleared. -/
theorem integral_of_deep_cell {b p k n D : ℕ} {S : Finset ℕ} (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (hb : 0<b) (base : ∀ r∈S,r∣b)
    (scale : k=Nat.log p n) (size : n≤2^D)
    (clean : ∀ m∈indices (insert p S) n, m+D≤n) (fail : n∈failedCells b 1 p k S) :
    (shifted b (insert p S) n).den=1 := by
  obtain ⟨region,zero⟩ := mem_filter.mp fail
  have hi : n<p^(k+1) := by simpa [pow_succ'] using (mem_Ico.mp region).2
  have h := canonical_prefix_residue (order:=1) (by decide) hp outside cop (k:=k) le_rfl hi
  simp only [Nat.sub_self,pow_zero,Nat.div_one,zero,pow_one] at h
  obtain ⟨a,d,hd,eqn,modEq⟩ := h
  have da : p^k ∣ a := (pow_dvd_pow p (Nat.le_succ k)).trans ((ZMod.natCast_eq_zero_iff ..).mp (by simpa using modEq.symm))
  obtain ⟨v,hv⟩ := da
  have cd := (ZMod.isUnit_iff_coprime ..).mp hd
  have dpos : 0<d := by
    by_contra! h; have dz : d=0 := by omega
    have h1 : 1<p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
    rw [dz,Nat.coprime_zero_left] at cd; exact (ne_of_gt h1) cd
  have er : (d:ℚ)*partialSum b (insert p S) n=v := by
    apply mul_left_cancel₀ (pow_ne_zero k (by exact_mod_cast hp.ne_zero) : (p:ℚ)^k≠0)
    simp only [powerPartial,powerWeight,pow_one] at eqn
    unfold partialSum weight
    rw [hv,Nat.cast_mul,Nat.cast_pow] at eqn; linear_combination eqn
  have ds := (reduced_info (x:=shifted b (insert p S) n) (S:=b^n*v) dpos (by
    dsimp [shifted]; push_cast; linear_combination -(b:ℚ)^n*er)).1
  exact Nat.eq_one_of_dvd_coprimes cd ds ((clean_denominator hp outside hb base size clean).trans
    (pow_dvd_pow p (by omega : Nat.log p n≤k+1)))

/-- Charge any selected mesh positions to recent insertions, an explicit initial
exceptional set, and a single anchored frequency of the actual orbit. -/
theorem deep_count_bound {b p N D : ℕ} {S : Finset ℕ} (hb : 2≤b) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (base : ∀ r∈S,r∣b) (size : N≤2^D) {δ : ℝ} (small : δ≤1)
    (F G : Finset ℕ) (domain : F⊆range N) (deep : ∀ n∈F,n∈failedCells b 1 p (Nat.log p n) S)
    (tail : ∀ n∈F,n∉G → 1/((n:ℝ)+1)<δ) :
    (F.card:ℝ) ≤ G.card+(D:ℝ)*(D+1)^(insert p S).card+
      N*frequency (shift b (value b (insert p S))) 0 δ N := by
  classical
  let A := insert p S
  let bad := ((indices A (2^D)) ×ˢ range D).image (fun t : ℕ×ℕ => t.1+t.2)
  let hit := (range N).filter (fun i => 0≤shift b (value b A) i ∧ shift b (value b A) i<δ)
  have cover : F⊆(G∪bad)∪hit := by
    intro n hn; have hi := mem_range.mp (domain hn)
    by_cases early : n∈G
    · exact mem_union_left _ (mem_union_left _ early)
    by_cases recent : n∈bad
    · exact mem_union_left _ (mem_union_right _ recent)
    have old (m : ℕ) (hm : m∈indices A n) : m+D≤n := by
      obtain ⟨mn,ms⟩ := mem_indices.mp hm; by_contra! h; apply recent
      exact mem_image.mpr ⟨(m,n-m),mem_product.mpr ⟨mem_indices.mpr ⟨mn.trans (hi.le.trans size),ms⟩,mem_range.mpr (by omega)⟩,by dsimp; omega⟩
    have integ := integral_of_deep_cell hp outside cop (by omega : 0<b) base
      rfl (hi.le.trans size) old (deep n hn)
    let z := (shifted b A n).num
    have eqn : (shifted b A n:ℝ)=(z:ℝ) := by
      have hq := (shifted b A n).num_div_den.symm
      simp only [show (shifted b A n).den=1 from integ,Nat.cast_one,div_one] at hq; exact_mod_cast hq
    obtain ⟨low,up⟩ := shift_error b A hb n; rw [eqn] at low up
    have cap := tail n hn early
    have win : shift b (value b A) n=(b:ℝ)^n*value b A-z := by
      unfold shift; rw [← Int.fract_sub_intCast _ z]; exact Int.fract_eq_self.mpr ⟨low,(up.trans_lt cap).trans_le small⟩
    exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr hi,by rw [win]; exact ⟨low,up.trans_lt cap⟩⟩)
  have count : (N:ℝ)*frequency (shift b (value b A)) 0 δ N = hit.card := by
    by_cases h : N=0
    · simp [hit,h]
    · change (N:ℝ)*(hit.card/N)=_; field_simp
  rw [count]; have coverCost := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le G bad) _))
  have bd : bad.card ≤ (D+1)^A.card * D := (card_image_le (f:=fun t : ℕ×ℕ => t.1+t.2) (s:=(indices A (2^D)) ×ˢ range D)).trans
    (by rw [card_product,card_range]; exact Nat.mul_le_mul_right D (insertion_count A D))
  apply (Nat.cast_le (α:=ℝ)).mpr coverCost |>.trans; push_cast
  gcongr; simpa [bad,mul_comm] using (Nat.cast_le (α:=ℝ)).mpr bd

/-- On a single scale, deep failures can only be recent insertions or visits
of the true orbit to a specified small interval at zero. -/
theorem deep_scale_count {b p k D : ℕ} {S : Finset ℕ} (hb : 2≤b) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (base : ∀ r∈S,r∣b)
    (size : p^(k+1)≤2^D) {δ : ℝ} (small : δ≤1) (tail : 1/((p:ℝ)^k+1)<δ) :
    let A := insert p S
    ((failedCells b 1 p k S).card:ℝ) ≤ (D:ℝ)*(D+1)^A.card +
      (p:ℝ)^(k+1)*frequency (shift b (value b A)) 0 δ (p^(k+1)) := by
  let F := failedCells b 1 p k S
  have region {n} (hn : n∈F) : p^k≤n ∧ n<p^(k+1) := by
    simpa [pow_succ'] using mem_Ico.mp (mem_filter.mp hn).1
  have h := deep_count_bound hb hp outside cop base size small F ∅ (fun _ hn => mem_range.mpr (region hn).2)
    (fun n hn => by rwa [Nat.log_eq_of_pow_le_of_lt_pow (region hn).1 (region hn).2])
    (fun n hn _ => lt_of_le_of_lt (by gcongr; exact_mod_cast (region hn).1) tail)
  simpa [F] using h

/-- Exact normality classification in terms of the infimum of the normalized
failed-cell counts, with a single off-radix prime and logarithmic order one. -/
theorem normal_iff_shrinking_cells {b p : ℕ} {S : Finset ℕ} (hb : 2≤b) (hp : p.Prime)
    (outside : p∉S) (cop : b.Coprime p) (primes : ∀ r∈S,r.Prime) (base : ∀ r∈S,r∣b) :
    NormalIn b (value b (insert p S)) ↔ ∀ ε : ℚ, 0<ε → ∃ k : ℕ,
      ((failedCells b 1 p k S).card:ℚ) ≤ ε*p^k := by
  refine ⟨?_,fun h => value_one b (insert p S) ▸ normal_of_shrinking_cells hb (by decide) hp outside cop primes h⟩
  intro hn ε hε
  let A := insert p S
  let δ := min ((ε:ℝ)/(4*p)) (1/2)
  have pp : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have ep : 0<(ε:ℝ) := by exact_mod_cast hε
  have dp : 0<δ := lt_min (by positivity) (by norm_num)
  have small : δ≤1 := (min_le_right ..).trans (by norm_num)
  have freq := (anchored_frequency_of_normal hn dp.le small).eventually_lt_const (show δ<2*δ by linarith)
  have G : Filter.Tendsto (fun k : ℕ => p^k) Filter.atTop Filter.atTop := tendsto_pow_atTop_atTop_of_one_lt hp.one_lt
  have G' := G.comp (Filter.tendsto_add_atTop_nat 1)
  have ratTail := (tendsto_one_div_add_atTop_nhds_zero_nat.comp G).eventually_lt_const dp
  let r := A.card+1
  let C := (2*(p:ℝ)+1)^r
  have price := ((tendsto_pow_const_div_const_pow_of_one_lt r pp).const_mul C).eventually_lt_const (show C*0<(ε:ℝ)/2 by rw [mul_zero]; positivity)
  obtain ⟨k,⟨hk,ff⟩,tt,pr⟩ := (((Filter.eventually_ge_atTop 1).and (G'.eventually freq)).and (ratTail.and price)).exists
  let D := p*(k+1)
  have size : p^(k+1)≤2^D := by dsimp [D]; rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
  have H := deep_scale_count hb hp outside cop base size small (by simpa using tt : 1/((p:ℝ)^k+1)<δ)
  have dk : (D:ℝ)+1≤(2*p+1)*k := by
    dsimp [D]; push_cast
    have kr : (1:ℝ)≤k := by exact_mod_cast hk
    nlinarith [mul_nonneg (by positivity : 0≤(p:ℝ)) (sub_nonneg.mpr kr)]
  have bd : (D:ℝ)*(D+1)^A.card≤C*(k:ℝ)^r := by
    calc _ ≤ ((D:ℝ)+1)^r := by dsimp [r]; rw [pow_succ']; gcongr; linarith
         _ ≤ ((2*p+1)*k:ℝ)^r := pow_le_pow_left₀ (by positivity) dk r
         _ = _ := mul_pow ..
  have pk : 0<(p:ℝ)^k := by positivity
  rw [← mul_div_assoc,div_lt_iff₀ pk] at pr
  have f : frequency (shift b (value b A)) 0 δ (p^(k+1))<2*δ := ff
  have dsmall := min_le_left ((ε:ℝ)/(4*p)) (1/2)
  have dprod : δ*(4*p)≤ε := (le_div_iff₀ (by positivity)).mp dsmall
  have fcost := mul_le_mul_of_nonneg_left f.le (by positivity : 0≤(p:ℝ)^(k+1))
  have dc := mul_le_mul_of_nonneg_right dprod pk.le
  dsimp only at H; rw [pow_succ] at H fcost
  refine ⟨k,?_⟩; apply (Rat.cast_le (K:=ℝ)).mp; push_cast
  change _≤(ε:ℝ)*(p:ℝ)^k
  change ((failedCells b 1 p k S).card:ℝ)≤(D:ℝ)*(D+1)^A.card+_ at H
  nlinarith only [H,bd,pr,fcost,dc]

end NormalityChecker.LocalizedSupport
