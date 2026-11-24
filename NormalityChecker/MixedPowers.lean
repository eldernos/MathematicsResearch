module

public import NormalityChecker.CompositeLayers
public import NormalityChecker.LocalizedMeshRate
public import NormalityChecker.IndexedExpansion

/-! All positive polylogarithm orders and composite coprime generators. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.Localized.Composite

structure Generators where
  b : ℕ
  q : ℕ
  c : ℕ
  hb : 2≤b
  hq : 2≤q
  hc : 2≤c
  cop : b.Coprime c
  clears : ∃ A : ℕ, q∣b^A

namespace Generators
variable (d : Generators)
abbrev p := d.c.minFac
lemma prime : d.p.Prime := Nat.minFac_prime (by have := d.hc; omega)
lemma qc : d.q.Coprime d.c := by
  obtain ⟨A,hA⟩ := d.clears; exact Nat.Coprime.of_dvd_left hA (d.cop.pow_left A)
lemma unit_at {v : ℕ} (h : v.Coprime d.c) : ¬d.p∣v :=
  d.prime.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left (Nat.minFac_dvd _) h.symm)
lemma norm_growth : 1<(padicNorm d.p (d.c:ℚ))⁻¹ := by
  let : Fact d.p.Prime := ⟨d.prime⟩
  apply (one_lt_inv₀ (lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.ne_zero (by exact_mod_cast (show d.c≠0 by have := d.hc; omega)))))).mpr
  exact (padicNorm.nat_lt_one_iff _).mpr (Nat.minFac_dvd _)
abbrev idx := index d.q d.c
lemma positive (v) : 0<d.idx v := Nat.mul_pos (pow_pos (by have := d.hq; omega) _) (pow_pos (by have := d.hc; omega) _)
lemma injective : Function.Injective d.idx := by
  let : Fact d.p.Prime := ⟨d.prime⟩
  have pw (x : ℚ) (k : ℕ) : padicNorm d.p (x^k)=(padicNorm d.p x)^k := by induction k with | zero => simp | succ _ ih => simp [pow_succ,ih]
  have norm (v : ℕ × ℕ) : padicNorm d.p (d.idx v:ℚ) = (padicNorm d.p (d.c:ℚ))^v.2 := by
    simp [idx,index,pw,(padicNorm.nat_eq_one_iff _).mpr (d.unit_at d.qc)]
  intro v w h
  have e : (padicNorm d.p (d.c:ℚ))⁻¹^v.2=(padicNorm d.p (d.c:ℚ))⁻¹^w.2 := by
    rw [inv_pow,inv_pow,← norm,← norm,h]
  have j := pow_right_injective₀ (zero_lt_one.trans d.norm_growth) d.norm_growth.ne' e
  have a := Nat.eq_of_mul_eq_mul_right (pow_pos (by have := d.hc; omega : 0<d.c) w.2) (by simpa only [idx,index,j] using h)
  exact Prod.ext (Nat.pow_right_injective d.hq a) j

noncomputable def value (s : ℕ) := ∑' v : ℕ × ℕ, (1:ℝ)/((d.idx v:ℝ)^s*(d.b:ℝ)^(d.idx v))
abbrev P (s : ℕ) := powerPrefix d.b d.q d.c s

theorem shifted_tail {s : ℕ} (hs : 0<s) : Tendsto (fun n => (d.b:ℝ)^n*d.value s-(d.P s n:ℝ)) atTop (𝓝 0) := by
  let a (v : ℕ × ℕ) : ℚ := 1/(d.idx v:ℚ)^s
  have large (v : ℕ × ℕ) : (1:ℚ)≤(d.idx v:ℚ)^s := one_le_pow₀ (by exact_mod_cast d.positive v)
  have small (ε : ℝ) (pos : 0<ε) : ∃ N : ℕ, ∀ i, N≤d.idx i → (a i:ℝ)≤ε := by
    obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
    refine ⟨N,fun i hi => ?_⟩
    have h1 : (d.idx i:ℝ)≤(d.idx i:ℝ)^s := by exact_mod_cast (show d.idx i≤(d.idx i)^s by simpa using Nat.pow_le_pow_right (d.positive i) hs)
    dsimp [a]; push_cast; apply (div_le_iff₀ (pow_pos (by exact_mod_cast d.positive i) _)).mpr
    have hr : (N:ℝ) ≤ d.idx i := by exact_mod_cast hi
    linarith only [(div_lt_iff₀ pos).mp (hN.trans_le (hr.trans h1))]
  have tail := indexed_shift_error d.hb d.idx d.injective a (fun _ => by dsimp [a]; positivity)
    (fun v => (div_le_one (zero_lt_one.trans_le (large v))).mpr (large v)) small (allowed d.q d.c) (fun _ _ => mem_allowed d.hq d.hc)
  simpa only [P,value,powerPrefix,a,Rat.cast_mul,Rat.cast_pow,Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,div_div] using tail

/-- Signed integer numerators on the common insertion schedule. Zero suppresses a term. -/
def weightedPrefix (w : ℕ × ℕ → ℤ) (s n : ℕ) : ℚ :=
  (d.b:ℚ)^n * ∑ v ∈ allowed d.q d.c n, (w v:ℚ) * (1 / ((d.idx v:ℚ)^s*(d.b:ℚ)^(d.idx v)))

@[simp] lemma weightedPrefix_one (s n : ℕ) : d.weightedPrefix (fun _ => 1) s n = d.P s n := by
  simp [weightedPrefix,P,powerPrefix]

private lemma clean (w : ℕ × ℕ → ℤ) {s n D A : ℕ} (base : d.q∣d.b^A) (size : n≤2^D)
    (age : ∀ v∈allowed d.q d.c n, d.idx v + A*s*D ≤ n) :
    (d.weightedPrefix w s n).den ∣ d.c^(D*s) := by
  have each (v : ℕ × ℕ) (hv : v∈allowed d.q d.c n) :
      ∃ z : ℕ, (z:ℚ)=d.c^(D*s)*((d.b:ℚ)^n*(1/((d.idx v:ℚ)^s*(d.b:ℚ)^(d.idx v)))) := by
    have hi := (mem_allowed d.hq d.hc).mp hv
    have ab : v.1≤D := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (((Nat.pow_le_pow_left d.hq _).trans
      (Nat.le_mul_of_pos_right _ (pow_pos (by have := d.hc; omega : 0<d.c) _))).trans (hi.trans size))
    have jb : v.2≤D := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (((Nat.pow_le_pow_left d.hc _).trans
      (Nat.le_mul_of_pos_left _ (pow_pos (by have := d.hq; omega : 0<d.q) _))).trans (hi.trans size))
    have cap : A*(v.1*s)≤n-d.idx v := by
      have H := age v hv
      have hle := Nat.mul_le_mul_left (A*s) ab
      rw [show A*(v.1*s)=A*s*v.1 by ring]; omega
    have hqa := pow_dvd_pow_of_dvd base (v.1*s); rw [← pow_mul] at hqa
    obtain ⟨z,hz⟩ := hqa.trans (pow_dvd_pow d.b cap)
    obtain ⟨w,hw⟩ := pow_dvd_pow d.c (Nat.mul_le_mul_right s jb)
    have eqn : (z*w)*(d.idx v)^s=d.c^(D*s)*d.b^(n-d.idx v) := by rw [hz,hw]; simp [idx,index,mul_pow,← pow_mul]; ring
    refine ⟨z*w,?_⟩
    have bp : (d.b:ℚ)≠0 := by exact_mod_cast (by have := d.hb; omega : d.b≠0)
    have eqn' : ((z*w:ℕ):ℚ)*(d.idx v:ℚ)^s=(d.c:ℚ)^(D*s)*(d.b:ℚ)^(n-d.idx v) := by exact_mod_cast eqn
    rw [pow_sub₀ _ bp hi] at eqn'; field_simp [bp,(d.positive v).ne'] at eqn' ⊢; linarith only [eqn']
  choose! z hz using each
  let S : ℤ := ∑ v ∈ allowed d.q d.c n, w v*z v
  have eqn : (S:ℚ)=(d.c^(D*s):ℕ)*d.weightedPrefix w s n := by
    simp only [S,weightedPrefix,Int.cast_sum,Int.cast_mul,Int.cast_natCast,Nat.cast_pow,mul_sum]
    apply sum_congr rfl; intro v hv; rw [hz v hv]; ring
  have repr : d.weightedPrefix w s n=Rat.divInt S (d.c^(D*s):ℕ) := by
    rw [Rat.divInt_eq_div,Int.cast_natCast]
    apply (eq_div_iff (by exact_mod_cast (pow_ne_zero _ (show d.c≠0 by have := d.hc; omega)))).mpr
    rw [eqn,mul_comm]
  exact_mod_cast (repr ▸ Rat.den_dvd S (d.c^(D*s):ℕ) : ((d.weightedPrefix w s n).den:ℤ) ∣ (d.c^(D*s):ℕ))

/-- For a fixed denominator cutoff, bad full-block starts occupy a vanishing
fraction of each cell. A single prime divisor of `c` detects separation. -/
theorem exceptional_of_separated (Z : ℕ → ℚ) (M : ℕ)
    (separates : ∃ J : ℕ, ∀ {a j n m}, J≤j → n<d.q^a*d.c^j → d.q^a*d.c^j≤m → m≤d.q*n →
      M≤max (Z n).den (Z m).den) (u : ℕ) (hu : 1≤u) {δ : ℝ} (pos : 0<δ) :
    ∀ᶠ k : ℕ in atTop, let K := d.c^k
      let bad := (range K).filter (fun l => (Z ((u*K+l)*K)).den<M)
      (bad.card:ℝ) ≤ δ*K+1 := by
  obtain ⟨J,sep⟩ := separates
  let U : ℝ := u+1
  have up : 0<U := by dsimp [U]; positivity
  obtain ⟨R,hR⟩ := exists_nat_gt (max 1 (3*U*Real.log d.q/δ))
  have Rpos : 0<R := by exact_mod_cast (zero_lt_one.trans ((le_max_left ..).trans_lt hR))
  have width : 3*U*Real.log d.q/(R+1) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]; linarith only [(div_lt_iff₀ pos).mp ((le_max_right ..).trans_lt hR),pos]
  filter_upwards [eventually_ge_atTop (R*d.q^2*d.c^R),eventually_ge_atTop J] with k hk big
  let K := d.c^k
  have kp : 0<K := pow_pos (by have := d.hc; omega) _
  have kr : (0:ℝ)<K := by exact_mod_cast kp
  apply card_of_diameter _ (mul_nonneg pos.le kr.le)
  intro l hl r hr
  obtain ⟨hl,bl⟩ := mem_filter.mp hl; obtain ⟨hr,br⟩ := mem_filter.mp hr
  have lr : l<K := mem_range.mp hl; have rr : r<K := mem_range.mp hr
  by_contra! apart
  let x : ℝ := u+l/K; let y : ℝ := u+r/K
  have rr' : (r:ℝ)<K := by exact_mod_cast rr
  have lower : 1≤x := by dsimp [x]; exact (by exact_mod_cast hu : (1:ℝ)≤u).trans (le_add_of_nonneg_right (by positivity))
  have upper : y≤U := by dsimp [y,U]; linarith only [(div_lt_one kr).mpr rr']
  have far : x+δ≤y := by dsimp [x,y]; have := (lt_div_iff₀ kr).mpr apart; rw [sub_div] at this; linarith
  obtain ⟨a,i,hi,hx,hy⟩ := effective_threshold_mesh d.hc d.hq d.qc.symm Rpos lower upper up (by linarith [width,far])
  have ik := hi.trans hk
  let j := 2*k-i
  have jk : k≤j := by dsimp [j]; omega
  have pw : (d.c:ℝ)^i*(d.c:ℝ)^j=(K:ℝ)^2 := by
    rw [← pow_add,show i+j=2*k by dsimp [j]; omega,Nat.mul_comm,pow_mul]; simp [K]
  have ci : (0:ℝ)<(d.c:ℝ)^i := pow_pos (by exact_mod_cast (by have := d.hc; omega : 0<d.c)) _
  have eqn : ((d.q:ℝ)^a/(d.c:ℝ)^i)*(K:ℝ)^2=(d.q:ℝ)^a*(d.c:ℝ)^j := by rw [← pw]; field_simp
  have left : (u*K+l)*K<d.q^a*d.c^j := by
    have H := mul_lt_mul_of_pos_right hx (sq_pos_of_pos kr); rw [eqn] at H; dsimp [x] at H
    exact_mod_cast (show ((u:ℝ)*K+l)*K < (d.q:ℝ)^a*(d.c:ℝ)^j by convert H using 1; field_simp)
  have right : d.q^a*d.c^j≤(u*K+r)*K := by
    have H := mul_lt_mul_of_pos_right hy (sq_pos_of_pos kr); rw [eqn] at H; dsimp [y] at H
    exact_mod_cast (show (d.q:ℝ)^a*(d.c:ℝ)^j ≤ ((u:ℝ)*K+r)*K by apply H.le.trans_eq; field_simp)
  have ratio : (u*K+r)*K≤d.q*((u*K+l)*K) := by
    rw [← Nat.mul_assoc]; apply Nat.mul_le_mul_right K
    have H := Nat.mul_le_mul_right (u*K+l) d.hq
    have low := Nat.le_mul_of_pos_left K hu; omega
  exact (not_lt_of_ge (sep (big.trans jk) left right ratio)) (max_lt bl br)

/-- Common clearing, insertion and orbit argument for all signed numerators. -/
theorem normal_weighted (w : ℕ × ℕ → ℤ) (s : ℕ) (x : ℝ)
    (tail : Tendsto (fun n => (d.b:ℝ)^n*x-(d.weightedPrefix w s n:ℝ)) atTop (𝓝 0))
    (exceptional : ∀ u : ℕ, 1≤u → ∀ M : ℕ, ∀ δ : ℝ, 0<δ → ∀ᶠ k : ℕ in atTop,
      let K := d.c^k
      (((range K).filter (fun l => (d.weightedPrefix w s ((u*K+l)*K)).den<M)).card:ℝ) ≤ δ*K+1) :
    NormalIn d.b x := by
  obtain ⟨A,base⟩ := d.clears
  let C := 2*d.c
  apply normal_of_arithmetic_certificate (B:=d.c) (L:=d.c) d.hb (by have := d.hc; omega) d.hc
    _ (d.weightedPrefix w s) tail (fixed_support_orbit_estimate d.hb d.hc d.cop) (2*C*s)
  intro u hu M η pos
  let δ := η/2
  have dp : 0<δ := half_pos pos
  have coef : 0<(d.c:ℝ) := by exact_mod_cast (by have := d.hc; omega : 0<d.c)
  let F : ℝ := 3+2*(2*(C:ℝ)+1)^2+A*s*(2*C)
  have grow := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by exact_mod_cast d.hc : (1:ℝ)<d.c)).const_mul F
  simp only [mul_zero] at grow
  filter_upwards [eventually_ge_atTop 1,exceptional u (mem_Ico.mp hu).1 M δ dp,
    grow.eventually_le_const (lt_min dp zero_lt_one)] with k hk diameter small
  let K := d.c^k; let D := C*(k+1)
  have kp : 0<K := pow_pos (by have := d.hc; omega) _
  have kr : (1:ℝ)≤k := by exact_mod_cast hk
  have dk : (D:ℝ)+1≤(2*C+1)*k := by dsimp [D]; push_cast; nlinarith [mul_le_mul_of_nonneg_left kr (Nat.cast_nonneg C)]
  have dcle : (A:ℝ)*s*D ≤ (A:ℝ)*s*(2*C)*k^2 := by
    have le : (D:ℝ) ≤ 2*C*k^2 := by dsimp [D]; push_cast; nlinarith [mul_le_mul_of_nonneg_left kr (Nat.cast_nonneg C),mul_le_mul_of_nonneg_left (show (k:ℝ)≤k^2 by nlinarith) (Nat.cast_nonneg C)]
    nlinarith only [mul_le_mul_of_nonneg_left le (show 0≤(A:ℝ)*s by positivity)]
  have kr' : (K:ℝ)=(d.c:ℝ)^k := by simp [K]
  rw [← kr',← mul_div_assoc,div_le_iff₀ (by exact_mod_cast kp : (0:ℝ)<K)] at small
  have budget : A*s*D≤K := by
    have H := small.trans (mul_le_mul_of_nonneg_right (min_le_right ..) (Nat.cast_nonneg K)); dsimp [F] at H
    exact_mod_cast (show (A:ℝ)*s*D≤K by nlinarith [dcle,mul_nonneg (sq_nonneg (2*(C:ℝ)+1)) (sq_nonneg (k:ℝ))])
  let idxs := ((range (D+1)) ×ˢ (range (D+1))).image d.idx
  let ins := insertionBlocks idxs K (u*K)
  let bad := (range K).filter (fun l => (d.weightedPrefix w s ((u*K+l)*K)).den<M)
  refine ⟨ins∪bad,?_,?_⟩
  · have H := card_union_le ins bad
    have cnt : ins.card≤2*((D+1)^2) := (card_insertionBlocks ..).trans (Nat.mul_le_mul_left _ (card_image_le.trans_eq (by simp; ring)))
    change (bad.card:ℝ)≤δ*K+1 at diameter
    have cnt' : (ins.card:ℝ) ≤ 2*((D:ℝ)+1)^2 := by exact_mod_cast cnt
    have H' : ((ins∪bad).card:ℝ)≤(ins.card:ℝ)+bad.card := by exact_mod_cast H
    have small' := small.trans (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg K))
    have sq := pow_le_pow_left₀ (by positivity) dk 2
    rw [mul_pow] at sq; dsimp [F] at small'; rw [← kr']; dsimp [δ] at *
    nlinarith only [H',cnt',diameter,small',sq,one_le_pow₀ kr (n:=2),mul_nonneg (show 0≤(A:ℝ)*s*(2*C) by positivity) (sq_nonneg (k:ℝ))]
  · intro l hl he
    have hn := not_or.mp (mt mem_union.mpr he)
    let n := (u*K+l)*K
    have endpt : (u*K+l+1)*K=n+K := by dsimp [n]; ring
    have high : (u*K+l+1)*K≤2^D := calc
      _ ≤ ((u+1)*K)*K := Nat.mul_le_mul_right K (by rw [Nat.add_mul,one_mul]; omega)
      _ ≤ ((d.c*d.c)*K)*K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (mem_Ico.mp hu).2)
      _ = (d.c^2)^(k+1) := by dsimp [K]; rw [pow_succ,← pow_mul,Nat.mul_comm 2 k,pow_mul]; ring
      _ ≤ (2^C)^(k+1) := Nat.pow_le_pow_left (by dsimp [C]; rw [pow_mul']; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _ ) _
      _ = _ := (pow_mul ..).symm
    have before (v : ℕ × ℕ) (hv : d.idx v < (u*K+l+1)*K) : d.idx v + K ≤ n := by
      have cap := hv.le.trans high
      have ab : v.1 ≤ D := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (((Nat.pow_le_pow_left d.hq _).trans (Nat.le_mul_of_pos_right _ (pow_pos (by have := d.hc; omega : 0<d.c) _))).trans cap)
      have jb : v.2 ≤ D := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (((Nat.pow_le_pow_left d.hc _).trans (Nat.le_mul_of_pos_left _ (pow_pos (by have := d.hq; omega : 0<d.q) _))).trans cap)
      exact insertionBlocks_free kp hn.1 (mem_image.mpr ⟨v,mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,rfl⟩ : d.idx v∈idxs) hv
    have clean := d.clean w (s:=s) base (n:=n) (by rw [endpt] at high; omega : n≤2^D) (fun v hv => by
      have le : d.idx v ≤ n := (mem_allowed d.hq d.hc).mp hv; have H := before v (by rw [endpt]; omega); omega)
    refine ⟨le_of_not_gt (fun h => hn.2 (mem_filter.mpr ⟨mem_range.mpr hl,h⟩)),⟨D*s,clean⟩,?_,?_⟩
    · apply (Nat.le_of_dvd (pow_pos (by have := d.hc; omega : 0<d.c) _) clean).trans
      rw [← pow_mul]; apply Nat.pow_le_pow_right (by have := d.hc; omega)
      dsimp [D]; nlinarith [Nat.mul_le_mul_right (C*s) hk]
    · intro i hi
      have eqn : allowed d.q d.c (n+i)=allowed d.q d.c n := by
        ext v; rw [mem_allowed d.hq d.hc,mem_allowed d.hq d.hc]; constructor
        · intro le; change d.idx v≤n+i at le; change d.idx v≤n; change i<K at hi
          have H := before v (by rw [endpt]; omega); omega
        · omega
      change d.weightedPrefix w s (n+i)=_ * d.weightedPrefix w s n
      simp only [weightedPrefix,eqn,pow_add]; ring

/-- Positive orders with unit numerator. -/
theorem normal (s : ℕ) (hs : 0<s) : NormalIn d.b (d.value s) := by
  apply d.normal_weighted (fun _ => 1) s _ (by simpa using d.shifted_tail hs)
  intro u hu M δ pos
  simp only [weightedPrefix_one]
  apply d.exceptional_of_separated (d.P s) M _ u hu pos
  have grow := tendsto_pow_atTop_atTop_of_one_lt (one_lt_pow₀ d.norm_growth hs.ne')
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (grow.eventually_ge_atTop (M:ℚ))
  refine ⟨J,fun {a j n m} hj left right short => ?_⟩
  have sep := power_separated hs d.hq d.hc d.prime (Nat.minFac_dvd _) (d.unit_at d.cop) (d.unit_at d.qc) left right short
  exact_mod_cast (hJ j hj).trans (sep.trans (max_le_max (padicNorm_le_den d.prime _) (padicNorm_le_den d.prime _)))

/-- The same result with the series and all generator assumptions written out. -/
theorem series_normal {b q c s : ℕ} (hb : 2 ≤ b) (hq : 2 ≤ q) (hc : 2 ≤ c)
    (cop : b.Coprime c) (clears : ∃ A : ℕ, q ∣ b^A) (hs : 0 < s) :
    NormalIn b (∑' v : ℕ × ℕ, 1 / (((q^v.1*c^v.2 : ℕ) : ℝ)^s * (b:ℝ)^(q^v.1*c^v.2))) :=
  (Generators.mk b q c hb hq hc cop clears).normal s hs

end Generators
end NormalityChecker.Localized.Composite
