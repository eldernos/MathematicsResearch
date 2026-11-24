module

public import NormalityChecker.LocalizedExpansion
public import NormalityChecker.LocalizedMesh
public import NormalityChecker.StonehamOrbit

/-! Normality of the mixed two-generator localized logarithm. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.Localized
variable (d : Parameters)

noncomputable def character (h : ℤ) (n : ℕ) := phase ((h:ℝ)*(shifted d n:ℝ))

def periodFactor := d.b^d.p.totient-1

lemma clean_block {h : ℤ} (hh : h ≠ 0) (odd : Odd d.p) {K s T J : ℕ}
    (large : d.p^J*h.natAbs*periodFactor d ≤ K) (hK : 2≤K) (hs : 0<s)
    (hi : s ≤ d.p^6*K^6) (hT : T ≤ K^5)
    (survives : (K:ℚ)^6 ≤ d.p^J * padicNorm d.p (shifted d s))
    (clean : ∀ v ∈ allowed d s, index d v + v.1 ≤ s)
    (free : ∀ m, s<m → m<s+T → ¬ Supported d m) :
    ‖∑ i ∈ range T, character d h (s+i)‖ ≤ ((d.p:ℝ)^6+2)*K^4 := by
  let x := shifted d s
  let y := (h:ℚ)*x
  let Q := y.den
  have h1 : Q ∣ x.den := by simpa [Q,y] using Rat.mul_den_dvd (h:ℚ) x
  have h2 : x.den ∣ h.natAbs*Q := by
    have recover : (h:ℚ)⁻¹*y=x := inv_mul_cancel_left₀ (by exact_mod_cast hh) x
    simpa only [recover,Rat.inv_intCast_den,hh,ite_false] using Rat.mul_den_dvd (h:ℚ)⁻¹ y
  have hd := clean_denominator d s clean
  obtain ⟨e,_,he⟩ := (Nat.dvd_prime_pow d.hp).mp hd
  obtain ⟨f,_,hf⟩ := (Nat.dvd_prime_pow d.hp).mp (h1.trans hd)
  let : NeZero Q := ⟨y.den_ne_zero⟩
  have period : Q ≤ periodFactor d * orderOf (d.b:ZMod Q) := by
    rw [hf]; exact stoneham_order_bound d.hb d.hp.one_lt odd d.coprime f
  have qbound : Q ≤ s := (Nat.le_of_dvd (pow_pos d.hp.pos _) (h1.trans hd)).trans (Nat.pow_log_le_self _ hs.ne')
  have survives' : K^6 ≤ d.p^J*x.den := by
    exact_mod_cast survives.trans (mul_le_mul_of_nonneg_left (norm_le_clean_den d he) (by positivity))
  have hscale : K^6 ≤ (d.p^J*h.natAbs*periodFactor d)*orderOf (d.b:ZMod Q) := calc
    K^6 ≤ d.p^J * x.den := survives'
    _ ≤ d.p^J * (h.natAbs * Q) := Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.mpr hh) y.pos) h2)
    _ ≤ d.p^J * (h.natAbs * (periodFactor d * orderOf (d.b:ZMod Q))) := by gcongr
    _ = _ := by ring
  have coef : 0<d.p^J*h.natAbs*periodFactor d := by
    have hf' : 0<periodFactor d := Nat.sub_pos_of_lt (one_lt_pow₀ d.hb (Nat.totient_pos.mpr d.hp.pos).ne')
    exact Nat.mul_pos (Nat.mul_pos (pow_pos d.hp.pos _) (Int.natAbs_pos.mpr hh)) hf'
  have hper : K^5 ≤ orderOf (d.b:ZMod Q) := by
    apply Nat.le_of_mul_le_mul_left _ coef
    exact (Nat.mul_le_mul_right (K^5) large).trans ((show K*K^5=K^6 by ring) ▸ hscale)
  have hcard : orderOf (d.b:ZMod Q) ≤ Q := by simpa [ZMod.card] using orderOf_le_card_univ (x:=(d.b:ZMod Q))
  have hk : 0<K := by omega
  have hr : (0:ℝ)<K := by exact_mod_cast hk
  have unit : IsUnit (y.num : ZMod Q) := (ZMod.isUnit_intCast_iff_isCoprime ..).mpr
    (Int.isCoprime_iff_nat_coprime.mpr (by simpa [Q] using y.reduced.symm))
  have bound := unit_orbit_bound d.b y.num unit (hT.trans hper) (hT.trans (hper.trans hcard))
    (pow_pos hk 4) ((Nat.pow_le_pow_right hk (by decide : 4≤5)).trans hper)
    (δ:=(K:ℝ)⁻¹^2) (by positivity) (by push_cast; field_simp; norm_num)
  have rep (i : ℕ) (hi' : i ∈ range T) : character d h (s+i) = phase ((y.num:ℝ)*d.b^i/Q) := by
    unfold character
    rw [prefix_orbit d (fun m hm hmi => free m hm (by have := mem_range.mp hi'; omega))]
    push_cast
    have e : (h:ℝ)*(shifted d s:ℝ) = (y.num:ℝ)/Q := by
      calc _ = (y:ℝ) := by simp [y,x]
           _ = _ := Rat.cast_def y
    congr 1; linear_combination (d.b:ℝ)^i * e
  rw [sum_congr rfl rep]; apply bound.trans
  have hq : (Q:ℝ) ≤ (d.p:ℝ)^6*K^6 := by exact_mod_cast qbound.trans hi
  push_cast; calc (K:ℝ)⁻¹^2*Q + 2*K^4 ≤ (K:ℝ)⁻¹^2*(d.p^6*K^6) + 2*K^4 := by gcongr
                _ = _ := by field_simp

private lemma exponent_bounds {v : ℕ × ℕ} {D : ℕ} (h : index d v ≤ 2^D) : v.1 ≤ D ∧ v.2 ≤ D := by
  constructor <;> apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  · exact ((Nat.pow_le_pow_left d.hq _).trans (Nat.le_mul_of_pos_right _ (pow_pos d.hp.pos _))).trans h
  · exact ((Nat.pow_le_pow_left d.hp.two_le _).trans (Nat.le_mul_of_pos_left _ (pow_pos (by have := d.hq; omega) _))).trans h

private def blockExceptions (D B U : ℕ) : Finset ℕ :=
  let supports := ((range (D+1)) ×ˢ (range (D+1))).image (index d)
  (supports.image (fun m => m/B-U)) ∪ (supports.image (fun m => m/B+1-U))

private lemma exception_count (D B U : ℕ) : (blockExceptions d D B U).card ≤ 2*(D+1)^2 := by
  unfold blockExceptions
  apply (card_union_le ..).trans
  have hc := card_image_le (f:=index d) (s:=(range (D+1)) ×ˢ (range (D+1)))
  exact (add_le_add (card_image_le.trans hc) (card_image_le.trans hc)).trans_eq (by simp; ring)

private lemma good_block {D B U l m : ℕ} (hB : 0 < B) (hg : l ∉ blockExceptions d D B U)
    (hm : Supported d m) (hD : m ≤ 2^D) (hi : m < (U+l+1)*B) : m+B ≤ (U+l)*B := by
  obtain ⟨v,rfl⟩ := hm
  let m := index d v
  have ha := (exponent_bounds d hD).1
  have hj := (exponent_bounds d hD).2
  have hm' : m ∈ ((range (D+1)) ×ˢ (range (D+1))).image (index d) :=
    mem_image.mpr ⟨v,mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,rfl⟩
  have neither : m/B ≠ U+l ∧ m/B+1 ≠ U+l := by
    constructor <;> intro e <;> apply hg
    · exact mem_union_left _ (mem_image.mpr ⟨m,hm',by rw [e]; omega⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨m,hm',by rw [e]; omega⟩)
  have hq := (Nat.div_lt_iff_lt_mul hB).mpr hi
  change m/B < U+l+1 at hq
  have hq' : m/B+2 ≤ U+l := by omega
  have H := Nat.mul_le_mul_right B hq'
  have bound := Nat.lt_mul_div_succ m hB
  change m+B ≤ _
  rw [Nat.add_mul] at H; rw [Nat.mul_add,Nat.mul_comm B (m/B)] at bound; omega

private lemma block_split (f : ℕ → ℂ) (s B L : ℕ) :
    ∑ i ∈ range (L*B), f (s+i) = ∑ l ∈ range L, ∑ j ∈ range B, f (s+l*B+j) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]; simp [Nat.add_assoc]

/-- The cost of an arbitrary partial cell consists of a vanishing block error
and the specified exceptional width. Only starts with a small denominator are charged. -/
lemma statistic_cell_bound (F : ℕ → ℂ) (bounded : ∀ n, ‖F n‖ ≤ 1) {K D u T J : ℕ} {G : ℝ} (hG : 0≤G)
    (hu : 1≤u) (hu' : u<d.p^6)
    (hK : 2≤K) (hD : D≤K^5) (hDpow : d.p^6*K^6 ≤ 2^D) (hT : T≤K^6)
    {δ : ℝ} (hδ : 0≤δ)
    (diam : ∀ s t : ℕ, u*K^6 ≤ s → t ≤ (u+1)*K^6 →
      (d.p:ℚ)^J * padicNorm d.p (shifted d s) < (K:ℚ)^6 →
      (d.p:ℚ)^J * padicNorm d.p (shifted d t) < (K:ℚ)^6 → (t:ℝ)-s < δ*K^6)
    (good_bound : ∀ s : ℕ, K^6 ≤ s → s ≤ d.p^6*K^6 → (K:ℚ)^6 ≤ d.p^J*padicNorm d.p (shifted d s) →
      (∀ v ∈ allowed d s, index d v + v.1 ≤ s) →
      (∀ m, s<m → m<s+K^5 → ¬ Supported d m) → ‖∑ i ∈ range (K^5), F (s+i)‖ ≤ G) :
    ‖∑ i ∈ range T, F (u*K^6+i)‖ ≤ (K:ℝ)*G + (2+2*((D:ℝ)+1)^2)*K^5 + δ*K^6 := by
  classical
  have trivial (s T : ℕ) : ‖∑ i ∈ range T, F (s+i)‖ ≤ T :=
    (norm_sum_le ..).trans ((sum_le_sum (fun i (_ : i∈range T) => bounded (s+i))).trans_eq (by simp))
  let B := K^5
  let U := u*K
  let s := u*K^6
  let L := T/B
  let start (l : ℕ) := s+l*B
  let bad := (range L).filter (fun l => (d.p:ℚ)^J * padicNorm d.p (shifted d (start l)) < (K:ℚ)^6)
  let E := blockExceptions d D B U ∪ bad
  let f (l : ℕ) := ∑ i ∈ range B, F (start l+i)
  have hB : 0<B := pow_pos (by omega) _
  have hL : L ≤ K := Nat.div_le_of_le_mul (by simpa [B,show K^6=K^5*K by ring] using hT)
  have hb (l : ℕ) : start l = (U+l)*B := by dsimp [start,s,B,U]; ring
  have right (l : ℕ) (hl : l∈range L) : start l+B ≤ (u+1)*K^6 := calc
    start l+B = s+(l+1)*B := by dsimp [start]; ring
    _ ≤ s+K*B := Nat.add_le_add_left (Nat.mul_le_mul_right B ((mem_range.mp hl).trans_le hL)) _
    _ = _ := by dsimp [s,B]; ring
  have small : (bad.card:ℝ) ≤ δ*K+1 := by
    apply card_of_diameter _ (by positivity)
    intro a ha b hb'
    obtain ⟨ha₁,ha₂⟩ := mem_filter.mp ha; obtain ⟨hb₁,hb₂⟩ := mem_filter.mp hb'
    have le := diam (start a) (start b) (Nat.le_add_right ..) ((Nat.le_add_right ..).trans (right b hb₁)) ha₂ hb₂
    have hp : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
    apply le_of_lt; apply (lt_of_mul_lt_mul_right (a:=(K:ℝ)^5) _ (by positivity))
    dsimp [start,s,B] at le; push_cast at le; linarith only [le]
  have good (l : ℕ) (hl : l ∈ range L) (hg : l ∉ E) : ‖f l‖ ≤ G := by
    have ge : l ∉ blockExceptions d D B U := fun h => hg (mem_union_left _ h)
    have surv : (K:ℚ)^6 ≤ d.p^J*padicNorm d.p (shifted d (start l)) := by
      by_contra! h; exact hg (mem_union_right _ (mem_filter.mpr ⟨hl,h⟩))
    have bound := (right l hl).trans (Nat.mul_le_mul_right (K^6) hu')
    have before (m : ℕ) (hm : Supported d m) (hi : m < start l+B) : m+B ≤ start l := by
      have hmD := (hi.le.trans bound).trans hDpow
      rw [hb] at hi ⊢; apply good_block d hB ge hm hmD; simpa [Nat.add_mul] using hi
    apply good_bound (start l) ((Nat.le_mul_of_pos_left _ hu).trans (Nat.le_add_right ..)) ((Nat.le_add_right ..).trans bound) surv
    · intro v hv
      have hm := (mem_allowed d).mp hv
      have H := before _ ⟨v,rfl⟩ (by omega)
      have ha := (exponent_bounds d (((hm.trans (Nat.le_add_right ..)).trans bound).trans hDpow)).1
      omega
    · intro m hm hi hp; have := before m hp hi; omega
  have each (l : ℕ) (hl : l ∈ range L) : ‖f l‖ ≤ G + (if l∈E then (B:ℝ) else 0) := by
    split_ifs with he
    · exact (trivial (start l) B).trans (le_add_of_nonneg_left (by positivity))
    · simpa using good l hl he
  have mass : ∑ l ∈ range L, (if l∈E then (B:ℝ) else 0) ≤ (2*((D:ℝ)+1)^2 + (δ*K+1))*B := by
    rw [← sum_filter]; simp only [sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hcard := (card_le_card (show (range L).filter (·∈E) ⊆ E from fun _ hl => (mem_filter.mp hl).2)).trans (card_union_le ..)
    exact (by exact_mod_cast hcard : _ ≤ ((blockExceptions d D B U).card:ℝ) + bad.card).trans
      (add_le_add (by exact_mod_cast exception_count d D B U) small)
  have bulk : ‖∑ l ∈ range L, f l‖ ≤ (K:ℝ)*G + (2*((D:ℝ)+1)^2+(δ*K+1))*B := by
    apply (norm_sum_le ..).trans ((sum_le_sum each).trans _)
    rw [sum_add_distrib]; simp only [sum_const,card_range,nsmul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hL) (by positivity)) mass
  let r := T%B
  have cut : T=L*B+r := by dsimp [L,r]; rw [Nat.mul_comm,Nat.div_add_mod]
  conv_lhs => rw [cut,sum_range_add,block_split]
  have tail := trivial (s+L*B) r
  simp only [Nat.add_assoc] at tail
  apply (norm_add_le ..).trans ((add_le_add bulk tail).trans _)
  have hr : (r:ℝ) ≤ B := by exact_mod_cast (Nat.mod_lt T hB).le
  change _ + _ + (r:ℝ) ≤ _
  dsimp only [B] at *; push_cast at *; nlinarith only [hr]

private lemma cell_bound {h : ℤ} (hh : h ≠ 0) (odd : Odd d.p) {K D u T J : ℕ}
    (hu : 1≤u) (hu' : u<d.p^6) (large : d.p^J*h.natAbs*periodFactor d ≤ K)
    (hK : 2≤K) (hD : D≤K^5) (hDpow : d.p^6*K^6 ≤ 2^D) (hT : T≤K^6)
    {δ : ℝ} (hδ : 0≤δ)
    (diam : ∀ s t : ℕ, u*K^6 ≤ s → t ≤ (u+1)*K^6 →
      (d.p:ℚ)^J * padicNorm d.p (shifted d s) < (K:ℚ)^6 →
      (d.p:ℚ)^J * padicNorm d.p (shifted d t) < (K:ℚ)^6 → (t:ℝ)-s < δ*K^6) :
    ‖∑ i ∈ range T, character d h (u*K^6+i)‖ ≤
       ((d.p:ℝ)^6+4+2*((D:ℝ)+1)^2)*K^5 + δ*K^6 := by
  have H := statistic_cell_bound d (character d h) (fun n => (norm_phase _).le)
    (G:=((d.p:ℝ)^6+2)*K^4) (by positivity) hu hu' hK hD hDpow hT hδ diam
    (fun s low high surv clean free => clean_block d hh odd large hK
      ((pow_pos (show 0<K by omega) _).trans_le low) high le_rfl surv clean free)
  exact H.trans_eq (by ring)

/-- Mixed two-generator normality in base `b`, for `q ∣ b` and an odd prime
`p` coprime to `b`. The hypotheses allow composite `q` as well. -/
theorem normal (odd : Odd d.p) : NormalIn d.b (value d) := by
  apply (normalIn_iff_prefix_fourier d.hb (value d) (fun n => (shifted d n:ℝ))
    (squeeze_zero (fun n => (shift_error d n).1) (fun n => (shift_error d n).2)
      tendsto_one_div_add_atTop_nhds_zero_nat)).mpr
  intro h hh
  rw [mean_phase]
  let C := d.p^6
  have hC : 1<C := one_lt_pow₀ d.hp.one_lt (by decide)
  apply mean_zero_of_radix_cells (c:=C) (S:=1) hC (by decide)
  intro u hu ε hε
  have hu₀ := (mem_Ico.mp hu).1
  have hu₁ : u<C := by simpa using (mem_Ico.mp hu).2
  let δ := ε/2
  have hδ : 0<δ := half_pos hε
  obtain ⟨J,diam⟩ := exceptional_diameter d u hu₀ hδ
  let A : ℝ := C+4+2*(2*(C:ℝ)+1)^2
  have hg : Tendsto (fun k : ℕ => d.p^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt d.hp.one_lt
  have err : Tendsto (fun k : ℕ => A*((k:ℝ)^2/(d.p:ℝ)^k)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 2 (by exact_mod_cast d.hp.one_lt : (1:ℝ)<d.p)).const_mul A
  filter_upwards [eventually_ge_atTop (max 1 J),hg.eventually_ge_atTop (d.p^J*h.natAbs*periodFactor d),
    err.eventually_lt_const (lt_min hδ zero_lt_one)] with k hk large small T hT
  let K := d.p^k
  let D := C*(k+1)
  have hk₀ := (le_max_left 1 J).trans hk
  have hkJ := (le_max_right 1 J).trans hk
  have hK : 2≤K := d.hp.two_le.trans (by simpa [K] using Nat.pow_le_pow_right d.hp.pos hk₀)
  have scale : C^k=K^6 := by dsimp [C,K]; rw [← pow_mul, Nat.mul_comm, pow_mul]
  have ps : d.p^(6*k) = K^6 := by rw [Nat.mul_comm,pow_mul]
  have hDpow : C*K^6 ≤ 2^D := by
    rw [← scale,← pow_succ']; dsimp [D]; rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
  have Kr : (K:ℝ)=(d.p:ℝ)^k := by simp [K]
  rw [← Kr,← mul_div_assoc,div_lt_iff₀ (by exact_mod_cast (by omega : 0<K) : (0:ℝ)<K)] at small
  have hk' : 1≤(k:ℝ) := by exact_mod_cast hk₀
  have hD' : (D:ℝ)+1 ≤ (2*(C:ℝ)+1)*k := by
    dsimp [D]; push_cast; nlinarith [mul_le_mul_of_nonneg_left hk' (Nat.cast_nonneg C)]
  have hcoef : (C:ℝ)+4+2*((D:ℝ)+1)^2 ≤ A*k^2 := by
    dsimp [A]; have hsq := pow_le_pow_left₀ (by positivity) hD' 2
    nlinarith only [hsq,mul_le_mul_of_nonneg_left (show (1:ℝ)≤(k:ℝ)^2 by nlinarith) (show 0≤(C:ℝ)+4 by positivity)]
  have hDK : (D:ℝ) ≤ K := by
    have H := small.trans_le (mul_le_mul_of_nonneg_right (min_le_right δ 1) (Nat.cast_nonneg K))
    nlinarith [sq_nonneg (D:ℝ), (Nat.cast_nonneg D : (0:ℝ)≤D), (Nat.cast_nonneg C : (0:ℝ)≤C)]
  have hD : D≤K^5 := (by exact_mod_cast hDK : D≤K).trans (by simpa using Nat.pow_le_pow_right (show 0<K by omega) (by decide : 1≤5))
  have hj : J≤6*k := by omega
  have hpow : (d.p:ℚ)^J*(d.p:ℚ)^(6*k-J)=(K:ℚ)^6 := by
    rw [← pow_add,Nat.add_sub_of_le hj]; exact_mod_cast ps
  have hpr : 0<(d.p:ℚ)^J := pow_pos (by exact_mod_cast d.hp.pos) _
  have bound := cell_bound d hh odd hu₀ hu₁ large hK hD hDpow (scale ▸ hT) hδ.le (fun s t hs ht bs bt => by
    have low {x : ℚ} (hx : (d.p:ℚ)^J*x < (K:ℚ)^6) : x < (d.p:ℚ)^(6*k-J) :=
      (mul_lt_mul_iff_right₀ hpr).mp (hx.trans_eq hpow.symm)
    have H := diam (6*k) hj s t (ps ▸ hs) (ps ▸ ht) (low bs) (low bt)
    have e : (d.p:ℝ)^(6*k)=(K:ℝ)^6 := by exact_mod_cast ps
    rwa [e] at H)
  have sco : (C:ℝ)+4+2*((D:ℝ)+1)^2 ≤ δ*K :=
    hcoef.trans (small.le.trans (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg K)))
  have scR : (C:ℝ)^k=(K:ℝ)^6 := by exact_mod_cast scale
  change ‖∑ i ∈ range T, character d h (u*C^k+i)‖ ≤ ε*(C:ℝ)^k
  rw [scale,scR]; apply bound.trans
  rw [← Nat.cast_pow (α:=ℝ) d.p 6]
  change ((C:ℝ)+4+2*((D:ℝ)+1)^2)*K^5+δ*K^6 ≤ _
  have H := mul_le_mul_of_nonneg_right sco (show 0≤(K:ℝ)^5 by positivity)
  dsimp [δ] at *; nlinarith only [H]

/-- The literal double series for every compatible base, including composite `q ∣ b`. -/
theorem series_normal (odd : Odd d.p) : NormalIn d.b (∑' j : ℕ, ∑' a : ℕ,
    1 / ((d.q:ℝ)^a*d.p^j*(d.b:ℝ)^(d.q^a*d.p^j : ℕ))) := value_eq_series d ▸ normal d odd

/-- The binary logarithmic series restricted to `{2,p}` is normal for every odd prime `p`. -/
theorem binary_series_normal {p : ℕ} (hp : p.Prime) (odd : Odd p) :
    NormalIn 2 (∑' j : ℕ, ∑' a : ℕ, 1 / ((2:ℝ)^a*p^j*2^(2^a*p^j : ℕ))) := by
  let pars : Parameters := ⟨2,2,p,by decide,by decide,hp,dvd_rfl,Nat.coprime_two_left.mpr odd⟩
  exact series_normal pars odd

end NormalityChecker.Localized
