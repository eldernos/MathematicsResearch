module

public import NormalityChecker.LocalizedCertificate
public import NormalityChecker.LocalizedClearing
public import NormalityChecker.StonehamOrbit

/-! A successful finite certificate implies normality when all cofactor primes divide the base. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedSupport

structure Certificate where
  b : ℕ
  p : ℕ
  S : Finset ℕ
  ell : ℕ
  seed : ℕ
  hb : 2 ≤ b
  hp : p.Prime
  odd : Odd p
  coprime : b.Coprime p
  outside : p ∉ S
  base : ∀ q ∈ S, q ∣ b
  pass : passes b p ell seed S = true

namespace Certificate
variable (c : Certificate)

abbrev support := insert c.p c.S
private abbrev X (s : ℕ) := shifted c.b c.support s
private noncomputable def character (h : ℤ) (s : ℕ) := phase ((h:ℝ)*(X c s:ℝ))
private def periodFactor := c.b^c.p.totient-1
private def loss := c.p^(c.ell+1)

private lemma clean_block {h : ℤ} (hh : h ≠ 0) {K D s T : ℕ}
    (large : loss c*h.natAbs*periodFactor c ≤ K) (stable : c.p^(c.seed+c.ell) ≤ K^6)
    (hK : 2 ≤ K) (hs : K^6 ≤ s) (hi : s ≤ 64*K^6) (hD : s ≤ 2^D) (hT : T ≤ K^5)
    (clean : ∀ m ∈ indices c.support s, m+D ≤ s)
    (free : ∀ m, s < m → m < s+T → m ∉ Nat.factoredNumbers c.support) :
    ‖∑ i ∈ range T, character c h (s+i)‖ ≤ 66*(K:ℝ)^4 := by
  let x := X c s
  let y := (h:ℚ)*x
  let Q := y.den
  let k := Nat.log c.p s
  have spos : 0<s := (pow_pos (show 0<K by omega) _).trans_le hs
  have dk := clean_denominator c.hp c.outside (by have := c.hb; omega) c.base hD clean
  have hk : c.seed+c.ell ≤ k := Nat.le_log_of_pow_le c.hp.one_lt (stable.trans hs)
  have lo := Nat.pow_log_le_self c.p spos.ne'
  have up := Nat.lt_pow_succ_log_self c.hp.one_lt s
  have survives := passes_denominator c.hp c.outside c.coprime hk lo up c.pass
  have h1 : Q ∣ x.den := by simpa [Q,y] using Rat.mul_den_dvd (h:ℚ) x
  have h2 : x.den ∣ h.natAbs*Q := by
    have recover : (h:ℚ)⁻¹*y=x := inv_mul_cancel_left₀ (by exact_mod_cast hh) x
    simpa only [recover,Rat.inv_intCast_den,hh,ite_false] using Rat.mul_den_dvd (h:ℚ)⁻¹ y
  obtain ⟨e,_,he⟩ := (Nat.dvd_prime_pow c.hp).mp (h1.trans dk)
  have qle := (Nat.le_of_dvd (pow_pos c.hp.pos _) (h1.trans dk)).trans lo
  let : NeZero Q := ⟨y.den_ne_zero⟩
  have period : Q ≤ periodFactor c * orderOf (c.b:ZMod Q) := by
    rw [he]; exact stoneham_order_bound c.hb c.hp.one_lt c.odd c.coprime e
  have preserved := Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.mpr hh) y.pos) (survives.trans h2)
  have hscale : K^6 ≤ (loss c*h.natAbs*periodFactor c)*orderOf (c.b:ZMod Q) := calc
    K^6 ≤ c.p^(k+1) := hs.trans up.le
    _ = loss c*c.p^(k-c.ell) := by unfold loss; rw [← pow_add]; congr 1; omega
    _ ≤ loss c*(h.natAbs*Q) := Nat.mul_le_mul_left _ preserved
    _ ≤ loss c*(h.natAbs*(periodFactor c*orderOf (c.b:ZMod Q))) := by gcongr
    _ = _ := by ring
  have fac : 0<periodFactor c := Nat.sub_pos_of_lt (one_lt_pow₀ c.hb (Nat.totient_pos.mpr c.hp.pos).ne')
  have coef := Nat.mul_pos (Nat.mul_pos (pow_pos c.hp.pos (c.ell+1)) (Int.natAbs_pos.mpr hh)) fac
  have hper : K^5 ≤ orderOf (c.b:ZMod Q) := by
    apply Nat.le_of_mul_le_mul_left _ coef
    exact (Nat.mul_le_mul_right (K^5) large).trans ((show K*K^5=K^6 by ring) ▸ hscale)
  have hcard : orderOf (c.b:ZMod Q) ≤ Q := by simpa [ZMod.card] using orderOf_le_card_univ (x:=(c.b:ZMod Q))
  have kpos : 0<K := by omega
  have kr : (0:ℝ)<K := by exact_mod_cast kpos
  have unit : IsUnit (y.num : ZMod Q) := (ZMod.isUnit_intCast_iff_isCoprime ..).mpr
    (Int.isCoprime_iff_nat_coprime.mpr (by simpa [Q] using y.reduced.symm))
  have bound := unit_orbit_bound c.b y.num unit (hT.trans hper) (hT.trans (hper.trans hcard))
    (pow_pos kpos 4) ((Nat.pow_le_pow_right kpos (by decide : 4≤5)).trans hper)
    (δ:=(K:ℝ)⁻¹^2) (by positivity) (by push_cast; field_simp; norm_num)
  have rep (i : ℕ) (hit : i ∈ range T) : character c h (s+i) = phase ((y.num:ℝ)*c.b^i/Q) := by
    unfold character X; rw [orbit (fun m hm hmi => free m hm (by have := mem_range.mp hit; omega))]
    push_cast
    have eqn : (h:ℝ)*(X c s:ℝ) = (y.num:ℝ)/Q := by
      calc _ = (y:ℝ) := by simp [y,x]
           _ = _ := Rat.cast_def y
    congr 1; linear_combination (c.b:ℝ)^i * eqn
  rw [sum_congr rfl rep]; apply bound.trans
  have hq : (Q:ℝ) ≤ 64*K^6 := by exact_mod_cast qle.trans hi
  push_cast; calc (K:ℝ)⁻¹^2*Q + 2*K^4 ≤ (K:ℝ)⁻¹^2*(64*K^6) + 2*K^4 := by gcongr
                _ = _ := by field_simp; ring

private def blockExceptions (D B U : ℕ) :=
  let A := indices c.support (2^D)
  A.image (fun m => m/B-U) ∪ A.image (fun m => m/B+1-U)

private lemma exception_count (D B U : ℕ) : (blockExceptions c D B U).card ≤ 2*(D+1)^c.support.card :=
  (card_union_le ..).trans ((add_le_add (card_image_le.trans (insertion_count ..))
    (card_image_le.trans (insertion_count ..))).trans_eq (by ring))

private lemma good_block {D B U l m : ℕ} (hB : 0 < B) (hg : l ∉ blockExceptions c D B U)
    (hm : m ∈ Nat.factoredNumbers c.support) (hD : m ≤ 2^D) (hi : m < (U+l+1)*B) : m+B ≤ (U+l)*B := by
  have hm' := mem_indices.mpr ⟨hD,hm⟩
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

private lemma trivial_character_bound (h : ℤ) (s T : ℕ) :
    ‖∑ i ∈ range T, character c h (s+i)‖ ≤ T := by
  simpa [character,norm_phase] using norm_sum_le (range T) (fun i => character c h (s+i))

/-- A bound uniform in the final cutoff of a scale cell. -/
private lemma cell_bound {h : ℤ} (hh : h ≠ 0) {K D u T : ℕ} (hu : 1 ≤ u) (hu' : u < 64)
    (hK : loss c*h.natAbs*periodFactor c ≤ K) (stable : c.p^(c.seed+c.ell) ≤ K^6) (hK0 : 2 ≤ K) (hD : D ≤ K^5) (hDpow : 64*K^6 ≤ 2^D)
    (hT : T ≤ K^6) :
    ‖∑ i ∈ range T, character c h (u*K^6+i)‖ ≤
      (67 + 2*((D:ℝ)+1)^c.support.card)*(K:ℝ)^5 := by
  let B := K^5
  let U := u*K
  let s := u*K^6
  let L := T/B
  let E := blockExceptions c D B U
  let f (l : ℕ) := ∑ i ∈ range B, character c h (s+l*B+i)
  have hB : 0 < B := pow_pos (by omega) _
  have hL : L ≤ K := Nat.div_le_of_le_mul (by simpa [B,show K^6=K^5*K by ring] using hT)
  have hb (l : ℕ) : s+l*B = (U+l)*B := by dsimp [s,B,U]; ring
  have good (l : ℕ) (hl : l ∈ range L) (hg : l ∉ E) : ‖f l‖ ≤ 66*(K:ℝ)^4 := by
    let start := s+l*B
    have left : K^6 ≤ start := (Nat.le_mul_of_pos_left (K^6) hu).trans (Nat.le_add_right ..)
    have right : (U+l+1)*B ≤ 64*K^6 := by
      have he : (U+l+1)*B = u*K^6+(l+1)*B := by dsimp [U,B]; ring
      have le := Nat.mul_le_mul_right B (show l+1 ≤ K from (mem_range.mp hl).trans_le hL)
      rw [he]; calc u*K^6+(l+1)*B ≤ u*K^6+K*B := Nat.add_le_add_left le _
                    _ = (u+1)*K^6 := by dsimp [B]; ring
                    _ ≤ 64*K^6 := Nat.mul_le_mul_right _ hu'
    have right' : start+B ≤ 64*K^6 := by simpa [start,hb,Nat.add_mul] using right
    have before (m : ℕ) (hm : m ∈ Nat.factoredNumbers c.support) (hi : m < start+B) : m+B ≤ start := by
      have hmD := (hi.le.trans right').trans hDpow
      rw [show start = (U+l)*B from hb l] at hi ⊢
      apply good_block c hB hg hm hmD
      simpa [Nat.add_mul] using hi
    have high := (Nat.le_add_right start B).trans right'
    apply clean_block c hh hK stable hK0 left high (high.trans hDpow) le_rfl
    · intro m hm; obtain ⟨hm,hms⟩ := mem_indices.mp hm
      have H := before _ hms (by omega); omega
    · intro m hm hi hp; have := before m hp hi; omega
  have each (l : ℕ) (hl : l ∈ range L) : ‖f l‖ ≤ 66*(K:ℝ)^4 + (if l∈E then (B:ℝ) else 0) := by
    split_ifs with he
    · exact (trivial_character_bound c h (s+l*B) B).trans (le_add_of_nonneg_left (by positivity))
    · simpa using good l hl he
  have mass : ∑ l ∈ range L, (if l∈E then (B:ℝ) else 0) ≤ (2*((D:ℝ)+1)^c.support.card)*B := by
    rw [← sum_filter]; simp only [sum_const,nsmul_eq_mul]
    gcongr
    exact_mod_cast (card_le_card (show (range L).filter (·∈E) ⊆ E from fun _ hl => (mem_filter.mp hl).2)).trans
      (exception_count c D B U)
  have bulk : ‖∑ l ∈ range L, f l‖ ≤ (K:ℝ)*(66*(K:ℝ)^4) + (2*((D:ℝ)+1)^c.support.card)*B := by
    apply (norm_sum_le ..).trans ((sum_le_sum each).trans _)
    rw [sum_add_distrib]; simp only [sum_const,card_range,nsmul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hL) (by positivity)) mass
  let r := T%B
  have cut : T=L*B+r := by dsimp [L,r]; rw [Nat.mul_comm, Nat.div_add_mod]
  change ‖∑ i ∈ range T, character c h (s+i)‖ ≤ _
  conv_lhs => rw [cut,sum_range_add,block_split]
  have tail := trivial_character_bound c h (s+L*B) r
  simp only [Nat.add_assoc] at tail
  apply (norm_add_le ..).trans ((add_le_add bulk tail).trans _)
  have hr : (r:ℝ) ≤ B := by exact_mod_cast (Nat.mod_lt T hB).le
  change _ + _ + (r:ℝ) ≤ _
  dsimp only [B] at *; push_cast at *; nlinarith only [hr]

private lemma degree_bound (k : ℕ) (hk : 6 ≤ k) : 6*(k+1) ≤ 2^k := by
  induction k,hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

/-- A successful denominator certificate proves normality for one off-base prime and
any finite set of cofactor primes dividing the base. -/
theorem normal : NormalIn c.b (value c.b c.support) := by
  apply (normalIn_iff_prefix_fourier c.hb _ (fun n => (X c n:ℝ))
    (squeeze_zero (fun n => (shift_error _ _ c.hb n).1) (fun n => (shift_error _ _ c.hb n).2)
      tendsto_one_div_add_atTop_nhds_zero_nat)).mpr
  intro h hh; rw [mean_phase]
  apply mean_zero_of_radix_cells (c:=64) (S:=1) (by decide) (by decide)
  intro u hu ε hε
  let r := c.support.card
  let A : ℝ := 67+2*13^r
  have grow : Tendsto (fun k : ℕ => 2^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have err : Tendsto (fun k : ℕ => A*((k:ℝ)^r/(2:ℝ)^k)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt r (by norm_num : (1:ℝ)<2)).const_mul A
  filter_upwards [eventually_ge_atTop 6,grow.eventually_ge_atTop (loss c*h.natAbs*periodFactor c),
    grow.eventually_ge_atTop (c.p^(c.seed+c.ell)),err.eventually_lt_const hε] with k hk large stable small T hT
  let K : ℕ := 2^k
  let D := 6*(k+1)
  have hK : 2≤K := (by decide : 2 ≤ 2^6).trans (Nat.pow_le_pow_right (by decide) hk)
  have hkpos : 0<K := by omega
  have kpow (i : ℕ) (hi : 1 ≤ i) : K ≤ K^i := by simpa using Nat.pow_le_pow_right hkpos hi
  have scale : 64^k = K^6 := by dsimp [K]; rw [← pow_mul,Nat.mul_comm,pow_mul]; rfl
  have deg := degree_bound k hk
  have dp : 64*K^6 ≤ 2^D := by rw [← scale,← pow_succ']; dsimp [D]; rw [pow_mul]; rfl
  have H := cell_bound c hh (mem_Ico.mp hu).1 (by simpa using (mem_Ico.mp hu).2)
    large (stable.trans (kpow 6 (by decide))) hK (deg.trans (kpow 5 (by decide))) dp (scale ▸ hT)
  have sr : (64:ℝ)^k=(K:ℝ)^6 := by exact_mod_cast scale
  change ‖∑ i ∈ range T, character c h (u*64^k+i)‖ ≤ ε*(64:ℝ)^k
  rw [scale,sr]; apply H.trans
  have hkr : (1:ℝ)≤k := by exact_mod_cast (by omega : 1≤k)
  have hc : (D:ℝ)+1 ≤ 13*k := by dsimp [D]; push_cast; linarith
  have co := pow_le_pow_left₀ (by positivity) hc r
  rw [mul_pow] at co
  have coef : 67+2*((D:ℝ)+1)^r ≤ A*k^r := by
    dsimp [A]; nlinarith only [co,one_le_pow₀ hkr (n:=r)]
  have hKr : (K:ℝ)=(2:ℝ)^k := by simp [K]
  rw [← hKr,← mul_div_assoc,div_lt_iff₀ (by exact_mod_cast hkpos : 0<(K:ℝ))] at small
  calc _ ≤ (A*k^r)*K^5 := mul_le_mul_of_nonneg_right coef (by positivity)
       _ ≤ (ε*K)*K^5 := mul_le_mul_of_nonneg_right small.le (by positivity)
       _ = _ := by ring

end Certificate
end NormalityChecker.LocalizedSupport
