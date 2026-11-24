module

public import NormalityChecker.LocalizedSeries
public import NormalityChecker.StonehamOrbit
public import NormalityChecker.FourierTest

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.LocalizedFive

private lemma frequency_denominator {s : ℕ} (hs : 25 ≤ s) (h : ℤ) (hh : h ≠ 0)
    (clean : ∀ a j : ℕ, 2^a*5^j ≤ s → 2^a*5^j+a ≤ s) :
    let y := (h:ℚ)*shiftedPrefix s
    ∃ e, y.den = 5^e ∧ y.den ≤ s ∧ s < 25*h.natAbs*y.den := by
  let x := shiftedPrefix s
  let y := (h:ℚ)*x
  have h1 : y.den ∣ x.den := by simpa [y] using Rat.mul_den_dvd (h:ℚ) x
  have h2 : x.den ∣ h.natAbs*y.den := by
    have recover : (h:ℚ)⁻¹*y=x := by dsimp [y]; rw [inv_mul_cancel_left₀ (by exact_mod_cast hh)]
    simpa only [recover,Rat.inv_intCast_den,hh,ite_false] using Rat.mul_den_dvd (h:ℚ)⁻¹ y
  have hd := clean_denominator s clean
  obtain ⟨e,he,hq⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp (h1.trans hd)
  refine ⟨e,hq,(Nat.le_of_dvd (by positivity) (h1.trans hd)).trans (Nat.pow_log_le_self 5 (by omega)),?_⟩
  let k := Nat.log 5 s - 2
  have hk : Nat.log 5 s = k+2 := by
    have := Nat.le_log_of_pow_le (by decide : 1<5) (show 5^2 ≤ s from hs); dsimp [k]; omega
  have lo := Nat.pow_log_le_self 5 (by omega : s≠0)
  have hi := Nat.lt_pow_succ_log_self (by decide : 1<5) s
  rw [hk] at lo hi
  have hv := denominator_fives lo hi
  have d : 5^(k+1) ∣ x.den := ((by decide : Nat.Prime 5).pow_dvd_iff_le_factorization x.den_ne_zero).mpr
    (by change _ ≤ (shiftedPrefix s).den.factorization 5; rw [hv]; split_ifs <;> omega)
  have le := Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.mpr hh) y.pos) (d.trans h2)
  calc s < 5^(k+3) := hi
       _ = 25*5^(k+1) := by ring
       _ ≤ 25*h.natAbs*y.den := by simpa [mul_assoc] using Nat.mul_le_mul_left 25 le

private noncomputable def character (h : ℤ) (n : ℕ) := phase ((h:ℝ)*(shiftedPrefix n:ℝ))

/-- Fourier cancellation on a whole block free of insertions, once the powers of two
have cleared. At scale `K^6` even a block of length `K^5` saves a factor `K`. -/
private lemma clean_block {h : ℤ} (hh : h ≠ 0) {K s T : ℕ}
    (hK : 375*h.natAbs ≤ K) (hK0 : 2 ≤ K) (hs : K^6 ≤ s) (hs' : s ≤ 15625*K^6)
    (hT : T ≤ K^5) (clean : ∀ a j : ℕ, 2^a*5^j ≤ s → 2^a*5^j+a ≤ s)
    (free : ∀ m, s < m → m < s+T → ¬ Supported m) :
    ‖∑ i ∈ range T, character h (s+i)‖ ≤ 15627*(K:ℝ)^4 := by
  let y := (h:ℚ)*shiftedPrefix s
  let q := y.den
  have h25 : 25 ≤ s := le_trans (by decide : 25≤2^6) ((Nat.pow_le_pow_left hK0 6).trans hs)
  obtain ⟨e,he,hqs,hsq⟩ := frequency_denominator h25 h hh clean
  change q = 5^e at he; change q ≤ s at hqs; change s < 25*h.natAbs*q at hsq
  let : NeZero q := ⟨y.den_ne_zero⟩
  have period : q ≤ 15*orderOf (2:ZMod q) := by
    rw [he]; simpa only [show 2^Nat.totient 5-1=15 by decide,Nat.cast_ofNat] using stoneham_order_bound (b:=2) (c:=5) (by decide) (by decide) (by decide) (by decide) e
  have hper : K^5 ≤ orderOf (2:ZMod q) := by
    have hc : 0<375*h.natAbs := Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hh)
    apply Nat.le_of_mul_le_mul_left (c:=375*h.natAbs) _ hc
    calc 375*h.natAbs*K^5 ≤ K^6 := by rw [show K^6=K*K^5 by ring]; exact Nat.mul_le_mul_right _ hK
         _ ≤ 25*h.natAbs*q := (hs.trans hsq.le)
         _ ≤ _ := by convert Nat.mul_le_mul_left (25*h.natAbs) period using 1; ring
  have hqper : orderOf (2:ZMod q) ≤ q := by simpa [ZMod.card] using orderOf_le_card_univ (x:=(2:ZMod q))
  have hH : K^4 ≤ K^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0<K)
  have unit : IsUnit (y.num : ZMod q) := (ZMod.isUnit_intCast_iff_isCoprime ..).mpr
    (Int.isCoprime_iff_nat_coprime.mpr (by simpa [q] using y.reduced.symm))
  have bound := unit_orbit_bound 2 y.num unit (hT.trans hper) (hT.trans (hper.trans hqper))
    (pow_pos (by omega : 0<K) 4) (hH.trans hper) (δ:=(K:ℝ)⁻¹^2) (by positivity)
    (by push_cast; field_simp; norm_num)
  have rep (i : ℕ) (hi : i ∈ range T) : character h (s+i) = phase ((y.num:ℝ)*2^i/q) := by
    unfold character
    rw [prefix_orbit (fun m hm hmi => free m hm (by have := mem_range.mp hi; omega))]
    have eqn : (h:ℝ)*(shiftedPrefix s:ℝ) = (y.num:ℝ)/q := by
      calc _ = (y:ℝ) := by simp [y]
           _ = _ := Rat.cast_def y
    congr 1; linear_combination 2^i * eqn
  rw [sum_congr rfl rep]; apply bound.trans
  have hq : (q:ℝ) ≤ 15625*(K:ℝ)^6 := by exact_mod_cast hqs.trans hs'
  push_cast; calc (K:ℝ)⁻¹^2*q + 2*K^4 ≤ (K:ℝ)⁻¹^2*(15625*K^6) + 2*K^4 := by gcongr
                _ = _ := by field_simp; ring

private def blockExceptions (D B U : ℕ) : Finset ℕ :=
  let supports := ((range (D+1)) ×ˢ (range (D+1))).image (fun v => 2^v.1*5^v.2)
  (supports.image (fun m => m/B-U)) ∪ (supports.image (fun m => m/B+1-U))

private lemma exception_count (D B U : ℕ) : (blockExceptions D B U).card ≤ 2*(D+1)^2 := by
  unfold blockExceptions
  apply (card_union_le ..).trans
  have hc := card_image_le (f:=fun v : ℕ×ℕ => 2^v.1*5^v.2) (s:=(range (D+1)) ×ˢ (range (D+1)))
  exact (add_le_add (card_image_le.trans hc) (card_image_le.trans hc)).trans_eq (by simp; ring)

private lemma good_block {D B U l m : ℕ} (hB : 0 < B) (hg : l ∉ blockExceptions D B U)
    (hm : Supported m) (hD : m ≤ 2^D) (hi : m < (U+l+1)*B) : m+B ≤ (U+l)*B := by
  obtain ⟨a,j,rfl⟩ := hm
  let m := 2^a*5^j
  have ha : a ≤ D := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    ((Nat.le_mul_of_pos_right (2^a) (pow_pos (by decide) j)).trans hD)
  have hj : j ≤ D := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    (((Nat.pow_le_pow_left (by decide : 2≤5) j).trans (Nat.le_mul_of_pos_left (5^j) (pow_pos (by decide) a))).trans hD)
  have hm' : m ∈ ((range (D+1)) ×ˢ (range (D+1))).image (fun v => 2^v.1*5^v.2) :=
    mem_image.mpr ⟨(a,j),mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,rfl⟩
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
    ‖∑ i ∈ range T, character h (s+i)‖ ≤ T := by
  simpa [character,norm_phase] using norm_sum_le (range T) (fun i => character h (s+i))

/-- A bound uniform in the final cutoff of a scale cell. -/
private lemma cell_bound {h : ℤ} (hh : h ≠ 0) {K D u T : ℕ} (hu : 1 ≤ u) (hu' : u < 15625)
    (hK : 375*h.natAbs ≤ K) (hK0 : 2 ≤ K) (hD : D ≤ K^5) (hDpow : 15625*K^6 ≤ 2^D)
    (hT : T ≤ K^6) :
    ‖∑ i ∈ range T, character h (u*K^6+i)‖ ≤
      (15628 + 2*((D:ℝ)+1)^2)*(K:ℝ)^5 := by
  let B := K^5
  let U := u*K
  let s := u*K^6
  let L := T/B
  let E := blockExceptions D B U
  let f (l : ℕ) := ∑ i ∈ range B, character h (s+l*B+i)
  have hB : 0 < B := pow_pos (by omega) _
  have hL : L ≤ K := Nat.div_le_of_le_mul (by simpa [B,show K^6=K^5*K by ring] using hT)
  have hb (l : ℕ) : s+l*B = (U+l)*B := by dsimp [s,B,U]; ring
  have good (l : ℕ) (hl : l ∈ range L) (hg : l ∉ E) : ‖f l‖ ≤ 15627*(K:ℝ)^4 := by
    let start := s+l*B
    have left : K^6 ≤ start := (Nat.le_mul_of_pos_left (K^6) hu).trans (Nat.le_add_right ..)
    have right : (U+l+1)*B ≤ 15625*K^6 := by
      have he : (U+l+1)*B = u*K^6+(l+1)*B := by dsimp [U,B]; ring
      have le := Nat.mul_le_mul_right B (show l+1 ≤ K from (mem_range.mp hl).trans_le hL)
      rw [he]; calc u*K^6+(l+1)*B ≤ u*K^6+K*B := Nat.add_le_add_left le _
                    _ = (u+1)*K^6 := by dsimp [B]; ring
                    _ ≤ 15625*K^6 := Nat.mul_le_mul_right _ hu'
    have right' : start+B ≤ 15625*K^6 := by simpa [start,hb,Nat.add_mul] using right
    have before (m : ℕ) (hm : Supported m) (hi : m < start+B) : m+B ≤ start := by
      have hmD := (hi.le.trans right').trans hDpow
      rw [show start = (U+l)*B from hb l] at hi ⊢
      apply good_block hB hg hm hmD
      simpa [Nat.add_mul] using hi
    apply clean_block hh hK hK0 left ((Nat.le_add_right start B).trans right') le_rfl
    · intro a j hm
      have H := before _ ⟨a,j,rfl⟩ (by omega)
      have ha : a ≤ D := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
        (((Nat.le_mul_of_pos_right (2^a) (pow_pos (by decide) j)).trans hm).trans
          (((Nat.le_add_right start B).trans right').trans hDpow))
      omega
    · intro m hm hi hp; have := before m hp hi; omega
  have each (l : ℕ) (hl : l ∈ range L) : ‖f l‖ ≤ 15627*(K:ℝ)^4 + (if l∈E then (B:ℝ) else 0) := by
    split_ifs with he
    · exact (trivial_character_bound h (s+l*B) B).trans (le_add_of_nonneg_left (by positivity))
    · simpa using good l hl he
  have mass : ∑ l ∈ range L, (if l∈E then (B:ℝ) else 0) ≤ (2*((D:ℝ)+1)^2)*B := by
    rw [← sum_filter]; simp only [sum_const,nsmul_eq_mul]
    gcongr
    exact_mod_cast (card_le_card (show (range L).filter (·∈E) ⊆ E from fun _ hl => (mem_filter.mp hl).2)).trans
      (exception_count D B U)
  have bulk : ‖∑ l ∈ range L, f l‖ ≤ (K:ℝ)*(15627*(K:ℝ)^4) + (2*((D:ℝ)+1)^2)*B := by
    apply (norm_sum_le ..).trans ((sum_le_sum each).trans _)
    rw [sum_add_distrib]; simp only [sum_const,card_range,nsmul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hL) (by positivity)) mass
  let r := T%B
  have cut : T=L*B+r := by dsimp [L,r]; rw [Nat.mul_comm, Nat.div_add_mod]
  change ‖∑ i ∈ range T, character h (s+i)‖ ≤ _
  conv_lhs => rw [cut,sum_range_add,block_split]
  have tail := trivial_character_bound h (s+L*B) r
  simp only [Nat.add_assoc] at tail
  apply (norm_add_le ..).trans ((add_le_add bulk tail).trans _)
  have hr : (r:ℝ) ≤ B := by exact_mod_cast (Nat.mod_lt T hB).le
  change _ + _ + (r:ℝ) ≤ _
  dsimp only [B] at *; push_cast at *; nlinarith only [hr]

/-- The binary localized logarithm supported on the primes two and five is normal.
The scale cells have length `K^6` for `K = 5^k`; their exceptional blocks
occupy at most a polynomial in `k` times `K^5` positions. -/
theorem binary_normal : NormalIn 2 value := by
  apply (normalIn_iff_prefix_fourier (by decide : 2 ≤ 2) value
    (fun n => (shiftedPrefix n:ℝ)) (squeeze_zero (fun n => (shift_error n).1)
      (fun n => (shift_error n).2) tendsto_one_div_add_atTop_nhds_zero_nat)).mpr
  intro h hh
  rw [mean_phase]
  apply mean_zero_of_radix_cells (c:=15625) (S:=1) (by decide) (by decide)
  intro u hu ε hε
  have grow : Tendsto (fun k : ℕ => 5^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have err : Tendsto (fun k : ℕ => 20000*((k:ℝ)^2/(5:ℝ)^k)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<5)).const_mul 20000
  have cutoff (k : ℕ) (hk : 4 ≤ k) : 18*(k+1) ≤ 5^k := by
    induction k,hk using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  filter_upwards [eventually_ge_atTop 4, grow.eventually_ge_atTop (375*h.natAbs),err.eventually_lt_const hε]
    with k hk hK hεk T hT
  let K : ℕ := 5^k
  let D := 18*(k+1)
  have hscale : 15625^k = K^6 := by dsimp [K]; rw [← pow_mul, Nat.mul_comm, pow_mul]; rfl
  have hK0 : 2 ≤ K := le_trans (by decide : 2 ≤ 5^4) (Nat.pow_le_pow_right (by decide) hk)
  have hD : D ≤ K^5 := (cutoff k hk).trans (by simpa using Nat.pow_le_pow_right (by omega : 0<K) (by decide : 1 ≤ 5))
  have hDpow : 15625*K^6 ≤ 2^D := by
    rw [← hscale,← pow_succ']; dsimp [D]; rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) _
  have H := cell_bound hh (mem_Ico.mp hu).1 (by simpa using (mem_Ico.mp hu).2)
    hK hK0 hD hDpow (hscale ▸ hT)
  rw [hscale]; change ‖∑ i ∈ range T, character h (u*K^6+i)‖ ≤ _
  apply H.trans
  have coef : 15628+2*((D:ℝ)+1)^2 ≤ 20000*(k:ℝ)^2 := by
    dsimp [D]; push_cast; have hk' : 4 ≤ (k:ℝ) := by exact_mod_cast hk
    nlinarith only [sq_nonneg ((k:ℝ)-1), hk']
  have hKr : (K:ℝ) = (5:ℝ)^k := by simp [K]
  have small : 20000*(k:ℝ)^2 < ε*K := by
    change 20000*((k:ℝ)^2/(5:ℝ)^k) < ε at hεk
    rw [hKr]; rw [← mul_div_assoc,div_lt_iff₀ (by positivity)] at hεk; exact hεk
  have scaleR : (15625:ℝ)^k=(K:ℝ)^6 := by exact_mod_cast hscale
  change _ ≤ ε*(15625:ℝ)^k
  rw [scaleR]
  calc _ ≤ (20000*(k:ℝ)^2)*K^5 := mul_le_mul_of_nonneg_right coef (by positivity)
       _ ≤ (ε*K)*K^5 := mul_le_mul_of_nonneg_right small.le (by positivity)
       _ = _ := by ring

/-- Normality for the literal nested series, without any project-specific constant. -/
theorem series_binary_normal : NormalIn 2 (∑' j : ℕ, ∑' a : ℕ,
    1 / ((2:ℝ)^a*5^j * 2^(2^a*5^j : ℕ))) := value_eq_series ▸ binary_normal

end NormalityChecker.LocalizedFive
