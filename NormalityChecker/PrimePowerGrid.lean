module

public import NormalityChecker.SurvivingGrid

/-! Interval counts on uniform grids and on prime-power Stoneham periods.

A rotated grid of `G` equally spaced circle points meets every interval in `G` times its
length up to one point. A full prime-power period of the sample `bⁿ a' / p^(e+g)` splits into
`t` rotated grids of `p^g` points, where `e` is the exact `p`-adic valuation of `b^t - 1`.
The arithmetic input is `SurvivingGrid.stride_order` with trivial complementary modulus. -/

public section

open Finset

namespace NormalityChecker.PrimePowerGrid

/-- A window sum of a `G`-periodic function over `G` consecutive integers is independent of the
starting point. -/
private lemma window_sum {G : ℕ} (F : ℤ → ℕ) (hF : ∀ x, F (x + G) = F x) (k : ℤ) :
    ∑ j ∈ range G, F (k + j) = ∑ j ∈ range G, F j := by
  have step (x : ℤ) : ∑ j ∈ range G, F (x + 1 + j) = ∑ j ∈ range G, F (x + j) := by
    have h1 := sum_range_succ (fun j : ℕ => F (x + j)) G
    have h2 := sum_range_succ' (fun j : ℕ => F (x + j)) G
    have h3 : F (x + ((0 : ℕ) : ℤ)) = F (x + (G : ℤ)) := by simp [hF x]
    have h4 : ∑ j ∈ range G, F (x + ((j + 1 : ℕ) : ℤ)) = ∑ j ∈ range G, F (x + 1 + j) :=
      sum_congr rfl fun j _ => by congr 1; push_cast; ring
    omega
  have hS (k : ℤ) : ∑ j ∈ range G, F (k + j) = ∑ j ∈ range G, F (0 + j) := by
    induction k using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [step, ih]
    | pred i ih => rw [← ih, ← step (-(i : ℤ) - 1)]; simp
  simpa using hS k

/-- **Rotated grid count.** For any rotation `s`, the number of the `G` points
`fract (s + j / G)` in `[a, c)` differs from `G (c - a)` by at most one. -/
theorem grid_count (s : ℝ) {G : ℕ} (hG : 0 < G) {a c : ℝ}
    (ha : 0 ≤ a) (hac : a < c) (hc : c ≤ 1) :
    |((((Finset.range G).filter fun j : ℕ =>
        a ≤ Int.fract (s + j / G) ∧ Int.fract (s + j / G) < c).card : ℕ) : ℝ) -
      G * (c - a)| ≤ 1 := by
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  set k : ℤ := ⌊(G : ℝ) * s⌋ with hk
  set s0 : ℝ := s - k / G with hs0
  have hGs0 : (G : ℝ) * s0 = Int.fract ((G : ℝ) * s) := by
    rw [hs0, Int.fract, ← hk]; field_simp
  have hs0nn : 0 ≤ s0 := by
    have := Int.fract_nonneg ((G : ℝ) * s); nlinarith
  have hs0lt : (G : ℝ) * s0 < 1 := hGs0 ▸ Int.fract_lt_one _
  let F : ℤ → ℕ := fun x =>
    if a ≤ Int.fract (s0 + x / G) ∧ Int.fract (s0 + x / G) < c then 1 else 0
  have hF (x : ℤ) : F (x + G) = F x := by
    have e : s0 + ((x + G : ℤ) : ℝ) / G = s0 + x / G + ((1 : ℤ) : ℝ) := by
      push_cast; field_simp; ring
    simp only [F, e, Int.fract_add_intCast]
  set α : ℝ := G * (a - s0) with hα
  set β : ℝ := G * (c - s0) with hβ
  have hαβ : α ≤ β := by rw [hα, hβ]; nlinarith
  have hα1 : -1 < α := by rw [hα]; nlinarith
  have hβG : β ≤ G := by rw [hβ]; nlinarith
  have hcount : ((range G).filter fun j : ℕ =>
      a ≤ Int.fract (s + j / G) ∧ Int.fract (s + j / G) < c).card = ⌈β⌉₊ - ⌈α⌉₊ := by
    rw [card_filter]
    have e1 : ∑ j ∈ range G,
        (if a ≤ Int.fract (s + (j : ℝ) / G) ∧ Int.fract (s + (j : ℝ) / G) < c then 1 else 0) =
        ∑ j ∈ range G, F (k + j) := by
      refine sum_congr rfl fun j _ => ?_
      have e : s + (j : ℝ) / G = s0 + ((k + (j : ℤ) : ℤ) : ℝ) / G := by
        rw [hs0]; push_cast; field_simp; ring
      simp only [F, e]
    rw [e1, window_sum F hF k, ← Nat.card_Ico, ← inter_eq_right.mpr (?_ : Ico ⌈α⌉₊ ⌈β⌉₊ ⊆ range G),
      ← filter_mem_eq_inter, card_filter]
    · refine sum_congr rfl fun j hj => ?_
      have hjG : (j : ℝ) + 1 ≤ G := by exact_mod_cast mem_range.mp hj
      have hfr : Int.fract (s0 + ((j : ℤ) : ℝ) / G) = s0 + j / G := by
        push_cast
        rw [Int.fract_eq_self]
        have e : s0 + (j : ℝ) / G = (G * s0 + j) / G := by field_simp
        rw [e, div_lt_one hGpos]
        exact ⟨by positivity, by linarith⟩
      simp only [F, hfr]
      refine if_congr ?_ rfl rfl
      rw [mem_Ico, Nat.ceil_le, Nat.lt_ceil, hα, hβ]
      have e : (G : ℝ) * (s0 + j / G) = G * s0 + j := by field_simp
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
      · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    · intro j hj
      rw [mem_Ico] at hj
      rw [mem_range]
      have := Nat.ceil_le.mpr hβG
      omega
  rw [hcount, Nat.cast_sub (Nat.ceil_mono hαβ)]
  have h1 := Nat.le_ceil α
  have h2 := Nat.ceil_lt_add_one_of_gt_neg_one hα1
  have h3 := Nat.le_ceil β
  have h4 := Nat.ceil_lt_add_one_of_gt_neg_one (hα1.trans_le hαβ)
  have e : (G : ℝ) * (c - a) = β - α := by rw [hα, hβ]; ring
  rw [e, abs_le]
  constructor <;> linarith

/-- Splitting a range of length `t K` into the `t` residue classes modulo `t`. -/
private lemma card_range_mul (P : ℕ → Prop) [DecidablePred P] (t K : ℕ) :
    ((range (t * K)).filter P).card =
      ∑ r ∈ range t, ((range K).filter fun k => P (r + t * k)).card := by
  simp only [card_filter]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, sum_range_add, ih, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_range_succ, add_comm (t * K) r]

/-- Filtering through a self-map of `range G` which is injective there preserves the count. -/
private lemma card_filter_comp {G : ℕ} (f : ℕ → ℕ) (hmap : ∀ k < G, f k < G)
    (hinj : ∀ k₁ < G, ∀ k₂ < G, f k₁ = f k₂ → k₁ = k₂) (Q : ℕ → Prop) [DecidablePred Q] :
    ((range G).filter fun k => Q (f k)).card = ((range G).filter Q).card := by
  have hinj' : Set.InjOn f (range G) := fun x hx y hy hxy =>
    hinj x (mem_range.mp hx) y (mem_range.mp hy) hxy
  have himg : (range G).image f = range G := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact mem_range.mpr (hmap x (mem_range.mp hx))
    · rw [card_image_of_injOn hinj']
  conv_rhs => rw [← himg]
  rw [filter_image, card_image_of_injOn (hinj'.mono (filter_subset _ _))]

/-- Shared arithmetic of the prime-power period: exact valuation, the lower power and the
order of `b^t` modulo `p^(e+g)`. -/
private lemma period_facts {b p t : ℕ} (hp : p.Prime) (hodd : Odd p) (hb : 2 ≤ b)
    (ht : 0 < t) (hdvd : p ∣ b ^ t - 1) (g : ℕ) :
    1 < b ^ t ∧ 1 ≤ padicValNat p (b ^ t - 1) ∧
      p ^ padicValNat p (b ^ t - 1) ∣ b ^ t - 1 ∧
      orderOf ((b ^ t : ℕ) : ZMod (p ^ (padicValNat p (b ^ t - 1) + g))) = p ^ g ∧
      p ^ (padicValNat p (b ^ t - 1) + g) ∣ (b ^ t) ^ (p ^ g) - 1 := by
  have hh1 : 1 < b ^ t := Nat.one_lt_pow ht.ne' (by omega)
  have hne : b ^ t - 1 ≠ 0 := by omega
  have hfac : (b ^ t - 1).factorization p = padicValNat p (b ^ t - 1) := by
    rw [Nat.factorization_def _ hp, Nat.padicValNat_def]
  have hc : p.Coprime 1 := Nat.coprime_one_right p
  have hord := NormalityChecker.SurvivingGrid.stride_order hp hodd hc hh1 hdvd (one_dvd _)
    (padicValNat p (b ^ t - 1) + g)
  rw [hfac, Nat.add_sub_cancel_left, mul_one] at hord
  have hret := (NormalityChecker.SurvivingGrid.return_iff hp hodd hc hh1 hdvd (one_dvd _)
    (padicValNat p (b ^ t - 1) + g) (p ^ g)).mpr (by rw [hfac, Nat.add_sub_cancel_left])
  rw [mul_one] at hret
  refine ⟨hh1, ?_, ?_, hord, hret⟩
  · rw [← hfac]
    exact (hp.pow_dvd_iff_le_factorization hne).mp (by simpa using hdvd)
  · exact (hp.pow_dvd_iff_le_factorization hne).mpr hfac.ge

/-- **Periodicity.** The prime-power Stoneham sample repeats after `t p^g` steps, for every
integer numerator. -/
theorem primePower_periodic {b p t : ℕ} (hp : p.Prime) (hodd : Odd p) (hb : 2 ≤ b)
    (hpb : ¬ p ∣ b) (ht : 0 < t) (hdvd : p ∣ b ^ t - 1) (g n : ℕ) (a' : ℤ) :
    Int.fract ((b : ℝ) ^ (n + t * p ^ g) * a' / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) =
      Int.fract ((b : ℝ) ^ n * a' / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) := by
  -- `hpb` is implied by `hdvd` and `ht`; it is kept for a uniform interface.
  have _ := hpb
  obtain ⟨-, -, -, -, hret⟩ := period_facts hp hodd hb ht hdvd g
  set e := padicValNat p (b ^ t - 1)
  obtain ⟨q, hq⟩ := hret
  have hpos : 1 ≤ (b ^ t) ^ (p ^ g) := Nat.one_le_pow _ _ (by positivity)
  have hnat : (b ^ t) ^ (p ^ g) = 1 + p ^ (e + g) * q := by omega
  have key : ((b : ℝ) ^ t) ^ (p ^ g) = 1 + (p : ℝ) ^ (e + g) * q := by exact_mod_cast hnat
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine Int.fract_eq_fract.mpr ⟨b ^ n * a' * q, ?_⟩
  rw [pow_add, pow_mul, key]
  push_cast
  field_simp
  ring

/-- **Prime-power period count.** Over one full period `n < t p^g`, the number of samples
`fract (bⁿ a' / p^(e+g))` in `[a, c)` differs from `t p^g (c - a)` by at most `t`, when `a'`
is a unit modulo `p` and `e` is the exact `p`-adic valuation of `b^t - 1`. -/
theorem primePower_period_count {b p t : ℕ} (hp : p.Prime) (hodd : Odd p) (hb : 2 ≤ b)
    (hpb : ¬ p ∣ b) (ht : 0 < t) (hdvd : p ∣ b ^ t - 1) (a' : ℤ) (ha' : ¬ (p : ℤ) ∣ a')
    (g : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hac : a < c) (hc : c ≤ 1) :
    |((((Finset.range (t * p ^ g)).filter fun n : ℕ =>
        a ≤ Int.fract ((b : ℝ) ^ n * a' / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) ∧
        Int.fract ((b : ℝ) ^ n * a' / (p : ℝ) ^ (padicValNat p (b ^ t - 1) + g)) < c).card :
          ℕ) : ℝ) - ((t * p ^ g : ℕ) : ℝ) * (c - a)| ≤ t := by
  obtain ⟨hh1, he1, hD, hord, -⟩ := period_facts hp hodd hb ht hdvd g
  set e := padicValNat p (b ^ t - 1)
  set h := b ^ t with hh
  set D := p ^ e with hDdef
  set P := p ^ g with hPdef
  set M := p ^ (e + g) with hM
  have hMDP : M = D * P := pow_add _ _ _
  have hD1 : 1 < D := Nat.one_lt_pow (by omega) hp.one_lt
  have hPpos : 0 < P := pow_pos hp.pos g
  have hMpos : 0 < M := pow_pos hp.pos _
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- residues of the powers of `h`
  let i : ℕ → ℕ := fun k => h ^ k % M / D
  have hmodD (k : ℕ) : h ^ k % M % D = 1 := by
    rw [Nat.mod_mod_of_dvd _ (hMDP ▸ dvd_mul_right D P)]
    have h1 : h ≡ 1 [MOD D] := ((Nat.modEq_iff_dvd' hh1.le).mpr hD).symm
    have := h1.pow k
    rw [one_pow] at this
    rw [this, Nat.mod_eq_of_lt hD1]
  have hres (k : ℕ) : h ^ k % M = D * i k + 1 := by
    have := Nat.div_add_mod (h ^ k % M) D
    rw [hmodD] at this
    exact this.symm
  have hiP (k : ℕ) : i k < P := by
    have : h ^ k % M < D * P := hMDP ▸ Nat.mod_lt _ hMpos
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; exact this)
  -- numerators and the induced grid index
  let u : ℕ → ℤ := fun r => (b : ℤ) ^ r * a'
  have hu (r : ℕ) : ¬ (p : ℤ) ∣ u r := by
    intro hd
    rcases hpZ.dvd_or_dvd hd with h1 | h1
    · exact hpb (Int.natCast_dvd_natCast.mp (hpZ.dvd_of_dvd_pow h1))
    · exact ha' h1
  let j : ℕ → ℕ → ℤ := fun r k => u r * (i k : ℤ) % (P : ℤ)
  have hj0 (r k : ℕ) : 0 ≤ j r k := Int.emod_nonneg _ (by omega)
  have hjP (r k : ℕ) : j r k < P := Int.emod_lt_of_pos _ (by omega)
  let f : ℕ → ℕ → ℕ := fun r k => (j r k).toNat
  have hf (r k : ℕ) : ((f r k : ℕ) : ℤ) = j r k := Int.toNat_of_nonneg (hj0 r k)
  have hfP (r k : ℕ) : f r k < P := by have := hf r k; have := hjP r k; omega
  -- the sample along a residue class is a rotated grid point
  have hsample (r k : ℕ) :
      Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) =
        Int.fract ((u r : ℝ) / (p : ℝ) ^ (e + g) + ((f r k : ℕ) : ℝ) / ((P : ℕ) : ℝ)) := by
    obtain ⟨q1, hq1⟩ : ∃ q1 : ℕ, h ^ k = M * q1 + h ^ k % M :=
      ⟨_, (Nat.div_add_mod _ _).symm⟩
    obtain ⟨q2, hq2⟩ : ∃ q2 : ℤ, u r * (i k : ℤ) = (P : ℤ) * q2 + j r k := by
      refine ⟨u r * (i k : ℤ) / (P : ℤ), ?_⟩
      have := Int.mul_ediv_add_emod (u r * (i k : ℤ)) (P : ℤ)
      simp only [j]; linarith
    have E1 : ((b : ℝ) ^ t) ^ k = (M : ℝ) * (q1 : ℝ) + ((h ^ k % M : ℕ) : ℝ) := by
      rw [hh] at hq1
      exact_mod_cast hq1
    have E2 : ((h ^ k % M : ℕ) : ℝ) = (D : ℝ) * (i k : ℝ) + 1 := by exact_mod_cast hres k
    have E3 : (u r : ℝ) * (i k : ℝ) = (P : ℝ) * (q2 : ℝ) + (j r k : ℝ) := by
      exact_mod_cast hq2
    have E4 : ((f r k : ℕ) : ℝ) = (j r k : ℝ) := by exact_mod_cast hf r k
    refine Int.fract_eq_fract.mpr ⟨u r * (q1 : ℤ) + q2, ?_⟩
    have Ej : (j r k : ℝ) = (u r : ℝ) * (i k : ℝ) - (P : ℝ) * (q2 : ℝ) := by linarith
    have hMr : ((p : ℝ) ^ (e + g)) = (D : ℝ) * (P : ℝ) := by
      rw [hDdef, hPdef]; push_cast; ring
    rw [E4, Ej, pow_add, pow_mul, E1, E2, hMr]
    have hM' : (M : ℝ) = (D : ℝ) * (P : ℝ) := by exact_mod_cast hMDP
    rw [hM']
    have hD0 : (D : ℝ) ≠ 0 := by positivity
    have hP0 : (P : ℝ) ≠ 0 := by positivity
    simp only [u]
    push_cast
    field_simp
    ring
  -- injectivity of the grid index on one period
  have hfinj (r : ℕ) : ∀ k₁ < P, ∀ k₂ < P, f r k₁ = f r k₂ → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hjeq : j r k₁ = j r k₂ := by rw [← hf, ← hf, heq]
    have hdvd' : (p : ℤ) ^ g ∣ u r * ((i k₂ : ℤ) - (i k₁ : ℤ)) := by
      have := (Int.ModEq.dvd (show u r * (i k₁ : ℤ) ≡ u r * (i k₂ : ℤ) [ZMOD (P : ℤ)] from hjeq))
      rw [hPdef] at this
      push_cast at this
      rw [mul_sub]; exact this
    have hdi := hpZ.pow_dvd_of_dvd_mul_left g (hu r) hdvd'
    have hi : i k₁ = i k₂ := by
      have h1 := hiP k₁
      have h2 := hiP k₂
      have hlt : |(i k₂ : ℤ) - (i k₁ : ℤ)| < (p : ℤ) ^ g := by
        have : ((P : ℕ) : ℤ) = (p : ℤ) ^ g := by rw [hPdef]; push_cast; rfl
        rw [abs_lt]; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hdi hlt
      omega
    have hmod : h ^ k₁ % M = h ^ k₂ % M := by rw [hres, hres, hi]
    have hz : ((h : ℕ) : ZMod M) ^ k₁ = ((h : ℕ) : ZMod M) ^ k₂ := by
      have := (ZMod.natCast_eq_natCast_iff' (h ^ k₁) (h ^ k₂) M).mpr hmod
      simpa only [Nat.cast_pow] using this
    exact pow_injOn_Iio_orderOf (by simpa [Set.mem_Iio, hord] using hk₁)
      (by simpa [Set.mem_Iio, hord] using hk₂) hz
  -- assemble the residue classes
  have hclass (r : ℕ) :
      |((((range P).filter fun k : ℕ =>
        a ≤ Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) ∧
        Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) < c).card : ℕ) : ℝ) -
        ((P : ℕ) : ℝ) * (c - a)| ≤ 1 := by
    have hcongr : ((range P).filter fun k : ℕ =>
        a ≤ Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) ∧
        Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) < c) =
        (range P).filter fun k : ℕ =>
          (fun x : ℕ => a ≤ Int.fract ((u r : ℝ) / (p : ℝ) ^ (e + g) + (x : ℝ) / ((P : ℕ) : ℝ)) ∧
            Int.fract ((u r : ℝ) / (p : ℝ) ^ (e + g) + (x : ℝ) / ((P : ℕ) : ℝ)) < c) (f r k) :=
      filter_congr fun k _ => by rw [hsample]
    rw [hcongr]
    have key := card_filter_comp (f r) (fun k _ => hfP r k) (hfinj r)
      (fun x : ℕ => a ≤ Int.fract ((u r : ℝ) / (p : ℝ) ^ (e + g) + (x : ℝ) / ((P : ℕ) : ℝ)) ∧
        Int.fract ((u r : ℝ) / (p : ℝ) ^ (e + g) + (x : ℝ) / ((P : ℕ) : ℝ)) < c)
    have hg := grid_count ((u r : ℝ) / (p : ℝ) ^ (e + g)) hPpos ha hac hc
    rw [← key] at hg
    exact hg
  rw [card_range_mul]
  push_cast
  calc |∑ r ∈ range t, ((((range P).filter fun k : ℕ =>
        a ≤ Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) ∧
        Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) < c).card : ℕ) : ℝ) -
        (t : ℝ) * (P : ℝ) * (c - a)|
      = |∑ r ∈ range t, (((((range P).filter fun k : ℕ =>
        a ≤ Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) ∧
        Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) < c).card : ℕ) : ℝ) -
        ((P : ℕ) : ℝ) * (c - a))| := by
        rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]; congr 1; ring
    _ ≤ ∑ r ∈ range t, |(((((range P).filter fun k : ℕ =>
        a ≤ Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) ∧
        Int.fract ((b : ℝ) ^ (r + t * k) * a' / (p : ℝ) ^ (e + g)) < c).card : ℕ) : ℝ) -
        ((P : ℕ) : ℝ) * (c - a))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ range t, (1 : ℝ) := sum_le_sum fun r _ => hclass r
    _ = t := by simp

end NormalityChecker.PrimePowerGrid
