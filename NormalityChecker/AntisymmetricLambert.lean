module

public import NormalityChecker.GeneralMassTransfer
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Antisymmetric periodic Lambert series and `q`-digamma reflection (Tracks B3 and B4)

Kernel-checked arithmetic, analytic, and discrepancy-transfer theorems for odd (antisymmetric)
`M`-periodic Lambert series and the `q`-digamma reflection difference at `q = b^(-M)`:

1. **Exact involution cancellation (`dirichletOneConv_eq_zero_of_odd_padicVal`).**
   For any odd `M`-periodic weight `f : ℕ → ℤ` (meaning `f` depends only on `m % M` and
   `f a + f b = 0` whenever `M ∣ a + b`), let `(1 * f)(n) = ∑_{d ∣ n} f(d)`.
   Whenever `p` is prime with `M ∣ p + 1` (i.e. `p ≡ -1 (mod M)`) and `v_p(n)` is odd,
   the divisor involution `d ↦ p^(v_p(n) - v_p(d)) · (d / p^(v_p(d)))` pairs opposite-sign
   divisors and forces `(1 * f)(n) = 0`.

2. **Logarithmic aggregate mass bound (`absMass_dirichletOneConv_le`).**
   For any bounded `f : ℕ → ℤ` with `|f m| ≤ B`,
   `absMass (dirichletOneConv f) X ≤ 2 * B * X * log (X + 2)`.

3. **Exact Lambert-to-Dirichlet and `q`-digamma reflection identities.**
   For every radix `b ≥ 2`, modulus `M ≥ 2`, and residue `1 ≤ r < M`,
   - `residueLambert_eq_coeffSeries`:
     `A_{r, M}(b) = coeffSeries b (dirichletOneConv (modIndicator M r))`.
   - `residueLambert_sub_eq_coeffSeries`:
     `A_{r, M}(b) - A_{M - r, M}(b) = coeffSeries b (dirichletOneConv (antiIndicator M r))`.
   - `qDigamma_reflection_eq_dirichletSeries`:
     `(ψ_q(r/M) - ψ_q(1 - r/M)) / log q = coeffSeries b (dirichletOneConv (antiIndicator M r))`
     at `q = b^(-M)`.

4. **Logarithmic-mass discrepancy transfer (`oddPeriodic_dirichlet_tendsto_one_of_sparse`,
   `qDigamma_reflection_tendsto_one_of_sparse`).**
   Combines `absMass_dirichletOneConv_le` with `GeneralMassTransfer.log_mass_sparse_tendsto_one`:
   once the analytic support bound `S(N) * log(log(N + 3)) / N → 0` is supplied (which follows on
   paper from `dirichletOneConv_eq_zero_of_odd_padicVal` and Landau/Wirsing/Halberstam–Richert
   for primes `p ≡ -1 (mod M)`), both `A_{r, M}(b) - A_{M - r, M}(b)` and the `q`-digamma
   reflection difference lie in `K_b` and preserve discrepancy for every `b ≥ 2`.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace NormalityChecker.AntisymmetricLambert

open CoefficientTransfer GeneralMassTransfer SharpTranslation

/-! ### Part 1: Odd `M`-periodic weights and exact divisor-involution cancellation -/

/-- A function `f : ℕ → ℤ` is odd `M`-periodic if it depends only on the residue modulo `M`
and satisfies `f a + f b = 0` whenever `M ∣ a + b`. -/
def IsOddPeriodic (M : ℕ) (f : ℕ → ℤ) : Prop :=
  (∀ a b, a % M = b % M → f a = f b) ∧ (∀ a b, (a + b) % M = 0 → f a + f b = 0)

/-- Indicator of residue class `r` modulo `M`. -/
def modIndicator (M r : ℕ) (m : ℕ) : ℤ :=
  if m % M = r then 1 else 0

/-- Antisymmetric residue-class indicator `1_{m ≡ r (mod M)} - 1_{m ≡ M - r (mod M)}`. -/
def antiIndicator (M r : ℕ) (m : ℕ) : ℤ :=
  modIndicator M r m - modIndicator M (M - r) m

theorem isOddPeriodic_antiIndicator {M r : ℕ} (hr1 : 1 ≤ r) (hrM : r < M) :
    IsOddPeriodic M (antiIndicator M r) := by
  refine ⟨fun a b hab => by simp [antiIndicator, modIndicator, hab], fun a b hab => ?_⟩
  have hmod : (a % M + b % M) % M = 0 := by rwa [Nat.add_mod] at hab
  have haM : a % M < M := Nat.mod_lt a (by omega)
  have hbM : b % M < M := Nat.mod_lt b (by omega)
  have hsum : a % M + b % M = 0 ∨ a % M + b % M = M := by
    have hlt : a % M + b % M < 2 * M := by omega
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hq2 : q < 2 := by nlinarith
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · left; omega
    · have hq1 : q = 1 := by omega
      subst hq1; right; omega
  unfold antiIndicator modIndicator
  rcases hsum with h0 | hM'
  · have ha0 : a % M = 0 := by omega
    have hb0 : b % M = 0 := by omega
    simp [ha0, hb0, show (0 : ℕ) ≠ r by omega, show (0 : ℕ) ≠ M - r by omega]
  · by_cases har : a % M = r <;> by_cases hamr : a % M = M - r <;>
      by_cases hbr : b % M = r <;> by_cases hbmr : b % M = M - r <;>
      simp [har, hamr, hbr, hbmr] <;> omega

/-- Dirichlet convolution `(1 * f)(n) = ∑_{d ∣ n} f(d)`. -/
def dirichletOneConv (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, f d

theorem dirichletOneConv_sub (f g : ℕ → ℤ) (n : ℕ) :
    dirichletOneConv (fun m => f m - g m) n = dirichletOneConv f n - dirichletOneConv g n := by
  simp [dirichletOneConv, Finset.sum_sub_distrib]

/-- **Exact involution cancellation for odd periodic Dirichlet convolutions (Track B3).**
If `f` is odd `M`-periodic, `p` is prime with `M ∣ p + 1`, `n ≠ 0`, and `v_p(n)` is odd,
then `(1 * f)(n) = 0`. -/
theorem dirichletOneConv_eq_zero_of_odd_padicVal {M p n : ℕ} {f : ℕ → ℤ}
    (hf : IsOddPeriodic M f) (hp : p.Prime) (hpM : M ∣ p + 1) (hn : n ≠ 0)
    (hodd : Odd (n.factorization p)) :
    dirichletOneConv f n = 0 := by
  set a : ℕ := n.factorization p
  set u : ℕ := n / p ^ a
  have hpa_dvd : p ^ a ∣ n := Nat.ordProj_dvd n p
  have hn_eq : p ^ a * u = n := Nat.mul_div_cancel' hpa_dvd
  have hu_ne : u ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hn_eq; exact hn hn_eq.symm
  let τ : ℕ → ℕ := fun d => p ^ (a - d.factorization p) * (d / p ^ (d.factorization p))
  -- Core properties of `τ` on `n.divisors`.
  have hτ_props : ∀ d ∈ n.divisors,
      τ d ∈ n.divisors ∧ τ (τ d) = d ∧ f d + f (τ d) = 0 := by
    intro d hd
    obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hd
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hdn
    set j : ℕ := d.factorization p
    set e : ℕ := d / p ^ j
    have hpj_dvd : p ^ j ∣ d := Nat.ordProj_dvd d p
    have hd_eq : p ^ j * e = d := Nat.mul_div_cancel' hpj_dvd
    have he0 : e ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hd_eq; exact hd0 hd_eq.symm
    have hpe : ¬ p ∣ e := by
      intro hdvd
      have hdvd_d : p ^ (j + 1) ∣ d := by
        rw [← hd_eq, pow_succ]
        exact mul_dvd_mul_left (p ^ j) hdvd
      have hle := (hp.pow_dvd_iff_le_factorization hd0).mp hdvd_d
      omega
    have hja : j ≤ a := (Nat.factorization_le_iff_dvd hd0 hn).mpr hdn p
    have he_dvd_u : e ∣ u := by
      have h1 : p ^ j * e ∣ p ^ a * u := by rw [hd_eq, hn_eq]; exact hdn
      have hpa_split : p ^ a = p ^ j * p ^ (a - j) := by
        rw [← pow_add, Nat.add_sub_of_le hja]
      rw [hpa_split, mul_assoc] at h1
      have h2 : e ∣ p ^ (a - j) * u := (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos j)).mp h1
      have hcop : Nat.Coprime e (p ^ (a - j)) :=
        (hp.coprime_iff_not_dvd.mpr hpe).symm.pow_right (a - j)
      exact hcop.dvd_of_dvd_mul_left h2
    have hτ_dvd : τ d ∣ n := by
      change p ^ (a - j) * e ∣ n
      rw [← hn_eq]
      exact mul_dvd_mul (pow_dvd_pow p (Nat.sub_le a j)) he_dvd_u
    have hτ_mem : τ d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hτ_dvd, hn⟩
    have hτ_fac : (τ d).factorization p = a - j := by
      change (p ^ (a - j) * e).factorization p = a - j
      rw [Nat.factorization_mul (pow_pos hp.pos _).ne' he0, Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hpe, add_zero]
    have hτ_inv : τ (τ d) = d := by
      have hdiv : τ d / p ^ (a - j) = e := by
        change (p ^ (a - j) * e) / p ^ (a - j) = e
        exact Nat.mul_div_cancel_left e (pow_pos hp.pos _)
      change p ^ (a - (τ d).factorization p) * (τ d / p ^ (τ d).factorization p) = d
      rw [hτ_fac, hdiv, Nat.sub_sub_self hja, hd_eq]
    have hsum_dvd : M ∣ d + τ d := by
      have hfac_sum : d + τ d = (p ^ j + p ^ (a - j)) * e := by
        change d + p ^ (a - j) * e = (p ^ j + p ^ (a - j)) * e
        rw [← hd_eq, add_mul]
      rw [hfac_sum]
      refine dvd_mul_of_dvd_left ?_ e
      have hne_j : j ≠ a - j := by
        rcases hodd with ⟨m, hm⟩
        omega
      rcases lt_or_gt_of_ne hne_j with hlt | hgt
      · set k : ℕ := a - j - j
        have hk_odd : Odd k := by
          rcases hodd with ⟨m, hm⟩
          exact ⟨m - j, by omega⟩
        have hsplit : p ^ j + p ^ (a - j) = p ^ j * (p ^ k + 1 ^ k) := by
          rw [one_pow, mul_add, mul_one, ← pow_add, show j + k = a - j by omega, add_comm]
        rw [hsplit]
        exact dvd_mul_of_dvd_right (hpM.trans (hk_odd.nat_add_dvd_pow_add_pow p 1)) _
      · set k : ℕ := j - (a - j)
        have hk_odd : Odd k := by
          rcases hodd with ⟨m, hm⟩
          exact ⟨j - m - 1, by omega⟩
        have hsplit : p ^ j + p ^ (a - j) = p ^ (a - j) * (p ^ k + 1 ^ k) := by
          rw [one_pow, mul_add, mul_one, ← pow_add, show (a - j) + k = j by omega]
        rw [hsplit]
        exact dvd_mul_of_dvd_right (hpM.trans (hk_odd.nat_add_dvd_pow_add_pow p 1)) _
    have hf_cancel : f d + f (τ d) = 0 := hf.2 d (τ d) (Nat.mod_eq_zero_of_dvd hsum_dvd)
    exact ⟨hτ_mem, hτ_inv, hf_cancel⟩
  -- Sum over `n.divisors` equals its image under `τ`, so `2 * sum = 0`.
  have hsum_eq : ∑ d ∈ n.divisors, f (τ d) = ∑ d ∈ n.divisors, f d := by
    refine Finset.sum_nbij' τ τ ?_ ?_ ?_ ?_ ?_
    · exact fun d hd => (hτ_props d hd).1
    · exact fun d hd => (hτ_props d hd).1
    · exact fun d hd => (hτ_props d hd).2.1
    · exact fun d hd => (hτ_props d hd).2.1
    · exact fun _ _ => rfl
  have htwice : (∑ d ∈ n.divisors, f d) + (∑ d ∈ n.divisors, f d) = 0 := by
    conv_lhs => arg 2; rw [← hsum_eq]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_const_zero (s := n.divisors)]
    exact Finset.sum_congr rfl (fun d hd => (hτ_props d hd).2.2)
  unfold dirichletOneConv
  omega

/-! ### Part 2: Elementary logarithmic aggregate mass bound `A(X) ≤ 2 B X log(X + 2)` -/

/-- Exact divisor-counting identity `∑_{n=1}^X τ(n) = ∑_{d=1}^X ⌊X / d⌋`. -/
theorem sum_card_divisors_eq (X : ℕ) :
    ∑ n ∈ Icc 1 X, n.divisors.card = ∑ d ∈ Icc 1 X, X / d := by
  have hL : ∑ n ∈ Icc 1 X, n.divisors.card =
      ((Icc 1 X).sigma (fun n => n.divisors)).card := by
    rw [Finset.card_sigma]
  have hR : ∑ d ∈ Icc 1 X, X / d =
      ((Icc 1 X).sigma (fun d => Icc 1 (X / d))).card := by
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Nat.card_Icc]; exact (Nat.add_sub_cancel (X / d) 1).symm
  rw [hL, hR]
  refine Finset.card_bij (fun p _ => (⟨p.2, p.1 / p.2⟩ : (d : ℕ) × ℕ)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := mem_sigma.mp hp
    obtain ⟨hn1, hnX⟩ := mem_Icc.mp hp1
    obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hp2
    have hd1 : 1 ≤ p.2 := Nat.pos_of_dvd_of_pos hdn (by omega)
    have hdX : p.2 ≤ X := (Nat.le_of_dvd (by omega) hdn).trans hnX
    have hq1 : 1 ≤ p.1 / p.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd1
    have hqX : p.1 / p.2 ≤ X / p.2 := Nat.div_le_div_right hnX
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hd1, hdX⟩, mem_Icc.mpr ⟨hq1, hqX⟩⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    obtain ⟨_, hp₁2⟩ := mem_sigma.mp hp₁
    obtain ⟨_, hp₂2⟩ := mem_sigma.mp hp₂
    obtain ⟨hd₁, _⟩ := Nat.mem_divisors.mp hp₁2
    obtain ⟨hd₂, _⟩ := Nat.mem_divisors.mp hp₂2
    have hf : p₁.2 = p₂.2 := congrArg Sigma.fst heq
    have hs : p₁.1 / p₁.2 = p₂.1 / p₂.2 := by
      have := congrArg Sigma.snd heq
      simpa using this
    have h1 : p₁.1 = p₂.1 := by
      have e1 := Nat.div_mul_cancel hd₁
      have e2 := Nat.div_mul_cancel hd₂
      rw [← e1, ← e2, hs, hf]
    exact Sigma.ext h1 (by simp [hf])
  · intro q hq
    obtain ⟨hq1, hq2⟩ := mem_sigma.mp hq
    obtain ⟨hd1, hdX⟩ := mem_Icc.mp hq1
    obtain ⟨hk1, hkX⟩ := mem_Icc.mp hq2
    refine ⟨⟨q.1 * q.2, q.1⟩, ?_, ?_⟩
    · have hprod1 : 1 ≤ q.1 * q.2 := Nat.mul_pos hd1 hk1
      have hprodX : q.1 * q.2 ≤ X := (Nat.mul_le_mul_left q.1 hkX).trans (Nat.mul_div_le X q.1)
      refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨hprod1, hprodX⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right q.1 q.2, (Nat.mul_pos hd1 hk1).ne'⟩⟩
    · exact Sigma.ext rfl (by simp [Nat.mul_div_cancel_left q.2 hd1])

/-- Elementary harmonic bound: `∑_{d=1}^X 1/d ≤ 1 + log X` for `X ≥ 1`. -/
theorem harmonic_sum_le_one_add_log {X : ℕ} (hX : 1 ≤ X) :
    ∑ d ∈ Icc 1 X, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (X : ℝ) := by
  induction X, hX using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hsplit : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk_pos hk1_pos)
      rw [Real.log_div hk_pos.ne' hk1_pos.ne'] at hlog
      have hrew : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp [hk1_pos.ne']; ring
      linarith
    linarith

/-- **Logarithmic aggregate mass bound for bounded Dirichlet convolutions (Tracks B3–B4).**
If `|f(m)| ≤ B` for all `m`, then `absMass (dirichletOneConv f) X ≤ 2 * B * X * log(X + 2)`. -/
theorem absMass_dirichletOneConv_le {f : ℕ → ℤ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ m : ℕ, |(f m : ℝ)| ≤ B) (X : ℕ) :
    absMass (dirichletOneConv f) X ≤ 2 * B * (X : ℝ) * Real.log ((X + 2 : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [absMass]
  have hlog3 : (1 : ℝ) ≤ Real.log (3 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogX2 : (1 : ℝ) ≤ Real.log ((X + 2 : ℕ) : ℝ) :=
    hlog3.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ X + 2 by omega)))
  have hlog_mono : Real.log (X : ℝ) ≤ Real.log ((X + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast (show X ≤ X + 2 by omega))
  have htri : absMass (dirichletOneConv f) X ≤ B * ((∑ n ∈ Icc 1 X, n.divisors.card : ℕ) : ℝ) := by
    unfold absMass dirichletOneConv
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun n _ => ?_)
    push_cast
    calc |∑ d ∈ n.divisors, (f d : ℝ)|
        ≤ ∑ d ∈ n.divisors, |(f d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ n.divisors, B := Finset.sum_le_sum (fun d _ => hf d)
      _ = B * (n.divisors.card : ℝ) := by simp [mul_comm]
  have hdiv_sum : ((∑ n ∈ Icc 1 X, n.divisors.card : ℕ) : ℝ) ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) := by
    rw [sum_card_divisors_eq, Nat.cast_sum]
    calc ∑ d ∈ Icc 1 X, ((X / d : ℕ) : ℝ)
        ≤ ∑ d ∈ Icc 1 X, (X : ℝ) * ((1 : ℝ) / (d : ℝ)) := by
          refine Finset.sum_le_sum (fun d hd => ?_)
          have hd_pos : (0 : ℝ) < (d : ℝ) := by
            exact_mod_cast (show 0 < d by have := (mem_Icc.mp hd).1; omega)
          rw [mul_one_div, le_div_iff₀ hd_pos]
          exact_mod_cast Nat.div_mul_le_self X d
      _ = (X : ℝ) * ∑ d ∈ Icc 1 X, (1 : ℝ) / (d : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (X : ℝ) * (1 + Real.log (X : ℝ)) :=
          mul_le_mul_of_nonneg_left (harmonic_sum_le_one_add_log hX) (Nat.cast_nonneg X)
  calc absMass (dirichletOneConv f) X
      ≤ B * ((∑ n ∈ Icc 1 X, n.divisors.card : ℕ) : ℝ) := htri
    _ ≤ B * ((X : ℝ) * (1 + Real.log (X : ℝ))) := mul_le_mul_of_nonneg_left hdiv_sum hB
    _ ≤ B * ((X : ℝ) * (2 * Real.log ((X + 2 : ℕ) : ℝ))) := by
        have h1 : 1 + Real.log (X : ℝ) ≤ 2 * Real.log ((X + 2 : ℕ) : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg X)) hB
    _ = 2 * B * (X : ℝ) * Real.log ((X + 2 : ℕ) : ℝ) := by ring

/-! ### Part 3: Exact Lambert-to-Dirichlet and `q`-digamma reflection identities -/

/-- Exact Lambert-to-Dirichlet expansion of a residue-class Lambert sum:
`∑' k, 1 / (b^(k*M + r) - 1) = ∑' n, (#{d ∣ n : d % M = r}) / b^n`. -/
theorem residueLambert_eq_coeffSeries {b M r : ℕ} (hb : 2 ≤ b) (hr1 : 1 ≤ r) (hrM : r < M) :
    residueLambert b M r = coeffSeries b (dirichletOneConv (modIndicator M r)) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < b := by positivity
  -- First rewrite each Lambert term as a geometric series in `b^(-(j + 1) * (k*M + r))`.
  have hterm : ∀ k : ℕ,
      (1 : ℝ) / ((b : ℝ) ^ (k * M + r) - 1) =
        ∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ ((j + 1) * (k * M + r)) := by
    intro k
    set m : ℕ := k * M + r
    have hm1 : 1 ≤ m := by omega
    have hbm1 : (1 : ℝ) < (b : ℝ) ^ m := one_lt_pow₀ hb1 (by omega)
    have hinv_lt : ((b : ℝ) ^ m)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hbm1
    have hts : ∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ ((j + 1) * m) =
        ((b : ℝ) ^ m)⁻¹ * ∑' j : ℕ, (((b : ℝ) ^ m)⁻¹) ^ j := by
      rw [← tsum_mul_left]
      congr 1; ext j
      rw [add_mul, one_mul, pow_add, pow_mul, inv_pow]
      ring
    rw [hts, tsum_geometric_of_lt_one (by positivity) hinv_lt]
    have hbm_ne : (b : ℝ) ^ m ≠ 0 := by positivity
    have hsub_ne : (b : ℝ) ^ m - 1 ≠ 0 := by linarith
    field_simp [hbm_ne, hsub_ne]
  -- Define the nonnegative function on `ℕ × ℕ` and its summability via the divisor series.
  let g : ℕ × ℕ → ℝ := fun p => (1 : ℝ) / (b : ℝ) ^ ((p.2 + 1) * (p.1 * M + r))
  let φ : ℕ × ℕ → ℕ := fun p => (p.2 + 1) * (p.1 * M + r)
  -- For each `n`, the fiber `{p : φ p = n}` has cardinality `dirichletOneConv (modIndicator M r) n`.
  have hfiber_fin : ∀ n : ℕ,
      ∃ s : Finset (ℕ × ℕ), (∀ p, p ∈ s ↔ φ p = n) ∧
        (s.card : ℤ) = dirichletOneConv (modIndicator M r) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨∅, fun p => ?_, by simp [dirichletOneConv]⟩
      simp only [Finset.notMem_empty, false_iff, φ]
      exact (Nat.mul_pos (Nat.succ_pos _) (by omega)).ne'
    · let divs := n.divisors.filter (fun d => d % M = r)
      let s := divs.image (fun d => (d / M, n / d - 1))
      refine ⟨s, fun p => ?_, ?_⟩
      · constructor
        · intro hp
          obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
          obtain ⟨hd_div, hd_mod⟩ := mem_filter.mp hd
          obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hd_div
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
          have hq_pos : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd_pos
          have hd_eq : (d / M) * M + r = d := by
            rw [← hd_mod, mul_comm]; exact Nat.div_add_mod d M
          simp only [φ, Nat.sub_add_cancel hq_pos, hd_eq]
          exact Nat.div_mul_cancel hdn
        · intro hφ
          set d : ℕ := p.1 * M + r
          have hd_pos : 0 < d := by omega
          have hdn : d ∣ n := ⟨p.2 + 1, by rw [← hφ, mul_comm]⟩
          have hd_mod : d % M = r := by
            simp only [d, Nat.mul_add_mod_self_right]
            exact Nat.mod_eq_of_lt hrM
          have hd_div_M : d / M = p.1 := by
            simp only [d]
            have hM_pos : 0 < M := by omega
            rw [mul_comm p.1 M, Nat.mul_add_div hM_pos, Nat.div_eq_of_lt hrM, add_zero]
          have hn_div_d : n / d = p.2 + 1 := by
            rw [← hφ]; exact Nat.mul_div_cancel (p.2 + 1) hd_pos
          refine mem_image.mpr ⟨d, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdn, hn.ne'⟩, hd_mod⟩, ?_⟩
          ext
          · exact hd_div_M
          · simp [hn_div_d]
      · have hinj : Set.InjOn (fun d : ℕ => (d / M, n / d - 1)) (divs : Set ℕ) := by
          intro d₁ hd₁ d₂ hd₂ heq
          have hm₁ : d₁ % M = r := (mem_filter.mp hd₁).2
          have hm₂ : d₂ % M = r := (mem_filter.mp hd₂).2
          have hq : d₁ / M = d₂ / M := congrArg Prod.fst heq
          have e1 := Nat.div_add_mod d₁ M
          have e2 := Nat.div_add_mod d₂ M
          rw [hq, hm₁] at e1
          rw [hm₂] at e2
          omega
        rw [Finset.card_image_of_injOn hinj]
        unfold dirichletOneConv modIndicator
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Summability of the target Dirichlet series via `absMass_dirichletOneConv_le`.
  have hbound : ∀ m : ℕ, |(modIndicator M r m : ℝ)| ≤ 1 := by
    intro m; unfold modIndicator; split_ifs <;> norm_num
  have hsum_dir_abs : Summable (fun n : ℕ => |(dirichletOneConv (modIndicator M r) n : ℝ)| / (b : ℝ) ^ n) :=
    summable_abs_of_log_mass hb (C := 2) (by norm_num) 1 (fun X => by
      have h := absMass_dirichletOneConv_le (B := 1) zero_le_one hbound X
      simpa [pow_one] using h)
  -- Fiberwise sum of `g` equals the Dirichlet series.
  have hfiber_sum : ∀ n : ℕ,
      HasSum (fun p : {p : ℕ × ℕ // φ p = n} => g p.1)
        ((dirichletOneConv (modIndicator M r) n : ℝ) / (b : ℝ) ^ n) := by
    intro n
    obtain ⟨s, hs_iff, hs_card⟩ := hfiber_fin n
    have hconst : ∀ p : {p : ℕ × ℕ // φ p = n}, g p.1 = (1 : ℝ) / (b : ℝ) ^ n := by
      intro p; simp only [g, ← p.2, φ]
    have hsub : {p : ℕ × ℕ // φ p = n} ≃ {p : ℕ × ℕ // p ∈ s} :=
      Equiv.subtypeEquivRight (fun p => (hs_iff p).symm)
    let _ : Fintype {p : ℕ × ℕ // φ p = n} := Fintype.ofEquiv _ hsub.symm
    have hcard : Fintype.card {p : ℕ × ℕ // φ p = n} = s.card := by
      rw [Fintype.card_congr hsub, Fintype.card_coe]
    have hval : ∑ p : {p : ℕ × ℕ // φ p = n}, g p.1 =
        (dirichletOneConv (modIndicator M r) n : ℝ) / (b : ℝ) ^ n := by
      calc ∑ p : {p : ℕ × ℕ // φ p = n}, g p.1
          = ∑ _p : {p : ℕ × ℕ // φ p = n}, (1 : ℝ) / (b : ℝ) ^ n :=
            Finset.sum_congr rfl (fun p _ => hconst p)
        _ = (s.card : ℝ) * ((1 : ℝ) / (b : ℝ) ^ n) := by simp [hcard]
        _ = (dirichletOneConv (modIndicator M r) n : ℝ) / (b : ℝ) ^ n := by
            have : (s.card : ℝ) = (dirichletOneConv (modIndicator M r) n : ℝ) := by exact_mod_cast hs_card
            rw [this, mul_one_div]
    rw [← hval]
    exact hasSum_fintype _
  have hsum_g : Summable g := by
    have hgeom : Summable (fun n : ℕ => ((b : ℝ)⁻¹) ^ n) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)
    have hprod : Summable (fun p : ℕ × ℕ => ((b : ℝ)⁻¹) ^ p.1 * ((b : ℝ)⁻¹) ^ p.2) :=
      hgeom.mul_of_nonneg hgeom (fun _ => by positivity) (fun _ => by positivity)
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hprod
    have hM1 : 1 ≤ M := by omega
    have h1 : p.1 + 1 ≤ p.1 * M + r := by nlinarith
    have hge : p.1 + p.2 ≤ (p.2 + 1) * (p.1 * M + r) := by nlinarith
    simp only [g, one_div, ← inv_pow, ← pow_add]
    exact pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hb1).le hge
  -- Compare the two ways of summing `g`: by `p.1` (giving `residueLambert`) and by `φ p` (giving `coeffSeries`).
  have hL : residueLambert b M r = ∑' p : ℕ × ℕ, g p := by
    unfold residueLambert
    simp_rw [hterm]
    have hrow : ∀ k : ℕ, Summable (fun j : ℕ => g (k, j)) := fun k =>
      hsum_g.comp_injective (fun j₁ j₂ h => congrArg Prod.snd h)
    exact (hsum_g.tsum_prod' hrow).symm
  have hR : ∑' p : ℕ × ℕ, g p = coeffSeries b (dirichletOneConv (modIndicator M r)) := by
    unfold coeffSeries
    have hcomp : Summable (g ∘ Equiv.sigmaFiberEquiv φ) :=
      (Equiv.sigmaFiberEquiv φ).summable_iff.mpr hsum_g
    rw [← (Equiv.sigmaFiberEquiv φ).tsum_eq g]
    change ∑' p : (n : ℕ) × {x : ℕ × ℕ // φ x = n}, (g ∘ Equiv.sigmaFiberEquiv φ) p = _
    rw [hcomp.tsum_sigma' (fun n => (hfiber_sum n).summable)]
    exact tsum_congr (fun n => (hfiber_sum n).tsum_eq)
  exact hL.trans hR

/-- **Exact antisymmetric residue-class Lambert identity (Track B3).**
For every radix `b ≥ 2`, modulus `M ≥ 2`, and `1 ≤ r < M`,
`A_{r, M}(b) - A_{M - r, M}(b) = coeffSeries b (dirichletOneConv (antiIndicator M r))`. -/
theorem residueLambert_sub_eq_coeffSeries {b M r : ℕ} (hb : 2 ≤ b) (hr1 : 1 ≤ r) (hrM : r < M) :
    residueLambert b M r - residueLambert b M (M - r) =
      coeffSeries b (dirichletOneConv (antiIndicator M r)) := by
  have hb_pos : (0 : ℝ) < b := by positivity
  have h1 := residueLambert_eq_coeffSeries hb hr1 hrM
  have h2 := residueLambert_eq_coeffSeries hb (show 1 ≤ M - r by omega) (show M - r < M by omega)
  have hsum1 : Summable (fun n : ℕ => (dirichletOneConv (modIndicator M r) n : ℝ) / (b : ℝ) ^ n) := by
    refine Summable.of_norm ?_
    have habs := summable_abs_of_log_mass hb (a := dirichletOneConv (modIndicator M r))
      (C := 2) (by norm_num) 1 (fun X => by
        simpa [pow_one] using absMass_dirichletOneConv_le (f := modIndicator M r) (B := 1) zero_le_one
          (fun m => by unfold modIndicator; split_ifs <;> norm_num) X)
    exact habs.congr (fun n => by rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb_pos n)])
  have hsum2 : Summable (fun n : ℕ => (dirichletOneConv (modIndicator M (M - r)) n : ℝ) / (b : ℝ) ^ n) := by
    refine Summable.of_norm ?_
    have habs := summable_abs_of_log_mass hb (a := dirichletOneConv (modIndicator M (M - r)))
      (C := 2) (by norm_num) 1 (fun X => by
        simpa [pow_one] using absMass_dirichletOneConv_le (f := modIndicator M (M - r)) (B := 1) zero_le_one
          (fun m => by unfold modIndicator; split_ifs <;> norm_num) X)
    exact habs.congr (fun n => by rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hb_pos n)])
  rw [h1, h2]
  unfold coeffSeries
  rw [← hsum1.tsum_sub hsum2]
  refine tsum_congr (fun n => ?_)
  have hsub : dirichletOneConv (antiIndicator M r) n =
      dirichletOneConv (modIndicator M r) n - dirichletOneConv (modIndicator M (M - r)) n :=
    dirichletOneConv_sub _ _ n
  rw [hsub]
  push_cast
  ring

/-- **Exact `q`-digamma reflection to Dirichlet series identity (Track B4).**
At `q = b^(-M)`,
`(ψ_q(r/M) - ψ_q(1 - r/M)) / log q = coeffSeries b (dirichletOneConv (antiIndicator M r))`. -/
theorem qDigamma_reflection_eq_dirichletSeries {b M r : ℕ} (hb : 2 ≤ b) (hr1 : 1 ≤ r) (hrM : r < M) :
    let q : ℝ := ((b : ℝ) ^ M)⁻¹
    (qDigamma q ((r : ℝ) / (M : ℝ)) - qDigamma q (1 - (r : ℝ) / (M : ℝ))) / Real.log q =
      coeffSeries b (dirichletOneConv (antiIndicator M r)) := by
  intro q
  have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have harg : (1 : ℝ) - (r : ℝ) / (M : ℝ) = ((M - r : ℕ) : ℝ) / (M : ℝ) := by
    rw [Nat.cast_sub hrM.le]; field_simp [hM_ne]
  rw [harg]
  have h1 := qDigamma_reflection_eq_residueLambert hb (show 2 ≤ M by omega) hr1 hrM
  have h2 := residueLambert_sub_eq_coeffSeries hb hr1 hrM
  exact h1.trans h2

/-! ### Part 4: Discrepancy transfer for odd periodic Lambert series and `q`-digamma reflection -/

/-- **Conditional-on-sparsity `K_b` transfer for bounded Dirichlet convolutions (Track B3).**
If `|f m| ≤ B` for all `m` and `supportCount (dirichletOneConv f) N * log(log(N + 3)) / N → 0`,
then `D_N(coeffSeries b (dirichletOneConv f); b) → 1` for every radix `b ≥ 2`. -/
theorem bounded_dirichletOneConv_tendsto_one_of_sparse {b : ℕ} (hb : 2 ≤ b)
    {f : ℕ → ℤ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ m : ℕ, |(f m : ℝ)| ≤ B)
    (hsparse : Tendsto (fun N : ℕ =>
      (supportCount (dirichletOneConv f) N : ℝ) * Real.log (Real.log ((N + 3 : ℕ) : ℝ)) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => radixDiscrepancy b (coeffSeries b (dirichletOneConv f)) N) atTop (𝓝 1) :=
  log_mass_sparse_tendsto_one hb (C := 2 * B) (by positivity) 1
    (fun X => by simpa [pow_one] using absMass_dirichletOneConv_le hB hf X) hsparse

/-- **`q`-digamma reflection `K_b` transfer (Track B4).**
Given the analytic support bound `S(N) * log(log(N + 3)) / N → 0` for
`dirichletOneConv (antiIndicator M r)` (which vanishes at every `n` with odd `v_p(n)` for
any prime `p ≡ -1 (mod M)` by `dirichletOneConv_eq_zero_of_odd_padicVal`), the normalized
`q`-digamma reflection difference at `q = b^(-M)` has limiting base-`b` discrepancy `1` and
preserves discrepancy under translation. -/
theorem qDigamma_reflection_tendsto_one_of_sparse {b M r : ℕ} (hb : 2 ≤ b) (hr1 : 1 ≤ r) (hrM : r < M)
    (hsparse : Tendsto (fun N : ℕ =>
      (supportCount (dirichletOneConv (antiIndicator M r)) N : ℝ) *
        Real.log (Real.log ((N + 3 : ℕ) : ℝ)) / (N : ℝ))
      atTop (𝓝 0)) :
    let q : ℝ := ((b : ℝ) ^ M)⁻¹
    Tendsto (fun N : ℕ => radixDiscrepancy b
      ((qDigamma q ((r : ℝ) / (M : ℝ)) - qDigamma q (1 - (r : ℝ) / (M : ℝ))) / Real.log q) N)
      atTop (𝓝 1) := by
  intro q
  have heq : (qDigamma q ((r : ℝ) / (M : ℝ)) - qDigamma q (1 - (r : ℝ) / (M : ℝ))) / Real.log q =
      coeffSeries b (dirichletOneConv (antiIndicator M r)) :=
    qDigamma_reflection_eq_dirichletSeries hb hr1 hrM
  rw [heq]
  refine bounded_dirichletOneConv_tendsto_one_of_sparse hb (B := 2) (by norm_num) (fun m => ?_) hsparse
  unfold antiIndicator modIndicator
  split_ifs <;> norm_num

end NormalityChecker.AntisymmetricLambert
