module

public import NormalityChecker.ArithmeticCertificate
public import NormalityChecker.CircleDiscrepancy
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! Finite discrepancy transfer on intervals of unequal lengths. Vandehey's
quantitative orbit estimate and Erdős–Turán are explicit hypotheses. -/
@[expose] public section
open Finset
namespace NormalityChecker.QuantitativeStoneham

/-- The all-length majorant in Vandehey, Theorem 5.1 (preprint numbering). -/
noncomputable def orbitBound (A B α γ ν r : ℝ) (q L : ℕ) : ℝ :=
  (A * (q : ℝ)^α * (L : ℝ)^γ + B * (q : ℝ)^(-α) * (L : ℝ)^ν) *
    (1 + Real.log q)^r

/-- Fixed support consists of the primes dividing `s`, taken coprime to `b`
in the application. Quantification over rationals uses their reduced denominator. -/
def FixedSupportBound (b s : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ (y : ℚ) (L : ℕ), 0 < L → (∃ k, y.den ∣ s^k) →
    ‖∑ i ∈ range L, phase ((b : ℝ)^i*y)‖ ≤ F y.den L

/-- Unnormalized extreme interval discrepancy and positive Fourier frequencies. -/
def ErdosTuran (C : ℝ) : Prop :=
  ∀ (u : ℕ → ℝ) (T H : ℕ), 0 < T → 0 < H →
    T * CircleDiscrepancy.disc u T ≤ C * (T / ((H : ℝ)+1) +
      ∑ h ∈ Icc 1 H, ‖∑ i ∈ range T, phase (h*u i)‖ / h)

/-- Exact loss at a growing frequency. -/
theorem frequency_denominator (y : ℚ) (h : ℕ) :
    y.den = ((h : ℚ)*y).den * h.gcd y.den := by
  simpa [Int.natAbs_mul, Nat.Coprime.gcd_mul_right_cancel _ y.reduced] using
    Rat.den_mul_den_eq_den_mul_gcd (h : ℚ) y

/-- Summing the loss from reducing a Fourier frequency against a denominator.
For fixed prime support and α < 1 the divisor sum is bounded by a finite
product of convergent geometric series, independently of the exponents. -/
theorem harmonic_gcd_bound {Q : ℕ} (pos : 0 < Q) (H : ℕ) (α : ℝ) :
    ∑ h ∈ Icc 1 H, (h.gcd Q : ℝ)^α / h ≤
      (1 + Real.log H) * ∑ r ∈ Q.divisors, (r : ℝ)^(α-1) := by
  classical
  let I := Icc 1 H
  let f (h : ℕ) := (h.gcd Q : ℝ)^α / h
  have divides (h : ℕ) (_ : h ∈ I) : h.gcd Q ∈ Q.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right .., pos.ne'⟩
  change ∑ h ∈ I, f h ≤ _
  rw [← sum_fiberwise_of_maps_to divides f, mul_sum]
  apply sum_le_sum
  intro r hr
  let U := I.filter (fun h => h.gcd Q = r)
  have rp : 0 < r := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hr).1 pos
  have div (h : ℕ) (hh : h ∈ U) : r ∣ h :=
    (mem_filter.mp hh).2 ▸ Nat.gcd_dvd_left h Q
  have inject : Set.InjOn (· / r) (U : Set ℕ) := by
    intro h hh k hk eqn
    simpa [Nat.div_mul_cancel (div _ hh), Nat.div_mul_cancel (div _ hk)] using
      congrArg (· * r) eqn
  have into : U.image (· / r) ⊆ I := by
    intro j hj
    obtain ⟨h, hh, rfl⟩ := mem_image.mp hj
    obtain ⟨lo, hi⟩ := mem_Icc.mp (mem_filter.mp hh).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd lo (div h hh)) rp,
      (Nat.div_le_self ..).trans hi⟩
  have eqn (h : ℕ) (hh : h ∈ U) :
      f h = (r : ℝ)^(α-1) * ((h/r : ℕ) : ℝ)⁻¹ := by
    dsimp [f]
    rw [(mem_filter.mp hh).2, Real.rpow_sub (by positivity), Real.rpow_one]
    have fac : ((h/r : ℕ) : ℝ) * r = h := by exact_mod_cast Nat.div_mul_cancel (div h hh)
    conv_lhs => rw [← fac]
    ring
  apply (sum_le_sum_of_injOn (g:=fun j : ℕ => (r : ℝ)^(α-1) * (j : ℝ)⁻¹) (· / r) inject into (fun h hh => (eqn h hh).le)
    (fun _ _ _ => by positivity)).trans
  rw [← mul_sum, mul_comm (1 + Real.log H)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  simpa [harmonic_eq_sum_Icc, I] using harmonic_le_one_add_log H

/-- The two terms in Vandehey's majorant after harmonic averaging, with the
frequency gone from the right-hand side and the actual divisor sum preserved. -/
theorem harmonic_orbit_bound (y : ℚ) (H L : ℕ) {A B α γ ν r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ α) (hr : 0 ≤ r) :
    ∑ h ∈ Icc 1 H, orbitBound A B α γ ν r ((h : ℚ)*y).den L / h ≤
      (1 + Real.log y.den)^r * (1 + Real.log H) *
        (A * (y.den : ℝ)^α * (L : ℝ)^γ +
          B * (y.den : ℝ)^(-α) * (L : ℝ)^ν * ∑ t ∈ y.den.divisors, (t : ℝ)^(α-1)) := by
  let U := A * (y.den : ℝ)^α * (L : ℝ)^γ
  let V := B * (y.den : ℝ)^(-α) * (L : ℝ)^ν
  let Z := (1 + Real.log y.den)^r
  have logpos (n : ℕ) (p : 0 < n) : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast p)
  have zpos : 0 ≤ Z := Real.rpow_nonneg (by linarith [logpos _ y.pos]) _
  have upos : 0 ≤ U := by dsimp [U]; positivity
  have vpos : 0 ≤ V := by dsimp [V]; positivity
  have bound (h : ℕ) (hh : h ∈ Icc 1 H) :
      orbitBound A B α γ ν r ((h : ℚ)*y).den L / h ≤
        Z * (U * (h : ℝ)⁻¹ + V * ((h.gcd y.den : ℝ)^α / h)) := by
    let q := ((h : ℚ)*y).den
    let g := h.gcd y.den
    have qp : 0 < q := Rat.pos _
    have gp : 0 < g := Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hh).1
    have fac : (y.den : ℝ) = (q : ℝ)*g := by exact_mod_cast frequency_denominator y h
    have le : (q : ℝ) ≤ y.den := by
      rw [fac]
      exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast gp)
    have neg : (q : ℝ)^(-α) = (y.den : ℝ)^(-α) * (g : ℝ)^α := by
      rw [fac, Real.mul_rpow (by positivity) (by positivity), mul_assoc, ← Real.rpow_add (by positivity)]
      simp
    have logle : (1 + Real.log q)^r ≤ Z := by
      dsimp [Z]
      apply Real.rpow_le_rpow (by linarith [logpos _ qp]) _ hr
      gcongr
    have first : A*(q : ℝ)^α*(L : ℝ)^γ ≤ U := by dsimp [U]; gcongr
    unfold orbitBound
    change ((A * (q : ℝ)^α * _ + B * (q : ℝ)^(-α) * _) * _) / _ ≤ _
    have second : B*((y.den : ℝ)^(-α)*(g : ℝ)^α)*(L : ℝ)^ν = V*(g : ℝ)^α := by
      dsimp [V]; ring
    rw [neg, second]
    calc
      _ ≤ ((U + V*(g : ℝ)^α)*Z) / h := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg h)
        exact mul_le_mul (add_le_add first le_rfl) logle
          (Real.rpow_nonneg (by linarith [logpos _ qp]) _) (by positivity)
      _ = _ := by dsimp [g]; ring
  have exactSum : (∑ h ∈ Icc 1 H, (U*(h : ℝ)⁻¹ + V*((h.gcd y.den : ℝ)^α/h))) =
      U*(∑ h ∈ Icc 1 H, (h : ℝ)⁻¹) + V*(∑ h ∈ Icc 1 H, (h.gcd y.den : ℝ)^α/h) := by
    rw [sum_add_distrib, mul_sum, mul_sum]
  have harmon : ∑ h ∈ Icc 1 H, (h : ℝ)⁻¹ ≤ 1 + Real.log H := by
    simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log H
  apply (sum_le_sum bound).trans
  rw [← mul_sum, exactSum]
  calc
    _ ≤ Z*(U*(1+Real.log H) + V*((1+Real.log H) *
        ∑ t ∈ y.den.divisors, (t : ℝ)^(α-1))) := by
      gcongr
      exact harmonic_gcd_bound y.pos H α
    _ = _ := by dsimp [Z,U,V]; ring

/-- Dividing a prefix by a fixed positive coefficient denominator preserves the
old reduced denominator as a divisor and adds at most the fixed factor. -/
theorem divided_prefix_denominator (y : ℚ) {D : ℕ} (pos : 0 < D) :
    y.den ∣ (y / D).den ∧ (y / D).den ∣ D * y.den := by
  have back : (D : ℚ)*(y/D) = y := by field_simp
  constructor
  · simpa only [back, Rat.den_natCast, one_mul] using Rat.mul_den_dvd (D : ℚ) (y / D)
  · simpa [div_eq_mul_inv, pos.ne', Nat.mul_comm] using Rat.mul_den_dvd y (D : ℚ)⁻¹

private theorem sum_pieces (f : ℕ → ℂ) (cut : ℕ → ℕ) (J : ℕ)
    (first : cut 0 = 0) (inc : ∀ j < J, cut j ≤ cut (j+1)) :
    ∑ i ∈ range (cut J), f i =
      ∑ j ∈ range J, ∑ i ∈ range (cut (j+1)-cut j), f (cut j+i) := by
  induction J with
  | zero => simp [first]
  | succ J ih =>
    have le := inc J (Nat.lt_succ_self J)
    rw [sum_range_succ, ← ih (fun j hj => inc j (by omega)), ← sum_range_add, Nat.add_sub_of_le le]

/-- All positions in a clean piece are close in real value to one rational
radix orbit. The error retains its frequency factor. -/
theorem clean_piece_bound {b s : ℕ} {F : ℕ → ℕ → ℝ} (orbit : FixedSupportBound b s F)
    (u : ℕ → ℝ) (y : ℚ) (h a L : ℕ) (len : 0 < L) (smooth : ∃ k, y.den ∣ s^k)
    {τ : ℝ} (close : ∀ i < L, |u (a+i) - (b : ℝ)^i*y| ≤ τ) :
    ‖∑ i ∈ range L, phase (h*u (a+i))‖ ≤
      F ((h : ℚ)*y).den L + L * (2*Real.pi*h*τ) := by
  let f (i : ℕ) := phase (h*u (a+i))
  let g (i : ℕ) := phase ((b : ℝ)^i * (((h : ℚ)*y : ℚ) : ℝ))
  have each (i : ℕ) (hi : i ∈ range L) : ‖f i - g i‖ ≤ 2*Real.pi*h*τ := by
    apply (phase_sub_le ..).trans
    push_cast
    rw [show (h : ℝ)*u (a+i) - (b : ℝ)^i*(h*y) = h*(u (a+i) - (b : ℝ)^i*y) by ring,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg h), ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (close i (mem_range.mp hi)) (by positivity)
  obtain ⟨k, hk⟩ := smooth
  have div : ((h : ℚ)*y).den ∣ y.den := by simpa using Rat.mul_den_dvd (h : ℚ) y
  have G := orbit ((h : ℚ)*y) L len ⟨k, div.trans hk⟩
  have diff := (norm_sum_le (range L) (fun i => f i - g i)).trans (sum_le_sum each)
  rw [sum_sub_distrib] at diff
  simp only [sum_const, card_range, nsmul_eq_mul] at diff
  exact (norm_le_norm_add_norm_sub' (∑ i ∈ range L, f i) (∑ i ∈ range L, g i)).trans
    (add_le_add G diff)

/-- A finite interval estimate for arbitrary cuts, including a shorter last
piece. In the double sum the actual denominator at each frequency is used. -/
theorem discrepancy_of_clean_pieces {b s J H : ℕ} {F : ℕ → ℕ → ℝ} {C τ : ℝ}
    (orbit : FixedSupportBound b s F) (et : ErdosTuran C) (hC : 0 ≤ C)
    (u : ℕ → ℝ) (cut : ℕ → ℕ) (y : ℕ → ℚ)
    (first : cut 0 = 0) (inc : ∀ j < J, cut j < cut (j+1))
    (len : 0 < cut J) (freq : 0 < H)
    (smooth : ∀ j < J, ∃ k, (y j).den ∣ s^k)
    (close : ∀ j < J, ∀ i < cut (j+1)-cut j, |u (cut j+i) - (b : ℝ)^i*y j| ≤ τ) :
    cut J * CircleDiscrepancy.disc u (cut J) ≤ C * (cut J / ((H : ℝ)+1) +
      ∑ h ∈ Icc 1 H, (∑ j ∈ range J,
        (F ((h : ℚ)*y j).den (cut (j+1)-cut j) +
          (cut (j+1)-cut j : ℕ) * (2*Real.pi*h*τ))) / h) := by
  apply (et u (cut J) H len freq).trans
  gcongr with h
  rw [sum_pieces _ cut J first (fun j hj => (inc j hj).le)]
  apply (norm_sum_le ..).trans (sum_le_sum (fun j hj => ?_))
  have hj' := mem_range.mp hj
  exact clean_piece_bound orbit u (y j) h (cut j) _ (Nat.sub_pos_of_lt (inc j hj'))
    (smooth j hj') (close j hj')

/-- Finite extreme discrepancy from the two external inequalities, expressed
solely in the piece lengths, prefix denominators, real error and Fourier cutoff. -/
theorem discrepancy_of_vandehey {b s J H : ℕ} {C τ A B α γ ν r : ℝ}
    (orbit : FixedSupportBound b s (orbitBound A B α γ ν r))
    (et : ErdosTuran C) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 ≤ α) (hr : 0 ≤ r) (u : ℕ → ℝ) (cut : ℕ → ℕ) (y : ℕ → ℚ)
    (first : cut 0 = 0) (inc : ∀ j < J, cut j < cut (j+1))
    (len : 0 < cut J) (freq : 0 < H)
    (smooth : ∀ j < J, ∃ k, (y j).den ∣ s^k)
    (close : ∀ j < J, ∀ i < cut (j+1)-cut j, |u (cut j+i) - (b : ℝ)^i*y j| ≤ τ) :
    cut J * CircleDiscrepancy.disc u (cut J) ≤ C * (cut J / ((H : ℝ)+1) +
      ∑ j ∈ range J, let Q := (y j).den; let L := cut (j+1)-cut j
        (1+Real.log Q)^r * (1+Real.log H) *
          (A * (Q : ℝ)^α * (L : ℝ)^γ +
           B * (Q : ℝ)^(-α) * (L : ℝ)^ν * ∑ t ∈ Q.divisors, (t : ℝ)^(α-1)) +
        H * (L * (2*Real.pi*τ))) := by
  apply (discrepancy_of_clean_pieces orbit et hC u cut y first inc len freq smooth close).trans
  apply mul_le_mul_of_nonneg_left (add_le_add le_rfl _) hC
  simp_rw [sum_div]
  rw [sum_comm]
  apply sum_le_sum
  intro j _
  let L := cut (j+1)-cut j
  have cancel (h : ℕ) (hh : h ∈ Icc 1 H) :
      (L : ℝ) * (2*Real.pi*h*τ) / h = L * (2*Real.pi*τ) := by
    have hp : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hh).1)
    field_simp
  simp_rw [add_div, sum_add_distrib]
  change _ + (∑ h ∈ Icc 1 H, (L : ℝ)*(2*Real.pi*h*τ)/h) ≤ _
  rw [sum_congr rfl cancel]
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  exact add_le_add (harmonic_orbit_bound (y j) H L hA hB ha hr) le_rfl

/-- Sum an estimate for every partial dyadic shell through an arbitrary final
cutoff. A monotone logarithmic factor can be included in `M` at the final scale. -/
theorem dyadic_prefix_bound {G : Type*} [SeminormedAddCommGroup G] (f : ℕ → G)
    {K N : ℕ} (lo : 2^K ≤ N) (hi : N ≤ 2^(K+1)) {M r : ℝ} (hr : 1 < r)
    (shell : ∀ k ≤ K, ∀ t ≤ 2^k, ‖∑ i ∈ range t, f (2^k+i)‖ ≤ M*r^k) :
    ‖∑ i ∈ range N, f i‖ ≤ ‖f 0‖ + M * ((r^(K+1)-1)/(r-1)) := by
  have full (k : ℕ) (hk : k ≤ K) :
      ‖∑ i ∈ range (2^k), f i‖ ≤ ‖f 0‖ + M * ∑ j ∈ range k, r^j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2^(k+1) = 2^k + 2^k by rw [pow_succ]; omega, sum_range_add, sum_range_succ, mul_add]
      exact (norm_add_le ..).trans ((add_le_add (ih (by omega))
        (shell k (by omega) _ le_rfl)).trans_eq (by ring))
  have cut : N = 2^K + (N-2^K) := (Nat.add_sub_of_le lo).symm
  have short : N-2^K ≤ 2^K := by rw [pow_succ] at hi; omega
  conv_lhs => rw [cut, sum_range_add]
  rw [← geom_sum_eq hr.ne' (K+1), sum_range_succ, mul_add]
  exact (norm_add_le ..).trans ((add_le_add (full K le_rfl)
    (shell K le_rfl _ short)).trans_eq (by ring))

end NormalityChecker.QuantitativeStoneham
