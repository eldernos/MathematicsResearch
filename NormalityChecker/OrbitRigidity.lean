module

public import NormalityChecker.ArithmeticCertificate

/-! Distinct fixed-support rational models are separated in mean circle distance. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

private theorem turn_sub_le (x y : ℝ) :
    turnDistance (x-y) ≤ turnDistance x + turnDistance y := by
  apply (round_le (x-y) (round x-round y)).trans
  rw [Int.cast_sub,show x-y-((round x:ℝ)-round y)=(x-round x)-(y-round y) by ring]
  exact abs_sub _ _

private theorem rational_grid_gap (w : ℚ) (nonint : w.den ≠ 1) :
    1/(w.den:ℝ) ≤ turnDistance (w:ℝ) := by
  let u := w-(round (w:ℝ):ℤ)
  have den : u.den=w.den := Rat.sub_intCast_den ..
  have ne : u.num ≠ 0 := by
    intro z
    have zero : u=0 := by rw [← Rat.num_div_den u,z]; simp
    exact nonint (by rw [← den,zero]; rfl)
  have one : (1:ℝ)≤|(u.num:ℝ)| := by exact_mod_cast Int.one_le_abs ne
  have val : turnDistance (w:ℝ)=|(u:ℝ)| := by simp [u,turnDistance]
  rw [val,Rat.cast_def,abs_div,abs_of_pos (by exact_mod_cast u.pos : (0:ℝ)<u.den),den]
  gcongr

/-- Uniform finite separation on every nonempty common block. Denominator one
means equality modulo one. The exponent is measured against the overlap length. -/
theorem smooth_overlap_separation {b c : ℕ} (hb : 1<b) (hc : 1<c) (cop : b.Coprime c)
    (d : ℕ) : ∃ δ : ℝ, 0<δ ∧ ∀ (x y : ℚ) (T : ℕ), 0<T →
      (∃ j : ℕ, x.den∣c^j) → (∃ j : ℕ, y.den∣c^j) → x.den≤T^d → y.den≤T^d →
      (x-y).den≠1 → ∀ f : ℕ → ℝ, δ*T ≤
      (∑ i∈range T, turnDistance (f i-(b:ℝ)^i*x)) +
      ∑ i∈range T, turnDistance (f i-(b:ℝ)^i*y) := by
  obtain ⟨M,cancel⟩ := fixed_support_orbit_estimate hb hc cop (d+d) (1/2) (by norm_num)
  let δ := min (1/((M:ℝ)+1)) (1/(4*Real.pi))
  refine ⟨δ,lt_min (by positivity) (by positivity),?_⟩
  rintro x y T hT ⟨j,hj⟩ ⟨k,hk⟩ sx sy nz f
  let z := x-y
  have dvd := Rat.sub_den_dvd x y
  have smooth : z.den∣c^(j+k) := by rw [pow_add]; exact dvd.trans (Nat.mul_dvd_mul hj hk)
  have poly : z.den≤T^(d+d) := by
    rw [pow_add]; exact (Nat.le_of_dvd (Nat.mul_pos x.pos y.pos) dvd).trans (Nat.mul_le_mul sx sy)
  let e (i : ℕ) := turnDistance (0-(b:ℝ)^i*z)
  have both : (∑ i∈range T,e i) ≤ _ := calc
    _ ≤ ∑ i∈range T, (turnDistance (f i-(b:ℝ)^i*x)+turnDistance (f i-(b:ℝ)^i*y)) := by
      apply sum_le_sum; intro i _
      convert turn_sub_le (f i-(b:ℝ)^i*x) (f i-(b:ℝ)^i*y) using 2
      dsimp [z]; push_cast; ring
    _ = _ := sum_add_distrib
  apply le_trans _ both
  by_cases large : M≤z.den
  · have bound := cancel z T large ⟨_,smooth⟩ poly
    have phaseBound := phase_model_sum_bound 1 T (fun _ => 0) (fun i => (b:ℝ)^i*z)
    simp only [Int.cast_one,one_mul,mul_zero,phase,Complex.ofReal_zero,Complex.exp_zero,sum_const,card_range,
      nsmul_eq_mul,mul_one,Complex.norm_natCast,abs_one] at phaseBound
    have defect : (T:ℝ) ≤ (1/2)*T+2*Real.pi*(∑ i∈range T,e i) := by
      change (T:ℝ) ≤ ‖∑ i∈range T,phase ((b:ℝ)^i*z)‖+2*Real.pi*(∑ i∈range T,e i) at phaseBound
      linarith only [phaseBound,bound]
    have cap : δ≤1/(4*Real.pi) := min_le_right ..
    apply (mul_le_mul_of_nonneg_right cap (Nat.cast_nonneg T)).trans
    rw [one_div_mul_eq_div,div_le_iff₀ (by positivity)]
    linarith only [defect]
  · have baseUnit : b.Coprime z.den := Nat.Coprime.coprime_dvd_right smooth (cop.pow_right _)
    have point (i : ℕ) : δ ≤ e i := by
      let w := ((b^i:ℕ):ℚ)*z
      have same : w.den=z.den := by
        have h := Rat.den_mul_den_eq_den_mul_gcd ((b^i:ℕ):ℚ) z
        simpa [w,Int.natAbs_mul,Nat.Coprime.gcd_mul_right_cancel _ z.reduced,
          (baseUnit.pow_left i).gcd_eq_one] using h.symm
      have gap := rational_grid_gap (-w) (by simpa [same] using nz)
      have le : (z.den:ℝ)≤(M:ℝ)+1 := by exact_mod_cast (by omega : z.den≤M+1)
      have small := (min_le_left (1/((M:ℝ)+1)) (1/(4*Real.pi))).trans
        (one_div_le_one_div_of_le (by exact_mod_cast z.pos) le)
      simpa [δ,e,w,same] using small.trans (by simpa [same] using gap : 1/(z.den:ℝ)≤turnDistance ((-w:ℚ):ℝ))
    simpa [mul_comm] using sum_le_sum (s:=range T) (fun i _ => point i)

/-- Vanishing total mean error on the common samples forces eventual agreement
of the two starting phases modulo one. -/
theorem smooth_overlap_rigidity {b c : ℕ} (hb : 1<b) (hc : 1<c) (cop : b.Coprime c)
    (d : ℕ) (x y : ℕ → ℚ) (T : ℕ → ℕ) (f : ℕ → ℕ → ℝ)
    (models : ∀ᶠ n in atTop, 0<T n ∧ (∃ j : ℕ, (x n).den∣c^j) ∧
      (∃ j : ℕ, (y n).den∣c^j) ∧ (x n).den≤T n^d ∧ (y n).den≤T n^d)
    (close : Tendsto (fun n =>
      ((∑ i∈range (T n), turnDistance (f n i-(b:ℝ)^i*x n))+
       ∑ i∈range (T n), turnDistance (f n i-(b:ℝ)^i*y n))/(T n:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ k : ℤ, x n-y n=k := by
  obtain ⟨δ,pos,gap⟩ := smooth_overlap_separation hb hc cop d
  filter_upwards [models,close.eventually_lt_const pos] with n model tiny
  obtain ⟨len,sx,sy,px,py⟩ := model
  have eqden : (x n-y n).den=1 := by
    by_contra ne
    exact (not_lt_of_ge (gap _ _ _ len sx sy px py ne (f n))) ((div_lt_iff₀ (by exact_mod_cast len)).mp tiny)
  exact ⟨_,((Rat.den_eq_one_iff _).mp eqden).symm⟩

/-- A chain of compatible overlaps in a fixed smooth support has eventually
constant reduced denominator, even when each successive block starts later. -/
theorem overlap_chain_denominator {b c : ℕ} (cop : b.Coprime c) (y : ℕ → ℚ) (stride : ℕ → ℕ)
    (smooth : ∀ᶠ n in atTop, ∃ j : ℕ, (y n).den∣c^j)
    (agree : ∀ᶠ n in atTop, ∃ k : ℤ, (b:ℚ)^(stride n)*y n-y (n+1)=k) :
    ∃ Q : ℕ, ∀ᶠ n in atTop, (y n).den=Q := by
  obtain ⟨N,late⟩ := eventually_atTop.mp (smooth.and agree)
  refine ⟨(y N).den,eventually_atTop.mpr ⟨N,?_⟩⟩
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    obtain ⟨⟨j,div⟩,k,eqn⟩ := late n hn
    have baseUnit := Nat.Coprime.coprime_dvd_right div (cop.pow_right j)
    have den := Rat.den_mul_den_eq_den_mul_gcd ((b^(stride n):ℕ):ℚ) (y n)
    have same : (((b:ℚ)^(stride n))*y n).den=(y n).den := by
      simpa [Int.natAbs_mul,Nat.Coprime.gcd_mul_right_cancel _ (y n).reduced,
        (baseUnit.pow_left (stride n)).gcd_eq_one] using den.symm
    have eq : y (n+1)=(b:ℚ)^(stride n)*y n-k := by linarith only [eqn]
    rw [eq,Rat.sub_intCast_den,same,ih]

end NormalityChecker
