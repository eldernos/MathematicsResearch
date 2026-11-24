module

public import NormalityChecker.OrbitRigidity

/-! Two overlapping observations of a phase known only up to translated rational grids. -/
@[expose] public section
namespace NormalityChecker

/-- Two compatible pairs of unwrapped lifts have the same displacement, on the gcd
grid. Integer translates handle either side of the circular cut. -/
theorem compatible_grid_differences {h k : ℕ} (hh : 0<h) (hk : 0<k)
    {a a' b b' : ℚ} (ha : a.den∣h) (ha' : a'.den∣h) (hb : b.den∣k) (hb' : b'.den∣k)
    (u v η : ℝ) (first : |(u+a)-(v+b)|≤η) (second : |(u+a')-(v+b')|≤η)
    (narrow : 2*η*(h.lcm k)<1) :
    a-a'=b-b' ∧ (a-a').den∣h.gcd k := by
  have x := (Rat.sub_den_dvd_lcm a a').trans (Nat.lcm_dvd ha ha')
  have y := (Rat.sub_den_dvd_lcm b b').trans (Nat.lcm_dvd hb hb')
  let z := (a-a')-(b-b')
  have zd : z.den∣h.lcm k := (Rat.sub_den_dvd_lcm ..).trans (Nat.lcm_dvd
    (x.trans (Nat.dvd_lcm_left ..)) (y.trans (Nat.dvd_lcm_right ..)))
  have eqn : |(z:ℝ)|≤2*η := by
    have tri := abs_sub_le ((u+a)-(v+b)) 0 ((u+a')-(v+b'))
    rw [sub_zero,zero_sub,abs_neg] at tri
    have id : (z:ℝ)=((u+a)-(v+b))-((u+a')-(v+b')) := by dsimp [z]; push_cast; ring
    rw [id]; linarith
  have small : |(z.num:ℝ)|<1 := by
    have denpos : (0:ℝ)<z.den := by exact_mod_cast z.pos
    have dn : (z.den:ℝ)≤h.lcm k := by exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos hh hk) zd
    rw [Rat.cast_def,abs_div,abs_of_pos denpos,div_le_iff₀ denpos] at eqn
    exact eqn.trans_lt ((mul_le_mul_of_nonneg_left dn (by linarith [abs_nonneg ((u+a)-(v+b))])).trans_lt narrow)
  have zi : |z.num|<(1:ℤ) := by exact_mod_cast small
  have zero := (Rat.num_eq_zero.mp (show z.num=0 by rw [abs_lt] at zi; omega))
  have id := sub_eq_zero.mp (show (a-a')-(b-b')=0 from zero)
  exact ⟨id,Nat.dvd_gcd x (id ▸ y)⟩

end NormalityChecker
