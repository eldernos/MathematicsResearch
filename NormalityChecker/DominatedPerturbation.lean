module

public import NormalityChecker.ArithmeticCertificate
public import NormalityChecker.LocalizedMesh

/-! Adding a rational-prefix perturbation of smaller local norm. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Outside a sparse insertion schedule, two prefixes follow the radix orbit.
A growing local norm of the first prefix survives addition of the second when
the second norm is strictly smaller. Both denominators must divide a common
smooth modulus polynomial in the block length. -/
theorem normal_of_dominated_perturbation {b c p B L : ℕ} (hb : 2≤b) (hc : 1<c)
    (cop : b.Coprime c) (hp : p.Prime) (hB : 0<B) (hL : 1<L)
    (x z : ℝ) (P R : ℕ → ℚ)
    (px : Tendsto (fun n => (b:ℝ)^n*x-(P n:ℝ)) atTop (𝓝 0))
    (rz : Tendsto (fun n => (b:ℝ)^n*z-(R n:ℝ)) atTop (𝓝 0))
    (A : ℕ → Finset ℕ) (d : ℕ) (sparse : ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop, (2:ℝ)*(A k).card≤η*(L:ℝ)^k)
    (arithmetic : ∀ M : ℕ, ∀ᶠ k : ℕ in atTop, ∀ n, (L*B)^k≤n → n<(L*B)^(k+1) →
      (M:ℚ) ≤ padicNorm p (P n) ∧ padicNorm p (R n)<padicNorm p (P n) ∧
      ∃ j : ℕ, (P n).den∣c^j ∧ (R n).den∣c^j ∧ c^j≤(B^k)^d)
    (orbit : ∀ k n i, n+i<(L*B)^(k+1) → (∀ m, n<m → m≤n+i → m∉A k) →
      P (n+i)+R (n+i)=(b:ℚ)^i*(P n+R n)) : NormalIn b (x+z) := by
  let : Fact p.Prime := ⟨hp⟩
  have tail : Tendsto (fun n => (b:ℝ)^n*(x+z)-((P n+R n:ℚ):ℝ)) atTop (𝓝 0) := by
    simpa only [mul_add,Rat.cast_add,add_sub_add_comm,add_zero] using px.add rz
  apply normal_of_arithmetic_certificate hb hB hL _ (fun n => P n+R n) tail (fixed_support_orbit_estimate hb hc cop) d
  intro u hu M η pos
  filter_upwards [sparse η pos,arithmetic M] with k size arith
  let K := L^k; let T := B^k
  let E := insertionBlocks (A k) T (u*K)
  refine ⟨E,(by exact_mod_cast card_insertionBlocks (A k) T (u*K) : (E.card:ℝ)≤2*(A k).card).trans size,?_⟩
  intro l hl hgood
  let n := (u*K+l)*T
  have tp : 0<T := pow_pos hB _
  have lo : (L*B)^k ≤ n := by rw [mul_pow]; exact Nat.mul_le_mul_right T ((Nat.le_mul_of_pos_left K (mem_Ico.mp hu).1).trans (Nat.le_add_right ..))
  have hi : n+T ≤ (L*B)^(k+1) := by
    rw [pow_succ',mul_pow]; change _≤ (L*B)*(K*T)
    calc n+T = (u*K+l+1)*T := by dsimp [n]; ring
         _ ≤ ((u+1)*K)*T := Nat.mul_le_mul_right _ (by rw [Nat.add_mul,one_mul]; omega)
         _ ≤ ((L*B)*K)*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (mem_Ico.mp hu).2)
         _ = _ := by ring
  obtain ⟨big,dominates,j,dp,dr,top⟩ := arith n lo (by omega)
  have norm := padicNorm.add_eq_max_of_ne dominates.ne'
  rw [max_eq_left dominates.le] at norm
  have both := (Rat.add_den_dvd_lcm (P n) (R n)).trans (Nat.lcm_dvd dp dr)
  refine ⟨by exact_mod_cast (big.trans (norm ▸ Localized.padicNorm_le_den hp (P n+R n))),⟨j,both⟩,
    (Nat.le_of_dvd (pow_pos (by omega : 0<c) _) both).trans top,?_⟩
  intro i hit; change i<T at hit; apply orbit k n i (by omega)
  intro m mn mi hm
  have H := insertionBlocks_free tp hgood hm (by rw [Nat.add_mul,one_mul]; change m<n+T; omega)
  change m+T≤n at H; omega

end NormalityChecker
