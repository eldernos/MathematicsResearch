module

public import NormalityChecker.StonehamPolynomialExpansion
public import NormalityChecker.ArithmeticCertificate
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-! Normality for a same-prime product and arbitrary lower-degree terms. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.StonehamPolynomial

/-- A product of dilated Stoneham series. The empty product represents one. -/
structure Monomial where
  degree : ℕ
  parameter : Vector degree
  positive : ∀ i, 0 < parameter i
  stride : Strides degree := fun _ => 1

namespace Monomial
variable (t : Monomial)
noncomputable def value (b p : ℕ) := ∏ i, axis b (p^(t.stride i : ℕ)) (t.parameter i)
def model (b p n : ℕ) := productPrefix b p t.stride t.parameter n
private def events (p k : ℕ) := (box t.degree (2*(k+1))).image (position p t.stride t.parameter)

private lemma event_mem {p k : ℕ} (hp : 2 ≤ p) (v : Vector t.degree)
    (h : position p t.stride t.parameter v < 4^(k+1)) : position p t.stride t.parameter v ∈ t.events p k := by
  apply mem_image.mpr ⟨v,mem_box.mpr ?_,rfl⟩
  intro i
  have lo : 2^(v i) ≤ position p t.stride t.parameter v := calc
    2^(v i) ≤ p^(v i) := Nat.pow_le_pow_left hp _
    _ ≤ p^(stretch t.stride v i) := Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_left _ (t.stride i).pos)
    _ ≤ t.parameter i * p^(stretch t.stride v i) := Nat.le_mul_of_pos_left _ (t.positive i)
    _ ≤ _ := single_le_sum (f:=fun j => t.parameter j*p^(stretch t.stride v j)) (fun _ _ => Nat.zero_le _) (mem_univ i)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    ((lo.trans_lt h).trans_eq (by rw [pow_mul]; rfl))

private lemma events_card (p k : ℕ) : (t.events p k).card ≤ (2*(k+1))^t.degree :=
  card_image_le.trans_eq (by simp [box])
end Monomial

/-- An integral leading coefficient and any rational perturbation with pole order
at most `v_p(q)(d-1)k` leave a pole of order at least `v_p(q)dk-C` at late scales. -/
theorem retained_with_lower_terms_at {b q p : ℕ} (hp : p.Prime) (hq : 3 ≤ q)
    (pq : p ∣ q) (cop : b.Coprime p) (stable : StablePowers b q p)
    (t : Monomial) (degree : 0 < t.degree) (c : ℤ) (nc : c ≠ 0) (R : ℕ → ℚ)
    (lower : ∀ n, (R n).den ∣ q^((t.degree-1)*Nat.log q n)) :
    ∃ C K : ℕ, ∀ n, K ≤ Nat.log q n → 0 < n →
      p^(q.factorization p * (t.degree * Nat.log q n) - C) ∣ ((c:ℚ)*t.model b q n + R n).den := by
  obtain ⟨L,K,retain⟩ := retained_denominator_at hp hq pq cop stable t.stride t.parameter
  let h := c.natAbs.factorization p
  refine ⟨L+h,max K (L+h+1),fun n late pos => ?_⟩
  let k := Nat.log q n
  let x := t.model b q n
  let y := (c:ℚ)*x+R n
  have xc : p^(q.factorization p*(t.degree*k)-L) ∣ x.den := retain n ((le_max_left ..).trans late) pos
  have recov : (c:ℚ)⁻¹*(y-R n) = x := by
    dsimp [y]; rw [add_sub_cancel_right,inv_mul_cancel_left₀ (by exact_mod_cast nc)]
  have xd := Rat.mul_den_dvd (c:ℚ)⁻¹ (y-R n)
  rw [recov,Rat.inv_intCast_den,ite_eq_right nc] at xd
  have div := xc.trans (xd.trans (Nat.mul_dvd_mul_left _ (Rat.sub_den_dvd_lcm y (R n))))
  have cp := Int.natAbs_pos.mpr nc
  have lp := Nat.lcm_pos y.pos (R n).pos
  have le := (hp.pow_dvd_iff_le_factorization (Nat.mul_pos cp lp).ne').mp div
  rw [Nat.factorization_mul cp.ne' lp.ne', Finsupp.add_apply,
    Nat.factorization_lcm y.pos.ne' (R n).pos.ne', Finsupp.sup_apply] at le
  have bot := (Nat.factorization_prime_le_iff_dvd (R n).pos.ne' (pow_pos (by omega : 0<q) _).ne').mpr (lower n) p hp
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, mul_comm _ (q.factorization p)] at bot
  have eqdeg : t.degree*k = (t.degree-1)*k+k := by
    calc t.degree*k = ((t.degree-1)+1)*k := by rw [Nat.sub_add_cancel degree]
         _ = _ := by ring
  have bound : L+h+1 ≤ k := (le_max_right ..).trans late
  apply (hp.pow_dvd_iff_le_factorization y.pos.ne').mpr
  change q.factorization p*(t.degree*k)-L ≤ h+max _ _ at le
  change _ ≤ q.factorization p*((t.degree-1)*k) at bot
  change q.factorization p*(t.degree*k)-(L+h) ≤ _
  have mult := Nat.le_mul_of_pos_left k (hp.factorization_pos_of_dvd (by omega : q ≠ 0) pq)
  have split := congrArg (q.factorization p * ·) eqdeg
  rw [Nat.mul_add] at split
  omega

theorem retained_with_lower_terms {b p : ℕ} (hp : p.Prime) (odd : 3 ≤ p) (cop : b.Coprime p)
    (t : Monomial) (degree : 0 < t.degree) (c : ℤ) (nc : c ≠ 0) (R : ℕ → ℚ)
    (lower : ∀ n, (R n).den ∣ p^((t.degree-1)*Nat.log p n)) :
    ∃ C K : ℕ, ∀ n, K ≤ Nat.log p n → 0 < n →
      p^(t.degree * Nat.log p n - C) ∣ ((c:ℚ)*t.model b p n + R n).den := by
  simpa [hp.factorization_self] using
    retained_with_lower_terms_at hp odd dvd_rfl cop (stablePowers_prime hp cop) t degree c nc R lower

/-- A unique highest-degree monomial with nonzero integer coefficient survives
addition of any finite sum of strictly lower-degree monomials. Each parameter is a
power of the same integer, which has a stabilizing prime divisor. -/
theorem integer_sum_normal_at {ι : Type*} {b q p : ℕ} (hb : 2 ≤ b) (hq : 3 ≤ q)
    (hp : p.Prime) (pq : p ∣ q) (stable : StablePowers b q p)
    (cop : b.Coprime q) (t : Monomial) (degree : 0 < t.degree) (c : ℤ) (nc : c ≠ 0)
    (s : Finset ι) (u : ι → Monomial) (a : ι → ℤ) (lt : ∀ i ∈ s, (u i).degree < t.degree) :
    NormalIn b (c * t.value b q + ∑ i ∈ s, (a i:ℝ)*(u i).value b q) := by
  classical
  have hq₀ : 0 < q := by omega
  have hq₁ : 1 < q := by omega
  let R (n : ℕ) := ∑ i ∈ s, (a i:ℚ)*(u i).model b q n
  let P (n : ℕ) := (c:ℚ)*t.model b q n + R n
  have lower (n : ℕ) : (R n).den ∣ q^((t.degree-1)*Nat.log q n) := by
    apply (Rat.den_sum_dvd_lcm_den ..).trans; apply Finset.lcm_dvd
    intro i hi
    have dd := Rat.mul_den_dvd (a i:ℚ) ((u i).model b q n)
    simp only [Rat.den_intCast,one_mul] at dd
    have le := lt i hi
    exact dd.trans ((denominator_dvd hq₀ (u i).stride _).trans (pow_dvd_pow _ (Nat.mul_le_mul_right _ (by omega))))
  have smooth (n : ℕ) : (P n).den ∣ q^(t.degree*Nat.log q n) := by
    apply (Rat.add_den_dvd_lcm ..).trans; apply Nat.lcm_dvd
    · have dd := Rat.mul_den_dvd (c:ℚ) (t.model b q n)
      simp only [Rat.den_intCast,one_mul] at dd
      exact dd.trans (denominator_dvd hq₀ t.stride t.parameter)
    · exact (lower n).trans (pow_dvd_pow _ (Nat.mul_le_mul_right _ (Nat.sub_le ..)))
  have scaled (v : Monomial) (z : ℤ) : Tendsto (fun n => (b:ℝ)^n * ((z:ℝ)*v.value b q) -
      (((z:ℚ)*v.model b q n:ℚ):ℝ)) atTop (𝓝 0) := by
    simpa only [Monomial.value,Monomial.model,Rat.cast_mul,Rat.cast_intCast,mul_zero,mul_sub,mul_left_comm (z:ℝ)] using
      (product_tail (b:=b) (p:=q) (e:=v.stride) hb hq₁ v.positive).const_mul (z:ℝ)
  have lowerTail := tendsto_finsetSum s (fun i _ => scaled (u i) (a i))
  have tail := (scaled t c).add lowerTail
  refine normal_of_arithmetic_certificate (B:=2) (L:=2) hb (by decide) (by decide) _ P ?_
    (fixed_support_orbit_estimate hb hq₁ cop) (4*t.degree) ?_
  · simpa only [P,R,Rat.cast_add,Rat.cast_sum,mul_add,mul_sum,← sum_sub_distrib,
      add_sub_add_comm,sum_const_zero,add_zero] using tail
  obtain ⟨C,K,retain⟩ := retained_with_lower_terms_at hp hq pq (cop.coprime_dvd_right pq) stable t degree c nc R lower
  let A (k : ℕ) := t.events q k ∪ s.biUnion (fun i => (u i).events q k)
  have count (k : ℕ) : (A k).card ≤ (s.card+1)*(2*(k+1))^t.degree := by
    have lift (i : ι) (hi : i ∈ s) := ((u i).events_card q k).trans
      (Nat.pow_le_pow_right (by positivity) (lt i hi).le)
    have small := card_biUnion_le.trans (sum_le_sum lift)
    have h := (card_union_le ..).trans (add_le_add (t.events_card q k) small)
    simp only [sum_const, smul_eq_mul] at h
    exact h.trans_eq (by ring)
  intro u₀ hu M η ηpos
  have lim := (tendsto_pow_const_div_const_pow_of_one_lt t.degree (by norm_num : (1:ℝ)<2)).const_mul
    (2*(s.card+1:ℝ)*4^t.degree)
  simp only [mul_zero] at lim
  let J := max K (M+C)
  filter_upwards [eventually_ge_atTop 1,lim.eventually_le_const ηpos,
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<4)).eventually_ge_atTop (q^J)] with k hk size late
  let B := 2^k
  let E := insertionBlocks (A k) B (u₀*B)
  have bp : 0 < B := pow_pos (by decide) _
  refine ⟨E,?_,fun l hl free => ?_⟩
  · have e := (card_insertionBlocks (A k) B (u₀*B)).trans (Nat.mul_le_mul_left 2
      ((count k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2*(k+1) ≤ 4*k) _))))
    have er : (E.card:ℝ) ≤ 2*(s.card+1)*(4*(k:ℝ))^t.degree := by
      exact_mod_cast (e.trans_eq (by ring))
    apply er.trans; rw [mul_pow]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at size
    simpa only [Nat.cast_ofNat,mul_assoc] using size
  · let n := (u₀*B+l)*B
    have base : 4^k = B*B := by dsimp [B]; rw [← mul_pow]; rfl
    have lo : 4^k ≤ n := by
      rw [base]; apply Nat.mul_le_mul_right; have := (mem_Ico.mp hu).1
      exact (Nat.le_mul_of_pos_left _ this).trans (Nat.le_add_right ..)
    have hi : n+B ≤ 4^(k+1) := by
      rw [pow_succ',base]
      have cap := Nat.mul_le_mul_right B (show u₀+1 ≤ 4 from (mem_Ico.mp hu).2)
      change l<B at hl
      calc n+B = (u₀*B+l+1)*B := by dsimp [n]; ring
           _ ≤ ((u₀+1)*B)*B := Nat.mul_le_mul_right _ (by rw [Nat.add_mul, one_mul]; omega)
           _ ≤ (4*B)*B := Nat.mul_le_mul_right _ cap
           _ = _ := by ring
    have pos : 0 < n := (pow_pos (by decide : 0<4) _).trans_le lo
    have big : J ≤ Nat.log q n := Nat.le_log_of_pow_le hq₁ (late.trans lo)
    have retained := retain n ((le_max_left ..).trans big) pos
    have denlo : M ≤ (P n).den := by
      apply le_trans _ (Nat.le_of_dvd (P n).pos retained)
      have le := (le_max_right ..).trans big
      have le' := Nat.le_mul_of_pos_left (Nat.log q n) degree
      have pad := Nat.le_mul_of_pos_left (t.degree * Nat.log q n)
        (hp.factorization_pos_of_dvd (by omega : q ≠ 0) pq)
      exact (by omega : M ≤ q.factorization p * (t.degree * Nat.log q n)-C).trans
        (Nat.lt_pow_self hp.one_lt).le
    have denhi : (P n).den ≤ (2^k)^(4*t.degree) := by
      apply (Nat.le_of_dvd (pow_pos hq₀ _) (smooth n)).trans
      rw [Nat.mul_comm t.degree,pow_mul q, pow_mul (2^k)]
      have top : n ≤ 2^(k*4) := by
        apply (Nat.le_add_right n B).trans (hi.trans _)
        rw [show 4=2^2 by decide, ← pow_mul]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      rw [← pow_mul (2:ℕ) k 4]
      exact Nat.pow_le_pow_left ((Nat.pow_log_le_self q pos.ne').trans top) _
    refine ⟨denlo,⟨_,smooth n⟩,denhi,?_⟩
    intro j hj
    change P (n+j) = (b:ℚ)^j*P n
    have follows (v : Monomial) (incl : v.events q k ⊆ A k) :
        v.model b q (n+j) = (b:ℚ)^j*v.model b q n := by
      apply prefix_follows hq₁ v.positive
      intro w newer; by_contra! le
      have hpos := incl (v.event_mem (by omega) w (le.trans_lt (by change j<B at hj; omega)))
      have gap := insertionBlocks_free bp free hpos (by
        rw [Nat.add_mul,one_mul]; change position q v.stride v.parameter w < n+B
        change j<B at hj; omega)
      change position q v.stride v.parameter w+B ≤ n at gap; omega
    dsimp only [P,R]; rw [follows t (subset_union_left),mul_add,mul_sum]
    congr 1
    · ring
    · apply sum_congr rfl; intro i hi
      rw [follows (u i) (fun _ h => mem_union_right _ (mem_biUnion.mpr ⟨i,hi,h⟩))]; ring

/-- The odd-prime specialization of the integer sum theorem. -/
theorem integer_sum_normal {ι : Type*} {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (odd : 3 ≤ p)
    (cop : b.Coprime p) (t : Monomial) (degree : 0 < t.degree) (c : ℤ) (nc : c ≠ 0)
    (s : Finset ι) (u : ι → Monomial) (a : ι → ℤ) (lt : ∀ i ∈ s, (u i).degree < t.degree) :
    NormalIn b (c * t.value b p + ∑ i ∈ s, (a i:ℝ)*(u i).value b p) :=
  integer_sum_normal_at hb odd hp dvd_rfl (stablePowers_prime hp cop) cop t degree c nc s u a lt

end NormalityChecker.StonehamPolynomial
