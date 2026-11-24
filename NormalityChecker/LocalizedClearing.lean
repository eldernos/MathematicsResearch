module

public import NormalityChecker.LocalizedSupport

@[expose] public section
open Finset
namespace NormalityChecker.LocalizedSupport

private lemma exponent_le {m D : ℕ} (hm : m ≠ 0) (hmD : m ≤ 2^D) (q : ℕ) :
    m.factorization q ≤ D := by
  by_cases hq : q.Prime
  · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
      (((Nat.pow_le_pow_left hq.two_le _).trans (Nat.ordProj_le q hm)).trans hmD)
  · simp [Nat.factorization_eq_zero_of_not_prime m hq]

/-- Count supported insertions by encoding every prime exponent in `[0,D]`. -/
theorem insertion_count (S : Finset ℕ) (D : ℕ) : (indices S (2^D)).card ≤ (D+1)^S.card := by
  classical
  let code (m : ℕ) (q : S) : Fin (D+1) := ⟨min D (m.factorization q),by omega⟩
  have inj : Set.InjOn code (indices S (2^D) : Set ℕ) := by
    intro m hm n hn h
    obtain ⟨hm,hms⟩ := mem_indices.mp hm; obtain ⟨hn,hns⟩ := mem_indices.mp hn
    apply Nat.factorization_inj hms.1 hns.1; ext q
    by_cases hq : q ∈ S
    · have H := congrArg Fin.val (congrFun h ⟨q,hq⟩)
      simpa [code,min_eq_right (exponent_le hms.1 hm q),min_eq_right (exponent_le hns.1 hn q)] using H
    · have outside {a : ℕ} (ha : a ∈ Nat.factoredNumbers S) : a.factorization q = 0 := by
        by_cases prime : q.Prime
        · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hq (Nat.mem_factoredNumbers'.mp ha q prime hd))
        · exact Nat.factorization_eq_zero_of_not_prime _ prime
      rw [outside hms,outside hns]
  simpa using card_le_card_of_injOn (t:=univ) code (fun _ _ => mem_univ _) inj

lemma cofactor_dvd {S : Finset ℕ} {b r D : ℕ} (hb : 0<b) (base : ∀ q ∈ S, q ∣ b)
    (hr : r ∈ Nat.factoredNumbers S) (hD : r ≤ 2^D) : r ∣ b^D := by
  apply (Nat.factorization_le_iff_dvd hr.1 (pow_pos hb _).ne').mp
  intro q; rw [Nat.factorization_pow,Finsupp.nsmul_apply,smul_eq_mul]
  by_cases hq : q.Prime ∧ q ∣ r
  · have H := base q (Nat.mem_factoredNumbers'.mp hr q hq.1 hq.2)
    exact (exponent_le hr.1 hD q).trans (Nat.le_mul_of_pos_right D (hq.1.factorization_pos_of_dvd hb.ne' H))
  · by_cases prime : q.Prime
    · simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ q ∣ r from fun h => hq ⟨prime,h⟩)]
    · simp [Nat.factorization_eq_zero_of_not_prime _ prime]

/-- Once every insertion is at least `D` shifts old, all base factors have cleared. -/
theorem clean_denominator {S : Finset ℕ} {p b n D : ℕ} (hp : p.Prime) (hs : p ∉ S)
    (hb : 0<b) (base : ∀ q ∈ S, q ∣ b) (size : n ≤ 2^D)
    (clean : ∀ m ∈ indices (insert p S) n, m+D ≤ n) :
    (shifted b (insert p S) n).den ∣ p^(Nat.log p n) := by
  let k := Nat.log p n
  let A (j r : ℕ) := p^(k-j)*(b^(n-p^j*r)/r)
  let num := ∑ j ∈ range (k+1), ∑ r ∈ indices S (n/p^j), A j r
  apply (reduced_info (S:=num) (pow_pos hp.pos k) _).1
  dsimp only [num,shifted,partialSum]
  rw [sum_layers hp hs n k (Nat.lt_pow_succ_log_self hp.one_lt n)]
  simp only [Nat.cast_sum,mul_sum]
  apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro r hr
  let m := p^j*r
  obtain ⟨hle,hsr⟩ := mem_indices.mp hr
  have hm : m ≤ n := by simpa [m,mul_comm] using (Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mp hle
  have age := clean m (mem_indices.mpr ⟨hm,Nat.pow_mul_mem_factoredNumbers hp _ hsr⟩)
  have rd : r ∣ b^(n-m) := (cofactor_dvd hb base hsr ((Nat.le_mul_of_pos_left r (pow_pos hp.pos j)).trans (hm.trans size))).trans
    (pow_dvd_pow b (by omega))
  have h1 := congrArg (fun z : ℕ => (z:ℚ)) (Nat.div_mul_cancel rd)
  have h2 := congrArg (fun z : ℕ => (p:ℚ)^z) (Nat.sub_add_cancel (show j ≤ k by simpa using mem_range.mp hj))
  have h3 := congrArg (fun z : ℕ => (b:ℚ)^z) (Nat.sub_add_cancel hm)
  simp only [pow_add] at h2 h3; push_cast at h1
  rw [Nat.cast_pow]
  change ((p^(k-j)*(b^(n-m)/r):ℕ):ℚ) = (p:ℚ)^k*((b:ℚ)^n*weight b m)
  simp only [Nat.cast_mul,Nat.cast_pow,weight]; rw [← h2,← h3]; dsimp only [m] at *
  push_cast; field_simp [hp.ne_zero,hsr.1,hb.ne']; exact h1

end NormalityChecker.LocalizedSupport
