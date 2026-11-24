module

public import NormalityChecker.LocalizedCertifiedNormal

@[expose] public section
open Finset
namespace NormalityChecker.LocalizedSupport

/-- Each of the five accumulated residues. Grid points 6 and 7 are in the same cell. -/
theorem decimal_residue_table : ∀ u : Fin 9, 3 ≤ u.val →
    (cellResidue 3 1 {2,5} (inverseLift 10 3 1 0) u).val =
      (if u.val < 4 then 1 else if u.val < 5 then 4 else if u.val < 6 then 1
       else if u.val < 8 then 6 else 3) := by decide +kernel

theorem decimal_denominator {k n : ℕ} (hk : 1 ≤ k) (lo : 3^k ≤ n) (hi : n < 3^(k+1)) :
    3^(k-1) ∣ (shifted 10 {2,3,5} n).den := by
  rw [show ({2,3,5}:Finset ℕ) = insert 3 {2,5} by decide]
  exact passes_denominator (seed:=0) (by decide) (by decide) (by decide) hk lo hi (by decide +kernel)

theorem decimal_235_normal : NormalIn 10 (value 10 {2,3,5}) := by
  let c : Certificate := ⟨10,3,{2,5},1,0,by decide,by decide,by decide,by decide,by decide,by decide,by decide +kernel⟩
  convert c.normal using 2
  decide

private def singletonPowers {p : ℕ} (hp : p.Prime) : ℕ ≃ Nat.factoredNumbers {p} :=
  let e := Nat.equivProdNatFactoredNumbers (s:=∅) hp (by simp)
  let one : Nat.factoredNumbers ∅ := ⟨1,by simp⟩
  { toFun := fun c => e (c,one)
    invFun := fun m => (e.symm m).1
    left_inv := fun c => congrArg Prod.fst (e.symm_apply_apply (c,one))
    right_inv := fun m => by
      apply e.symm.injective; simp only [Equiv.symm_apply_apply]; refine Prod.ext ?_ ?_
      · rfl
      · apply Subtype.ext; have h := (e.symm m).2.property
        exact (show ((e.symm m).2:ℕ)=1 by simpa using h).symm }

private def decimalIndex : (ℕ × ℕ × ℕ) ≃ Nat.factoredNumbers {2,3,5} :=
  (Equiv.prodCongr (Equiv.refl ℕ) ((Equiv.prodCongr (Equiv.refl ℕ)
    (singletonPowers (p:=5) (by decide))).trans
    (Nat.equivProdNatFactoredNumbers (s:={5}) (p:=3) (by decide) (by decide)))).trans
    (Nat.equivProdNatFactoredNumbers (s:={3,5}) (p:=2) (by decide) (by decide))

/-- Reindex the positive series by its three independent prime exponents. -/
theorem decimal_value_eq_series : value 10 {2,3,5} = ∑' a : ℕ, ∑' j : ℕ, ∑' c : ℕ,
    1 / ((2:ℝ)^a*3^j*5^c*10^(2^a*3^j*5^c : ℕ)) := by
  let g (v : ℕ × ℕ × ℕ) := (decimalIndex v).val - 1
  have pos (v) : 0 < (decimalIndex v).val := Nat.pos_of_ne_zero (decimalIndex v).property.1
  have succ (v) : g v + 1 = (decimalIndex v).val := Nat.sub_add_cancel (pos v)
  have inj : Function.Injective g := by
    intro v w h; apply decimalIndex.injective; apply Subtype.ext
    rw [← succ,← succ,h]
  have H : HasSum (term 10 {2,3,5} ∘ g) (value 10 {2,3,5}) := (inj.hasSum_iff (fun i hi => by
    have absent : i+1 ∉ Nat.factoredNumbers {2,3,5} := by
      intro hs; apply hi; refine ⟨decimalIndex.symm ⟨i+1,hs⟩,?_⟩; simp [g]
    simp [term,absent])).mpr (summable_term 10 _ (by decide)).hasSum
  rw [← H.tsum_eq,H.summable.tsum_prod' (fun i => H.summable.prod_factor i)]
  apply tsum_congr; intro a
  have hs := H.summable.prod_factor a
  rw [hs.tsum_prod' (fun j => hs.prod_factor j)]
  apply tsum_congr; intro j; apply tsum_congr; intro c
  let v := (a,j,c)
  have idx : (decimalIndex v).val = 2^a*(3^j*(5^c*1)) := rfl
  have e : (g v:ℝ)+1 = (decimalIndex v).val := by exact_mod_cast succ v
  change term 10 {2,3,5} (g v) = _
  rw [term,succ,ite_eq_left (decimalIndex v).property,e,idx]
  push_cast; simp [mul_assoc]

theorem decimal_series_normal : NormalIn 10 (∑' a : ℕ, ∑' j : ℕ, ∑' c : ℕ,
    1 / ((2:ℝ)^a*3^j*5^c*10^(2^a*3^j*5^c : ℕ))) := decimal_value_eq_series ▸ decimal_235_normal

theorem decimal_2511_normal : NormalIn 10 (value 10 {2,5,11}) := by
  let c : Certificate := ⟨10,11,{2,5},0,0,by decide,by decide,by decide,by decide,by decide,by decide,by decide +kernel⟩
  convert c.normal using 2
  decide

theorem base30_2357_normal : NormalIn 30 (value 30 {2,3,5,7}) := by
  let c : Certificate := ⟨30,7,{2,3,5},0,0,by decide,by decide,by decide,by decide,by decide,by decide,by decide +kernel⟩
  convert c.normal using 2
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem decimal_257_normal : NormalIn 10 (value 10 {2,5,7}) := by
  let c : Certificate := ⟨10,7,{2,5},2,2,by decide,by decide,by decide,by decide,by decide,by decide,by decide +kernel⟩
  convert c.normal using 2
  decide

/-- More than one off-base prime. These tests certify the selected denominator prime. -/
theorem binary_certificates : passes 2 7 0 0 {2,5} = true ∧ passes 2 11 0 0 {2,5} = true ∧
    passes 2 13 0 0 {2,5,7,11} = true := by decide +kernel

end NormalityChecker.LocalizedSupport
