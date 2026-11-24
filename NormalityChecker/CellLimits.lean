module

public import NormalityChecker.ScaleTransfer

@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker

/-- Averages at ends of complete scales, for cells with prescribed limiting means. -/
theorem mean_at_scale {p S : ℕ} (hp : 1<p) (hS : 0<S) (f : ℕ → ℂ) (label : ℕ → ℂ)
    (H : ∀ u ∈ Ico S (p*S), RadixCellCancellation p (fun n => f n-label u) u) :
    Tendsto (fun k : ℕ => mean f (S*p^k)) atTop
      (𝓝 ((∑ u ∈ Ico S (p*S), label u)/(((p:ℂ)-1)*S))) := by
  let g (n : ℕ) := label (n / p^(Nat.log p (n/S)))
  have step {u k i : ℕ} (hu : u∈Ico S (p*S)) (hi : i<p^k) : g (u*p^k+i)=label u := by
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp hu
    have qpos := pow_pos (by omega : 0<p) k
    have hl : p^k ≤ (u*p^k+i)/S := (Nat.le_div_iff_mul_le hS).mpr (by nlinarith [Nat.mul_le_mul_right (p^k) hlo])
    have hh : (u*p^k+i)/S < p^(k+1) := (Nat.div_lt_iff_lt_mul hS).mpr (by rw [pow_succ]; nlinarith [Nat.mul_le_mul_right (p^k) (Nat.succ_le_of_lt hhi)])
    dsimp [g]; rw [Nat.log_eq_of_pow_le_of_lt_pow hl hh,Nat.mul_comm u (p^k),Nat.mul_add_div qpos,Nat.div_eq_of_lt hi,Nat.add_zero]
  have diff := mean_zero_of_radix_cells hp hS (f:=fun n => f n-g n) (by
    intro u hu ε hε
    filter_upwards [H u hu ε hε] with k hk T hT
    convert hk T hT using 3
    rename_i i hi; rw [step hu ((mem_range.mp hi).trans_le hT)])
  let P (n : ℕ) := ∑ i ∈ range n, g i
  let L := ∑ u ∈ Ico S (p*S), label u
  have addCells (k l : ℕ) (hl : S+l≤p*S) :
      P ((S+l)*p^k) = P (S*p^k) + (p:ℂ)^k*∑ a ∈ range l, label (S+a) := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hu : S+l∈Ico S (p*S) := mem_Ico.mpr ⟨by omega,by omega⟩
      have e : P ((S+(l+1))*p^k) = P ((S+l)*p^k) + ∑ i ∈ range (p^k), g ((S+l)*p^k+i) := by
        dsimp [P]; rw [show (S+(l+1))*p^k=(S+l)*p^k+p^k by ring,sum_range_add]
      rw [e,ih (by omega),sum_congr rfl (fun i hi => step hu (mem_range.mp hi)),sum_range_succ]
      simp; ring
  have hs : S≤p*S := Nat.le_mul_of_pos_left _ (by omega)
  have recur (k : ℕ) : P (S*p^(k+1)) = P (S*p^k)+(p:ℂ)^k*L := by
    have e := addCells k (p*S-S) (by omega)
    rw [Nat.add_sub_of_le hs, ← sum_Ico_eq_sum_range] at e
    simpa [L, pow_succ,mul_assoc,mul_comm,mul_left_comm] using e
  have hp' : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : p≠1))
  have geom (k : ℕ) : P (S*p^k) = P S + ((p:ℂ)^k-1)*(L/(p-1)) := by
    induction k with
    | zero => simp
    | succ k ih => rw [recur,ih,pow_succ]; field_simp; ring
  let N (k : ℕ) := S*p^k
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono
    (fun k => Nat.le_mul_of_pos_left (p^k) hS) (tendsto_pow_atTop_atTop_of_one_lt hp)
  have base : Tendsto (fun k => mean g (N k)) atTop (𝓝 (L/(((p:ℂ)-1)*S))) := by
    have small := (tendsto_const_div_atTop_nhds_zero_nat (𝕜:=ℂ) (P S - L/(p-1))).comp grow
    have hh := small.add (tendsto_const_nhds (x:=L/(((p:ℂ)-1)*S)))
    rw [zero_add] at hh
    apply hh.congr; intro k
    change (P S-L/(p-1))/(N k)+_ = P (N k)/(N k)
    dsimp [N]; rw [geom]; push_cast; field_simp [hS.ne', (show p≠0 by omega)]; ring
  have total := (diff.comp grow).add base
  rw [zero_add] at total
  apply total.congr; intro k
  simp [N,mean,sum_sub_distrib,sub_div]

end NormalityChecker
