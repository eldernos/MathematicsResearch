module

public import NormalityChecker.PartialUniformity

/-! Endpoint certificates for additive Fourier and centered counting sums. -/
@[expose] public section
open Finset
namespace NormalityChecker.Coverage

variable {E : Type*} [NormedAddCommGroup E]

def partialSum (f : ℕ → E) (n : ℕ) := ∑ i ∈ range n, f i

/-- The cost of a certified edge applies in either direction. Vertices may repeat. -/
theorem endpoint_path (f : ℕ → E) (v : ℕ → ℕ) (cost : ℕ → ℝ) (m : ℕ)
    (edges : ∀ i<m, dist (partialSum f (v i)) (partialSum f (v (i+1))) ≤ cost i) :
    dist (partialSum f (v 0)) (partialSum f (v m)) ≤ ∑ i∈range m, cost i :=
  dist_le_range_sum_of_dist_le (f:=fun i => partialSum f (v i)) m (fun h => edges _ h)

theorem prefix_edge (f : ℕ → E) (a t : ℕ) :
    dist (partialSum f a) (partialSum f (a+t)) = ‖∑ i∈range t, f (a+i)‖ := by
  simp [partialSum,sum_range_add,dist_eq_norm]

/-- Applying endpoint certificates to a single Fourier character, including
paths that go past the desired endpoint and return along a certified edge. -/
theorem fourier_of_path (f : ℕ → ℝ) (h : ℤ) (v : ℕ → ℕ) (m N : ℕ) (cost : ℕ → ℝ)
    (start : v 0=0) (stop : v m=N)
    (edges : ∀ i<m, let S := partialSum (fun j => phase (h*f j)); dist (S (v i)) (S (v (i+1)))≤cost i) :
    ‖∑ j∈range N, phase (h*f j)‖ ≤ ∑ i∈range m, cost i := by
  simpa only [start,stop,partialSum,range_zero,sum_empty,dist_zero_left]
    using endpoint_path _ v cost m edges

private theorem trivial_edge (f : ℕ → E) (unit : ∀ i, ‖f i‖≤1) (a t : ℕ) :
    dist (partialSum f a) (partialSum f (a+t)) ≤ t := by
  rw [prefix_edge]; exact (norm_sum_le ..).trans (by simpa using sum_le_sum (s:=range t) (fun i _ => unit (a+i)))

/-- Restrict a full interval to its middle, charging its two discarded ends.
Taking the right discard to be positive includes unfinished final blocks. -/
theorem restrict_edge (f : ℕ → E) (unit : ∀ i, ‖f i‖≤1) (a l t r : ℕ) {cost : ℝ}
    (full : dist (partialSum f a) (partialSum f (a+l+t+r)) ≤ cost) :
    dist (partialSum f (a+l)) (partialSum f (a+l+t)) ≤ min (t:ℝ) (cost+l+r) := by
  refine le_min (trivial_edge f unit _ _) ?_
  calc
    _ ≤ dist (partialSum f (a+l)) (partialSum f a) + dist (partialSum f a) (partialSum f (a+l+t+r)) +
        dist (partialSum f (a+l+t+r)) (partialSum f (a+l+t)) := dist_triangle4 _ _ _ _
    _ ≤ _ := by
      rw [dist_comm (partialSum f (a+l)) (partialSum f a),dist_comm (partialSum f (a+l+t+r)) (partialSum f (a+l+t))]
      linarith only [full,trivial_edge f unit a l,trivial_edge f unit (a+l+t) r]

/-- Disjoint certified pieces may be taken from different overlapping input
intervals. Each uncovered observation is charged exactly once. -/
theorem disjoint_cover {ι : Type*} [DecidableEq ι] (f : ℕ → E) (unit : ∀ i, ‖f i‖≤1)
    (J : Finset ι) (piece : ι → Finset ℕ) (cost : ι → ℝ) (N : ℕ)
    (inside : ∀ j∈J, piece j ⊆ range N)
    (disjoint : (J:Set ι).PairwiseDisjoint piece)
    (cert : ∀ j∈J, ‖∑ i∈piece j, f i‖ ≤ cost j) :
    ‖partialSum f N‖ ≤ (∑ j∈J, cost j) + ((range N \ J.biUnion piece).card:ℝ) := by
  have sub : J.biUnion piece ⊆ range N := by
    intro i hi; obtain ⟨j,hj,h⟩ := mem_biUnion.mp hi; exact inside j hj h
  unfold partialSum; rw [← sum_sdiff sub, add_comm, sum_biUnion disjoint]
  apply (norm_add_le ..).trans
  exact add_le_add ((norm_sum_le ..).trans (sum_le_sum cert))
    ((norm_sum_le ..).trans (by simpa using sum_le_sum (s:=range N \ J.biUnion piece) (fun i _ => unit i)))

/-- A path for each centered test interval bounds the extreme interval discrepancy.
The path may depend on the interval tested. -/
theorem discrepancy_of_paths {b N : ℕ} {x D : ℝ} (pos : 0<N)
    (cert : ∀ a e : ℝ, 0≤a → a<e → e≤1 → ∃ (v : ℕ → ℕ) (m : ℕ) (cost : ℕ → ℝ),
      v 0=0 ∧ v m=N ∧ (∑ i∈range m, cost i)≤D*N ∧
      ∀ i<m, let S := partialSum (Localized.centered (shift b x) a e)
             dist (S (v i)) (S (v (i+1)))≤cost i) : radixDiscrepancy b x N ≤ D := by
  unfold radixDiscrepancy
  refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
  rintro _ ⟨a,e,ha,ae,he,rfl⟩
  obtain ⟨v,m,cost,start,stop,bound,edges⟩ := cert a e ha ae he
  have h := (endpoint_path _ v cost m edges).trans bound
  rw [start,stop,← Nat.zero_add N,prefix_edge,Localized.centered_sum] at h
  simp only [Nat.zero_add] at h
  change |(IntervalFourier.count (shift b x) a e N:ℝ)/N-(e-a)| ≤ D
  have nr : (0:ℝ)<N := by exact_mod_cast pos
  rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_iff₀ nr]; simpa [mul_comm] using h

end NormalityChecker.Coverage
