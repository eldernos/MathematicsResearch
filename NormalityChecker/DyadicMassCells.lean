module

public import NormalityChecker.StonehamPolynomialPrefix
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff

/-! A finite polynomial for the jumps of a symmetric binary cut. Coefficients
are geometric weights of ordered tuples, reduced at a prescribed precision. -/
@[expose] public section
open Finset Polynomial
namespace NormalityChecker.DyadicMassCells
open StonehamPolynomial

/-- A grid coordinate is an integer multiple of the finest retained dyadic step. -/
def gridPosition {d : ℕ} (D : ℕ) (v : Vector d) : ℕ := ∑ i, 2^(D-v i)

/-- Each monomial of the single-axis polynomial records a position and a weight. -/
noncomputable def axisPoly (D L : ℕ) : (ZMod (2^L))[X] :=
  ∑ j ∈ range L, monomial (2^(D-j)) (2^j)

private theorem prod_monomials {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (x : ι → ℕ) (w : ι → R) :
    ∏ i ∈ s, monomial (x i) (w i) = monomial (∑ i ∈ s, x i) (∏ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih, monomial_mul_monomial]

/-- Taking the power counts every ordered tuple with its multiplicity. -/
theorem power_expansion (D L d : ℕ) :
    axisPoly D L ^ d =
      ∑ v ∈ box d L, monomial (gridPosition D v) ((2 : ZMod (2^L)) ^ weight v) := by
  classical
  rw [← show (∏ _ : Fin d, axisPoly D L) = axisPoly D L ^ d by simp]
  rw [axisPoly, prod_univ_sum]
  apply sum_congr rfl
  intro v _
  rw [prod_monomials, prod_pow_eq_pow_sum]
  rfl

/-- Sum the coefficients up to and including the cutoff. -/
noncomputable def through {R : Type*} [Semiring R] (q : ℕ) (P : R[X]) : R :=
  ∑ x ∈ range (q+1), P.coeff x

private theorem through_monomial {R : Type*} [Semiring R] (q x : ℕ) (a : R) :
    through q (monomial x a) = if x ≤ q then a else 0 := by
  simp [through, coeff_monomial, Finsupp.single_apply, sum_ite_eq]

theorem grid_mass (D L d q : ℕ) :
    (mass 2 L {v : Vector d | gridPosition D v ≤ q} : ZMod (2^L)) =
      through q (axisPoly D L ^ d) := by
  classical
  rw [power_expansion, through, mass, weightedMass, sum_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat,
    finsetSum_coeff]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [← through, through_monomial]
  simp [stretch, weight]

/- A sparse list implementation makes the following closed computation reduce
inside the kernel. No decidable equality on polynomials or native oracle is used. -/
private abbrev Terms := List (ℕ × ℕ)

private noncomputable def decode (N : ℕ) : Terms → (ZMod N)[X]
  | [] => 0
  | (x,a) :: xs => monomial x (a : ZMod N) + decode N xs

private def insertTerm (N x a : ℕ) : Terms → Terms
  | [] => if a % N = 0 then [] else [(x, a % N)]
  | (y,b) :: xs =>
    if x = y then
      if (a+b) % N = 0 then xs else (x,(a+b)%N) :: xs
    else if x < y then
      if a % N = 0 then (y,b) :: xs else (x,a%N) :: (y,b) :: xs
    else (y,b) :: insertTerm N x a xs

private theorem decode_insert (N x a : ℕ) (xs : Terms) :
    decode N (insertTerm N x a xs) = monomial x (a : ZMod N) + decode N xs := by
  have clear (b : ℕ) (h : b % N = 0) : (b : ZMod N) = 0 := by
    rw [← ZMod.natCast_mod b N, h]; simp
  induction xs with
  | nil =>
    simp only [insertTerm]
    split_ifs with h <;> simp [decode, *]
  | cons p xs ih =>
    obtain ⟨y,b⟩ := p
    simp only [insertTerm]
    split_ifs with h z lt z' <;>
      simp_all [decode, ← map_add, add_comm, add_left_comm]
    exact_mod_cast clear (a+b) z

private def addRow (N x a : ℕ) (ys acc : Terms) : Terms :=
  ys.foldr (fun t tail => insertTerm N (x+t.1) (a*t.2) tail) acc

private theorem decode_row (N x a : ℕ) (ys acc : Terms) :
    decode N (addRow N x a ys acc) =
      monomial x (a : ZMod N) * decode N ys + decode N acc := by
  induction ys with
  | nil => simp [addRow, decode]
  | cons p ys ih =>
    obtain ⟨y,b⟩ := p
    change decode N (insertTerm N (x+y) (a*b) (addRow N x a ys acc)) = _
    rw [decode_insert, ih, decode, mul_add, monomial_mul_monomial, Nat.cast_mul, add_assoc]

private def multiply (N : ℕ) (xs ys : Terms) : Terms :=
  xs.foldr (fun t acc => addRow N t.1 t.2 ys acc) []

private theorem decode_multiply (N : ℕ) (xs ys : Terms) :
    decode N (multiply N xs ys) = decode N xs * decode N ys := by
  induction xs with
  | nil => simp [multiply, decode]
  | cons p xs ih =>
    obtain ⟨x,a⟩ := p
    change decode N (addRow N x a ys (multiply N xs ys)) = _
    rw [decode_row, ih, decode, add_mul]

private def letters (D : ℕ) : ℕ → Terms
  | 0 => []
  | j+1 => (2^(D-j),2^j) :: letters D j

private theorem decode_letters (N D j : ℕ) :
    decode N (letters D j) = ∑ i ∈ range j, monomial (2^(D-i)) ((2:ZMod N)^i) := by
  induction j with
  | zero => simp [decode, letters]
  | succ j ih => simp [letters, decode, ih, sum_range_succ, add_comm]

private def below (H : ℕ) (xs : Terms) := xs.filter (fun t => t.1 < H)

private lemma through_cons (N q x a : ℕ) (xs : Terms) :
    through q (decode N ((x,a) :: xs)) =
      (if x ≤ q then (a : ZMod N) else 0) + through q (decode N xs) := by
  rw [decode, ← through_monomial]
  simp [through, sum_add_distrib]

private lemma through_below (N H q : ℕ) (hq : q < H) (xs : Terms) :
    through q (decode N (below H xs)) = through q (decode N xs) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨x,a⟩ := p
    by_cases h : x < H
    · simp [below, h, through_cons] at ih ⊢
      exact ih
    · have no : ¬x ≤ q := by omega
      simpa [below, h, through_cons, no] using ih

/-- The four quartic residues on the internal grid used by the positive-index
shift. Its mesh is 1/2048 of the physical shell. -/
theorem quartic_grid_profile (q : ℕ) (lo : 2048 ≤ q) (hi : q < 4096) :
    through q (axisPoly 12 13 ^ 4) =
      (if q < 3072 then 4096 else if q < 3328 then 2048 else
       if q < 3584 then 6144 else 4096 : ZMod (2^13)) := by
  let letters' := letters 12 13
  let square := multiply (2^13) letters' letters'
  let fourth := multiply (2^13) square square
  have expansion : decode (2^13) fourth = axisPoly 12 13 ^ 4 := by
    simp only [fourth, square, letters', decode_multiply, decode_letters, axisPoly]
    ring
  have table : below 4096 fourth = [(2048,4096),(3072,6144),(3328,4096),(3584,6144)] := by
    decide +kernel
  rw [← expansion, ← through_below _ _ _ hi, table]
  simp only [through_cons, ite_eq_left lo]
  have empty : through q (decode (2^13) []) = 0 := by simp [decode, through]
  rw [empty]
  split_ifs <;> first | omega | decide

end NormalityChecker.DyadicMassCells
