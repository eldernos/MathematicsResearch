module

public import NormalityChecker.ProductThreeFiveResidues

/-! Removing the dependence of each binary factor on its own prime index
at full nominal precision, including partially occupied rows and columns. -/

@[expose] public section

open Finset
namespace NormalityChecker.ProductThreeFive

/-- After multiplication by a common binary unit, a term on the i-th row
has the same binary weight as every other row, modulo the full shell power. -/
theorem freeze_prime_layer {p i K u n : ℕ} (hp : p.Prime) (odd : Nat.Coprime 2 p)
    (hi : 0 < i) (hK : i ≤ K) (activeTerm : p^i + u ≤ n) :
    2^(p^K) * (2^(n-(p^i+u))*p^(K-i)) ≡
      2^(n-u)*p^(K-i) [MOD p^K] := by
  have split : p^K = p^i * p^(K-i) := by rw [← pow_add, Nat.add_sub_of_le hK]
  have gap : p^K - p^i = p^i * (p^(K-i)-1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← split]
  have dv : (p^i).totient ∣ p^K-p^i := by
    rw [Nat.totient_prime_pow hp hi, gap]
    exact mul_dvd_mul (pow_dvd_pow _ (by omega)) (Nat.sub_one_dvd_pow_sub_one _ _)
  obtain ⟨t, ht⟩ := dv
  have unit : 2^(p^K-p^i) ≡ 1 [MOD p^i] := by
    rw [ht, pow_mul]
    simpa using (Nat.ModEq.pow_totient (odd.pow_right i)).pow t
  have mono := Nat.pow_le_pow_right hp.pos hK
  have exps : p^K+(n-(p^i+u)) = (p^K-p^i)+(n-u) := by omega
  have base : 2^(p^K)*2^(n-(p^i+u)) ≡ 2^(n-u) [MOD p^i] := by
    rw [← pow_add, exps, pow_add]
    simpa using unit.mul_right (2^(n-u))
  simpa only [← mul_assoc, ← pow_add, Nat.add_sub_of_le hK] using base.mul_right' (p^(K-i))

private lemma modEq_sum {α : Type*} {m : ℕ} {f g : α → ℕ} (s : Finset α)
    (h : ∀ i ∈ s, f i ≡ g i [MOD m]) :
    (∑ i ∈ s, f i) ≡ ∑ i ∈ s, g i [MOD m] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self ..)).add (ih (fun j hj => h _ (mem_insert_of_mem hj)))

/-- Full precision reduction at three. Opposite endpoints remain those of
the actual active set. -/
theorem freeze_ternary (n : ℕ) :
    2^(3^Nat.log 3 n)*commonNum n ≡
      ∑ v ∈ active n, 2^(n-5^(v.2+1))*3^(Nat.log 3 n-(v.1+1))*5^(Nat.log 5 n-(v.2+1))
      [MOD 3^Nat.log 3 n] := by
  rw [commonNum, mul_sum]
  apply modEq_sum
  intro v hv
  obtain ⟨hi, _⟩ := mem_product.mp (mem_filter.mp hv).1
  simpa only [← mul_assoc, location] using
    (freeze_prime_layer Nat.prime_three (by decide) (Nat.zero_lt_succ v.1)
      (mem_range.mp hi) (mem_active.mp hv)).mul_right (5^(Nat.log 5 n-(v.2+1)))

/-- Full precision reduction at five with the same normalization convention. -/
theorem freeze_quinary (n : ℕ) :
    2^(5^Nat.log 5 n)*commonNum n ≡
      ∑ v ∈ active n, 2^(n-3^(v.1+1))*5^(Nat.log 5 n-(v.2+1))*3^(Nat.log 3 n-(v.1+1))
      [MOD 5^Nat.log 5 n] := by
  rw [commonNum, mul_sum]
  apply modEq_sum
  intro v hv
  obtain ⟨_, hj⟩ := mem_product.mp (mem_filter.mp hv).1
  have incl := mem_active.mp hv
  change 3^(v.1+1)+5^(v.2+1) ≤ n at incl
  rw [Nat.add_comm] at incl
  simpa only [location, Nat.add_comm (5^(v.2+1)), mul_assoc, mul_comm, mul_left_comm] using
    (freeze_prime_layer Nat.prime_five (by decide) (Nat.zero_lt_succ v.2)
      (mem_range.mp hj) incl).mul_right (3^(Nat.log 3 n-(v.1+1)))

private lemma layer_geometric {p K t : ℕ} (hp : 0 < p) (ht : t ≤ K) :
    (p-1)*(∑ i ∈ range t, p^(K-(i+1))) + p^(K-t) = p^K := by
  induction t with
  | zero => simp
  | succ t ih =>
    have step : p^(K-t) = p^(K-(t+1))*p := by
      rw [← pow_succ, show K-(t+1)+1 = K-t by omega]
    rw [sum_range_succ, Nat.mul_add]
    rw [← ih (by omega), step]
    have hp' : p-1+1=p := by omega
    nlinarith only [congrArg (fun x : ℕ => x * p^(K-(t+1))) hp']

/-- Sum a full binary-weight-free fibre. The opposite endpoint enters only
as the number of missing top layers, including an empty fibre. -/
theorem collapse_fibres (p q n L : ℕ) (hp : 1 < p) (W : ℕ → ℕ) :
    let K := Nat.log p n
    (p-1)*(∑ j ∈ range L, ∑ i ∈ range K, if p^(i+1)+q^(j+1) ≤ n
      then p^(K-(i+1))*W j else 0) +
      ∑ j ∈ range L, p^(K-Nat.log p (n-q^(j+1)))*W j = p^K * ∑ j ∈ range L, W j := by
  dsimp only
  rw [mul_sum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  let u := q^(j+1)
  let t := Nat.log p (n-u)
  have ht : t ≤ Nat.log p n := Nat.log_mono_right (Nat.sub_le ..)
  have fibre : (range (Nat.log p n)).filter (fun i => p^(i+1)+u ≤ n) = range t := by
    ext i
    simp only [mem_filter, mem_range]
    by_cases e : n-u = 0
    · have t0 : t=0 := by simp [t,e]
      have := pow_pos (by omega : 0<p) (i+1)
      omega
    · have eq := Nat.le_log_iff_pow_le (x:=i+1) hp e
      change i+1 ≤ t ↔ p^(i+1) ≤ n-u at eq
      omega
  change (p-1)*(∑ i ∈ range (Nat.log p n), if p^(i+1)+u ≤ n
    then p^(Nat.log p n-(i+1))*W j else 0) + p^(Nat.log p n-t)*W j = _
  rw [← sum_filter, fibre, ← sum_mul, ← mul_assoc, ← add_mul, layer_geometric (by omega) ht]

/-- One-dimensional numerator after summation of the geometric fibres. -/
def endpointNum (p q n : ℕ) : ℕ := ∑ j ∈ range (Nat.log q n),
  p^(Nat.log p n-Nat.log p (n-q^(j+1))) * (2^(n-q^(j+1))*q^(Nat.log q n-(j+1)))

/-- The actual one-dimensional numerator has only three weights: one on
complete fibres, p on unfinished interior fibres, and the endpoint power on
the last fibre. A zero-length top row or column is allowed. -/
theorem endpoint_num_shape {p q n : ℕ} (hp : 1 < p) (hq : 1 < q) (hn : p ≤ n) :
    let H := Nat.log p n
    let m := Nat.log q n
    let J := Nat.log q (n-p^H)
    endpointNum p q n = ∑ j ∈ range m,
      (if j+1 ≤ J then 1 else if j+1 < m then p else p^(H-Nat.log p (n-q^m))) *
        (2^(n-q^(j+1))*q^(m-(j+1))) := by
  dsimp only [endpointNum]
  apply sum_congr rfl
  intro j hj
  congr 1
  let H := Nat.log p n
  let m := Nat.log q n
  let Q := q^(j+1)
  have npos : n ≠ 0 := by omega
  have pcap : p^H ≤ n := Nat.pow_log_le_self _ npos
  have jcap : j+1 ≤ m := mem_range.mp hj
  have qpos : 0 < Q := pow_pos (by omega) _
  have inRow : j+1 ≤ Nat.log q (n-p^H) ↔ p^H+Q ≤ n := by
    by_cases e : n-p^H = 0
    · rw [e, Nat.log_zero_right]; omega
    · rw [Nat.le_log_iff_pow_le hq e]; dsimp [Q]; omega
  change p^(H-Nat.log p (n-Q)) =
    if j+1 ≤ Nat.log q (n-p^H) then 1 else if j+1 < m then p else p^(H-Nat.log p (n-q^m))
  simp only [inRow]
  split_ifs with full interior
  · have h : H ≤ Nat.log p (n-Q) := Nat.le_log_of_pow_le hp (by omega)
    rw [Nat.sub_eq_zero_of_le h, pow_zero]
  · have hH : 1 ≤ H := Nat.le_log_of_pow_le hp (by simpa using hn)
    obtain ⟨k, hk⟩ : ∃ k, H=k+1 := ⟨H-1, by omega⟩
    have qnext := (Nat.pow_le_pow_right (by omega : 0<q) interior).trans (Nat.pow_log_le_self q npos)
    change q^((j+1)+1) ≤ n at qnext
    rw [pow_succ] at qnext
    change Q*q ≤ n at qnext
    rw [hk, pow_succ] at pcap
    have qsmall : Q*2 ≤ n := (Nat.mul_le_mul_left Q hq).trans qnext
    have psmall : p^k*2 ≤ n := (Nat.mul_le_mul_left _ hp).trans pcap
    have lower : p^k ≤ n-Q := by omega
    have upper : n-Q < p^(k+1) := by
      rw [← hk]; have pos := pow_pos (by omega : 0<p) H; omega
    rw [Nat.log_eq_of_pow_le_of_lt_pow lower upper, hk, Nat.add_sub_cancel_left, pow_one]
  · dsimp only [Q]; rw [show j+1=m by omega]

/-- The compressed ternary numerator differs from the actual cleared prefix
by an explicit unit, modulo the entire nominal denominator power of three. -/
theorem ternary_endpoint_num (n : ℕ) :
    3^Nat.log 3 n ∣ 2*(2^(3^Nat.log 3 n)*commonNum n) + endpointNum 3 5 n := by
  have h := ((freeze_ternary n).mul_left 2).add_right (endpointNum 3 5 n)
  have coll := collapse_fibres 3 5 n (Nat.log 5 n) (by decide)
    (fun j => 2^(n-5^(j+1))*5^(Nat.log 5 n-(j+1)))
  dsimp only at coll
  rw [active, sum_filter, sum_product, sum_comm] at h
  apply Nat.modEq_zero_iff_dvd.mp
  apply h.trans
  apply Nat.modEq_zero_iff_dvd.mpr
  refine ⟨∑ j ∈ range (Nat.log 5 n), 2^(n-5^(j+1))*5^(Nat.log 5 n-(j+1)), ?_⟩
  simpa only [location, endpointNum, mul_left_comm, mul_comm, mul_assoc] using coll

/-- The corresponding full-precision congruence at five. -/
theorem quinary_endpoint_num (n : ℕ) :
    5^Nat.log 5 n ∣ 4*(2^(5^Nat.log 5 n)*commonNum n) + endpointNum 5 3 n := by
  have h := ((freeze_quinary n).mul_left 4).add_right (endpointNum 5 3 n)
  have coll := collapse_fibres 5 3 n (Nat.log 3 n) (by decide)
    (fun i => 2^(n-3^(i+1))*3^(Nat.log 3 n-(i+1)))
  dsimp only at coll
  rw [active, sum_filter, sum_product] at h
  apply Nat.modEq_zero_iff_dvd.mp
  apply h.trans
  apply Nat.modEq_zero_iff_dvd.mpr
  refine ⟨∑ j ∈ range (Nat.log 3 n), 2^(n-3^(j+1))*3^(Nat.log 3 n-(j+1)), ?_⟩
  simpa only [location, endpointNum, Nat.add_comm (3^_), mul_left_comm, mul_comm, mul_assoc] using coll

/-- The entire rectangle below both top indices is active. -/
theorem interior_active {n : ℕ} {v : ℕ × ℕ}
    (hi : v.1+1 < Nat.log 3 n) (hj : v.2+1 < Nat.log 5 n) : v ∈ active n := by
  have hn : n ≠ 0 := by rintro rfl; simp at hi
  have a := (Nat.pow_le_pow_right (by decide : 0<3) hi).trans (Nat.pow_log_le_self 3 hn)
  have b := (Nat.pow_le_pow_right (by decide : 0<5) hj).trans (Nat.pow_log_le_self 5 hn)
  rw [pow_succ] at a b
  apply mem_active.mpr
  change 3^(v.1+1)+5^(v.2+1) ≤ n
  omega


/-- The opposite-axis summand with its binary exponent reduced by Euler's
totient. For the unit moduli below it represents q⁻ʲ 2⁻ᵠʲ. -/
def crossWeight (M q j : ℕ) : ZMod M :=
  ((q:ZMod M)^j * 2^(q^j % M.totient))^(M.totient-1)

def partialCross (M q : ℕ) : ℕ → ZMod M
  | 0 => 0
  | j+1 => partialCross M q j + crossWeight M q (j+1)

/-- At the top-failure lengths m = d+1+u*z, the positive endpoint
numerator has d+1 missing columns and e+1 missing rows. -/
def cornerCross (M p q d e u z : ℕ) : ZMod M :=
  let J := u*z
  partialCross M q J + p*(partialCross M q (d+J) - partialCross M q J) +
    (p:ZMod M)^(e+1)*crossWeight M q (d+1+J)

private lemma weight_period {M q T : ℕ} (value : (q:ZMod M)^T = 1)
    (exponent : q^T ≡ 1 [MOD M.totient]) (j : ℕ) :
    crossWeight M q (j+T) = crossWeight M q j := by
  have ex := exponent.mul_left (q^j)
  simp only [mul_one, ← pow_add] at ex
  change q^(j+T) % M.totient = q^j % M.totient at ex
  simp only [crossWeight, pow_add (q:ZMod M) j T, value, mul_one, ex]

private lemma reduce_period {α : Type*} {f : ℕ → α} {T : ℕ} (hT : 0<T)
    (period : ∀ j, f (j+T) = f j) (j : ℕ) : f j = f (j%T) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases small : j<T
    · rw [Nat.mod_eq_of_lt small]
    · obtain ⟨k, rfl⟩ : ∃ k, j=k+T := ⟨j-T, by omega⟩
      rw [period, ih k (by omega), Nat.add_mod_right]

private lemma partial_period {M q T : ℕ} (period : ∀ j, crossWeight M q (j+T)=crossWeight M q j)
    (zeroSum : partialCross M q T = 0) (j : ℕ) : partialCross M q (j+T) = partialCross M q j := by
  induction j with
  | zero => simpa [partialCross] using zeroSum
  | succ j ih =>
    have shift (k : ℕ) : partialCross M q (k+1) = partialCross M q k + crossWeight M q (k+1) :=
      rfl
    rw [show j+1+T = (j+T)+1 by omega, shift, ih, shift j, show j+T+1 = (j+1)+T by omega, period]

private lemma corner_lift_two {M p q T u c : ℕ} (positive : 0<T)
    (value : (q:ZMod M)^T = 1) (exponent : q^T ≡ 1 [MOD M.totient])
    (zeroSum : partialCross M q T = 0)
    (table : ∀ i : Fin T, ((p:ZMod M)*partialCross M q ((i:ℕ)+u) = p*partialCross M q i) ∧
      ((p:ZMod M)*crossWeight M q ((i:ℕ)+u) = p*crossWeight M q i) ∧
      (u ∣ (i:ℕ) → partialCross M q ((i:ℕ)+u) = partialCross M q i + c))
    (div : u ∣ T) (d e z : ℕ) :
    cornerCross M p q d e u z = (z:ZMod M)*c + cornerCross M p q d e u 0 := by
  have w := weight_period value exponent
  have f := partial_period w zeroSum
  have prog (g : ℕ → ZMod M) (per : ∀ j, g (j+T) = g j) (j : ℕ) :
      g (j+u) = g (j%T+u) := by
    rw [reduce_period positive per (j+u), reduce_period positive per (j%T+u),
      Nat.mod_add_mod]
  have step (j : ℕ) := table ⟨j%T,Nat.mod_lt _ positive⟩
  have ps (j : ℕ) : (p:ZMod M)*partialCross M q (j+u) = p*partialCross M q j := by
    rw [prog (partialCross M q) f, reduce_period positive f j]; exact (step j).1
  have ws (j : ℕ) : (p:ZMod M)*crossWeight M q (j+u) = p*crossWeight M q j := by
    rw [prog (crossWeight M q) w, reduce_period positive w j]; exact (step j).2.1
  have main (z : ℕ) : partialCross M q (u*z+u) = partialCross M q (u*z) + c := by
    rw [prog (partialCross M q) f, reduce_period positive f (u*z)]
    exact (step _).2.2 ((Nat.dvd_mod_iff div).mpr (dvd_mul_right ..))
  induction z with
  | zero => simp
  | succ z ih =>
    rw [Nat.cast_succ, add_mul, one_mul, add_assoc, add_comm (c:ZMod M), ← add_assoc, ← ih]
    unfold cornerCross
    simp only [Nat.mul_succ, ← Nat.add_assoc, mul_sub, pow_succ, mul_assoc, ps, ws]
    rw [main]
    ring

/-- The ternary branch advances by 6 per shell-index step modulo 9 for every
pair of positive deficits. In particular, exactly one of three lifts fails. -/
theorem ternary_corner_lift_two (d e z : ℕ) :
    cornerCross 9 3 5 d e 2 z = (z:ZMod 9)*6 + cornerCross 9 3 5 d e 2 0 := by
  exact corner_lift_two (T:=6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) d e z

/-- The quinary branch advances by 15 per shell-index step modulo 25 for every
pair of positive deficits. Exactly one of five lifts fails. -/
theorem quinary_corner_lift_two (d e z : ℕ) :
    cornerCross 25 5 3 d e 4 z = (z:ZMod 25)*15 + cornerCross 25 5 3 d e 4 0 := by
  exact corner_lift_two (T:=20) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) d e z

end NormalityChecker.ProductThreeFive
