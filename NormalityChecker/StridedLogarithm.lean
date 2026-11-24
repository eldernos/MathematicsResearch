module

public import NormalityChecker.PrimeCancellation
public import NormalityChecker.FirstFrequency
public import NormalityChecker.BBPDenominator

/-! A two-stride series for the binary logarithm and Fourier certificates for integer multiples. -/
@[expose] public section
open Finset
namespace NormalityChecker

/-- The two series have digit exponents 2j and 3j. -/
theorem logTwo_two_stride_series :
    HasSum (fun i : ℕ => 2*((1/4:ℝ)^(i+1)/(i+1))-(-1/8:ℝ)^(i+1)/(i+1)) (Real.log 2) := by
  have a := Real.hasSum_pow_div_log_of_abs_lt_one (x:=1/4) (by norm_num)
  have b := Real.hasSum_pow_div_log_of_abs_lt_one (x:=-1/8) (by norm_num)
  have eqn : 2*(-Real.log (1-1/4))-(-Real.log (1-(-1/8)))=Real.log 2 := by
    have v : (1-(-1/8:ℝ)) / (1-1/4)^2=2 := by norm_num
    rw [← v, Real.log_div (by norm_num) (by norm_num),Real.log_pow]; ring
  simpa only [eqn] using (a.mul_left 2).sub b

/-- Shift a truncated series by 2^N, retaining every exponent at most N. -/
def stridedPrefix (k N : ℕ) (w : ℕ → ℤ) : ℚ :=
  ∑ i∈range (N/k), ((w (i+1) * (2:ℤ)^(N-k*(i+1)) : ℤ):ℚ)/(i+1)

/-- Both actual components fit on the half-length common denominator. -/
def twoStridePrefix (N : ℕ) : ℚ :=
  stridedPrefix 2 N (fun _ => 2) + stridedPrefix 3 N (fun j => -(-1)^j)

private theorem den_div_nat (a : ℤ) {j : ℕ} : ((a:ℚ)/j).den ∣ j := by
  have h := Rat.den_dvd a (j:ℤ)
  rw [Rat.divInt_eq_div,Int.cast_natCast] at h
  exact_mod_cast h

private theorem prefix_den {k N M : ℕ} (len : N/k≤M) (w : ℕ → ℤ) :
    (stridedPrefix k N w).den ∣ Nat.lcmUpto M := by
  let term := fun i : ℕ => ((w (i+1)*(2:ℤ)^(N-k*(i+1)):ℤ):ℚ)/(i+1)
  have partial_den (j : ℕ) (hj : j≤M) : (∑ i∈range j, term i).den ∣ Nat.lcmUpto M := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ]
      apply (Rat.add_den_dvd_lcm ..).trans (Nat.lcm_dvd (ih (by omega)) ?_)
      have d := den_div_nat (w (j+1)*2^(N-k*(j+1))) (j:=j+1)
      exact (by simpa [term] using d : (term j).den ∣ j+1).trans (index_dvd_lcm (by omega) hj)
  exact partial_den _ len

theorem twoStridePrefix_den (N : ℕ) : (twoStridePrefix N).den ∣ Nat.lcmUpto (N/2) :=
  (Rat.add_den_dvd_lcm ..).trans (Nat.lcm_dvd (prefix_den le_rfl _) (prefix_den (by omega) _))

private theorem unshift_stride (k : ℕ) (N : ℕ) (w : ℕ → ℤ) :
    (stridedPrefix k N w:ℝ)/2^N =
      ∑ i∈range (N/k), (w (i+1):ℝ)*((1/(2:ℝ)^k)^(i+1)/(i+1)) := by
  unfold stridedPrefix
  push_cast
  rw [Finset.sum_div]
  apply sum_congr rfl; intro i hi
  have le : k*(i+1)≤N := by simpa only [mul_comm] using Nat.mul_le_of_le_div k _ _ (mem_range.mp hi)
  have pw : (2:ℝ)^(N-k*(i+1))*2^(k*(i+1))=2^N := by rw [← pow_add,Nat.sub_add_cancel le]
  rw [one_div_pow,← pow_mul,← pw]
  field_simp

private theorem normalized_limit :
    Filter.Tendsto (fun N => (twoStridePrefix N:ℝ)/2^N) Filter.atTop (nhds (Real.log 2)) := by
  have a := Real.hasSum_pow_div_log_of_abs_lt_one (x:=1/4) (by norm_num)
  have b := Real.hasSum_pow_div_log_of_abs_lt_one (x:=-1/8) (by norm_num)
  have eqn : 2*(-Real.log (1-1/4))-(-Real.log (1-(-1/8)))=Real.log 2 := by
    have v : (1-(-1/8:ℝ)) / (1-1/4)^2=2 := by norm_num
    rw [← v,Real.log_div (by norm_num) (by norm_num),Real.log_pow]; ring
  rw [← eqn]
  apply (((a.mul_left 2).tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop (by decide : 2≠0))).sub
    (b.tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop (by decide : 3≠0)))).congr
  intro N
  simp only [Function.comp_apply,twoStridePrefix,Rat.cast_add,add_div,unshift_stride 2,
    unshift_stride 3,Int.cast_ofNat,Int.cast_neg,Int.cast_pow,Int.cast_one]
  norm_num
  rw [sub_eq_add_neg,← sum_neg_distrib]
  congr 1
  rw [← sum_neg_distrib]; apply sum_congr rfl; intro i _
  rw [show (-(1/8):ℝ)=(-1)*(1/8) by ring,mul_pow]; ring

theorem stride_step (k : ℕ) (N : ℕ) (w : ℕ → ℤ) :
    stridedPrefix k (N+1) w = 2*stridedPrefix k N w +
      if k∣N+1 then (w ((N+1)/k):ℚ)/((N+1)/k:ℕ) else 0 := by
  let term (n i : ℕ) := ((w (i+1)*(2:ℤ)^(n-k*(i+1)):ℤ):ℚ)/(i+1)
  have prev : (∑ i∈range (N/k),term (N+1) i)=2*stridedPrefix k N w := by
    rw [stridedPrefix,mul_sum]; apply sum_congr rfl; intro i hi
    have le : k*(i+1)≤N := by simpa only [mul_comm] using Nat.mul_le_of_le_div k _ _ (mem_range.mp hi)
    dsimp [term]; rw [show N+1-k*(i+1)=N-k*(i+1)+1 by omega, pow_succ]; push_cast; ring
  change (∑ i∈range ((N+1)/k),term (N+1) i)=_
  split_ifs with dvd
  · have q := Nat.succ_div_of_dvd dvd
    rw [q,sum_range_succ,prev]
    congr 1
    have ident : k*(N/k+1)=N+1 := by rw [← q,Nat.mul_div_cancel' dvd]
    simp [term,ident]
  · rw [Nat.succ_div_of_not_dvd dvd,prev,add_zero]

private theorem stride_increment (N : ℕ) :
    0 ≤ twoStridePrefix (N+1)-2*twoStridePrefix N ∧
    twoStridePrefix (N+1)-2*twoStridePrefix N ≤ 4/((N:ℚ)+1) := by
  simp only [twoStridePrefix,stride_step 2,stride_step 3,
    Int.cast_ofNat,Int.cast_neg,Int.cast_pow,Int.cast_one]
  have np : (0:ℚ)<N+1 := by positivity
  have quotient {k : ℕ} (hk : 0<k) (hd : k∣N+1) :
      (((N+1)/k:ℕ):ℚ)=((N:ℚ)+1)/k := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hk.ne')).mpr
    exact_mod_cast Nat.div_mul_cancel hd
  by_cases h₂ : 2∣N+1 <;> by_cases h₃ : 3∣N+1 <;> simp only [h₂,h₃,ite_true,ite_false]
  · have even : Even ((N+1)/3) := ⟨(N+1)/6,by omega⟩
    rw [quotient (by decide) h₂,quotient (by decide) h₃,even.neg_one_pow]; constructor <;> field_simp <;> norm_num <;> ring_nf <;> linarith
  · rw [quotient (by decide) h₂]; constructor <;> field_simp <;> norm_num <;> ring_nf <;> linarith
  · have odd : Odd ((N+1)/3) := ⟨(N+1)/6,by omega⟩
    rw [quotient (by decide) h₃,odd.neg_one_pow]; constructor <;> field_simp <;> norm_num <;> ring_nf <;> linarith
  · constructor <;> field_simp <;> norm_num <;> ring_nf <;> linarith

/-- The smaller-denominator prefix follows every true binary shift, with an explicit
one-sided error. -/
theorem twoStridePrefix_tail (N : ℕ) :
    0≤(2:ℝ)^N*Real.log 2-twoStridePrefix N ∧
    (2:ℝ)^N*Real.log 2-twoStridePrefix N≤4/((N:ℝ)+1) := by
  let f (j : ℕ) := (twoStridePrefix (N+j):ℝ)/2^j-(twoStridePrefix N:ℝ)
  have all (j : ℕ) : 0≤f j ∧ f j≤(4/((N:ℝ)+1))*(1-(2:ℝ)⁻¹^j) := by
    induction j with
    | zero => simp [f]
    | succ j ih =>
      let v := (twoStridePrefix (N+j+1):ℝ)-2*(twoStridePrefix (N+j):ℝ)
      have lower : 0≤v := by dsimp [v]; exact_mod_cast (stride_increment (N+j)).1
      have upper : v≤4/((N:ℝ)+j+1) := by
        have bound := (Rat.cast_le (K:=ℝ)).mpr (stride_increment (N+j)).2
        simpa [v] using bound
      have relax : v≤4/((N:ℝ)+1) := upper.trans (by gcongr; linarith [Nat.cast_nonneg (α:=ℝ) j])
      have step : f (j+1)=f j+v/2^(j+1) := by
        dsimp [f,v]; rw [show N+(j+1)=N+j+1 by omega]; simp only [pow_succ]; field_simp; ring_nf
      rw [step]; refine ⟨add_nonneg ih.1 (div_nonneg lower (by positivity)),?_⟩
      apply (add_le_add ih.2 (div_le_div_of_nonneg_right relax (by positivity : (0:ℝ)≤2^(j+1)))).trans_eq
      rw [inv_pow,inv_pow,pow_succ]; ring
  have lim : Filter.Tendsto f Filter.atTop (nhds ((2:ℝ)^N*Real.log 2-twoStridePrefix N)) := by
    have grow : Filter.Tendsto (fun j : ℕ => N+j) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr (fun k => ⟨k,fun j h => by omega⟩)
    apply (((normalized_limit.comp grow).const_mul ((2:ℝ)^N)).sub_const (twoStridePrefix N:ℝ)).congr
    intro j
    change 2^N*((twoStridePrefix (N+j):ℝ)/2^(N+j))-_ = _
    dsimp [f]; rw [pow_add]; field_simp
  exact ⟨ge_of_tendsto' lim (fun j => (all j).1),le_of_tendsto' lim (fun j =>
    (all j).2.trans (mul_le_of_le_one_right (by positivity) (by linarith [pow_nonneg (by norm_num : (0:ℝ)≤2⁻¹) j])))⟩

/-- At these primes exactly one term of the two-stride prefix has a pole. -/
theorem twoStridePrefix_survival {p N : ℕ} (hp : p.Prime) (odd : 2<p)
    (lo : 2*p≤N) (hi : N<3*p) : p∣(twoStridePrefix N).den := by
  let term := fun i : ℕ => ((2*(2:ℤ)^(N-2*(i+1)) : ℤ):ℚ)/(i+1)
  have single : p∣(stridedPrefix 2 N (fun _ => 2)).den := by
    apply unique_prime_denominator hp (range (N/2)) term (a:=p-1) (mem_range.mpr (by omega))
    · have idx : p-1+1=p := by omega
      let a : ℤ := 2*2^(N-2*p)
      have unit : ¬p∣2 := fun h => (Nat.le_of_dvd (by decide) h).not_gt odd
      have cop : p.Coprime a.natAbs := hp.coprime_iff_not_dvd.mpr (by
        simp only [a, Int.natAbs_mul, Int.natAbs_pow, show (2:ℤ).natAbs=2 by decide, hp.dvd_mul]
        exact not_or.mpr ⟨unit,fun h => unit (hp.dvd_of_dvd_pow h)⟩)
      have repr : term (p-1)=(a:ℚ)/(p:ℤ) := by
        dsimp [term,a]; rw [idx]; push_cast [Nat.cast_sub (by omega : 1≤p)]; ring
      have ed := Rat.den_div_eq_of_coprime (a:=a) (b:=(p:ℤ)) (by exact_mod_cast hp.pos) (by simpa using cop.symm)
      rw [repr, show ((a:ℚ)/(p:ℤ)).den = p by exact_mod_cast ed]
    · intro i mem ne dvd
      have ij : i<N/2 := mem_range.mp mem
      have d := den_div_nat (2*(2:ℤ)^(N-2*(i+1))) (j:=i+1)
      obtain ⟨k,hk⟩ := dvd.trans (by simpa [term] using d : (term i).den∣i+1)
      rcases k with _|_|k
      · simp at hk
      · simp at hk; omega
      · have twice := Nat.mul_le_mul_left p (show 2≤k+1+1 by omega)
        omega
  have no : ¬p∣(stridedPrefix 3 N (fun j => -(-1)^j)).den := by
    intro h
    have ld := h.trans (prefix_den (M:=N/3) le_rfl _)
    rw [hp.dvd_iff_one_le_factorization (Nat.lcmUpto_ne_zero _),
      Nat.factorization_lcmUpto _ hp,Nat.log_of_lt (by omega : N/3<p)] at ld
    omega
  have eqn : stridedPrefix 2 N (fun _ => 2) =
      twoStridePrefix N-stridedPrefix 3 N (fun j => -(-1)^j) := by simp [twoStridePrefix]
  rw [eqn] at single
  exact (hp.dvd_mul.mp (single.trans (Rat.sub_den_dvd ..))).resolve_right no

/-- First-frequency escape at an integer multiple gives a quantitative lower
bound on first-frequency escape at the original point. -/
theorem cosineEscape_multiple (m : ℕ) (u : ℝ) :
    cosineEscape (m*u) ≤ (m:ℝ)^2*cosineEscape u := by
  have s := Real.abs_sin_sum_le (range m) (fun _ => Real.pi*u)
  simp only [sum_const,card_range,nsmul_eq_mul] at s
  have h (v : ℝ) : cosineEscape v = 2*Real.sin (Real.pi*v)^2 := by
    unfold cosineEscape
    rw [mul_assoc,Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq (Real.pi*v)]
  rw [h,h,show Real.pi*((m:ℝ)*u) = m*(Real.pi*u) by ring]
  have sq := pow_le_pow_left₀ (abs_nonneg _) s 2
  rw [sq_abs,mul_pow,sq_abs] at sq
  nlinarith

end NormalityChecker
