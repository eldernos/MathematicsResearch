module

public import NormalityChecker.DominatedPerturbation
public import NormalityChecker.IndexedExpansion
public import NormalityChecker.RadixTelescoping
public import NormalityChecker.StonehamComponents

/-! Polynomial schedules added to the binary Stoneham component. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.PolynomialInsertions

structure Schedule where
  g : ℕ → ℕ
  e : ℕ → ℕ
  mono : StrictMono g
  unbounded : ∀ J : ℕ, ∃ N : ℕ, ∀ i, N≤g i → J≤e i

namespace Schedule
variable (s : Schedule)
def active (n : ℕ) := (range (n+1)).filter (fun i => s.g i≤n)
lemma mem {i n} : i∈s.active n ↔ s.g i≤n := by
  simp only [active,mem_filter,mem_range]; exact ⟨And.right,fun h => ⟨Nat.lt_succ_of_le ((s.mono.id_le i).trans h),h⟩⟩
def coeff (i : ℕ) := 1/(3:ℚ)^(s.e i)
def pre (n : ℕ) := (2:ℚ)^n*∑ i∈s.active n,s.coeff i/(2:ℚ)^(s.g i)
noncomputable def value := ∑' i, (s.coeff i:ℝ)/(2:ℝ)^(s.g i)
lemma tail : Tendsto (fun n => (2:ℝ)^n*s.value-(s.pre n:ℝ)) atTop (𝓝 0) := by
  apply indexed_shift_error (b:=2) (by decide) s.g s.mono.injective s.coeff (fun _ => by unfold coeff; positivity)
    (fun i => (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))) _ _ (fun _ _ => s.mem)
  intro ε pos
  obtain ⟨J,hJ⟩ := exists_nat_gt (1/ε)
  obtain ⟨N,hN⟩ := s.unbounded J
  refine ⟨N,fun i hi => ?_⟩
  dsimp [coeff]; push_cast; rw [div_le_iff₀ (by positivity)]
  have cap : J≤3^(s.e i) := (hN i hi).trans (Nat.lt_pow_self (by decide : 2≤3)).le
  have rc : (J:ℝ)≤(3:ℝ)^(s.e i) := by exact_mod_cast cap
  linarith only [(div_lt_iff₀ pos).mp (hJ.trans_le rc)]
lemma follows {n i : ℕ} (free : ∀ v, n<s.g v → n+i<s.g v) : s.pre (n+i)=(2:ℚ)^i*s.pre n := by
  have eqn : s.active (n+i)=s.active n := by
    ext v; rw [mem,mem]; constructor
    · intro h; exact le_of_not_gt (fun hh => (free v hh).not_ge h)
    · omega
  simp only [pre,eqn,pow_add]; ring
lemma denominator {n J : ℕ} (cap : ∀ i∈s.active n,s.e i≤J) : (s.pre n).den∣3^J := by
  let z (i : ℕ) := 2^(n-s.g i)*3^(J-s.e i)
  apply (reduced_info (S:=∑ i∈s.active n,z i) (by positivity : 0<3^J) _).1
  simp only [pre,Nat.cast_sum,Nat.cast_pow,mul_sum]; apply sum_congr rfl; intro i hi
  have gn := s.mem.mp hi; have ej := cap i hi
  dsimp [z,coeff]; push_cast; rw [pow_sub₀ _ (by norm_num : (2:ℚ)≠0) gn,pow_sub₀ _ (by norm_num : (3:ℚ)≠0) ej]; ring
end Schedule

private def stone : Schedule := ⟨fun i => 3^i,id,pow_right_strictMono₀ (by decide),fun J =>
  ⟨3^J,fun i hi => (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp hi⟩⟩
private def poly (r : ℕ) (hr : 0<r) : Schedule where
  g i := (i+1)^r
  e i := Nat.log 3 (i+1)
  mono := fun i j h => Nat.pow_lt_pow_left (by omega) hr.ne'
  unbounded J := ⟨(3^J)^r,fun _ h => Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_iff_left hr.ne').mp h)⟩

private lemma stone_norm {n : ℕ} (pos : 0<n) : padicNorm 3 (stone.pre n)=(3:ℚ)^(Nat.log 3 n) := by
  let k := Nat.log 3 n
  let w (i : ℕ) := stone.coeff i/(2:ℚ)^(stone.g i)
  have pw (x : ℚ) (m : ℕ) : padicNorm 3 (x^m)=(padicNorm 3 x)^m := by induction m with | zero => simp | succ _ ih => simp [pow_succ,ih]
  have h2 : padicNorm 3 (2:ℚ)=1 := (padicNorm.nat_eq_one_iff 2).mpr (by decide)
  have h3 : padicNorm 3 (3:ℚ) = (3:ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime (p:=3)
  have weight (i : ℕ) : padicNorm 3 (w i)=(3:ℚ)^i := by
    change padicNorm 3 ((1/(3:ℚ)^i)/(2:ℚ)^(3^i)) = _
    rw [padicNorm.div,padicNorm.div,pw,pw,h2,one_pow,div_one,padicNorm.one,h3]; simp
  have active : k∈stone.active n := stone.mem.mpr (Nat.pow_log_le_self 3 pos.ne')
  have ultr : IsNonarchimedean (padicNorm 3) := fun _ _ => padicNorm.nonarchimedean
  have H := ultr.apply_sum_eq_of_lt w padicNorm.neg active (fun i hi ne => by
    rw [weight,weight]; apply pow_lt_pow_right₀ (by norm_num : (1:ℚ)<3)
    exact lt_of_le_of_ne (Nat.le_log_of_pow_le (by decide : 1<3) (stone.mem.mp hi)) ne)
  change padicNorm 3 ((2:ℚ)^n*∑ i∈stone.active n,w i)=_
  rw [padicNorm.mul,pw,h2,one_pow,one_mul,H,weight]

/-- The sum starts at `m=1`, represented by `i+1`. -/
noncomputable def perturbation (r : ℕ) : ℝ :=
  ∑' i : ℕ, 1 / ((3:ℝ)^(Nat.log 3 (i+1)) * (2:ℝ)^((i+1)^r))

/-- Every power schedule of degree at least two, including squares and cubes. -/
theorem normal {r : ℕ} (hr : 2≤r) : NormalIn 2 (radixComponent 2 3 1 + perturbation r) := by
  let s := poly r (by omega)
  have stone_value : stone.value=radixComponent 2 3 1 := by
    apply tsum_congr; intro i; simp [stone,Schedule.coeff]; ring
  have poly_value : s.value=perturbation r := by
    apply tsum_congr; intro i; dsimp [s,poly,Schedule.coeff]; push_cast; ring
  rw [← stone_value,← poly_value]
  -- On the scale 16^k the square schedule already bounds every higher degree.
  let A (k : ℕ) := (range (4*(k+1)+1)).image stone.g ∪ (range (4*4^k)).image s.g
  have contain (k : ℕ) (v : ℕ) : (stone.g v<16^(k+1) → stone.g v∈A k) ∧ (s.g v<16^(k+1) → s.g v∈A k) := by
    constructor
    · intro h; apply mem_union_left _ (mem_image.mpr ⟨v,mem_range.mpr ?_,rfl⟩)
      have lo := Nat.pow_le_pow_left (by decide : 2≤3) v
      have upper : 16^(k+1)=2^(4*(k+1)) := by rw [pow_mul]; rfl
      have less := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp ((lo.trans_lt h).trans_eq upper); omega
    · intro h; apply mem_union_right _ (mem_image.mpr ⟨v,mem_range.mpr ?_,rfl⟩)
      change (v+1)^r<16^(k+1) at h
      have eqn : (4*4^k)^2=16^(k+1) := by rw [mul_pow,← pow_mul,Nat.mul_comm k 2,pow_mul,show (4:ℕ)^2=16 by decide,pow_succ' 16]
      have cap := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (((Nat.pow_le_pow_right (Nat.succ_pos v) hr).trans_lt h).trans_eq eqn.symm); omega
  apply normal_of_dominated_perturbation (c:=3) (p:=3) (B:=2) (L:=8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ _ stone.pre s.pre stone.tail s.tail A 8
  · intro η pos
    have geo := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul 18
    simp only [mul_zero] at geo
    filter_upwards [geo.eventually_le_const pos] with k hk
    have card := (card_union_le ..).trans (add_le_add (card_image_le (s:=range (4*(k+1)+1)) (f:=stone.g)) (card_image_le (s:=range (4*4^k)) (f:=s.g)))
    simp only [card_range] at card
    have z : k+1≤4^k := (Nat.lt_two_pow_self (n:=k)).trans_le (Nat.pow_le_pow_left (by decide : 2≤4) _)
    have ncap : 2*(A k).card≤18*4^k := by
      change (A k).card≤_ at card
      have one : 0<4^k := by positivity
      omega
    apply (by exact_mod_cast ncap : (2:ℝ)*(A k).card≤18*4^k).trans
    have eqn : (1/2:ℝ)^k*(8:ℝ)^k=4^k := by rw [← mul_pow]; norm_num
    norm_num only [Nat.cast_ofNat]; nlinarith only [mul_le_mul_of_nonneg_right hk (show (0:ℝ)≤8^k by positivity),congrArg (18 * ·) eqn]
  · intro M; filter_upwards [eventually_ge_atTop (max 1 M)] with k hk n low high
    change 16^k≤n at low; change n<16^(k+1) at high
    have kn : 3^k≤n := (Nat.pow_le_pow_left (by decide) k).trans low
    let j := Nat.log 3 n
    have kj : k≤j := Nat.le_log_of_pow_le (by decide) kn
    have jk : 1≤j := (le_max_left 1 M).trans (hk.trans kj)
    have np := (pow_pos (by decide : 0<3) k).trans_le kn
    have cap : ∀ v∈s.active n,s.e v≤j-1 := by
      intro v hv; have h : (v+1)^r≤n := s.mem.mp hv
      have up := Nat.lt_pow_succ_log_self (by decide : 1<3) n
      have sm : v+1<3^j := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (calc
        (v+1)^2 ≤ (v+1)^r := Nat.pow_le_pow_right (by omega) hr
        _ < 3^(j+1) := h.trans_lt up
        _ ≤ (3^j)^2 := by rw [← pow_mul]; apply Nat.pow_le_pow_right (by decide); omega)
      have fine := Nat.log_lt_of_lt_pow (Nat.succ_ne_zero _) sm
      change Nat.log 3 (v+1)<j at fine
      change Nat.log 3 (v+1)≤j-1; omega
    have den := s.denominator cap
    have pre := stone_norm np; change padicNorm 3 (stone.pre n)=(3:ℚ)^j at pre
    have sm := (Localized.padicNorm_le_den Nat.prime_three (s.pre n)).trans (by exact_mod_cast Nat.le_of_dvd (pow_pos (by decide : 0<3) _) den : ((s.pre n).den:ℚ)≤3^(j-1))
    refine ⟨pre ▸ ?_,pre ▸ sm.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega)),j,
      stone.denominator (fun v hv => Nat.le_log_of_pow_le (by decide) (stone.mem.mp hv)),
      den.trans (pow_dvd_pow 3 (Nat.sub_le ..)),?_⟩
    · exact_mod_cast (((le_max_right 1 M).trans (hk.trans kj)).trans (Nat.lt_pow_self (by decide : 2≤3)).le)
    · apply (Nat.pow_log_le_self 3 np.ne').trans (high.le.trans _)
      have kpos := (le_max_left 1 M).trans hk
      rw [show 16=2^4 by decide,← pow_mul,← pow_mul]
      apply Nat.pow_le_pow_right (by decide); omega
  · intro k n i high free
    have orbit (sched : Schedule) (all : ∀ v, sched.g v<16^(k+1) → sched.g v∈A k) : sched.pre (n+i)=(2:ℚ)^i*sched.pre n := by
      apply sched.follows; intro v lo; apply lt_of_not_ge; intro hi
      exact free _ lo hi (all v (hi.trans_lt high))
    rw [orbit stone (fun v => (contain k v).1),orbit s (fun v => (contain k v).2),mul_add]; norm_num

/-- In the linear schedule the coefficients stay constant from `3^j` through
`3^(j+1)-1`. Summing each such range gives an affine Stoneham expression. -/
theorem linear_value : perturbation 1 = 3-4*radixComponent 2 3 1 := by
  let z : ℝ := 1/2
  let a (j : ℕ) : ℝ := 1/3^j
  let w (j : ℕ) := a j*z^(3^j)
  have az (j : ℕ) : 0≤a j := by dsimp [a]; positivity
  have one (j : ℕ) : a j≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤3))
  have geo := summable_geometric_of_lt_one (by norm_num : 0≤z) (by norm_num : z<1)
  have conv : Summable (fun i : ℕ => a (Nat.log 3 (i+1))*z^(i+1)) := .of_nonneg_of_le
    (fun i => mul_nonneg (az _) (pow_nonneg (by norm_num : 0≤z) _))
    (fun i => mul_le_of_le_one_left (pow_nonneg (by norm_num : 0≤z) _) (one _)) ((summable_nat_add_iff 1).mpr geo)
  have h := radix_plateau_sum (by decide : 1<3) (by norm_num : z≠1) a conv
  have wp : Summable w := Summable.of_nonneg_of_le (fun i => mul_nonneg (az _) (pow_nonneg (by norm_num : 0≤z) _))
    (fun i => mul_le_of_le_one_left (pow_nonneg (by norm_num : 0≤z) _) (one i)) (geo.comp_injective (pow_right_injective₀ (by decide : 0<3) (by decide : 3≠1)))
  have total : ∑' j,w j = radixComponent 2 3 1 := by
    apply tsum_congr; intro j; simp [w,a,z]; ring
  have h0 : w 0 = 1/2 := by norm_num [w,a,z]
  have cut := wp.sum_add_tsum_nat_add 1
  simp only [sum_range_one,h0,total] at cut
  have step (j : ℕ) : a j*((z^(3^j)-z^(3^(j+1)))/(1-z)) = 2*w j-6*w (j+1) := by
    dsimp only [w,a,z]; rw [pow_succ (3:ℝ)]; ring
  calc perturbation 1 = ∑' i : ℕ, a (Nat.log 3 (i+1))*z^(i+1) := by
         apply tsum_congr; intro i; simp [a,z]; ring
       _ = _ := h
       _ = 3-4*radixComponent 2 3 1 := by
         simp_rw [step]; rw [(wp.mul_left 2).tsum_sub (((summable_nat_add_iff 1).mpr wp).mul_left 6),
           tsum_mul_left,tsum_mul_left,total]; linarith only [cut]

/-- Dense linear insertions and all sparser power schedules preserve binary normality here. -/
theorem normal_of_positive_degree {r : ℕ} (hr : 0<r) :
    NormalIn 2 (radixComponent 2 3 1 + perturbation r) := by
  by_cases h : 2≤r
  · exact normal h
  have eqn : r=1 := by omega
  let x := radixComponent 2 3 1
  rw [eqn,linear_value]; change NormalIn 2 (x+(3-4*x))
  rw [show x+(3-4*x)=(-3*x)+(3:ℚ) by push_cast; ring,normal_add_rat_iff (by decide)]
  have hx := radixComponent_normal (b:=2) (c:=3) (m:=1) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply normal_of_fourier (by decide); intro h hn
  have result := fourier_of_normal hx (h*(-3)) (mul_ne_zero hn (by decide))
  convert result using 3; push_cast; dsimp [x]; ring_nf

end NormalityChecker.PolynomialInsertions
