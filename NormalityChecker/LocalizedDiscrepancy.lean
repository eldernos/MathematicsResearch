module

public import NormalityChecker.BinaryDiscrepancy
public import NormalityChecker.LocalizedMeshRate
public import NormalityChecker.IntervalFourier
public import NormalityChecker.LocalizedMixed

/-! Quantitative interval discrepancy of mixed two-generator localized logarithms. -/
@[expose] public section
open Finset Filter
open scoped Topology
namespace NormalityChecker.Localized

noncomputable def centered (u : ℕ → ℝ) (a c : ℝ) (n : ℕ) : ℂ :=
  ((if a ≤ u n ∧ u n < c then 1 else 0 : ℝ) - (c-a) : ℝ)

lemma centered_norm (u : ℕ → ℝ) {a c : ℝ} (ha : 0≤a) (hac : a≤c) (hc : c≤1) (n : ℕ) :
    ‖centered u a c n‖ ≤ 1 := by
  rw [centered,Complex.norm_real,Real.norm_eq_abs,abs_le]; split_ifs <;> constructor <;> linarith

lemma centered_sum (u : ℕ → ℝ) (a c : ℝ) (s T : ℕ) :
    ‖∑ i ∈ range T, centered u a c (s+i)‖ =
    |(IntervalFourier.count (fun i => u (s+i)) a c T : ℝ)-T*(c-a)| := by
  classical
  unfold centered IntervalFourier.count
  rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,sum_sub_distrib,← sum_filter]
  simp [mul_sub]

variable (d : Parameters)
private noncomputable abbrev orbit := shift d.b (value d)

private lemma good_interval {a c : ℝ} (ha : 0≤a) (hac : a≤c) (hc : c≤1)
    (odd : Odd d.p) {K s J z : ℕ} (hz : 1≤z) (hK : 2≤K) (budget : d.p^J*z^3*periodFactor d ≤ K)
    (small : z^4 ≤ K) (low : K^6 ≤ s) (high : s ≤ d.p^6*K^6)
    (surv : (K:ℚ)^6 ≤ d.p^J*padicNorm d.p (shifted d s))
    (clean : ∀ v ∈ allowed d s, index d v + v.1 ≤ s)
    (free : ∀ m, s<m → m<s+K^5 → ¬ Supported d m) :
    ‖∑ i ∈ range (K^5), centered (orbit d) a c (s+i)‖ ≤
      (2*(5+3+((d.p:ℝ)^6+2+2*Real.pi)))*(K:ℝ)^5/z := by
  have kr : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have zr : (0:ℝ)<z := by exact_mod_cast hz
  have z1 : (1:ℝ)≤z := by exact_mod_cast hz
  have sz : (z:ℝ)^4 ≤ K := by exact_mod_cast small
  let H := z^3
  let : NeZero H := ⟨(pow_pos hz 3).ne'⟩
  let E := ((d.p:ℝ)^6+2+2*Real.pi)*K^4
  have fourier (h : ℤ) (hh : h ≠ 0) (hf : h.natAbs < H) :
      ‖∑ i ∈ range (K^5), phase (h*orbit d (s+i))‖ ≤ E := by
    have hl : d.p^J*h.natAbs*periodFactor d ≤ K := (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf.le)).trans budget
    have hs := (pow_pos (show 0<K by omega) 6).trans_le low
    have old := clean_block d hh odd hl hK hs high le_rfl surv clean free
    let f (i : ℕ) := phase (h*orbit d (s+i))
    let g (i : ℕ) := character d h (s+i)
    have diff (i : ℕ) : ‖f i-g i‖ ≤ 2*Real.pi/K := by
      dsimp [f,g,orbit,shift,character]; rw [phase_fract]
      apply (phase_sub_le ..).trans
      rw [← mul_sub,abs_mul,abs_of_nonneg (shift_error d _).1,← Int.cast_abs,← Nat.cast_natAbs]
      have hsz : (K:ℝ)^6 ≤ ((s+i:ℕ):ℝ)+1 := by exact_mod_cast (show K^6 ≤ s+i+1 by omega)
      have hzK : h.natAbs ≤ K := hf.le.trans ((Nat.pow_le_pow_right hz (by decide : 3≤4)).trans small)
      have hk' : (1:ℝ)≤K := by exact_mod_cast (show 1≤K by omega)
      have hk2 : (K:ℝ)^2 ≤ (K:ℝ)^6 := pow_le_pow_right₀ hk' (by decide)
      have htail := (shift_error d (s+i)).2.trans (one_div_le_one_div_of_le (by positivity) (hk2.trans hsz))
      calc _ ≤ 2*Real.pi*((K:ℝ)*(1/K^2)) := by
             apply mul_le_mul_of_nonneg_left _ (by positivity)
             exact mul_le_mul (by exact_mod_cast hzK) htail (shift_error d _).1 (by positivity)
           _ = _ := by field_simp
    have dist := (norm_sum_le (range (K^5)) (fun i => f i - g i)).trans (sum_le_sum (fun i (_ : i ∈ range (K^5)) => diff i))
    rw [sum_sub_distrib] at dist
    have tri' := norm_add_le ((∑ i ∈ range (K^5), f i) - (∑ i ∈ range (K^5), g i)) (∑ i ∈ range (K^5), g i)
    rw [sub_add_cancel] at tri'
    change ‖∑ i ∈ range (K^5), f i‖ ≤ _
    apply tri'.trans ((add_le_add dist old).trans _)
    simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_pow]; dsimp [E]; apply le_of_eq; field_simp; ring
  have bound := IntervalFourier.interval_count_bound (H:=H) (T:=K^5) (fun i => orbit d (s+i))
    (fun i => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩) ha hac hc (δ:=1/(z:ℝ)) (by positivity) (E:=E) (by dsimp [E]; positivity) fourier
  rw [centered_sum]; apply bound.trans
  dsimp [H,E]; push_cast
  have coef : 0≤(d.p:ℝ)^6+2+2*Real.pi := by positivity
  have grid : 3/(z:ℝ)^3 ≤ 3/z := by gcongr; exact (by simpa using pow_le_pow_right₀ z1 (by decide : 1≤3))
  have smooth : (1/(1/(z:ℝ)))^2/(z:ℝ)^3=1/z := by field_simp
  rw [smooth]
  calc _ ≤ 2 * ((K:ℝ)^5*(4*(1/z)+3/z+1/z)+z^3*(((d.p:ℝ)^6+2+2*Real.pi)*K^4)) := by gcongr
       _ ≤ _ := by apply (le_div_iff₀ zr).mpr; field_simp; nlinarith only [mul_le_mul_of_nonneg_right sz coef]

private noncomputable def cellConstant :=
  2*(8+((d.p:ℝ)^6+2+2*Real.pi))+1+3*(d.p:ℝ)^6*Real.log d.q

private lemma cellConstant_pos : 0 < cellConstant d := by
  have : 0≤Real.log d.q := Real.log_nonneg (by exact_mod_cast (show 1≤d.q by have := d.hq; omega))
  unfold cellConstant; positivity

private lemma insertion_budget : ∀ᶠ k : ℕ in atTop,
    k*(2+2*(d.p^6*(k+1)+1)^2) ≤ d.p^k := by
  let C := d.p^6
  let A : ℝ := 2+2*(2*(C:ℝ)+1)^2
  have vanishes : Tendsto (fun k : ℕ => A*((k:ℝ)^3/(d.p:ℝ)^k)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 3 (by exact_mod_cast d.hp.one_lt : (1:ℝ)<d.p)).const_mul A
  filter_upwards [eventually_ge_atTop 1,vanishes.eventually_lt_const zero_lt_one] with k hk small
  rw [← mul_div_assoc,div_lt_iff₀ (pow_pos (by exact_mod_cast d.hp.pos) _),one_mul] at small
  have h1 : (1:ℝ)≤k := by exact_mod_cast hk
  have linear : (C:ℝ)*(k+1)+1 ≤ (2*(C:ℝ)+1)*k := by nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg C)]
  have sq := pow_le_pow_left₀ (by positivity) linear 2
  have cubic := mul_le_mul_of_nonneg_right sq (Nat.cast_nonneg (α:=ℝ) k)
  have rhs : (k:ℝ)*(2+2*((C:ℝ)*(k+1)+1)^2) ≤ A*k^3 := by
    dsimp [A]; nlinarith only [cubic,show (k:ℝ)≤(k:ℝ)^3 by simpa using pow_le_pow_right₀ h1 (by decide : 1≤3)]
  change k*(2+2*(C*(k+1)+1)^2) ≤ _
  exact_mod_cast rhs.trans small.le

private lemma quantitative_cell (odd : Odd d.p) {M k u T : ℕ} {a c : ℝ}
    (ha : 0≤a) (hac : a≤c) (hc : c≤1) (hm : 0<M) (hu : 1≤u) (hu' : u<d.p^6)
    (hT : T≤(d.p^6)^k) (scale_budget : M*d.q^2*d.p^M+3*(M+1)+periodFactor d ≤ k)
    (small : (M+1)^4 ≤ k) (inserts : k*(2+2*(d.p^6*(k+1)+1)^2) ≤ d.p^k) :
    ‖∑ i ∈ range T, centered (orbit d) a c (u*(d.p^6)^k+i)‖ ≤
      (cellConstant d/((M:ℝ)+1))*((d.p^6:ℕ):ℝ)^k := by
  let K := d.p^k
  let J := M*d.q^2*d.p^M
  let C := d.p^6
  let z := M+1
  let D := C*(k+1)
  have zpos : 1≤z := Nat.succ_pos _
  have zk : z ≤ k := (show z≤z^4 by simpa using Nat.pow_le_pow_right zpos (by decide : 1≤4)).trans small
  have kpos : 1≤k := zpos.trans zk
  have kK (v : ℕ) : v ≤ d.p^v := (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left d.hp.two_le v)
  have hK : 2≤K := d.hp.two_le.trans (by simpa [K] using Nat.pow_le_pow_right d.hp.pos kpos)
  have large : d.p^J*z^3*periodFactor d ≤ K := calc
    _ ≤ d.p^J*(d.p^z)^3*d.p^(periodFactor d) := by gcongr <;> apply kK
    _ = d.p^(J+3*z+periodFactor d) := by rw [← pow_mul,← pow_add,← pow_add,Nat.mul_comm z 3]
    _ ≤ K := Nat.pow_le_pow_right d.hp.pos scale_budget
  have budget : z*(2+2*(D+1)^2) ≤ K := (Nat.mul_le_mul_right _ zk).trans inserts
  have boundD : D≤K := (by nlinarith [Nat.le_mul_of_pos_left (2+2*(D+1)^2) zpos] : D≤z*(2+2*(D+1)^2)).trans budget
  have scale : C^k=K^6 := by dsimp [C,K]; rw [← pow_mul,Nat.mul_comm,pow_mul]
  have ps : d.p^(6*k)=K^6 := by rw [Nat.mul_comm,pow_mul]
  have hDpow : C*K^6 ≤ 2^D := by rw [← scale,← pow_succ']; dsimp [D]; rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have Jk : J ≤ 6*k := by change J+3*z+periodFactor d ≤ k at scale_budget; omega
  let δ := 3*(C:ℝ)*Real.log d.q/(z:ℝ)
  have logpos : 0<Real.log d.q := Real.log_pos (by exact_mod_cast (show 1<d.q from d.hq))
  have hpC : 0<C := pow_pos d.hp.pos _
  have δpos : 0<δ := by dsimp [δ]; positivity
  have diam := exceptional_diameter_of_mesh d u hu (J:=J) (ε:=δ) (fun x y hx hy wide =>
    effective_threshold_mesh d.hp.two_le d.hq (d.hp.coprime_iff_not_dvd.mpr (prime_not_dvd_cofactor d)) hm
      ((by exact_mod_cast hu : (1:ℝ)≤u).trans hx) (hy.trans (by exact_mod_cast hu' : (u:ℝ)+1≤C))
      (by exact_mod_cast hpC) (by simpa [δ,z] using wide))
  have hpow : (d.p:ℚ)^J*(d.p:ℚ)^(6*k-J)=(K:ℚ)^6 := by rw [← pow_add,Nat.add_sub_of_le Jk]; exact_mod_cast ps
  have bound := statistic_cell_bound d (centered (orbit d) a c) (centered_norm _ ha hac hc)
    (G:=(2*(5+3+((d.p:ℝ)^6+2+2*Real.pi)))*(K:ℝ)^5/z) (by positivity) hu hu' hK
    (boundD.trans (by simpa using Nat.pow_le_pow_right (show 0<K by omega) (by decide : 1≤5))) hDpow
    (scale ▸ hT) δpos.le (J:=J) (fun s t hs ht bs bt => by
      have low {x : ℚ} (hx : (d.p:ℚ)^J*x < (K:ℚ)^6) : x < (d.p:ℚ)^(6*k-J) :=
        (mul_lt_mul_iff_right₀ (pow_pos (by exact_mod_cast d.hp.pos) J)).mp (hx.trans_eq hpow.symm)
      have H := diam (6*k) Jk s t (ps ▸ hs) (ps ▸ ht) (low bs) (low bt)
      rwa [show (d.p:ℝ)^(6*k)=(K:ℝ)^6 by exact_mod_cast ps] at H)
    (fun _ low high surv clean free => good_interval d ha hac hc odd zpos hK large (small.trans (kK k)) low high surv clean free)
  rw [show (M:ℝ)+1=(z:ℝ) by simp [z]]
  change ‖∑ i ∈ range T, centered (orbit d) a c (u*C^k+i)‖ ≤ cellConstant d/(z:ℝ)*(C:ℝ)^k
  rw [scale,show (C:ℝ)^k=(K:ℝ)^6 by exact_mod_cast scale]
  apply bound.trans
  have br : (z:ℝ)*(2+2*((D:ℝ)+1)^2)≤K := by exact_mod_cast budget
  have zr : (0:ℝ)<z := by exact_mod_cast zpos
  dsimp only [cellConstant,δ,C]; push_cast; field_simp; linarith only [br]

/-- All cells admit one uniform estimate after an exponential threshold in the precision. -/
private lemma scale_threshold (odd : Odd d.p) : ∃ R : ℕ, 2≤R ∧ ∀ M : ℕ, 0<M →
    ∀ k≥R^(M+1), ∀ u ∈ Ico 1 (d.p^6*1), ∀ T≤(d.p^6)^k, ∀ a c : ℝ, 0≤a → a≤c → c≤1 →
    ‖∑ i ∈ range T, centered (orbit d) a c (u*(d.p^6)^k+i)‖ ≤ (cellConstant d/((M:ℝ)+1))*((d.p^6:ℕ):ℝ)^k := by
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp (insertion_budget d)
  let R := 16+2*d.p+d.q^2+3+periodFactor d+k₀
  have rpos : 1≤R := by dsimp [R]; omega
  refine ⟨R,by dsimp [R]; omega,?_⟩
  intro M hm k hk u hu T hT a c ha hac hc
  have z : M+1 ≤ 2^M := Nat.lt_two_pow_self
  have rp : 1≤R^M := Nat.one_le_pow _ _ rpos
  have hi : (2*d.p)^M ≤ R^M := Nat.pow_le_pow_left (by dsimp [R]; omega) _
  have hz : M+1 ≤ R^M := z.trans (Nat.pow_le_pow_left (by dsimp [R]; omega) _)
  have j : M*d.q^2*d.p^M ≤ d.q^2*R^M := calc
    _ ≤ 2^M*d.q^2*d.p^M := by gcongr; omega
    _ = d.q^2*(2*d.p)^M := by rw [mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hi
  have le1 : d.q^2+3+periodFactor d ≤ R := by dsimp [R]; omega
  have factor : periodFactor d ≤ periodFactor d*R^M := Nat.le_mul_of_pos_right _ rp
  have budget : M*d.q^2*d.p^M+3*(M+1)+periodFactor d ≤ k := calc
    _ ≤ d.q^2*R^M+3*R^M+periodFactor d*R^M := by gcongr
    _ = (d.q^2+3+periodFactor d)*R^M := by ring
    _ ≤ R^(M+1) := by rw [pow_succ' R M]; exact Nat.mul_le_mul_right _ le1
    _ ≤ k := hk
  have sm : (M+1)^4 ≤ k := calc
    _ ≤ (2^M)^4 := Nat.pow_le_pow_left z _
    _ = 16^M := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    _ ≤ R^M := Nat.pow_le_pow_left (by dsimp [R]; omega) _
    _ ≤ R^(M+1) := Nat.pow_le_pow_right rpos (by omega)
    _ ≤ k := hk
  have hk₀ : k₀≤k := calc k₀ ≤ R := by dsimp [R]; omega
                           _ ≤ R^(M+1) := by simpa using Nat.pow_le_pow_right rpos (show 1≤M+1 by omega)
                           _ ≤ k := hk
  exact quantitative_cell d odd ha hac hc hm (mem_Ico.mp hu).1 (by simpa using (mem_Ico.mp hu).2) hT budget sm (h₀ k hk₀)

/-- Uniform in both interval endpoints, through every integer prefix length. -/
theorem interval_discrepancy_rate (odd : Odd d.p) : ∃ A : ℝ, 0<A ∧ ∀ᶠ N : ℕ in atTop,
    ∀ a c : ℝ, 0≤a → a≤c → c≤1 →
    |frequency (shift d.b (value d)) a c N-(c-a)| ≤ A/Real.log (Real.log N) := by
  obtain ⟨R,hR,threshold⟩ := scale_threshold d odd
  let C := d.p^6
  have hc : 1<C := one_lt_pow₀ d.hp.one_lt (by decide)
  have lC : 0<Real.log C := Real.log_pos (by exact_mod_cast hc)
  have lR : 0<Real.log R := Real.log_pos (by exact_mod_cast hR)
  let B := 1+((C:ℝ)+1)*cellConstant d
  let G := 3*Real.log R + |Real.log (Real.log C)| + 1
  have hB : 0<B := by dsimp [B]; have := cellConstant_pos d; positivity
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨B*G,mul_pos hB hG,?_⟩
  have llim := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [eventually_ge_atTop (C^(R^3)),llim.eventually_gt_atTop 0] with N hN llpos a c ha hac hc'
  change 0 < Real.log (Real.log N) at llpos
  have npos : 0<N := (pow_pos (by omega : 0<C) _).trans_le hN
  let k := Nat.log C N
  have hk : R^3 ≤ k := (Nat.le_log_iff_pow_le hc npos.ne').mpr hN
  let l := Nat.log R k
  have kpos : 0<k := (pow_pos (by omega : 0<R) _).trans_le hk
  have hl : 3≤l := (Nat.le_log_iff_pow_le hR kpos.ne').mpr hk
  let M := l-2
  have hm : 0<M := by dsimp [M]; omega
  have e : M+2=l := Nat.sub_add_cancel (by omega)
  let L := R^(M+1)
  have zL : M+1 ≤ L := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hR _)
  have tN : C^(R^(M+2)) ≤ N := by
    rw [e]; exact (Nat.pow_le_pow_right (by omega : 0<C) (Nat.pow_log_le_self R kpos.ne')).trans (Nat.pow_log_le_self C npos.ne')
  have initial : C^L*(M+1) ≤ N := calc
    _ ≤ C^L*C^L := Nat.mul_le_mul_left _ (zL.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hc _)))
    _ = C^(2*L) := by rw [two_mul,pow_add]
    _ ≤ C^(R^(M+2)) := by apply Nat.pow_le_pow_right (by omega); rw [pow_succ']; exact Nat.mul_le_mul_right L hR
    _ ≤ N := tN
  have low : 1*C^L ≤ N := (by simpa using Nat.le_mul_of_pos_right (C^L) (Nat.succ_pos M) : 1*C^L ≤ C^L*(M+1)).trans initial
  have zp : (0:ℝ)<(M:ℝ)+1 := by positivity
  have nr : (0:ℝ)<N := by exact_mod_cast npos
  have pre := prefix_of_radix_cells (c:=C) (S:=1) hc (by decide) (div_pos (cellConstant_pos d) zp) low
    (fun v hv u hu T hT => threshold M hm v hv u hu T hT a c ha hac hc')
  have triv : ‖∑ i ∈ range (1*C^L), centered (orbit d) a c i‖ ≤ C^L := by
    apply (norm_sum_le ..).trans ((sum_le_sum (fun i (_ : i∈range (1*C^L)) => centered_norm _ ha hac hc' i)).trans_eq _); simp
  have first : (C:ℝ)^L ≤ N/((M:ℝ)+1) := (le_div_iff₀ zp).mpr (by exact_mod_cast initial)
  have pre' := pre.trans (add_le_add (triv.trans first) le_rfl)
  simp only [Nat.cast_one,mul_one] at pre'
  have cent := centered_sum (orbit d) a c 0 N
  simp only [zero_add] at cent
  rw [cent] at pre'
  have freq : |frequency (orbit d) a c N-(c-a)| ≤ B/((M:ℝ)+1) := by
    unfold frequency; change |(IntervalFourier.count (orbit d) a c N:ℝ)/N-(c-a)| ≤ _
    rw [div_sub' nr.ne',abs_div,abs_of_pos nr,div_le_iff₀ nr]
    apply pre'.trans; dsimp [B]; apply le_of_eq; ring
  have upperN : N < C^(R^(M+3)) := by
    have high := Nat.lt_pow_succ_log_self hR k
    change k<R^(l+1) at high
    rw [show M+3=l+1 by omega]
    exact (Nat.lt_pow_succ_log_self hc N).trans_le (Nat.pow_le_pow_right (by omega) high)
  have logBound : Real.log (Real.log N) ≤ ((M:ℝ)+1)*G := by
    have firstLog := Real.log_le_log nr (by exact_mod_cast upperN.le : (N:ℝ)≤(C:ℝ)^(R^(M+3)))
    rw [Real.log_pow] at firstLog
    have powBound : C ≤ C^(R^3) := by simpa using Nat.pow_le_pow_right (by omega : 0<C) (show 1≤R^3 from Nat.one_le_pow _ _ (by omega))
    have lnpos : 0<Real.log N := Real.log_pos (by exact_mod_cast hc.trans_le (powBound.trans hN))
    have secondLog := Real.log_le_log lnpos firstLog
    rw [Real.log_mul (by positivity) lC.ne', Nat.cast_pow,Real.log_pow] at secondLog
    dsimp [G]; push_cast at secondLog
    nlinarith [le_abs_self (Real.log (Real.log C)),mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) (abs_nonneg (Real.log (Real.log C))),mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) lR.le]
  apply freq.trans; rw [div_le_div_iff₀ zp llpos]
  exact (mul_le_mul_of_nonneg_left logBound hB.le).trans_eq (by ring)

/-- Extreme interval discrepancy is O(1/log(log N)) for each fixed mixed family member. -/
theorem discrepancy_rate (odd : Odd d.p) : ∃ A : ℝ, 0<A ∧ ∀ᶠ N : ℕ in atTop,
    radixDiscrepancy d.b (value d) N ≤ A/Real.log (Real.log N) := by
  obtain ⟨A,hA,uniform⟩ := interval_discrepancy_rate d odd
  refine ⟨A,hA,?_⟩
  filter_upwards [uniform] with N h
  unfold radixDiscrepancy
  refine csSup_le ⟨_,0,1,le_rfl,zero_lt_one,le_rfl,rfl⟩ ?_
  rintro _ ⟨a,c,ha,hac,hc,rfl⟩; exact h a c ha hac.le hc

end NormalityChecker.Localized
