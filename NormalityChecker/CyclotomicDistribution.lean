module

public import NormalityChecker.CyclotomicClassification

@[expose] public section
open Finset Filter Complex
open scoped Topology
namespace NormalityChecker

/-- Convergence against continuous functions on the circle to the mixture
of uniform measure (weight 1-w) and a point mass at zero (weight w). -/
theorem circle_mixture_of_characters (s : ℕ → ℝ) (N : ℕ → ℕ) (hN : ∀ k, 0<N k)
    {w : ℝ} (hw : 0≤w) (hw' : w≤1)
    (H : ∀ h : ℤ, h≠0 → Tendsto (fun k => Weyl.fourierMean s h (N k)) atTop (𝓝 (w:ℂ)))
    (f : C(AddCircle (1:ℝ),ℂ)) :
    Tendsto (fun k => Weyl.cMean s f (N k)) atTop (𝓝 ((1-(w:ℂ))*Weyl.cInt f+w*f 0)) := by
  let L (g : C(AddCircle (1:ℝ),ℂ)) := (1-(w:ℂ))*Weyl.cInt g+w*g 0
  have addL (a b : C(AddCircle (1:ℝ),ℂ)) : L (a+b)=L a+L b := by
    dsimp [L]; rw [Weyl.cInt_add]; ring
  have nL (g : C(AddCircle (1:ℝ),ℂ)) : ‖L g‖ ≤ ‖g‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,← ofReal_one,← ofReal_sub,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hw'),abs_of_nonneg hw]
    nlinarith [mul_le_mul_of_nonneg_left (Weyl.norm_cInt_le g) (sub_nonneg.mpr hw'),
      mul_le_mul_of_nonneg_left (g.norm_coe_le_norm 0) hw]
  let good : Submodule ℂ C(AddCircle (1:ℝ),ℂ) := {
    carrier := {g | Tendsto (fun k => Weyl.cMean s g (N k)) atTop (𝓝 (L g))}
    zero_mem' := by simp [L,Weyl.cMean,Weyl.cInt]
    add_mem' := by
      intro a b ha hb; change Tendsto _ _ (𝓝 (L (a+b)))
      simp_rw [Weyl.cMean_add,addL]; exact ha.add hb
    smul_mem' := by
      intro a g hg; change Tendsto _ _ (𝓝 (L (a • g)))
      have e : L (a • g)=a*L g := by dsimp [L]; rw [Weyl.cInt_smul]; ring
      simp_rw [Weyl.cMean_smul,e]; exact hg.const_mul a }
  have close : f ∈ closure (good : Set C(AddCircle (1:ℝ),ℂ)) := by
    have span : Submodule.span ℂ (Set.range (fourier (T:=(1:ℝ)))) ≤ good := by
      apply Submodule.span_le.mpr; rintro g ⟨h,rfl⟩
      change Tendsto _ _ (𝓝 (L (fourier h)))
      by_cases hz : h=0
      · subst h
        have eqn (k : ℕ) : Weyl.cMean s (fourier 0) (N k)=1 := by
          simp [Weyl.cMean,(hN k).ne']
        simp [eqn,L,Weyl.cInt_fourier_zero]
      · simpa only [L,Weyl.cInt_fourier_ne h hz,mul_zero,zero_add,fourier_eval_zero,mul_one,
          Weyl.cMean_eq_fourierMean] using H h hz
    have ht := span_fourier_closure_eq_top (T:=(1:ℝ))
    have hf : f∈(Submodule.span ℂ (Set.range (fourier (T:=(1:ℝ))))).topologicalClosure := by rw [ht]; trivial
    have hsub : ((Submodule.span ℂ (Set.range (fourier (T:=(1:ℝ))))) : Set C(AddCircle (1:ℝ),ℂ)) ⊆ (good : Set _) := span
    apply closure_mono hsub
    rwa [← Submodule.topologicalClosure_coe]
  change Tendsto _ _ (𝓝 (L f))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.mp close (ε/3) (by linarith)
  have lim : Tendsto (fun k => Weyl.cMean s g (N k)) atTop (𝓝 (L g)) := hg
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp lim (ε/3) (by linarith)
  refine ⟨K,fun k hk => ?_⟩
  have A := Weyl.cMean_add s (f-g) g (N k)
  have B := addL (f-g) g
  rw [sub_add_cancel] at A B
  have hn : ‖f-g‖ < ε/3 := by rwa [← dist_eq_norm]
  have hd := Weyl.norm_cMean_le s (f-g) (N k)
  have hL := nL (f-g)
  have E := hK k hk
  rw [dist_eq_norm] at E ⊢
  rw [A,B,show ∀ a b c d : ℂ, a+b-(c+d)=a+(b-d)-c by intros; ring]
  exact (norm_sub_le ..).trans_lt (by linarith [norm_add_le (Weyl.cMean s (f-g) (N k)) (Weyl.cMean s g (N k)-L g)])

noncomputable def resonanceMass (b p S : ℕ) (M : Finset ℕ) (a : ℕ → ℚ) : ℚ :=
  (resonantCells b p S M a).card / (((p:ℚ)-1)*S)

/-- Exact weak limit at N = S p^k for the explicitly integer-scaled sum. -/
theorem cyclotomic_distribution {b p S : ℕ} [Fact p.Prime] (hb : 1<b) (ho : Odd p)
    (hbc : b.Coprime p) (hS : 0<S) (M : Finset ℕ) (a : ℕ → ℚ) (hm : ∀ m∈M, 0<m ∧ m≤S)
    (f : C(AddCircle (1:ℝ),ℂ)) :
    let w : ℂ := resonanceMass b p S M a
    let x := (radixDilation p M a:ℝ)*radixSum b p M a
    Tendsto (fun k => Weyl.cMean (fun n => (b:ℝ)^n*x) f (S*p^k)) atTop
      (𝓝 ((1-w)*Weyl.cInt f+w*f 0)) := by
  classical
  have hp := Fact.out (p:=p.Prime)
  let R := resonantCells b p S M a
  let w : ℝ := R.card/(((p:ℝ)-1)*S)
  have hw : (resonanceMass b p S M a:ℂ) = (w:ℂ) := by simp [resonanceMass,w,R]
  dsimp only; rw [hw]
  have hpr : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have pos : 0<((p:ℝ)-1)*S := by positivity
  apply circle_mixture_of_characters _ _ (fun k => Nat.mul_pos hS (pow_pos hp.pos _)) (div_nonneg (by positivity) pos.le)
  · apply (div_le_one pos).mpr
    have H := card_filter_le (Ico S (p*S)) (fun u => Polynomial.cyclotomic (orderOf (b:ZMod p)) ℚ ∣ cellPolynomial p u M a)
    change R.card≤_ at H; rw [Nat.card_Ico] at H
    have hs := Nat.le_mul_of_pos_left S hp.pos
    have hr := Nat.cast_le (α:=ℝ).mpr H
    push_cast [Nat.cast_sub hs] at hr; linarith
  · intro h hh
    simpa [mean_phase,w,R] using cyclotomic_fourier_limit hb ho hbc hS M a hm h hh

end NormalityChecker
