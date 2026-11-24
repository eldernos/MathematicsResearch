module

public import NormalityChecker.ArithmeticCertificate
public import NormalityChecker.IntervalFourier

/-! A finite interval-count bound from an approximate block certificate. -/
@[expose] public section
open Finset
namespace NormalityChecker

/-- For normalized observations, uniform estimates through frequency `H-1`
give a bound for every interval and every partial cell. The grid width `w`
and the model tolerance `δ` can be chosen independently. -/
theorem approximate_interval_count_bound {H : ℕ} [NeZero H] (f : ℕ → ℝ) (model : ℕ → ℕ → ℝ)
    {start B L T : ℕ} (hb : 0<B) (len : T≤L*B) (E : Finset ℕ) {ε δ w : ℝ}
    (he : 0≤ε) (hd : 0≤δ) (hw : 0<w) (unit : ∀ n, 0≤f n ∧ f n<1)
    (orbit : ∀ h : ℤ, h≠0 → h.natAbs<H → ∀ l<L, l∉E → ‖∑ i ∈ range B, phase (h*model l i)‖ ≤ ε*B)
    (close : ∀ l<L, l∉E → ∑ i ∈ range B, turnDistance (f (start+l*B+i)-model l i) ≤ δ*B)
    {a c : ℝ} (ha : 0≤a) (hac : a≤c) (hc : c≤1) :
    let fourierBound := (ε+2*Real.pi*H*δ)*(L*B)+(E.card+1:ℝ)*B
    |(IntervalFourier.count (fun i => f (start+i)) a c T:ℝ)-T*(c-a)| ≤
      2*(T*(4*w+3/H+(1/w)^2/H)+H*fourierBound) := by
  apply IntervalFourier.interval_count_bound _ (fun _ => unit _) ha hac hc hw (by positivity)
  intro h hn small
  apply (approximate_prefix_bound h f model hb len E he hd (orbit h hn small) close).trans
  have abs_le : |(h:ℝ)| ≤ (H:ℝ) := by
    have cast : (h.natAbs:ℤ)≤H := by exact_mod_cast small.le
    rw [Int.natCast_natAbs] at cast; exact_mod_cast cast
  gcongr

end NormalityChecker
