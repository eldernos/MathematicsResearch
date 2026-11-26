import NormalityChecker.LocalizedJoint
import NormalityChecker.LocalizedCertificateModulus
import NormalityChecker.LocalizedSignedAxis
import NormalityChecker.LocalizedDiscrepancy
import NormalityChecker.LocalizedMixed
import NormalityChecker.MaskPeriods
import NormalityChecker.MaskDensity
import NormalityChecker.MaskQuotients
import NormalityChecker.MaskThirds
import NormalityChecker.MaskWindows
import NormalityChecker.HigherOrderPhase
import NormalityChecker.JointPersistent
import NormalityChecker.SmoothOrbit
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  let L := "NormalityChecker.LocalizedSupport."
  let P := "NormalityChecker.PolynomialMasks."
  let names : List String :=
    [L++"unsigned_discrepancy_limit", L++"unsigned_finite_support_normal", L++"unsigned_persistent_null",
     L++"unsigned_certificate_tendsTo_zero", L++"discrepancy_le_certificate", L++"persistent_iff_phaseMoment_zero",
     L++"discrepancy_tracks_jointPhase", L++"jointOrder_density_tendsTo_discrepancy", L++"discrepancy_eq_log_flow_max",
     L++"order_two_deep_counterexample", L++"distinct_orders_checked", L++"joint_full_orders",
     L++"joint_full_polynomial_orders", L++"joint_of_masked_poles", L++"joint_axis_orders_iff",
     L++"joint_infinite_axis_orders", L++"joint_late_twos_orders", L++"certificateModulus_spec",
     L++"exists_common_depth", L++"periodic_axis_normal_iff", L++"periodic_axis_counterexample",
     P++"full_rational_normal_iff", P++"rational_boundary", P++"rational_grid", P++"integer_mask_maximal",
     P++"masked_cancel", P++"rational_window_bound", P++"axis_normal_iff", P++"rational_pole_bound",
     P++"bounded_gap_discrepancy", P++"late_powers_discrepancy", P++"normal_of_late_twos",
     P++"quotient_window_bound", P++"ternary_linear_thirds", P++"dyadic_reciprocal_thirds",
     P++"exact_window_density", P++"periodic_discrepancy", P++"periodic_mask_price",
     "NormalityChecker.Localized.discrepancy_rate", "NormalityChecker.Localized.value_eq_series",
     "NormalityChecker.Localized.series_normal", "NormalityChecker.fixed_support_orbit_estimate"]
  -- A missing declaration or an unexpected axiom is an error, so that the exit status of
  -- `lake env lean` can serve as audit evidence, as in `Check.lean`.
  for n in names do
    let decl := n.toName
    let env ← getEnv
    unless env.contains decl do
      throwError "missing declaration {n}"
    let axioms ← collectAxioms decl
    let bad := axioms.filter fun a => !permitted.contains a
    unless bad.isEmpty do
      throwError "{n} depends on unexpected axioms {bad}"
    logInfo m!"OK  {n}"
