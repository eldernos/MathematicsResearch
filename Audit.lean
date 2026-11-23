import NormalityChecker
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  let results := [
    ``NormalityChecker.normalIn_iff_uniform_approx,
    ``NormalityChecker.not_normal_of_frequent_excess,
    ``NormalityChecker.logTwo_tail_bounds,
    ``NormalityChecker.logTwo_normal_iff,
    ``NormalityChecker.logPrefix_run_bound,
    ``NormalityChecker.pair_divisibility,
    ``NormalityChecker.resonant_zero_block,
    ``NormalityChecker.components_not_binary_normal,
    ``NormalityChecker.hasSum_components_logTwo,
    ``NormalityChecker.ordered_phase_ne_zero,
    ``NormalityChecker.logDen_ten,
    ``NormalityChecker.logDen_dvd_lcm,
    ``NormalityChecker.prime_cancellation,
    ``NormalityChecker.logLoss_nonneg,
    ``NormalityChecker.logLoss_le,
    ``NormalityChecker.logLoss_isBigO,
    ``NormalityChecker.tendsto_logDen_div,
    ``NormalityChecker.reciprocal_logDen]
  for decl in results do
    let axioms ← collectAxioms decl
    let unexpected := axioms.filter fun a => !permitted.contains a
    unless unexpected.isEmpty do
      throwError "{decl} depends on unexpected axioms {unexpected}"
    logInfo m!"{decl}: {axioms}"
