import RectangleCLTCompanion.SplitV4.Printed.LowerActivation
import RectangleCLTCompanion.SplitV4.Printed.LowerOptimal
import RectangleCLTCompanion.SplitV4.Printed.LowerModerateGeneral
import RectangleCLTCompanion.SplitV4.Printed.EndpointGaussian
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.uniformScalarModerateTail_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.independent_copy_variance_integral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyMaskedSignMaximum_all_active_real_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyGlobal_master_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_sparseFamily_orthantError_div_rate_printed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["LowerActivation", "LowerMaster", "LowerGlobalRates", "LowerGlobalComparison",
    "LowerPrintedThreshold", "LowerTheorems", "LowerConstruction", "LowerOptimal", "LowerGaussianShifts",
    "LowerModerateArray", "LowerModerateCumulants",
    "LowerStrictTail", "LowerModerateTail", "LowerModerateGeneral", "LowerLaplace"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.any (fun m => env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed." ++ m) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed lower/F.1 proof route"
  logInfo m!"Audited {names.size} printed common-lower/F.1 declarations; only permitted axioms."

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[``RectangleCLT.Companion.SplitV4.Printed.uniformScalarModerateTail_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.smoothingLemma2_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianEndpointSmoothing_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_fourthFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_maskedFourthFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_sparseFamily_orthantError_div_rate_printed]
  let forbidden := #[``RectangleCLT.Companion.SplitV4.smoothingLemma2,
    ``RectangleCLT.Companion.SplitV4.gaussianEndpointSmoothing,
    ``RectangleCLT.Companion.SplitV4.familyLocal_master_comparison,
    ``RectangleCLT.Companion.SplitV4.independent_local_shift_comparison,
    ``RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_amplifiedFamily_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_familyRare_discrepancy_div_scale]
  for target in targets do
    let (_, state) := ((CollectAxioms.collect target).run env).run {}
    for bad in forbidden do
      if state.visited.contains bad then
        throwError "Old alternative final route {bad} occurs in dependency closure of {target}"
  let (_, f1) := ((CollectAxioms.collect targets[0]!).run env).run {}
  for bad in #[``RectangleCLT.Companion.SplitV4.moderateTiltVariance_exp_bounds,
    ``RectangleCLT.Companion.SplitV4.moderateArray_local_taylor,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_small_threshold,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_bound] do
    if f1.visited.contains bad then
      throwError "Old alternative F.1 step {bad} occurs in literal all-threshold F.1 closure"
  for required in #[``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_taylor_printed] do
    unless f1.visited.contains required do
      throwError "Literal printed F.1 step {required} is absent from final dependency closure"
  logInfo m!"Checked {targets.size} actual printed terminal dependency closures: old alternative endpoint/local-lower finals absent; literal F.1 omits old variance-minimization and small-threshold branches."

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[``RectangleCLT.Companion.SplitV4.Printed.boundedSymmetricLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.fourthMomentLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.maskedFourthLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.sparseMomentLower_printed]
  let required := #[``RectangleCLT.Companion.SplitV4.Printed.familyGlobal_master_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error,
    ``RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_by_union_tail]
  let forbidden := #[``RectangleCLT.Companion.SplitV4.familyLocal_master_comparison,
    ``RectangleCLT.Companion.SplitV4.independent_local_shift_comparison,
    ``RectangleCLT.Companion.normalMaxThreshold,
    ``RectangleCLT.Companion.SplitV4.tendsto_gaussianMaximumMean_div_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.boundedSymmetricLower,
    ``RectangleCLT.Companion.SplitV4.fourthMomentLower,
    ``RectangleCLT.Companion.SplitV4.maskedFourthLower,
    ``RectangleCLT.Companion.SplitV4.sparseMomentLower]
  for target in targets do
    let (_, state) := ((CollectAxioms.collect target).run env).run {}
    for needed in required do
      unless state.visited.contains needed do
        throwError "Printed lower step {needed} is absent from actual terminal {target}"
    for bad in forbidden do
      if state.visited.contains bad then
        throwError "Old alternative lower step {bad} occurs in actual printed terminal {target}"
  logInfo m!"Checked {targets.size} full T4/T5/T6/T8 construction closures: global master/CDF, exact printed quantile/density, Gaussian UI mean and union-tail moments present; old local and old quantile routes absent."
