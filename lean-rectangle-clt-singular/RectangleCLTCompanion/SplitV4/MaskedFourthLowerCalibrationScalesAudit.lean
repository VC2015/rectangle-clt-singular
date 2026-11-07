import RectangleCLTCompanion.SplitV4.MaskedFourthLowerCalibrationScales
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthLog

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthCount

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthTheta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthPi

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthAmplitude

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthVariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthRate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthCutoff

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthBoundedScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthLog_bounds

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthCount_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthTheta_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthAmplitude_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthScale_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthTheta_count

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_envelope_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_variance_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_fourth_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthRate_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthScale_square

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthScale_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_rate_conversion

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthPi_log_bound

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_fifth_div_le_rate_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthTheta_le_ell_div

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_fifth_div

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_cube_div

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourthTheta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourthPi_log

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourthScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourthVariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourthCount

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_variance_scale_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_count_cost_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_gaussian_cost_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_count_cost

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_gaussian_cost

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_log_half_pi

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_coverage_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_coverage

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_scale_bounded_ratio

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_scale_bounded_ratio_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_scale_bounded_ratio

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_gaussian_coefficient_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_gaussian_coefficient

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_maskedFourth_probabilities

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.maskedFourthLog,
    ``RectangleCLT.Companion.SplitV4.maskedFourthCount,
    ``RectangleCLT.Companion.SplitV4.maskedFourthTheta,
    ``RectangleCLT.Companion.SplitV4.maskedFourthPi,
    ``RectangleCLT.Companion.SplitV4.maskedFourthAmplitude,
    ``RectangleCLT.Companion.SplitV4.maskedFourthVariance,
    ``RectangleCLT.Companion.SplitV4.maskedFourthScale,
    ``RectangleCLT.Companion.SplitV4.maskedFourthRate,
    ``RectangleCLT.Companion.SplitV4.maskedFourthCutoff,
    ``RectangleCLT.Companion.SplitV4.maskedFourthBoundedScale,
    ``RectangleCLT.Companion.SplitV4.maskedFourthLog_bounds,
    ``RectangleCLT.Companion.SplitV4.maskedFourthCount_pos,
    ``RectangleCLT.Companion.SplitV4.maskedFourthTheta_pos,
    ``RectangleCLT.Companion.SplitV4.maskedFourthAmplitude_pos,
    ``RectangleCLT.Companion.SplitV4.maskedFourthScale_pos,
    ``RectangleCLT.Companion.SplitV4.maskedFourthTheta_count,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_envelope_identity,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_variance_identity,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.maskedFourthRate_fourth,
    ``RectangleCLT.Companion.SplitV4.maskedFourthScale_square,
    ``RectangleCLT.Companion.SplitV4.maskedFourthScale_fourth,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_rate_conversion,
    ``RectangleCLT.Companion.SplitV4.maskedFourthPi_log_bound,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_fifth_div_le_rate_fourth,
    ``RectangleCLT.Companion.SplitV4.maskedFourthTheta_le_ell_div,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_fifth_div,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_cube_div,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourthTheta,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourthPi_log,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourthScale,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourthVariance,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourthCount,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_variance_scale_identity,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_count_cost_identity,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_gaussian_cost_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_count_cost,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_gaussian_cost,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_log_half_pi,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_coverage_lower,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_coverage,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_scale_bounded_ratio,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_scale_bounded_ratio_lower,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_scale_bounded_ratio,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_gaussian_coefficient_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourth_gaussian_coefficient,
    ``RectangleCLT.Companion.SplitV4.eventually_maskedFourth_probabilities]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in masked fourth-moment lower numerical calibration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual deterministic Theorem 6 masked parameters, rounded-count coverage divergence, exact rate conversion, probabilities, Gaussian mean coefficient and negligible original/Gaussian second-moment costs."
