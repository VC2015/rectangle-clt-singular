import RectangleCLTCompanion.SplitV4.SparseLowerCalibrationLimits
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate_div_scale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCoordinateRate_div_scale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCoordinateRate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_fifth_div

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_cube_div

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerTheta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi_log

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerVariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCount

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerScale_square

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_variance_scale_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_count_cost_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_gaussian_cost_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_count_cost

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_gaussian_cost

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_gaussian_coefficient_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_gaussian_coefficient

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_coverage_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_coverage

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate_ge_bounded

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_scale_bounded_ratio

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_sparseLower_probabilities

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCoordinateRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCoordinateRate,
    ``RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate_fourth,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_fifth_div,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_cube_div,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerTheta,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi_log,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerVariance,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCount,
    ``RectangleCLT.Companion.SplitV4.sparseLowerScale_square,
    ``RectangleCLT.Companion.SplitV4.sparseLower_variance_scale_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLower_count_cost_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLower_gaussian_cost_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_count_cost,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_gaussian_cost,
    ``RectangleCLT.Companion.SplitV4.sparseLower_gaussian_coefficient_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_gaussian_coefficient,
    ``RectangleCLT.Companion.SplitV4.sparseLower_coverage_lower,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_coverage,
    ``RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate_ge_bounded,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_scale_bounded_ratio,
    ``RectangleCLT.Companion.SplitV4.eventually_sparseLower_probabilities]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual sparse lower numerical calibration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited genuine scalar sparse-mask calibration: exact powers, logarithmic probability asymptotics, original rounded-count coverage, valid probabilities and negligible genuine comparison costs."
