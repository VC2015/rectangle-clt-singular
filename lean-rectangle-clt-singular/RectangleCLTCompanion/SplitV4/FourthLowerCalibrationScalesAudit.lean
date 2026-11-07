import RectangleCLTCompanion.SplitV4.FourthLowerCalibrationScales
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerTheta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerAmplitude

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerRate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerTheta_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerScale_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerRate_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerScale_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerRate_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerRate_scale_ratio_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLowerRate_div_scale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLower_cube_div_le_rate_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLower_cube_div

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLowerTheta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerScale_le_rate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLowerScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourth_amplitude_square_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourth_amplitude_fourth_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourth_amplitude_inverse_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_square

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_sqrt_cube_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude_sqrt_cube

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude_square_theta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_fourthLowerAmplitude_ge_one

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude_inv

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_fourthLowerTheta_lt_quarter

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.fourthLowerTheta,
    ``RectangleCLT.Companion.SplitV4.fourthLowerAmplitude,
    ``RectangleCLT.Companion.SplitV4.fourthLowerScale,
    ``RectangleCLT.Companion.SplitV4.fourthLowerRate,
    ``RectangleCLT.Companion.SplitV4.fourthLowerTheta_pos,
    ``RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_pos,
    ``RectangleCLT.Companion.SplitV4.fourthLowerScale_pos,
    ``RectangleCLT.Companion.SplitV4.fourthLowerRate_pos,
    ``RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_fourth,
    ``RectangleCLT.Companion.SplitV4.fourthLowerScale_fourth,
    ``RectangleCLT.Companion.SplitV4.fourthLowerRate_fourth,
    ``RectangleCLT.Companion.SplitV4.fourthLowerRate_scale_ratio_fourth,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLowerRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.fourthLower_cube_div_le_rate_fourth,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLower_cube_div,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLowerTheta,
    ``RectangleCLT.Companion.SplitV4.fourthLowerScale_le_rate,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLowerScale,
    ``RectangleCLT.Companion.SplitV4.fourth_amplitude_square_identity,
    ``RectangleCLT.Companion.SplitV4.fourth_amplitude_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.fourth_amplitude_inverse_identity,
    ``RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_square,
    ``RectangleCLT.Companion.SplitV4.fourthLowerAmplitude_sqrt_cube_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude_sqrt_cube,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude_square_theta,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude,
    ``RectangleCLT.Companion.SplitV4.eventually_fourthLowerAmplitude_ge_one,
    ``RectangleCLT.Companion.SplitV4.tendsto_fourthLowerAmplitude_inv,
    ``RectangleCLT.Companion.SplitV4.eventually_fourthLowerTheta_lt_quarter]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in deterministic fourth-moment lower calibration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited deterministic fourth-moment amplitude calibration, exact theta identities, rate/shift limit four, vanishing Taylor ratios, variance and amplitude limits."
