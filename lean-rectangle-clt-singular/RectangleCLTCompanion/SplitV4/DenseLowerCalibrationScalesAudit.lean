import RectangleCLTCompanion.SplitV4.DenseLowerCalibrationScales
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerAmplitude

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.dense_amplitude_inverse_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.dense_amplitude_moment_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.dense_amplitude_square_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.dense_amplitude_fourth_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerAmplitude_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerScale_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerScale_factor

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate_div_scale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerEnvelopeRate_div_scale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate_root

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLower_cube_div_le_rate_root

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLower_cube_div

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerTheta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseLowerAmplitude_sqrt_cube_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_sqrt_cube

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_moment_theta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_square_theta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_fourth_theta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_inv

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_denseLowerAmplitude_ge_one

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_denseLowerVariance_lt_half

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.denseLowerAmplitude,
    ``RectangleCLT.Companion.SplitV4.denseLowerScale,
    ``RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate,
    ``RectangleCLT.Companion.SplitV4.dense_amplitude_inverse_identity,
    ``RectangleCLT.Companion.SplitV4.dense_amplitude_moment_identity,
    ``RectangleCLT.Companion.SplitV4.dense_amplitude_square_identity,
    ``RectangleCLT.Companion.SplitV4.dense_amplitude_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.denseLowerAmplitude_pos,
    ``RectangleCLT.Companion.SplitV4.denseLowerScale_pos,
    ``RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate_pos,
    ``RectangleCLT.Companion.SplitV4.denseLowerScale_factor,
    ``RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerEnvelopeRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.denseLowerEnvelopeRate_root,
    ``RectangleCLT.Companion.SplitV4.denseLower_cube_div_le_rate_root,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLower_cube_div,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerTheta,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerScale,
    ``RectangleCLT.Companion.SplitV4.denseLowerAmplitude_sqrt_cube_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_sqrt_cube,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_moment_theta,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_square_theta,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_fourth_theta,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerAmplitude_inv,
    ``RectangleCLT.Companion.SplitV4.eventually_denseLowerAmplitude_ge_one,
    ``RectangleCLT.Companion.SplitV4.eventually_denseLowerVariance_lt_half]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in dense polynomial lower numerical calibration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited dense q>4 amplitude calibration, exact moment identities, prescribed envelope/shift ratio, vanishing Taylor and variance/fourth moments, and divergent amplitude."
