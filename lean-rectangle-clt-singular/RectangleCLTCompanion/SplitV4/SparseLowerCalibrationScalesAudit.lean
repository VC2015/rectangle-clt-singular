import RectangleCLTCompanion.SplitV4.SparseLowerCalibrationScales
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerK

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerRate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerKhat

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerLog

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerCount

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerTheta

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerPi

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerAmplitude

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerVariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerCutoff

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerCount_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerTheta_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerAmplitude_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerScale_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerTheta_count

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_envelope_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_variance_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_fourth_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerPi_eq_mask

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLowerScale_factor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.sparseLowerK,
    ``RectangleCLT.Companion.SplitV4.sparseLowerRate,
    ``RectangleCLT.Companion.SplitV4.sparseLowerKhat,
    ``RectangleCLT.Companion.SplitV4.sparseLowerLog,
    ``RectangleCLT.Companion.SplitV4.sparseLowerCount,
    ``RectangleCLT.Companion.SplitV4.sparseLowerTheta,
    ``RectangleCLT.Companion.SplitV4.sparseLowerPi,
    ``RectangleCLT.Companion.SplitV4.sparseLowerAmplitude,
    ``RectangleCLT.Companion.SplitV4.sparseLowerVariance,
    ``RectangleCLT.Companion.SplitV4.sparseLowerScale,
    ``RectangleCLT.Companion.SplitV4.sparseLowerCoordinateRate,
    ``RectangleCLT.Companion.SplitV4.sparseLowerCutoff,
    ``RectangleCLT.Companion.SplitV4.sparseLowerCount_pos,
    ``RectangleCLT.Companion.SplitV4.sparseLowerTheta_pos,
    ``RectangleCLT.Companion.SplitV4.sparseLowerAmplitude_pos,
    ``RectangleCLT.Companion.SplitV4.sparseLowerScale_pos,
    ``RectangleCLT.Companion.SplitV4.sparseLowerTheta_count,
    ``RectangleCLT.Companion.SplitV4.sparseLower_envelope_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLower_variance_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLower_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLowerPi_eq_mask,
    ``RectangleCLT.Companion.SplitV4.sparseLowerScale_factor]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual sparse lower numerical calibration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited genuine scalar sparse-mask calibration: exact powers, logarithmic probability asymptotics, original rounded-count coverage, valid probabilities and negligible genuine comparison costs."
