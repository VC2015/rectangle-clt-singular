import RectangleCLTCompanion.SplitV4.BennettCalibration
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_large_calibration_identities

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_large_tail_identities

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.bennett_large_calibration_identities,
    ``RectangleCLT.Companion.SplitV4.bennett_large_tail_identities]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in Bennett large-regime calibration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited exact Bennett large-regime amplitude, cost, maximum, and denominator identities."
