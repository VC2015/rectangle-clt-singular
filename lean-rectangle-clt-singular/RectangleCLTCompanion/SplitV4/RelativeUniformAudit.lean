import RectangleCLTCompanion.SplitV4.RelativeUniform
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeFourthAdmissible_projected

#print axioms RectangleCLT.Companion.SplitV4.relativeFourthAdmissible_projected

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.RelativeFourthAdmissible,
    ``RectangleCLT.Companion.SplitV4.RelativeIndependentHypotheses,
    ``RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_fourth_admissible,
    ``RectangleCLT.Companion.SplitV4.RelativeIndependentHypotheses.relativeMomentBounds,
    ``RectangleCLT.Companion.SplitV4.relativeFourthAdmissible_of_envelope,
    ``RectangleCLT.Companion.SplitV4.RelativeIndependentHypotheses.of_bounded,
    ``RectangleCLT.Companion.SplitV4.relativeFourthAdmissible_projected]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative scalar/class closure"
  logInfo "Audited 7 RelativeUniform declarations; only the three standard axioms are permitted."
