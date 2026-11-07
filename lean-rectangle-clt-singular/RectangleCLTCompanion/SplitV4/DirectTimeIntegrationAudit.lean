import RectangleCLTCompanion.SplitV4.DirectTimeIntegration
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.direct_time_increment_le

#print axioms RectangleCLT.Companion.SplitV4.direct_time_increment_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let action : CollectAxioms.M Unit := CollectAxioms.collect ``RectangleCLT.Companion.SplitV4.direct_time_increment_le
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in direct time integration"
  logInfo "Audited 1 DirectTimeIntegration declaration; only the three standard axioms are permitted."
