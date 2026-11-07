import RectangleCLTCompanion.SplitV4.GaussianThresholdIdentity
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianThresholdTrace_update
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_eq_raw
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_identity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianThresholdTrace_update,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_eq_raw,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_identity]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual common-threshold derivative identity"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual radial-trace coordinate derivatives and the full common-threshold identity, retaining the exact ordered-pair factor one half."
