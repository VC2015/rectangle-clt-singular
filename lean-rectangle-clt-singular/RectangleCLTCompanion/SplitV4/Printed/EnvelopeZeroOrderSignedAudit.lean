import RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrderSigned
import Lean.Util.CollectAxioms

#print axioms RectangleCLT.Companion.SplitV4.Printed.signedTwoFaceSmoother_eq_closedBox
#print axioms RectangleCLT.Companion.SplitV4.Printed.no_uniform_signed_zero_order_averaged_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrderSigned" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed signed-face order-zero counterexample"
  logInfo m!"Audited {names.size} signed-face order-zero scope theorem declarations; only the permitted three axioms."
