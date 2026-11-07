import RectangleCLTCompanion.SplitV4.ContinuousPartials
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasFDerivAt_of_continuous_coordinate_derivatives
#print axioms RectangleCLT.Companion.SplitV4.hasFDerivAt_of_continuous_coordinate_derivatives

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.ContinuousPartials" then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in continuous-partials calculus"
  logInfo m!"Audited {names.size} continuous-partials declarations; only the three permitted axioms."
