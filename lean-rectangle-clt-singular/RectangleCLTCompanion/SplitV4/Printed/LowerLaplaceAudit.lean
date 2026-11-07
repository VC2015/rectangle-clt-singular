import RectangleCLTCompanion.SplitV4.Printed.LowerLaplace
import Lean.Util.CollectAxioms

#print axioms RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison
#print axioms RectangleCLT.Companion.SplitV4.Printed.integrable_strict_laplace_correction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.LowerLaplace" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed strict Laplace closure"
  logInfo m!"Audited {names.size} printed strict Laplace theorem declarations; only the permitted three axioms."
