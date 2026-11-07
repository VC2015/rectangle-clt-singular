import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorFiber
import RectangleCLTCompanion.SplitV4.Printed.ProjectionTail
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["PolarPlane", "ProjectionTail", "RidgeSector", "RidgeAngular",
    "RidgeSectorGeometry", "RidgeSectorFiber"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.any (fun m => env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed." ++ m) then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed polar/sector declarations selected"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed polar/sector argument"
  logInfo m!"Audited {names.size} printed polar, Gaussian radial-tail and sector declarations; only permitted axioms."
