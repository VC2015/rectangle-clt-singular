import RectangleCLTCompanion.SplitV4.RelativeFourthRefinement
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_fourth_admissibility
#print axioms RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_fourth_admissibility

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.RelativeFourthRefinement" then
          names := names.push name
  unless names.size > 0 do
    throwError "No relative fourth-refinement declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative fourth refinement"
  logInfo m!"Audited {names.size} relative fourth-refinement declarations; only the permitted three axioms."
