import RectangleCLTCompanion.SplitV4.CoordinateDuplication
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleDistance_duplicateCoordinates_of_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.coordinatePadding_pairGap_zero_of_unit_gram

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.CoordinateDuplication" then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in coordinate duplication"
  logInfo m!"Audited {names.size} coordinate duplication declarations; only the three permitted axioms."
