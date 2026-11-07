import RectangleCLTCompanion.SplitV4.CommonPointFourth
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.coordinateFourthBudget
#print RectangleCLT.Companion.SplitV4.diagonalFourth
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.common_point_fourth_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_common_point_fourth_contraction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! == `RectangleCLTCompanion.SplitV4.CommonPointFourth then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in common-point fourth contraction dependency closure"
  logInfo m!"Audited {names.size} common-point fourth contraction theorem declarations."
