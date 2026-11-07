import RectangleCLTCompanion.SplitV4.RestorationPairedBounds
import Lean.Util.CollectAxioms

/-! Actual paired third/fourth expectation bounds, baseline and signed
M1 / two-face M2 refinements, with the zero-scale case kept explicit. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_paired_baseline_of_matrixEstimate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_third_relative_signed_of_matrixEstimate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_fourth_relative_pair_of_matrixEstimate
#print axioms RectangleCLT.Companion.SplitV4.restoration_paired_baseline_of_matrixEstimate
#print axioms RectangleCLT.Companion.SplitV4.restoration_third_relative_signed_of_matrixEstimate
#print axioms RectangleCLT.Companion.SplitV4.restoration_fourth_relative_pair_of_matrixEstimate

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationPairedBounds" then
          names := names.push n
  unless names.size > 0 do
    throwError "No paired restoration bounds found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in paired restoration bounds closure"
  logInfo m!"Audited all {names.size} paired restoration bound theorem declarations."
