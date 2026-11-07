import RectangleCLTCompanion.SplitV4.LogisticMatrixPaper
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exists_logistic_matrix_paper_constant
#print axioms RectangleCLT.Companion.SplitV4.exists_logistic_matrix_paper_constant

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.LogisticMatrixPaper" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in paper matrix edge wrappers"
  logInfo m!"Audited {names.size} zero-scale and quantified-constant theorem declarations; only the permitted three axioms."
