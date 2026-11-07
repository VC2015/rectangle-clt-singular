import RectangleCLTCompanion.SplitV4.RestorationConditionalInterchange
import Lean.Util.CollectAxioms

/-! Genuine integrability and dominated-convergence audit for B.2. -/
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.translated_score_array_series_interchange
#print axioms RectangleCLT.Companion.SplitV4.integrable_random_repeatedDirectionScore
#print axioms RectangleCLT.Companion.SplitV4.translated_score_array_series_interchange

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationConditionalInterchange" then
          names := names.push n
  unless names.size > 0 do
    throwError "No conditional restoration interchange declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional restoration interchange closure"
  logInfo m!"Audited all {names.size} conditional restoration interchange theorem declarations."
