import RectangleCLTCompanion.SplitV4.SeededRelativeCopyBudgets
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_copy_conditional_third_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fourth_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fresh_fourth_budget
#print axioms RectangleCLT.Companion.SplitV4.seeded_copy_conditional_third_budget
#print axioms RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fourth_budget
#print axioms RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fresh_fourth_budget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.SeededRelativeCopyBudgets" then
          names := names.push n
  unless names.size > 0 do
    throwError "No seeded relative copy budget declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in seeded relative copy budget closure"
  logInfo m!"Audited all {names.size} seeded relative copy budget theorem declarations."
