import RectangleCLTCompanion.SplitV4.PairedMoments
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.pairedIncrement
#print RectangleCLT.Companion.SplitV4.pairedTruncatedArray
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.iIndepFun_pairedTruncatedArray
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_pairedIncrement_fourth_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_pairedFourthBudget_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_pairedFourthBudget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.PairedMoments" then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in paired moment/independence dependency closure"
  logInfo m!"Audited {names.size} paired moment and independence theorem declarations."
