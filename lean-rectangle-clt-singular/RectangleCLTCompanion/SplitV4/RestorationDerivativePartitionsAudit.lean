import RectangleCLTCompanion.SplitV4.RestorationDerivativePartitions
import Lean.Util.CollectAxioms

/-! Exact actual derivative expectations and the first/two second
derivative partitions used in B.2. Numerical coefficients are -1, 2, -1. -/

#print RectangleCLT.Companion.SplitV4.restorationThirdExpectation
#print RectangleCLT.Companion.SplitV4.restorationFourthExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationThirdExpectation_eq_selector
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationFourthExpectation_eq_selectors
#print axioms RectangleCLT.Companion.SplitV4.restorationThirdExpectation_eq_selector
#print axioms RectangleCLT.Companion.SplitV4.restorationFourthExpectation_eq_selectors

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationDerivativePartitions" then
          names := names.push n
  unless names.size > 0 do
    throwError "No restoration derivative partition declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in restoration derivative partition closure"
  logInfo m!"Audited all {names.size} restoration derivative partition theorem declarations."
