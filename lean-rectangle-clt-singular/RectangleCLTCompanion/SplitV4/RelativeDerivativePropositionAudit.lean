import RectangleCLTCompanion.SplitV4.RelativeDerivativeProposition
import Lean.Util.CollectAxioms

/-! Exact Proposition 1 contracts and strict axiom closure. -/

#print RectangleCLT.Companion.SplitV4.relativeDerivativeBandwidth
#print RectangleCLT.Companion.SplitV4.relativeDerivativeConstant
#print RectangleCLT.Companion.SplitV4.RelativeDerivativePropositionContract
#print RectangleCLT.Companion.SplitV4.initializationDiscrepancy
#print RectangleCLT.Companion.SplitV4.directInitializationGap
#print RectangleCLT.Companion.SplitV4.normalizedSeededCubicTerm
#print RectangleCLT.Companion.SplitV4.normalizedSeededFourthRemainder
#print RectangleCLT.Companion.SplitV4.normalizedSeededExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.proposition_relative_derivatives
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relative_derivative_proposition
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relative_smooth_comparison_bound
#print axioms RectangleCLT.Companion.SplitV4.proposition_relative_derivatives
#print axioms RectangleCLT.Companion.SplitV4.relative_smooth_comparison_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! == `RectangleCLTCompanion.SplitV4.RelativeDerivativeProposition then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in whole relative derivative proposition closure"
  logInfo m!"Audited all {names.size} whole relative derivative proposition theorem declarations."
