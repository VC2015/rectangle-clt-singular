import RectangleCLTCompanion.SplitV4.PairedCoefficients
import Lean.Util.CollectAxioms

/-! Strict audit of actual conditional-copy coefficient contractions. -/

#print RectangleCLT.Companion.SplitV4.copyLargeIncrementMean
#print RectangleCLT.Companion.SplitV4.copyTruncatedCovariance
#print RectangleCLT.Companion.SplitV4.C4Test.hessianCoordinate
#print RectangleCLT.Companion.SplitV4.C4Test.hessianTrace

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hessianTrace_copyTruncatedCovariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.gradient_copyLargeIncrementMean
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.integral_hessianTrace_copyTruncatedCovariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.integral_gradient_copyLargeIncrementMean
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.shifted_hessianTrace_copyArrayTruncatedCovariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.shifted_gradient_copyArrayLargeMean

#print axioms RectangleCLT.Companion.SplitV4.C4Test.secondDiagonal_eq_rankOne_hessianTrace
#print axioms RectangleCLT.Companion.SplitV4.C4Test.hessianTrace_copyTruncatedCovariance
#print axioms RectangleCLT.Companion.SplitV4.C4Test.gradient_copyLargeIncrementMean
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_hessianTrace_copyTruncatedCovariance
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_gradient_copyLargeIncrementMean
#print axioms RectangleCLT.Companion.SplitV4.C4Test.shifted_hessianTrace_copyArrayTruncatedCovariance
#print axioms RectangleCLT.Companion.SplitV4.C4Test.shifted_gradient_copyArrayLargeMean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.PairedCoefficients" then
          names := names.push n
  unless names.size > 0 do
    throwError "No paired-coefficient theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in paired-coefficient dependency closure"
  logInfo m!"Audited all {names.size} paired-coefficient theorem declarations, including private helpers."
