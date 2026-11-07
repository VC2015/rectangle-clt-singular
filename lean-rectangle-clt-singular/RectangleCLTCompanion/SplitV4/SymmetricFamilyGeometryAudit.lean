import RectangleCLTCompanion.SplitV4.SymmetricFamilyGeometry
import Lean.Util.CollectAxioms

/-! Strict audit for the actual common-family covariance rank and gap. -/

#print RectangleCLT.Companion.SplitV4.additiveGridFactor
#print RectangleCLT.Companion.SplitV4.additiveGridKernelVector
#print RectangleCLT.Companion.SplitV4.familyPairCovariance
#print RectangleCLT.Companion.SplitV4.familyCovariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.additiveGridFactor_ker
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyCovariance_rank
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyCovariance_pairGap

#print axioms RectangleCLT.Companion.SplitV4.additiveGridFactor_ker
#print axioms RectangleCLT.Companion.SplitV4.additiveGridFactor_rank
#print axioms RectangleCLT.Companion.SplitV4.familyCovariance_rank
#print axioms RectangleCLT.Companion.SplitV4.familyCovariance_maxOffDiagonal
#print axioms RectangleCLT.Companion.SplitV4.familyCovariance_pairGap

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.SymmetricFamilyGeometry" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in symmetric-family geometry closure"
  logInfo m!"Audited {names.size} symmetric-family geometry theorem declarations; only the permitted three axioms."
  logInfo "Actual covariance rank is 2*m-1 and the pair gap is v, with no rank assumption as a premise."
