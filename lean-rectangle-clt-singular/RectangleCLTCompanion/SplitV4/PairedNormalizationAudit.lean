import RectangleCLTCompanion.SplitV4.PairedNormalization
import Lean.Util.CollectAxioms

/-! Exact finite-moment normalization, fourth-moment budget and Gaussian
factor contracts. No historical boundedness or covariance-gap premise is
added to the actual observation class. -/

#print RectangleCLT.Companion.SplitV4.normalizedSummands
#print RectangleCLT.Companion.SplitV4.coordinateFourthMomentSums
#print RectangleCLT.Companion.SplitV4.arrayFourthMomentBudget
#print RectangleCLT.Companion.SplitV4.deltaOne

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_factor_exists_of_coordinate_memLp_two
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedSummands_unit_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedSummands_fourth_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTruncatedArray_normalizedSummands

#print axioms RectangleCLT.Companion.SplitV4.normalizedSummands_gaussian_factor_exists
#print axioms RectangleCLT.Companion.SplitV4.normalizedSummands_unit_covariance
#print axioms RectangleCLT.Companion.SplitV4.normalizedSummands_fourth_budget
#print axioms RectangleCLT.Companion.SplitV4.arrayFourthMomentBudget_attained

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.PairedNormalization then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in finite-moment normalization closure"
  logInfo m!"Audited {names.size} finite-moment normalization helpers."
