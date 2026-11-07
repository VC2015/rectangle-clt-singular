import RectangleCLTCompanion.SplitV4.LargeIncrementComparison
import Lean.Util.CollectAxioms

/-! Actual smooth comparison, conditional coefficients, Gaussian derivative
averages and endpoint integration in the current Appendix G proof. -/

#print RectangleCLT.Companion.SplitV4.largeIncrementComparisonConstant
#print RectangleCLT.Companion.SplitV4.largeIncrementBudgetConstant
#print RectangleCLT.Companion.SplitV4.largeIncrementMasterConstant
#print RectangleCLT.Companion.SplitV4.largeIncrementBandwidthRate
#print RectangleCLT.Companion.SplitV4.largeIncrementMasterRate
#print RectangleCLT.Companion.SplitV4.largeIncrementMatrixCost
#print RectangleCLT.Companion.SplitV4.largeIncrementMeanCost
#print RectangleCLT.Companion.SplitV4.largeIncrementFourthCost
#print RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum
#print RectangleCLT.Companion.SplitV4.pairedTailVariance
#print RectangleCLT.Companion.SplitV4.deltaOne
#print RectangleCLT.Companion.SplitV4.normalizedSummands
#check RectangleCLT.Companion.SplitV4.one_le_largeIncrementMasterConstant
#check RectangleCLT.Companion.SplitV4.normalizedSummands_gaussian_factor_exists
#check RectangleCLT.Companion.SplitV4.abs_sub_le_three_time_weights
#check RectangleCLT.Companion.SplitV4.abs_largeIncrementHessianTerm_le
#check RectangleCLT.Companion.SplitV4.abs_largeIncrementGradientTerm_le
#check RectangleCLT.Companion.SplitV4.abs_largeIncrementRemainderTerm_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.largeIncrement_smooth_expectation_comparison_conditional
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.largeIncrement_smooth_expectation_comparison
#check RectangleCLT.Companion.SplitV4.largeIncrementGaussianComparison_bandwidth
#check RectangleCLT.Companion.SplitV4.bandwidthRate_inv_mul_eq_master
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.largeIncrementGaussianComparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianComparisonWithLargeIncrementRemainders
#print axioms RectangleCLT.Companion.SplitV4.largeIncrement_smooth_expectation_comparison
#print axioms RectangleCLT.Companion.SplitV4.gaussianComparisonWithLargeIncrementRemainders

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.LargeIncrementComparison then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Appendix G smooth comparison dependency closure"
  logInfo m!"Audited {names.size} large-increment smooth comparison theorem declarations; only propext, Classical.choice and Quot.sound."
