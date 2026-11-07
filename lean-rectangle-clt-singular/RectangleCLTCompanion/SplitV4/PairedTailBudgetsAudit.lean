import RectangleCLTCompanion.SplitV4.PairedTailBudgets
import Lean.Util.CollectAxioms

/-! The actual conditional large-mean and covariance truncation budgets,
with the expected maximum of the sum and the exact factor one half. -/

#print RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum
#print RectangleCLT.Companion.SplitV4.pairedTailCoordinateSecond
#print RectangleCLT.Companion.SplitV4.pairedTailVariance
#print RectangleCLT.Companion.SplitV4.meanTruncatedCovariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_copyArrayLargeMean_norm_le_of_memLp_two
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.half_sum_pairedIncrement_product_eq_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.meanTruncatedCovariance_bias_norm_le

#print axioms RectangleCLT.Companion.SplitV4.expected_copyArrayLargeMean_norm_le_of_memLp_two
#print axioms RectangleCLT.Companion.SplitV4.half_sum_pairedIncrement_product_eq_covariance
#print axioms RectangleCLT.Companion.SplitV4.meanTruncatedCovariance_bias_norm_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.PairedTailBudgets then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in paired tail-budget closure"
  logInfo m!"Audited {names.size} actual paired tail and covariance-bias budgets."
