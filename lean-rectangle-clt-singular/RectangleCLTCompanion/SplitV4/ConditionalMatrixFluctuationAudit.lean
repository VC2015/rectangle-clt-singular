import RectangleCLTCompanion.SplitV4.ConditionalMatrixFluctuation
import Lean.Util.CollectAxioms

/-! Strict audit of actual centered rank-one matrix fluctuations and their
conditional averages. Matrix entries may be dependent within
each summand; only independence of the whole summands is required. -/

#print RectangleCLT.Companion.SplitV4.matrixFluctuationConstant
#print RectangleCLT.Companion.SplitV4.matrixMaxEntryNorm
#print RectangleCLT.Companion.SplitV4.centeredRankOneSum
#print RectangleCLT.Companion.SplitV4.centeredRankOnePiSum
#check RectangleCLT.Companion.SplitV4.norm_matrixEntriesVector
#check RectangleCLT.Companion.SplitV4.centeredRankOneEntries_boundedHypotheses
#check RectangleCLT.Companion.SplitV4.centeredRankOneEntries_variance_budget
#check RectangleCLT.Companion.SplitV4.integrable_centeredRankOnePiSum
#check RectangleCLT.Companion.SplitV4.measurable_copyArrayTruncatedCovariance_entry
#check RectangleCLT.Companion.SplitV4.copyArrayTruncatedCovariance_eq_copy_integral
#check RectangleCLT.Companion.SplitV4.integral_copyArrayTruncatedCovariance_eq
#check RectangleCLT.Companion.SplitV4.half_copyAverage_centeredRankOnePiSum_paired_ae_eq
#check RectangleCLT.Companion.SplitV4.integrable_copyArrayTruncatedCovariance_fluctuation
#check RectangleCLT.Companion.SplitV4.integrable_copyArrayTruncatedCovariance_sub_const
#check RectangleCLT.Companion.SplitV4.integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_centeredRankOneSum_norm_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_half_copyAverage_centeredRankOneSum_norm_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_copyArrayTruncatedCovariance_fluctuation_le

#print axioms RectangleCLT.Companion.SplitV4.expected_centeredRankOneSum_norm_le
#print axioms RectangleCLT.Companion.SplitV4.expected_half_copyAverage_centeredRankOneSum_norm_le
#print axioms RectangleCLT.Companion.SplitV4.expected_copyArrayTruncatedCovariance_fluctuation_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.ConditionalMatrixFluctuation then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional matrix fluctuation dependency closure"
  logInfo m!"Audited {names.size} conditional matrix fluctuation theorems; only propext, Classical.choice and Quot.sound."
