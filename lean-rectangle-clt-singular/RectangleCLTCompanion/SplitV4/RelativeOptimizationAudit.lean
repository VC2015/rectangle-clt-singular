import RectangleCLTCompanion.SplitV4.RelativeOptimization
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relative_rate_of_small_bandwidth_estimate

#print axioms RectangleCLT.Companion.SplitV4.relative_rate_of_small_bandwidth_estimate

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.relativeRate_envelope_le,
    ``RectangleCLT.Companion.SplitV4.relativeRate_envelope_capped_le,
    ``RectangleCLT.Companion.SplitV4.relativeRate,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth,
    ``RectangleCLT.Companion.SplitV4.relativeComparisonLog,
    ``RectangleCLT.Companion.SplitV4.relativeOptimizationConstant,
    ``RectangleCLT.Companion.SplitV4.relativeRate_nonneg,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_admissible,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_pos,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_le_sum,
    ``RectangleCLT.Companion.SplitV4.log_one_add_square_le_logPlus,
    ``RectangleCLT.Companion.SplitV4.relativeComparisonLog_le_D_L,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_fourth_cost_le,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_total_cost_le,
    ``RectangleCLT.Companion.SplitV4.large_relativeBandwidth_rate,
    ``RectangleCLT.Companion.SplitV4.relative_rate_of_small_bandwidth_estimate]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative scalar/class closure"
  logInfo "Audited 16 RelativeOptimization declarations; only the three standard axioms are permitted."
