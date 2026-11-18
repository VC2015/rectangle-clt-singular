import RectangleCLTArxivV1.LowerSparseWidthLimits
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.lowerSparseKhat_factor,
    ``RectangleCLTArxivV1.lowerSparse_logKhat_sub_bound,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_eq,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_factor,
    ``RectangleCLTArxivV1.lowerSparseCoordinateWidth_fourth,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_pos,
    ``RectangleCLTArxivV1.lowerSparse_cube_div_le_coordinateWidth_fourth,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_le_intrinsicRate,
    ``RectangleCLTArxivV1.lowerSparseIntrinsicRate_le_raw,
    ``RectangleCLTArxivV1.eventually_lowerSparse_logKhat_sub_bound,
    ``RectangleCLTArxivV1.tendsto_lowerSparseKhat,
    ``RectangleCLTArxivV1.eventually_lowerSparseLog_bounds,
    ``RectangleCLTArxivV1.tendsto_lowerSparseLog_div_rareLog,
    ``RectangleCLTArxivV1.tendsto_lowerSparseCoordinateWidth,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEll_cube_div,
    ``RectangleCLTArxivV1.tendsto_lowerSparseTheta,
    ``RectangleCLTArxivV1.tendsto_lowerSparseVariance,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEffectiveAmplitude,
    ``RectangleCLTArxivV1.tendsto_lowerSparseRawWidth]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
