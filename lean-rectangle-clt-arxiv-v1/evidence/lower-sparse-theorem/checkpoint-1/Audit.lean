import RectangleCLTArxivV1.LowerSparseTheorem
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.lowerSparseKhat_factor,
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
    ``RectangleCLTArxivV1.tendsto_lowerSparseRawWidth,
    ``RectangleCLTArxivV1.eventually_lowerSparseSequence_fields,
    ``RectangleCLTArxivV1.lowerSparseCalibration_of_scalar_limits,
    ``RectangleCLTArxivV1.lowerSparse_width_rate_le_twice_of_coordinate,
    ``RectangleCLTArxivV1.eventually_lowerSparse_width_rate_le_twice,
    ``RectangleCLTArxivV1.eventually_lowerSparse_membership,
    ``RectangleCLTArxivV1.exists_lowerSparse_actual_detection_constant,
    ``RectangleCLTArxivV1.exists_lowerSparse_upper_constant,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_lower,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_two_sided]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_lower,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_two_sided]
  let action : CollectAxioms.M Unit := targets.forM CollectAxioms.collect
  let (_,deps) := (action.run env).run {}
  let blocked := #["RectangleCLT.Companion.SplitV4.sparseFamilyCalibration",
    "RectangleCLT.Companion.SplitV4.sparsePaperCalibration",
    "RectangleCLT.Companion.SplitV4.eventually_sparseFamily_parameters",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLowerScale_of_paperRate",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLowerTheta",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLowerVariance",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLower_scale_bounded_ratio"]
  for n in deps.visited.toList do
    if blocked.contains n.toString then
      throwError "Forbidden old worst-dimension scale-small route {n}"
  let required := #[``RectangleCLTArxivV1.lowerSparseCalibration_of_scalar_limits,
    ``RectangleCLTArxivV1.tendsto_lowerSparseRawWidth,
    ``RectangleCLTArxivV1.tendsto_lowerSparseTheta,
    ``RectangleCLTArxivV1.tendsto_lowerSparseVariance,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEffectiveAmplitude,
    ``RectangleCLTArxivV1.exists_lowerFamily_masked_width_detection_constant,
    ``RectangleCLTArxivV1.eventually_lowerSparse_membership,
    ``RectangleCLTArxivV1.theorem_2_ii_intrinsic]
  for n in required do
    unless deps.visited.contains n then
      throwError "Sparse final proof route omits required checked declaration {n}"
  logInfo m!"Checked sparse final proof route through {deps.visited.size} constants: no forbidden old scale-small route; every required actual-law, weak-width and matching-upper component present."
