import RectangleCLTArxivV1.LowerSparseReadingOrder
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
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
    ``RectangleCLTArxivV1.tendsto_lowerSparseRawWidth,
    ``RectangleCLTArxivV1.eventually_lowerSparseSequence_fields,
    ``RectangleCLTArxivV1.lowerSparseCalibration_of_scalar_limits,
    ``RectangleCLTArxivV1.lowerSparse_width_rate_le_twice_of_coordinate,
    ``RectangleCLTArxivV1.eventually_lowerSparse_width_rate_le_twice,
    ``RectangleCLTArxivV1.eventually_lowerSparse_membership,
    ``RectangleCLTArxivV1.exists_lowerSparse_actual_detection_constant,
    ``RectangleCLTArxivV1.exists_lowerSparse_upper_constant,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_lower,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_two_sided,
    ``RectangleCLTArxivV1.lowerSparseIntrinsicK_four,
    ``RectangleCLTArxivV1.lowerSparseIntrinsicRate_four,
    ``RectangleCLTArxivV1.lowerSparseSequence_four,
    ``RectangleCLTArxivV1.lowerSparse_cube_dimension_sq_le_coordinateWidth_fourth,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEll_cube_dimensionLog_sq_div,
    ``RectangleCLTArxivV1.lowerSparseCalibration_from_headline,
    ``RectangleCLT.Companion.SplitV4.sparseLower_envelope_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLower_variance_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLower_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.sparseLowerTheta_count,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi_log,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCount,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_coverage,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_gaussian_coefficient,
    ``RectangleCLT.Companion.SplitV4.familyMasked_failure_bound,
    ``RectangleCLT.Companion.SplitV4.tendsto_familyMasked_maximum_mean_ratio,
    ``RectangleCLT.Companion.SplitV4.integral_familyMaskedSignMaximum_sq_le,
    ``RectangleCLTArxivV1.lowerFamily_masked_shift_second_moment_budget,
    ``RectangleCLTArxivV1.tendsto_lowerFamilyMasked_reverse_mean_ratio,
    ``RectangleCLTArxivV1.tendsto_lowerFamilyMaskedMasterRemainder_div_width,
    ``RectangleCLTArxivV1.eventually_lowerFamily_masked_leading_range,
    ``RectangleCLTArxivV1.exists_lowerFamily_masked_width_detection_constant,
    ``RectangleCLTArxivV1.lowerFamilyMasked_width_profile,
    ``RectangleCLTArxivV1.lowerFamilyGaussian_width_bounds,
    ``RectangleCLTArxivV1.lemma_lower_family_properties,
    ``RectangleCLTArxivV1.theorem_6_growing_fourth_moment_lower]
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then
      continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := ci.type.getUsedConstants ++
      (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])
    let deps := deps.toList.eraseDups.toArray
    let projectDeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining"
    graph := graph.push <| Json.mkObj [
      ("name", toJson target.toString),
      ("direct_project_dependencies", toJson (projectDeps.map Name.toString))]
    queue := projectDeps.toList ++ queue
    if targets.contains target then
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "F6 actual two-count sparse lower proofs, full exported types and project dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
