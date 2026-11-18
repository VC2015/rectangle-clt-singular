import RectangleCLTArxivV1.ConcentrationLemma
import RectangleCLTArxivV1.SeededIntrinsicConcentration
import RectangleCLTArxivV1.NormalizedObservationsIntrinsic
import RectangleCLTArxivV1.SmoothingError
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_test_transport,
    ``RectangleCLT.Companion.SplitV4.cubePairDifference_bound,
    ``RectangleCLT.Companion.SplitV4.integral_cubeConditionalRowSquares_coordinate,
    ``RectangleCLTArxivV1.projectedObservations_boundedHypotheses,
    ``RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_eq_half_copy,
    ``RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_le_norm_sum,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed_avg,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_translated_boundary_printed,
    ``RectangleCLTArxivV1.coordinateBoundary_product_printed,
    ``RectangleCLT.Companion.SplitV4.finiteMaximum_pair_contraction,
    ``RectangleCLT.Companion.SplitV4.cube_average_contraction,
    ``RectangleCLT.Companion.SplitV4.cube_square_contraction_intrinsic,
    ``RectangleCLT.Companion.SplitV4.independent_square_sum_fluctuation_le,
    ``RectangleCLT.Companion.SplitV4.probability_bad_rows_le_norm_fluctuation,
    ``RectangleCLT.Companion.SplitV4.cube_pair_bad_variance_probability_le,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed,
    ``RectangleCLTArxivV1.coordinateLayer_product_printed,
    ``RectangleCLTArxivV1.boundedFaceLayer_intrinsic,
    ``RectangleCLT.BoundedIndependentHypotheses.integral_norm_sum_le_of_variance,
    ``RectangleCLTArxivV1.coordinateLayer_product_log_printed,
    ``RectangleCLTArxivV1.boundedRectangleBoundary_product_logarithmic,
    ``RectangleCLTArxivV1.integral_norm_le_independent_add,
    ``RectangleCLTArxivV1.integral_norm_finset_sum_mono,
    ``RectangleCLTArxivV1.integral_norm_maskObservationSum_le,
    ``RectangleCLTArxivV1.integral_norm_bernoulliArraySum_le,
    ``RectangleCLTArxivV1.seededRectangleBoundary_intrinsic_bounded_dominant,
    ``RectangleCLTArxivV1.seededRectangleBoundary_intrinsic_gaussian_dominant,
    ``RectangleCLTArxivV1.seededRectangleBoundary_logarithmic,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_bounded_endpoint,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussian_endpoint,
    ``RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_unit,
    ``RectangleCLT.Companion.SplitV4.gaussianFaceRow_normSq,
    ``RectangleCLTArxivV1.gaussianModel_covariance,
    ``RectangleCLTArxivV1.gaussianModel_supported_on_factor_range,
    ``RectangleCLTArxivV1.mergedGaussianThreshold_le,
    ``RectangleCLTArxivV1.mergedGaussianThreshold_attains,
    ``RectangleCLTArxivV1.gaussianAffineMaximum_merge_thresholds,
    ``RectangleCLT.Companion.SplitV4.gaussianFaceWeight_nonneg,
    ``RectangleCLT.Companion.SplitV4.gaussianFaceWeight_sum,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_hasDerivAt,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_hasDerivAt,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_le_one,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceHessian_trace_nonneg,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_test_bound,
    ``RectangleCLTArxivV1.positiveGaussianFaceMaximum_eq_projection_norm,
    ``RectangleCLT.Companion.SplitV4.gaussian_affine_branches_ae_distinct_rows_ne,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_tendsto_one,
    ``RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianLinearRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp_deriv_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsicGaussianBoundary_printed_mollification,
    ``RectangleCLTArxivV1.gaussianUnitRowsBoundary_printed,
    ``RectangleCLT.Companion.SplitV4.integral_exp_positiveGaussianFaceMaximum_le,
    ``RectangleCLT.Companion.SplitV4.integral_positiveGaussianFaceMaximum_le_sqrt_log,
    ``RectangleCLTArxivV1.gaussianUnitRowsMaximum_logarithmic,
    ``RectangleCLTArxivV1.gaussianFaceNorm_mean_le_sharp,
    ``RectangleCLTArxivV1.face_log_le_two_dimensionLog,
    ``RectangleCLTArxivV1.gaussianFaceNorm_mean_le_dimension,
    ``RectangleCLTArxivV1.gaussianFaceNorm_intrinsic_coefficient_le,
    ``RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_projection_norm,
    ``RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_integral_projection_norm,
    ``RectangleCLT.Companion.SplitV4.gaussianPolyhedronLayer_subset_standardized_shell,
    ``RectangleCLTArxivV1.normalizedGaussianFaceRows_opposite,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift,
    ``RectangleCLT.Companion.SplitV4.product_event_probability_le_of_sections,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_product,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_independent_shift,
    ``RectangleCLTArxivV1.lemma_C1_gaussian_model,
    ``RectangleCLTArxivV1.sum_normalizedObservationArray,
    ``RectangleCLTArxivV1.boundedIndependent_normalizedObservationArray,
    ``RectangleCLTArxivV1.covariance_normalizedObservationArray_diagonal,
    ``RectangleCLTArxivV1.normalized_intrinsic_envelope_rate,
    ``RectangleCLTArxivV1.normalizedObservationsIntrinsicCLT,
    ``RectangleCLTArxivV1.corollary_1_normalized_observations,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_nonneg_radius,
    ``RectangleCLTArxivV1.endpoint_error_le_intrinsic_average_radius,
    ``RectangleCLTArxivV1.rectangleDistance_le_smoothingDiscrepancy_intrinsic,
    ``RectangleCLTArxivV1.lemma_2_smoothing_error,
    ``RectangleCLTArxivV1.dimensionLog_faces_le,
    ``RectangleCLTArxivV1.lemma_1_bounded_model,
    ``RectangleCLT.Companion.SplitV4.Printed.face_coordinate_real,
    ``RectangleCLT.Companion.SplitV4.Printed.face_coordinate_measurePreserving,
    ``RectangleCLT.Companion.SplitV4.Printed.clock_pair_measurePreserving,
    ``RectangleCLT.Companion.SplitV4.Printed.exponential_pair_upper_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.exponential_pair_lower_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.exponential_pair_abs_log_ratio_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail_le,
    ``RectangleCLT.Companion.SplitV4.Printed.randomThresholdShift_norm,
    ``RectangleCLT.Companion.SplitV4.Printed.measurable_clockLogMaximum,
    ``RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum_nonneg,
    ``RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius_shift_le,
    ``RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum_tail_le,
    ``RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum_tail_le_min,
    ``RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius_tail_le_min,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_le_log_add_one_of_exponential_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_clockLogMaximum,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_clockLogMaximum_le,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_randomThresholdRadius,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le_log,
    ``RectangleCLT.Companion.SplitV4.Printed.random_rectangle_sandwich,
    ``RectangleCLT.Companion.SplitV4.Printed.inside_subset_outer,
    ``RectangleCLT.Companion.SplitV4.Printed.inner_subset_inside,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_symmDiff_subset_boundary,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_indicator_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_probability_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_error_le_average_radius]
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
      let axioms ← Lean.collectAxioms target
      let forbidden := axioms.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n
      unless forbidden.isEmpty do
        throwError "Unexpected axioms in {target}: {forbidden}"
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "Fresh early passage correspondence: C1 bounded/Gaussian, Corollary1 normalization, Lemma2 actual endpoint smoothing; no q0 derivative correspondence claim"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
