import RectangleCLTArxivV1.IntrinsicDerivativeProposition
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.intrinsicRestorationConstant,
    ``RectangleCLTArxivV1.intrinsicRestorationConstant_pos,
    ``RectangleCLTArxivV1.intrinsic_seeded_matrix_estimate_with_copies,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_cubic_product_bound,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_fourth_product_bound,
    ``RectangleCLTArxivV1.intrinsicSeededDerivativeConstant,
    ``RectangleCLTArxivV1.intrinsicSeededDerivativeConstant_pos,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_cubic_product_rate,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_fourth_product_rate,
    ``RectangleCLTArxivV1.intrinsic_seeded_fourth_remainder_bound,
    ``RectangleCLTArxivV1.intrinsic_seeded_derivative_bounds,
    ``RectangleCLTArxivV1.intrinsic_seeded_time_comparison_bound,
    ``RectangleCLTArxivV1.intrinsicBoundaryConstant,
    ``RectangleCLTArxivV1.intrinsicBoundaryConstant_pos,
    ``RectangleCLTArxivV1.intrinsicBoundaryConstant_ge_512,
    ``RectangleCLTArxivV1.intrinsicBoundaryConstant_ge_1024,
    ``RectangleCLTArxivV1.combine_intrinsicBoundary,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_bounded_endpoint,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussian_endpoint,
    ``RectangleCLTArxivV1.seededRectangleBoundary_intrinsic_bounded_dominant,
    ``RectangleCLTArxivV1.seededRectangleBoundary_intrinsic_gaussian_dominant,
    ``RectangleCLTArxivV1.sqrt_dimensionLog_div_le_two,
    ``RectangleCLTArxivV1.seededRectangleBoundary_logarithmic,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase,
    ``RectangleCLTArxivV1.intrinsicPropositionDerivativeConstant,
    ``RectangleCLTArxivV1.intrinsicPropositionDerivativeConstant_pos,
    ``RectangleCLTArxivV1.intrinsicPropositionDerivativeConstant_ge_direct,
    ``RectangleCLTArxivV1.intrinsicPropositionDerivativeConstant_ge_seeded,
    ``RectangleCLTArxivV1.initializationDiscrepancy_intrinsic_le,
    ``RectangleCLTArxivV1.IntrinsicDerivativePropositionContract,
    ``RectangleCLTArxivV1.intrinsic_derivative_proposition,
    ``RectangleCLTArxivV1.proposition_1_intrinsic_derivatives,
    ``RectangleCLT.Companion.SplitV4.seededNormalization,
    ``RectangleCLT.Companion.SplitV4.seededNormalization_pos,
    ``RectangleCLT.Companion.SplitV4.seededNormalization_ge_one,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother_bandwidth,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother_bandwidth_ge,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother_F,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother_third,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother_relativeCubic,
    ``RectangleCLT.Companion.SplitV4.normalizedSeededInterpolationLaw,
    ``RectangleCLT.Companion.SplitV4.integral_normalizedSeeded_test,
    ``RectangleCLT.Companion.SplitV4.continuous_relativeCubicContraction,
    ``RectangleCLT.Companion.SplitV4.integral_normalizedSeeded_cubic,
    ``RectangleCLT.Companion.SplitV4.continuousOn_seeded_test_expectation,
    ``RectangleCLT.Companion.SplitV4.map_sum_standardGaussian_factor,
    ``RectangleCLT.Companion.SplitV4.map_add_left_conv,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_eq_conv,
    ``RectangleCLT.Companion.SplitV4.seededGaussianHalves_conv,
    ``RectangleCLT.Companion.SplitV4.seededGaussianSplit_law,
    ``RectangleCLT.Companion.SplitV4.integrable_linear_weighted_entry,
    ``RectangleCLT.Companion.SplitV4.restorationCoefficient_linear_quadratic,
    ``RectangleCLT.Companion.SplitV4.whitened_covariance_quadratic,
    ``RectangleCLT.Companion.SplitV4.relativeThird_whitened_budget,
    ``RectangleCLT.Companion.SplitV4.relativeFourth_whitened_budget,
    ``RectangleCLT.Companion.SplitV4.relativeFreshFourthMatrix_eq_first_copy,
    ``RectangleCLT.Companion.SplitV4.integrable_fresh_relative_weighted_entry,
    ``RectangleCLT.Companion.SplitV4.relativeFreshFourth_whitened_budget,
    ``RectangleCLT.Companion.SplitV4.conditionalRestorationCoefficient_copy_ae_eq,
    ``RectangleCLT.Companion.SplitV4.restorationCoefficient_prod_fst,
    ``RectangleCLT.Companion.SplitV4.relativeThird_whitened_face_budget,
    ``RectangleCLT.Companion.SplitV4.relativeFourth_whitened_face_budget,
    ``RectangleCLT.Companion.SplitV4.relativeFreshFourth_whitened_face_budget,
    ``RectangleCLT.Companion.SplitV4.seededCopyWhitened,
    ``RectangleCLT.Companion.SplitV4.seededCopyOriginal,
    ``RectangleCLT.Companion.SplitV4.seededCopyFresh,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_third_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fourth_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fresh_fourth_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_covariance_budget,
    ``RectangleCLT.Companion.SplitV4.seededCopyWhitened_measurable,
    ``RectangleCLT.Companion.SplitV4.seededCopyOriginal_measurable,
    ``RectangleCLT.Companion.SplitV4.seededCopyFresh_measurable,
    ``RectangleCLT.Companion.SplitV4.seededCopyWhitened_integrable_coordinate_pair,
    ``RectangleCLT.Companion.SplitV4.seededCopyWhitened_reconstruct,
    ``RectangleCLT.Companion.SplitV4.seededCopyOriginal_bounded,
    ``RectangleCLT.Companion.SplitV4.seededCopyFresh_bounded,
    ``RectangleCLT.Companion.SplitV4.seededSplitGaussianScale,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseValue,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_isProbability,
    ``RectangleCLT.Companion.SplitV4.seededSplitGaussianScale_sq,
    ``RectangleCLT.Companion.SplitV4.seededSplitGaussianScale_pos,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_eq_bounded_shift,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_eq_gaussian_shift,
    ``RectangleCLT.Companion.SplitV4.seededSplitGaussianScale_ge_delta_sqrt,
    ``RectangleCLT.Companion.SplitV4.map_seededSplitBaseValue_fst,
    ``RectangleCLT.Companion.SplitV4.seededRestorationBandwidth,
    ``RectangleCLT.Companion.SplitV4.seededRestorationBandwidth_ge_two,
    ``RectangleCLT.Companion.SplitV4.seededCopyDirection,
    ``RectangleCLT.Companion.SplitV4.seededCopyShift,
    ``RectangleCLT.Companion.SplitV4.seededCopyDirection_measurable,
    ``RectangleCLT.Companion.SplitV4.seededCopyDirection_bounded,
    ``RectangleCLT.Companion.SplitV4.seededCopyShift_bounded,
    ``RectangleCLT.Companion.SplitV4.seededCopyDirection_conditional_fourth_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_width_scale_conditions,
    ``RectangleCLT.Companion.SplitV4.seeded_integral_fourthTensor_gaussian_split,
    ``RectangleCLT.Companion.SplitV4.seeded_convolutionFourthExpectation_eq_product,
    ``RectangleCLT.Companion.SplitV4.seededFourthArrayExperiment_eq_product,
    ``RectangleCLT.Companion.SplitV4.seededFourthMaskExperiment_eq_array,
    ``RectangleCLT.Companion.SplitV4.seededFourthMaskExperiment_eq_product,
    ``RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandB_eq_seeded_product,
    ``RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandC_eq_seeded_product,
    ``RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandA_eq_seeded_product,
    ``RectangleCLT.Companion.SplitV4.relativeCubicContraction_eq_copy_integral,
    ``RectangleCLT.Companion.SplitV4.relativeCubicContraction_eq_generic,
    ``RectangleCLT.Companion.SplitV4.seeded_relative_cubic_law_eq_product,
    ``RectangleCLT.Companion.SplitV4.seededNormalization_cube_eq_rpow,
    ``RectangleCLT.Companion.SplitV4.normalizedSeededCubicTerm,
    ``RectangleCLT.Companion.SplitV4.normalizedSeededFourthRemainder,
    ``RectangleCLT.Companion.SplitV4.normalizedSeededExpectation,
    ``RectangleCLT.Companion.SplitV4.normalizedSeededExpectation_eq_seeded_test,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_normalizedSeededExpectation,
    ``RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel_abs_le_one,
    ``RectangleCLT.Companion.SplitV4.seededFourthRemainder,
    ``RectangleCLT.Companion.SplitV4.abs_unit_intervalIntegral_le_const]
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
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" || s.startsWith "Kane" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining" || s.startsWith "_private.Kane"
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
    ("scope", toJson "Main06 seeded4653–4932 actual normalized test/Gaussian-half joint law, seed scale, true base concentration, copy conditional signed-third and bothfourth budgets, alloriginal/fresh shifts, actual cubic and three fourth kernel/remainder law transport"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
