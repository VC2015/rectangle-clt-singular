import RectangleCLTArxivV1
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLT.Companion.SplitV4.C4Test.gradient_segment_trapezoidal,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_centered_copy_gradient,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_paired_gradient_increment,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_paired_truncated_gradient,
    ``RectangleCLT.Companion.SplitV4.C4Test.shifted_hessianTrace_copyArrayTruncatedCovariance,
    ``RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.integral_exceptionalPart_coordinate_sq_le,
    ``RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.integral_exceptionalPart_q_le,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_good_covariance_le_envelope_sq,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_original_covariance_le_envelope_sq,
    ``RectangleCLT.Companion.SplitV4.Printed.bad_probability_mul_envelope_sq_le,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_normalized_maximum_le,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_conditional_covariance_deviation_actual,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_maximum_under_envelope_moment,
    ``RectangleCLT.Companion.SplitV4.Printed.norm_second_moment_le_envelope_sq,
    ``RectangleCLT.Companion.SplitV4.Printed.observed_exceptional_shift_maximum_le,
    ``RectangleCLT.Companion.SplitV4.abs_sub_le_three_time_weights,
    ``RectangleCLT.Companion.SplitV4.bennettLogComparisonConstant_bound,
    ``RectangleCLT.Companion.SplitV4.bennettRatioConstant_bound,
    ``RectangleCLT.Companion.SplitV4.bennett_large_calibration_identities,
    ``RectangleCLT.Companion.SplitV4.bennett_small_calibration_identities,
    ``RectangleCLT.Companion.SplitV4.bounded_vector_bennett_maximum,
    ``RectangleCLT.Companion.SplitV4.bounded_vector_bennett_maximum_optimized,
    ``RectangleCLT.Companion.SplitV4.common_point_fourth_contraction,
    ``RectangleCLT.Companion.SplitV4.conditionalExceptionalPart_centered,
    ``RectangleCLT.Companion.SplitV4.conditionalExceptionalPart_independent,
    ``RectangleCLT.Companion.SplitV4.conditionalRetained_boundedIndependent,
    ``RectangleCLT.Companion.SplitV4.conditional_decomposition,
    ``RectangleCLT.Companion.SplitV4.expected_copyArrayLargeMean_norm_le_of_memLp_two,
    ``RectangleCLT.Companion.SplitV4.expected_copyArrayTruncatedCovariance_sub_covariance_le,
    ``RectangleCLT.Companion.SplitV4.expected_pairedFourthBudget_le,
    ``RectangleCLT.Companion.SplitV4.independent_sum_bennett_mgf,
    ``RectangleCLT.Companion.SplitV4.normalized_coordinate_fourth_budget,
    ``RectangleCLT.Companion.SplitV4.normalized_product_rectangleDistance_eq,
    ``RectangleCLT.Companion.SplitV4.normalized_q_envelope_budget,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_bennett_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_direct_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_zero_of_variance_zero,
    ``RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_bound,
    ``RectangleCLT.Companion.SplitV4.polynomialTruncationThreshold_ge,
    ``RectangleCLT.Companion.SplitV4.polynomialTruncation_threshold_rate_le,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.conditional_marginal_inputs,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.coordinate_memLp_two,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.covariance_eq_originalAverageCovariance,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.gaussian_factor_exists,
    ``RectangleCLTArxivV1.conditionalAllCovariance_diagonal_lower,
    ``RectangleCLTArxivV1.conditionalAllGaussian_rectangleDistance_intrinsic,
    ``RectangleCLTArxivV1.conditionalCovarianceForMask_gaussianMaximumMean_le,
    ``RectangleCLTArxivV1.conditionalCovarianceForMask_quadratic_le,
    ``RectangleCLTArxivV1.conditionalCovarianceForMask_quadratic_le_allRetained,
    ``RectangleCLTArxivV1.conditionalGoodCovariance_maxDiagonal_le,
    ``RectangleCLTArxivV1.conditionalGoodKernel_rectangle_error_intrinsic_diagonal,
    ``RectangleCLTArxivV1.conditionalKernel_rectangle_error_intrinsic_diagonal,
    ``RectangleCLTArxivV1.conditionalMaskDifference_factor_exists,
    ``RectangleCLTArxivV1.conditionalMaskGaussian_rectangleDistance_diagonal,
    ``RectangleCLTArxivV1.conditionalMask_maxDiagonal_le_sum,
    ``RectangleCLTArxivV1.conditionalOmittedCovariance_diagonal_le,
    ``RectangleCLTArxivV1.conditionalOmittedCovariance_factor_exists,
    ``RectangleCLTArxivV1.conditionalPolynomial_intrinsic_raw,
    ``RectangleCLTArxivV1.conditionalPolynomial_intrinsic_threshold,
    ``RectangleCLTArxivV1.conditionalResidualCovariance_diagonal_le,
    ``RectangleCLTArxivV1.conditionalResidualCovariance_eq_average,
    ``RectangleCLTArxivV1.conditionalResidualCovariance_factor_exists,
    ``RectangleCLTArxivV1.conditionalRetained_intrinsicRectangleDistanceCLT,
    ``RectangleCLTArxivV1.conditional_D_L_le,
    ``RectangleCLTArxivV1.conditional_covariance_restoration,
    ``RectangleCLTArxivV1.covariance_conditionalExceptionalPart,
    ``RectangleCLTArxivV1.expected_observedOmittedDiagonalMaximum_le,
    ``RectangleCLTArxivV1.gaussianMaximumMean_le_of_covariance_addition,
    ``RectangleCLTArxivV1.gaussianMaximumMean_le_of_diagonal_le,
    ``RectangleCLTArxivV1.gaussianMaximumMean_le_sqrt_mul_jensen,
    ``RectangleCLTArxivV1.gaussianMaximumMean_mono_jensen,
    ``RectangleCLTArxivV1.gaussianMaximumMean_scaledFactor_le,
    ``RectangleCLTArxivV1.gaussianMaximumMean_slepian_scale_div,
    ``RectangleCLTArxivV1.gaussianMaximumMean_standardized_le,
    ``RectangleCLTArxivV1.gaussian_addition_law_eq_of_covariance_sum,
    ``RectangleCLTArxivV1.gaussian_rectangle_shift_min_variance,
    ``RectangleCLTArxivV1.gaussian_smallerEnvelope_intrinsic,
    ``RectangleCLTArxivV1.gaussian_two_additions_rectangleDistance_le,
    ``RectangleCLTArxivV1.goodConditional_covariance_quadratic_le,
    ``RectangleCLTArxivV1.intrinsicEnvelopeCLT_after_standardization,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementGradientTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementHessianTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementRemainderTerm_le,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT_observations,
    ``RectangleCLTArxivV1.intrinsic_bennett_normalized_width_identity,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_large_regime,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_small_regime,
    ``RectangleCLTArxivV1.intrinsic_gaussian_common_point_fourth_random_data,
    ``RectangleCLTArxivV1.intrinsic_largeIncrementGaussianComparison_bandwidth,
    ``RectangleCLTArxivV1.intrinsic_largeIncrement_smooth_expectation_comparison,
    ``RectangleCLTArxivV1.lemma_B5_intrinsic_threshold,
    ``RectangleCLTArxivV1.lemma_E2_intrinsic_comparison,
    ``RectangleCLTArxivV1.lemma_E3_intrinsic_smoothing,
    ``RectangleCLTArxivV1.lemma_E4_paired_slepian,
    ``RectangleCLTArxivV1.lemma_E5_truncated_bennett_maximum,
    ``RectangleCLTArxivV1.lemma_E5_truncated_bennett_maximum_zero_variance,
    ``RectangleCLTArxivV1.polynomialEnvelopeWidthRate_eq_scaled_old,
    ``RectangleCLTArxivV1.polynomialEnvelope_intrinsic_CLT,
    ``RectangleCLTArxivV1.theorem_2_i_intrinsic,
    ``RectangleCLTArxivV1.theorem_2_ii_intrinsic,
    ``RectangleCLTArxivV1.theorem_2_intrinsic,
    ``RectangleCLTArxivV1.theorem_2_intrinsic_with_min]
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
    ("scope", toJson "Checked C.2 and intrinsic comparison endpoints and project proof dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
