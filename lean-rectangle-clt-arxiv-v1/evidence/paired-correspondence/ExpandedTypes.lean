import RectangleCLTArxivV1.PublishedPairedEndpoints
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_centered_copy_gradient,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_paired_truncated_gradient,
    ``RectangleCLT.Companion.SplitV4.C4Test.gradient_segment_trapezoidal,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_paired_gradient_increment,
    ``RectangleCLT.Companion.SplitV4.C4Test.shifted_hessianTrace_copyArrayTruncatedCovariance,
    ``RectangleCLTArxivV1.lemma_E4_paired_slepian,
    ``RectangleCLT.Companion.SplitV4.expected_copyArrayLargeMean_norm_le_of_memLp_two,
    ``RectangleCLT.Companion.SplitV4.expected_copyArrayTruncatedCovariance_sub_covariance_le,
    ``RectangleCLT.Companion.SplitV4.expected_pairedFourthBudget_le,
    ``RectangleCLT.Companion.SplitV4.common_point_fourth_contraction,
    ``RectangleCLTArxivV1.intrinsic_gaussian_common_point_fourth_random_data,
    ``RectangleCLTArxivV1.gaussian_smallerEnvelope_intrinsic,
    ``RectangleCLTArxivV1.gaussianMaximumMean_slepian_scale_div,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementHessianTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementGradientTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementRemainderTerm_le,
    ``RectangleCLT.Companion.SplitV4.abs_sub_le_three_time_weights,
    ``RectangleCLTArxivV1.intrinsic_largeIncrement_smooth_expectation_comparison,
    ``RectangleCLTArxivV1.intrinsic_largeIncrementGaussianComparison_bandwidth,
    ``RectangleCLTArxivV1.lemma_E2_intrinsic_comparison,
    ``RectangleCLT.Companion.SplitV4.independent_sum_bennett_mgf,
    ``RectangleCLT.Companion.SplitV4.bounded_vector_bennett_maximum,
    ``RectangleCLT.Companion.SplitV4.bounded_vector_bennett_maximum_optimized,
    ``RectangleCLTArxivV1.lemma_E5_truncated_bennett_maximum,
    ``RectangleCLTArxivV1.lemma_E5_truncated_bennett_maximum_zero_variance,
    ``RectangleCLT.Companion.SplitV4.normalized_coordinate_fourth_budget,
    ``RectangleCLT.Companion.SplitV4.normalized_q_envelope_budget,
    ``RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_bennett_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_direct_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_zero_of_variance_zero,
    ``RectangleCLT.Companion.SplitV4.bennett_small_calibration_identities,
    ``RectangleCLT.Companion.SplitV4.bennett_large_calibration_identities,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_small_regime,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_large_regime,
    ``RectangleCLT.Companion.SplitV4.bennettLogComparisonConstant_bound,
    ``RectangleCLT.Companion.SplitV4.bennettRatioConstant_bound,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT,
    ``RectangleCLTArxivV1.intrinsic_bennett_normalized_width_identity,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT_observations,
    ``RectangleCLTArxivV1.theorem_2_ii_intrinsic,
    ``RectangleCLTArxivV1.lemma_E3_intrinsic_smoothing]
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
    ("scope", toJson "Actual intrinsic paired comparison and Theorem2(ii) Bennett transfer"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
