import RectangleCLTArxivV1
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.cap_one_projection_small_interval_nonneg,
    ``RectangleCLTArxivV1.cap_two_projection_small_box_nonneg,
    ``RectangleCLTArxivV1.lemma_F_1_weighted_normal_derivative,
    ``RectangleCLTArxivV1.lemma_F_1_weighted_normal_log_derivative,
    ``RectangleCLTArxivV1.cap_covariance_minimal_factor,
    ``RectangleCLTArxivV1.cap_covariance_rank_pos,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_complementary_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_abs_intervalIntegrable,
    ``RectangleCLTArxivV1.proposition_G1_dimension_log_cap_normalized,
    ``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_bounded_integral_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_bounded_integral_bound,
    ``RectangleCLTArxivV1.dimensionCapCLT,

    ``RectangleCLTArxivV1.theorem_3_intrinsic,
    ``RectangleCLTArxivV1.theorem_3_intrinsic_positive_dimensions,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_lower,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_two_sided,
    ``RectangleCLTArxivV1.lemma_F_1_uniform_scalar_moderate_tail,
    ``RectangleCLTArxivV1.lemma_F_2_independently_shifted_variables,
    ``RectangleCLTArxivV1.lemma_F_3_common_symmetric_construction,
    ``RectangleCLTArxivV1.lemma_E1_expected_maximum,
    ``RectangleCLTArxivV1.cap_one_projection_small_interval,
    ``RectangleCLTArxivV1.cap_two_projection_small_box,
    ``RectangleCLTArxivV1.cap_one_projection_small_interval_of_lower_variance,
    ``RectangleCLTArxivV1.cap_two_projection_small_box_of_lower_variance,
    ``RectangleCLTArxivV1.lemma_H2_gaussian_matrix,
    ``RectangleCLTArxivV1.lemma_H2_projected_reference,
    ``RectangleCLTArxivV1.lemma_B1_gaussian_seed_interpolation,
    ``RectangleCLTArxivV1.lemma_B2_intrinsic_paired_restoration,
    ``RectangleCLTArxivV1.bounded_width_example_one_eighth_from_main_regime,
    ``RectangleCLTArxivV1.cap_integrated_remainder_min_bound,
    ``RectangleCLTArxivV1.dimensionCap_rate_of_small_bandwidth_estimate,

    ``RectangleCLTArxivV1.corollary_2_intrinsic,
    ``RectangleCLTArxivV1.corollary_3_intrinsic,
    ``RectangleCLTArxivV1.theorem4_bounded_symmetric_lower,
    ``RectangleCLTArxivV1.theorem_5_fourth_moment_lower,
    ``RectangleCLTArxivV1.theorem_5_fourth_moment_two_sided,
    ``RectangleCLTArxivV1.theorem_6_growing_fourth_moment_lower,
    ``RectangleCLTArxivV1.theorem_7_polynomial_envelope_lower,
    ``RectangleCLTArxivV1.theorem_7_fixed_envelope_fourth_lower,
    ``RectangleCLTArxivV1.exists_lowerDense_upper_constant,
    ``RectangleCLTArxivV1.lemma_lower_family_properties,
``GenericChaining.dirksen_expectation,
    ``GenericChaining.gamma2_le_gaussianWidth,
    ``RectangleCLTArxivV1.signedIndex_card,
    ``RectangleCLTArxivV1.signedMaximum_eq_norm,
    ``RectangleCLTArxivV1.signedAbsMaximum_eq_norm,
    ``RectangleCLTArxivV1.signed_incrementMaximum_eq_norm,
    ``RectangleCLTArxivV1.signedGaussianLinear,
    ``RectangleCLTArxivV1.signedDiscreteMetric_self,
    ``RectangleCLTArxivV1.signedDiscreteMetric_symm,
    ``RectangleCLTArxivV1.signedDiscreteMetric_triangle,
    ``RectangleCLTArxivV1.signedContrast_observation_measurable,
    ``RectangleCLTArxivV1.signedContrast_independent,
    ``RectangleCLTArxivV1.integral_signedContrast_zero,
    ``RectangleCLTArxivV1.signedContrast_discrete_bound,
    ``RectangleCLTArxivV1.sum_variance_signedContrast,
    ``RectangleCLTArxivV1.signedProcess_hasMixedTail,
    ``RectangleCLTArxivV1.bounded_sum_upper_tail,
    ``RectangleCLTArxivV1.bounded_sum_abs_tail,
    ``RectangleCLTArxivV1.signedVarianceMetric_eq_canonicalDist,
    ``RectangleCLTArxivV1.gamma1_eq_admissible_subsets,
    ``RectangleCLTArxivV1.gamma2_eq_admissible_subsets,
    ``RectangleCLTArxivV1.admissible_first_card,
    ``RectangleCLTArxivV1.gaussian_level_weight,
    ``RectangleCLTArxivV1.gamma1_metric_homogeneity,
    ``RectangleCLTArxivV1.gamma2_metric_homogeneity,
    ``RectangleCLTArxivV1.signed_dirksen_expectation,
    ``RectangleCLTArxivV1.signed_dirksen_expectation_log,
    ``RectangleCLTArxivV1.integral_sum_coordinate_sq,
    ``RectangleCLTArxivV1.integral_abs_le_one_of_second_moment,
    ``RectangleCLTArxivV1.signed_first_absolute_moment_le_one,
    ``RectangleCLTArxivV1.discreteCutoff_le_iff,
    ``RectangleCLTArxivV1.discreteCutoff_pos,
    ``RectangleCLTArxivV1.discreteCutoff_weight_le_log,
    ``RectangleCLTArxivV1.signedDiscreteNets_initial,
    ``RectangleCLTArxivV1.signedDiscreteNets_terminal,
    ``RectangleCLTArxivV1.signed_gamma1_discrete_le,
    ``RectangleCLTArxivV1.gaussianWidth_signedFactorRows,
    ``RectangleCLTArxivV1.gaussianLaw_ae_mem_factor_range,
    ``RectangleCLTArxivV1.gaussian_factor_exists,
    ``RectangleCLTArxivV1.signed_factorRows_norm_sq,
    ``RectangleCLTArxivV1.gaussianLaw_integral_signedContrast_sq,
    ``RectangleCLTArxivV1.gaussianLaw_signedCoordinate_ae_eq_of_zero_dist,
    ``RectangleCLTArxivV1.gamma2_signedFactorRows_ne_top,
    ``RectangleCLTArxivV1.gamma2_signedFactorRows_le,
    ``RectangleCLTArxivV1.gamma2_signedFactorRows_eq_range,
    ``RectangleCLTArxivV1.gaussianMaximum_signedFactorRows_ae_eq_range,
    ``RectangleCLTArxivV1.gaussianWidth_signedFactorRows_eq_range,
    ``RectangleCLTArxivV1.gaussianWidth_signedFactorRows_range,
    ``RectangleCLTArxivV1.gaussianMaximumMean_eq_of_covariance,
    ``RectangleCLTArxivV1.standardNormal_integral_abs,
    ``RectangleCLTArxivV1.sqrt_two_div_pi_le_gaussianMaximumMean,
    ``RectangleCLTArxivV1.expectedMaximumConstant_pos,
    ``RectangleCLTArxivV1.bounded_sum_expected_maximum,
    ``RectangleCLTArxivV1.bounded_sum_expected_maximum_factor_exists,
    ``RectangleCLTArxivV1.boundedIndependent_of_raw,
    ``RectangleCLTArxivV1.lemma_C2_expected_maximum,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT,
    ``RectangleCLTArxivV1.intrinsicEnvelopeCLT,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT_factor_exists,
    ``RectangleCLTArxivV1.theorem_1_intrinsic_clt,
    ``RectangleCLTArxivV1.proposition_1_intrinsic_derivatives,
    ``RectangleCLTArxivV1.normalizedObservationsIntrinsicCLT,
    ``RectangleCLTArxivV1.corollary_1_normalized_observations,
    ``RectangleCLTArxivV1.lemma_1_bounded_model,
    ``RectangleCLTArxivV1.lemma_C1_gaussian_model,
    ``RectangleCLTArxivV1.lemma_2_smoothing_error,
    ``RectangleCLTArxivV1.integral_logisticEnvelope_intrinsic,
    ``RectangleCLTArxivV1.averaged_translated_derivative_intrinsic,
    ``RectangleCLTArxivV1.logistic_matrix_estimate_intrinsic,
    ``RectangleCLTArxivV1.selector_nuclear_bound_intrinsic_paper,
    ``RectangleCLTArxivV1.gaussian_mean_relative_to_single_face,
    ``RectangleCLTArxivV1.lemma_C1_rademacher_boundary,
    ``RectangleCLTArxivV1.lemma_C1_rademacher_maximum,
    ``RectangleCLTArxivV1.gaussian_probability_shiftedBox_intrinsic,
    ``RectangleCLTArxivV1.gaussian_probability_le_contractedBox_intrinsic,
    ``RectangleCLTArxivV1.intrinsicGaussianSmoothingConstant_ge_two,
    ``RectangleCLTArxivV1.gaussianEndpointSmoothing_intrinsic,
    ``RectangleCLTArxivV1.rectangleError_le_gaussianEndpointSmoothing_intrinsic,
    ``RectangleCLTArxivV1.theorem_2_i_intrinsic,
    ``RectangleCLTArxivV1.theorem_2_ii_intrinsic,
    ``RectangleCLTArxivV1.theorem_2_intrinsic,
    ``RectangleCLTArxivV1.theorem_2_intrinsic_with_min,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.gaussian_factor_exists,
    ``RectangleCLTArxivV1.lemma_E2_intrinsic_comparison,
    ``RectangleCLTArxivV1.lemma_E3_intrinsic_smoothing,
    ``RectangleCLTArxivV1.lemma_E4_paired_slepian,
    ``RectangleCLTArxivV1.lemma_E5_truncated_bennett_maximum,
    ``RectangleCLTArxivV1.lemma_E5_truncated_bennett_maximum_zero_variance,
    ``RectangleCLTArxivV1.intrinsic_concentratedThresholdBase_rescale,
    ``RectangleCLTArxivV1.lemma_B5_intrinsic_threshold,
    ``RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf]
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
    ("scope", toJson "Checked C.2 and intrinsic comparison endpoints and project proof dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
