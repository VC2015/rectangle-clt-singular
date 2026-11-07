import RectangleCLTCompanion.SplitV4.PrintedProofs
import Lean.Util.CollectAxioms

/-! Exact declaration/type correspondence checks for every reference in
printed-proof-extension/coverage.json. The official transitive axiom collector
also audits mapped definitions and constructors, not just theorems. -/

set_option pp.all true in
#check RectangleCLT.BoundedIndependentHypotheses.integral_norm_sum_le
set_option pp.all true in
#check RectangleCLT.BoundedIndependentHypotheses.integral_norm_sum_le_of_variance
set_option pp.all true in
#check RectangleCLT.Companion.F_mul_prod_pi_translation
set_option pp.all true in
#check RectangleCLT.Companion.Psi1IndependentHypotheses.exponentialHypotheses
set_option pp.all true in
#check RectangleCLT.Companion.SignedSurface.averagedGaussianSelectorTrace_binomial
set_option pp.all true in
#check RectangleCLT.Companion.SignedSurface.selector_weight_binomial_succ
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.continuousOn_slepianExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatDerivative_eq_spatial_add_heat
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.gradient_segment_trapezoidal
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_genericVariableSelectorExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_integral_variableSeededInterpolationLaw
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.integral_array_summand_paired
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.slepian_gaussian_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConditionalTranslatedCoefficientBudget.relative_pair
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.abs_good_covariance_le_threshold_sq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_eq_flux
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_upper
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.gradient_energy_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_ramp_composition
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.PolynomialDimensionGrowth
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.TransitionMassBound.oneFace_via_threshold_limit
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_gaussianThresholdTrace_partial_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_gaussianThreshold_facet_term_le_mass_from_radial_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_gaussianThreshold_pair_term_le_sector_mass
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_good_covariance_bias_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_good_covariance_le_envelope_sq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_log_normalWeightedTail_deriv_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_mul_standardNormalPDF_le_at_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_original_covariance_le_envelope_sq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.abs_thresholdSignedSection_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.adaptive_sector_fiber_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.adaptive_sector_point
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.affineCubeMaximum_threshold_stability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.angular_pair_coefficient
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.averagedGaussianThresholdDerivative_sector_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.averagedGaussianThresholdDerivative_sector_bound_of_log_le_two
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bennettCorrection_le_bernstein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bernstein_factorial_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.boundedFamily_printed_discrepancy_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.boundedRectangleDistanceCLT_of_marginal_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.boundedSymmetricLower_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_after_standardization_via_current_theorem
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_boundary_layer_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_polyhedral_via_current_theorem
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_polynomial_dimension_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_vector_bernstein_exp_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_vector_bernstein_maximum_by_tail_integration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.canonical_hessian_taylor_triangle
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.centered_gradient_hessian_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.centered_value_hessian_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum_tail_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.clockLogVector
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.concaveOn_log_gaussian_convolution_nonnegative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.concentratedBase_sector_adaptiveLayer_average
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.conditionalGoodKernel_ownGaussian_rectangle_error_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.conditionalPolynomial_threshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.conditionalRetainedRectangleDistanceCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.conditionalRetained_marginal_half_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.conditional_finite_cauchy_schwarz
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.conditional_finite_pair_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.contDiff_gaussianMollifiedRamp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.contDiff_gaussianWeightPotential
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.continuous_integrableOn_planeSector
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.continuous_weighted_gaussianFiniteThreshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.convexOn_cubeRampPrimitive_comp_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.convexOn_realAffineCubeMaximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.coordinateRate_tendsto_zero_under_sparse_conditions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.cube_boundary_bound_of_all_positive_radii
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.cube_boundary_event_subset_perturbed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.cube_boundary_indicator_le_perturbed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.cube_boundary_unique_case
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.cube_translated_boundary_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.endpoint_error_le_average_radius
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.endpoint_indicator_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.endpoint_probability_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.endpoint_symmDiff_subset_boundary
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.envelope_tendsto_atTop_under_sparse_conditions_above_four
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_lowerMaximum_global_CDF
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_actual_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_distance_le_symmetricWorstDistance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_parameters
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_polynomialIndependent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_rank_and_gap
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_rademacher_cutoff_conditions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_capped_logarithmic_gain
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_envelope_asymptotic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_fourth_asymptotic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_fourth_correction_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_rates_tendsto_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_sign_actual_model
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_normalization
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_power_sum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_eq_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_printed_interval
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exists_four_moment_absorption_constant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exists_polynomialBennett_rate_four_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exists_small_threshold_perturbation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exists_small_unique_threshold_perturbation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.expectedClockCutoff_bad_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.expected_conditional_covariance_deviation_actual
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.expected_le_exp_moment_by_tail_integration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.expected_maximum_under_envelope_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyGlobal_discrepancy_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyGlobal_discrepancy_div_scale_at
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyGlobal_master_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyGlobal_remainder_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyMaskedSignMaximum_all_active_real_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyMaskedSignMaximum_printed_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyMasked_printed_failure_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyMasked_printed_failure_coverage_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_above_cutoff_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_central_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_damped_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_low_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_moderate_far_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_outer_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherUpperTail_subgaussian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_log_tail_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_scalar_berryEsseen
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyUnmasked_printed_failure_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.fourthMomentLower_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.fourthMomentOptimal_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianComparisonWithLargeIncrementRemainders
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianEndpointSmoothing_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianLinearRamp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp_deriv_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp_deriv_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianPDFReal_mul_sq_add_dimension_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianPairSectorEvent_mem_adaptiveOutwardTube
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianPairSectorEvent_section
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdDerivative_le_sectorAdaptiveLayer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdFirst_le_weighted_facet_event_from_radial_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdMixed_le_weighted_sector_event
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdSectorStratumEvent_indicator_sum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdSectorStratumEvent_shared_point
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdTrace_update_eq_signed_section_integral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianThreshold_facet_sector_weighted_sum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_cgf_sub_quadratic_eq_nonnegative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_directional_variance_le_nonnegative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian_ge_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_integral_potential_density
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_isProbability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_of_potential_hessian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_via_printed_potential
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_boundary_layer_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_convex_indicator_covariance_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_endpoint_expected_width
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_integral_shift_pos_of_mass
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_norm_tail_union
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_one_face_exponential_via_independence
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_shifted_probability_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_translation_rectangle_error_le_of_marginal_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_unit_interval_mass_pos
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_weightCovariance_contraction_nonnegative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.genericRowOperator_eq_signed_hessian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.genericRowOperator_fourth_from_signed_hessian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.genericSelectorOperator_eq_signedHessian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.goodConditional_norm_second_moment_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_integral_gaussianThresholdTrace_commonShift_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_seededExpectation_signedHessian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_shiftOffsets_theta_pow
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.iid_normalized_coordinate_power_integral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.iid_normalized_third_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.iid_sign_pi_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.independent_copy_tilt_integral_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.independent_copy_variance_integral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integrable_randomThresholdRadius
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_by_union_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_le_four_dimensionLog
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_le_log_add_one_of_exponential_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_normalizedGaussianMaximum_sq_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_pow_eq_weighted_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_pow_le_of_gaussian_tail_split
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_signedTwoFaceSmoother_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_singleFaceSmoother_standardGaussian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integrate_good_event_variable_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.intrinsicGaussianBoundary_printed_mollification
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed_avg
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.lemma2_printed_endpoint_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.linear_variance_le_of_potential_hessian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.log_polynomialSparseParameter
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.logisticPaddedScore_full_entry_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.logisticPaddedScore_full_nuclear_sum_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.logisticPaddedScore_full_nuclear_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.maskedFourthLower_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.mem_psi1Scales_at_positive_norm_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.mem_psi1Scales_of_norm_le_of_lt
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateArrayCGF_cubic_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateArrayFourth_abs_le_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_quadratic_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_strictMono_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateArrayVariance_exp_bounds_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateArrayVariance_linear_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_taylor_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateProductTail_nonneg_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateProductWeightedTail_log_error_nonneg
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.no_uniform_closedBox_zero_order_averaged_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.no_uniform_signed_zero_order_averaged_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.no_uniform_zero_order_averaged_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.nonnegative_logConcave_weight_nuclear_reduction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.norm_second_moment_le_envelope_sq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.norm_unit_sub_half_angle
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.norm_unit_sum_half_angle
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalCDF_power_pred_le_exp_half_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumCDF_second_derivative_global_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_far_positive
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_global_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_negative_region
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_positive_region
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_small_dimension
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_tail_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalPair_radius_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalWeightedTail_printed_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalWeightedTail_printed_upper
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normal_tail_mass_far_positive
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_L1_error_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_L1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_in_probability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_integrability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalized_observations_unequal_variance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalized_observations_via_current_theorem
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.oneFaceReference_integral_le_via_threshold_limit
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.oneFaceThresholds_exp_sum_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.oneFaceThresholds_transition_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.orlicz_polyhedral_via_printed_transfer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.orlicz_transfer_via_printed_clipping
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.planeSector_maps_into_cone
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.planeSector_mem_adaptiveOutwardTube
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.planeSector_positive_coefficients
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.planeSector_real_area
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransfer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_exponent_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_isBigO_polylog
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_polylog_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelope_rates_six
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialMomentCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialMomentCLTExists
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialMomentWorstDistanceCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialMoment_four_uniform_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_above_four_eq_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_four
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_atTop_below_four
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_zero_above_four
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_div_coordinateRate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_dominates_coordinate_below_four
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_four
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_negligible_to_coordinate_above_four
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomial_decay_exponent_gt_quarter
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomial_dimension_log_factor
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomial_times_gaussian_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.positive_standardization_via_current_theorem
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseAmplitude_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseLower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal_constant_first
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseParameters
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseScale_factor
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDense_uniform_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold_tail_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printed_dense_fourth_tendsto_one
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printed_dense_uniform_upper
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.probability_power_difference_with_cap
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.probability_power_difference_with_tail_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.product_power_mean_value
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.psi1_hypotheses_exponential_at_same_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.psi1_projected_at_exact_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.rademacherCutoffAmplitude_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.rademacherRelativeTailError_central
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.rademacherRelativeTailError_gaussian_weighted
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius_markov
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius_tail_le_min
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.randomThresholdShift_norm
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.random_rectangle_sandwich
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.rank_le_two_projection_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.relativeRate_le_of_fourth_cost
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.relativeRate_smoothing_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.ridgeDisplacement_norm
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sample_dimension_ratio_tendsto_atTop_under_sparse_conditions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sector_averaged_upper_power_trace_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sector_exists_logistic_matrix_paper_constant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_bound_unit_independent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_estimate_full_first
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_full_padding_estimate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sector_signed_upper_selector_trace_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.signedTwoFaceSmoother_eq_closedBox
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.signed_hessian_fourth_kernel_expectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.signed_hessian_fourth_kernel_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skewMaintextScale_div_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_detecting_rectangle_liminf_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_exact_product_asymptotic_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_exponentiation_quadratic_error_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_ereal_liminf_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_eventual_lower_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_log_tail_normalized_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_log_tail_remainder_ratio_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_maintext_sharpness_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_mean_value_prefactor_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_rate_tendsto_zero_of_maintext_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_relative_tail_facts_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_signed_product_normalized_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_tail_from_F1_eventually
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.smoothingLemma2_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sparseMomentLower_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sparseMomentOptimal_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sparseMoment_uniform_comparison_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sparse_log_dimension_condition_of_log_n
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.sparse_regime_four_iff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.standardGaussian_map_orthogonal_pair
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.standardGaussian_map_unit_faceDot
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.standardGaussian_orthogonal_faceDots_independent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.standardNormalCDF_printedNormalMaxThreshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.standardNormalPDF_le_at_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.standardNormalPDF_le_uniform_mills
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.standardNormalUpperTail_subgaussian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.subexponential_polynomial_dimension_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.subexponential_via_printed_clipping
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.subspaceProjectionRadius_tail_union
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_amplifiedFamily_discrepancy_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_gaussianShift_mean_ratio_printed_ui
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_orthantError_div_rate_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_shiftMean_difference_ratio_printed_ui
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_familyRare_gaussian_mean_ratio_printed_ui
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_familyRare_leading_comparison_ratio_printed_ui
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_fourthFamily_orthantError_div_rate_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_maskedFourthFamily_orthantError_div_rate_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_printedDense_orthantError_div_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_printedDense_rate_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_printedNormalMaxThreshold_div_sqrt_two_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_rareFamily_discrepancy_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_sparseFamily_orthantError_div_rate_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.thresholdPair_planeComponent_norm_le_radius
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.thresholdPair_sector_coefficient_le_radius
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_second_third_moments_from_radial_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_tail_beyond_sqrt_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_tail_union
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.thresholdSector_fiber_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.transition_weight_eq_theta_power_derivative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.twoPoint_normalized_tail_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.uniformScalarModerateTail_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.weighted_sign_fourth_matrices
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.weighted_triangle_integral_swap
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.zero_order_local_envelope_fails
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.RelativeMomentBounds.abs_third_entry_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.RelativeMomentBounds.sum_integral_abs_coordinate_four_product_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.RelativeMomentBounds.sum_integral_abs_copy_coordinate_four_product_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_directSlepianCopyFourthIntegrand_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_directSlepianCubicTerm_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_directSlepianFourthRemainder_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_familyMaskedSignMaximum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_iteratedFDeriv_logisticNullWeight_shift_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_largeIncrementRemainderTerm_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_relativeCubicContraction_le_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_smoother_gradient_le_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_smoother_hessianTrace_le_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_sub_le_three_time_weights
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.additiveGridFactor_ker
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.additiveGridFactor_rank
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.affineCubeEdgeFlux_nonneg
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.affineCube_edge_oscillation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.affineCube_edge_support
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.array_gradient_selector_partition
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.array_hessian_selector_partitions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.array_restorationFourthDerivative_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.array_restorationThirdDerivative_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_rectangle_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averaged_hard_trace_increment_le_of_L1_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averaged_logistic_power_trace_le_of_L1_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averaged_translated_derivative_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averaged_translated_derivative_signed_faces
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.avg_affineCubeEdgeFlux_sum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.avg_exp_cubeLinear
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.avg_exp_cubeLinear_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.avg_exp_selected_cubeLinear_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.avg_selected_cubeLinear_le_sqrt
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bandwidthRate_inv_mul_eq_master
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennettPolynomialCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennettPolynomialCLT_observations
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennettPolynomialParameter_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_large_regime_ratio_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_polynomial_large_regime
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_polynomial_small_regime
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_small_calibration_identities
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundary_active_slope_square_le_flux
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedFamilyParameters
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedIndependent_faceProjectedArray
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedPolyhedralEnvelopeCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedRectangleDistanceCLT_of_marginal_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_face_intrinsic_concentration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_face_intrinsic_concentration_signed_faces
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_intrinsic_boundary_fixed_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_independent_shift_min
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_product_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_product_shift_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_lower_constant_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance_diagonal
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_vector_bennett_maximum_optimized
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_vector_bernstein_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.calibrated_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.calibrated_cubic_coefficient
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel_abs_integral_le_one
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.calibrated_independent_copy_kernel
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.calibrated_third_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.canonicalFourthTensor_pair_slot_equivalence
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.canonicalFourthTensor_triple_slot_equivalence
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.canonical_fourth_reverse
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.canonical_hessianTrace_covariance_eq_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.canonical_hessian_taylor_two
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.canonical_mixed_cubic_integral_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.centeredRankOneEntries_variance_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.common_point_fourth_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalGoodKernel_rectangle_error_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalKernel_rectangle_error_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalPolynomial_raw_rectangleDistance_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalPolynomial_threshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalRetained_marginal_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalRetained_normalized_boundedIndependent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalTranslatedRestorationCoefficient
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_restoration_coefficient_relative_signed_zero_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_restoration_matrix_order_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_baseline
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_relative_pair
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_score_restoration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_directSlepianExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.copyArrayLargeMean_ae_eq_condExp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.copyArrayTruncatedCovariance_ae_eq_condExp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cubeEdgeFlux_controls_squares
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_eq_half_copy
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_le_norm_sum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_average_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_average_one_column_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_avg_signed_coordinate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_boundary_indicator_energy_le_flux
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_pair_bad_variance_probability_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_square_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_translated_boundary_le_intrinsic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.direct_initialization_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.direct_slepian_scalar_kernel_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.direct_time_increment_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_boundedHypotheses
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_second_moment_sum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.envelope_cutoff_rate_identities
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.envelope_relativeThirdMatrix_abs
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_sparseFamily_parameters
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_sparseFamily_polynomialIndependent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_sparseLower_probabilities
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.existsUnique_moderateArrayMean_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exists_bennett_log_denominator_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exists_logistic_matrix_paper_constant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exists_moderateArrayMean_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exp_le_chord_of_nonneg_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_cdf_shift_taylor_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_centeredRankOneSum_norm_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_copyArrayLargeMean_norm_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_copyArrayTruncatedCovariance_fluctuation_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_maximum_under_envelope_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_norm_le_log_signed_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_pairedFourthBudget_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.facePolyhedron_eq_preimage_standardized
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyAllSelected_probability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyArrayLaw
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyCovariance_maxOffDiagonal
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyCovariance_pairGap
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyCovariance_rank
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyFinite_minkowski
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyGaussianPairMap_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyGaussianPairMap_scaled_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyGaussianShift_independent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyMaskedSignMaximum_mean_deficit
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyNoSelectedColumns_probability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyNormalizedObservations_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyObservation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyObservationShift_independent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyRawObservations_Lq_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyRawObservations_fourth_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familySeedFlip_preserving
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familySeparatedSum_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familySeparatedSum_scaled_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyUnmasked_failure_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.finiteMaximum_pair_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthFamilyParameters
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthFamily_polynomialIndependent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourth_lower_constant_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gammaMixture_integral_signed_test
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianComparisonWithLargeIncrementRemainders
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianFacetEvent_disjoint
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianFacetEvent_mem_outerLayer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianFacetEvent_pairEvent_disjoint
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_fixed_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianLaw_map_mulVec_eq_of_gram
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairEvent_disjoint_of_active_ne
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairEvent_mem_outerLayer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdFirst_le_weighted_facet_event
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_eq_pairBase
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_le_weighted_pair_event
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdTrace_eq_radial_first
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThreshold_diagonal_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThreshold_facet_pair_weighted_sum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_affine_branches_ae_distinct_rows_ne
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_common_point_fourth_random_data
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_gradient_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_hessian_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_restorationFourthDerivative_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_restorationThirdDerivative_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericCubicContraction_eq_signedTensor
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericFixedHeat_eq_half_sum_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericFourthRowB_eq_correction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericFourthRowC_eq_correction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericVariableSelectorDerivative_eq_operator
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.half_sum_pairedIncrement_product_eq_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_directSlepianExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_normalMaximumDensity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_normalizedSeededExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasSum_integral_restorationSeries_ae
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_shift_cdf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_shift_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_square_sum_fluctuation_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_sum_bennett_log_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_sum_bennett_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_sum_norm_symmetrization
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.initializationDiscrepancy_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_random_repeatedDirectionScore
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_bennettTruncate_coordinate_eq_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_canonical_hessian_shift_sub
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_canonical_third_shift_sub
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_cubeConditionalRowSquares_coordinate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_familyActivationCount
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_familyActivationCount_sq_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_familyObservation_fourth
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_familyObservation_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_fourthTimeWeight
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_gaussianTimeWeight
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_genericCommonCubic_eq_seededLaw
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_bounded_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_gaussian_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_le_of_layer_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_nonnegative_limit_le_uniform_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_norm_center_le_copy
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_norm_sum_bennettRemainder_le_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_norm_sum_le_centeredTruncation_add_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_pairedIncrement_fourth_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_pairedTimeWeight
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_positiveGaussianFaceMaximum_le_sqrt_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_selector_nuclear_sum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_smallerEnvelope_directSlepian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_smallerEnvelope_le_of_matching_boundary
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.interval_probability_le_of_smooth_tests
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsicCubeMean_le_sqrt_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.iteratedFDeriv_linearExpTotal_apply
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.iteratedFDeriv_linearLogistic_partition
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.largeIncrementGaussianComparison_bandwidth
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.large_relativeBandwidth_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.lemma_concentration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.lemma_derivative_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.lemma_paired_restoration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticNullWeight
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticPaddedBase_concentrated
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticPaddedNormals_linearIndependent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticPaddedNormals_unit
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticPaddedScore_upperLeft_entry_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticPaddedScore_upperLeft_nuclear_tendsto
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logistic_allOrder_local_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logistic_matrix_bound_unit_independent
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logistic_matrix_estimate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logistic_smallerEnvelope_shift_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourth_rate_conversion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.masked_fourth_lower_constant_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.meanTruncatedCovariance_bias_norm_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateArrayCGF_cubic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateArrayFourth_abs_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateArrayGamma_abs_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateArrayMean_quadratic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateArrayVariance_linear
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateProductTail_large_threshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateProductWeightedTail_abs_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateProductWeightedTail_log_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateProduct_log_esscher_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateProduct_strict_tail_standardized
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateProduct_strict_tail_tilt
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateTiltFourthCumulant_abs_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateTiltVariance_exp_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateTilt_density_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_inverse_expansion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_legendre_expansion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_sqrt_variance_expansion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_tilted_threshold_cancellation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.nonnegative_vector_expected_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.norm_duplicateCoordinates
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedSeededInterpolationLaw_one
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedSeededInterpolationLaw_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.orliczPolyhedralCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedIncrement_norm_moment_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTailCoordinateSecond_sq_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_bennett_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_direct_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTruncatedArray_fourth_budget_from_original
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.paired_derivative_three_weight_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polyhedralDistance_delete_zero_variance_faces
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polyhedralDistance_le_projected_rectangleDistance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransfer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransferRate_ge_one_of_small
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialTruncation_threshold_rate_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.probability_bad_rows_le_norm_fluctuation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.projected_exponential_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.proposition_relative_derivatives
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleDistance_duplicateCoordinates
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleDistance_le_smoothingDiscrepancy_add_endpoint
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeBandwidth
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeBandwidth_admissible
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeBandwidth_fourth_cost_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeBandwidth_pos
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeBandwidth_total_cost_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeCLT_of_uniform_smooth_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeComparisonLog_le_D_L
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeEnvelopeCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeFourthAdmissible_of_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeIndependent_standardizedFaces
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_fourth_admissible
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativePolyhedralCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativePolyhedralDistance_zero_of_all_face_variances_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeRate_envelope_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relative_rate_of_small_bandwidth_estimate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relative_smooth_comparison_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationFourthExpectation_bound_of_budgets
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationFourthExpectation_conditional_transport
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationHessianCoefficients_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationPairedBandwidth_suffices
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationThirdExpectation_bound_of_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationThirdExpectation_conditional_transport
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_data_gaussian_identDistrib
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_fourth_relative_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_paired_baseline_of_matrixEstimate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_paired_baseline_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_scalar_series_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_third_relative_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededCopyShift_bounded
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededFourthKernel_eq_integral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededInitializationTime_sqrt
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededInitializationTime_sqrt_complement
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededRescaledSmoother_F
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededRescaledSmoother_relativeCubic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_eq_bounded_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_eq_gaussian_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededSplitGaussianScale_ge_delta_sqrt
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededSplitGaussianScale_sq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_copy_conditional_covariance_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fourth_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fresh_fourth_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_copy_conditional_third_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_derivative_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_fourth_remainder_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_relative_cubic_product_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_relative_fourth_product_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_time_comparison_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_time_increment_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_width_scale_conditions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.selectedSum_eq_midpoint_add_signed_difference
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.selectorWeight_nuclear_reduction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.shifted_taylor_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.signedCoordinateRows_faceProjectionNorm
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.signedCubicTensor_triple
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.signedDensity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.signedDensity_can_be_negative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.signedDensity_first_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.signedDensity_mass
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.signed_logistic_power_eq_gamma_hard_trace
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.slepian_fourth_kernel
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smallerEnvelope_scaled_bounded_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smallerEnvelope_scaled_gaussian_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_tendsto_one
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_test_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoother_gap_le_actual_two_stage_gaps
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoothingLemma2
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_coverage_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseLower_fourth_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMomentOptimal
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sumVector_ae_zero_of_envelope_budget_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sum_mask_genericBernoulliMoment_commonPoint
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.symmetricFamilyProperties
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_amplifiedFamily_discrepancy_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_discrepancy_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_leading_comparison_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_boundedSymmetricLowerRate_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseLowerEnvelopeRate_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_familyRare_discrepancy_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_familyRare_leading_comparison_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_familyUnmasked_maximum_mean_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_log_exp_add_rpow_div_rpow
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourthFamily_discrepancy_div_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseFamily_discrepancy_div_nativeScale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCoordinateRate_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerRate_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerTheta
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_coverage
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdFacet_fiber_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairSpan_finrank_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPair_coefficient_identity
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_add_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdRidge_fiber_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.translatedFaceDerivativeSupremum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.translated_score_array_series_interchange
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.translationD1_eq_selector_partition
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.truncated_bennett_maximum_zero_variance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformBoundaryConcentration_seededSplitBase
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_identDistrib
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variableEta_slepianAmplitude
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw_isProbability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variable_covariance_calibration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variable_cubic_coefficient
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variable_signed_hessian_coefficient
set_option pp.all true in
#check RectangleCLT.Companion.TransitionMassBound.oneFace
set_option pp.all true in
#check RectangleCLT.Companion.abs_restorationTranslationCoefficient_le
set_option pp.all true in
#check RectangleCLT.Companion.bounded_standardization_data
set_option pp.all true in
#check RectangleCLT.Companion.bounded_unrestrictedCLT_after_standardization
set_option pp.all true in
#check RectangleCLT.Companion.clipped_standardDeviation_ge_half
set_option pp.all true in
#check RectangleCLT.Companion.concaveOn_log_gaussian_convolution
set_option pp.all true in
#check RectangleCLT.Companion.concaveOn_log_selectorWeight_affine
set_option pp.all true in
#check RectangleCLT.Companion.gaussianTilt_cgf_sub_quadratic_eq
set_option pp.all true in
#check RectangleCLT.Companion.gaussian_exponential_translation
set_option pp.all true in
#check RectangleCLT.Companion.gaussian_mean_relative_to_one_face
set_option pp.all true in
#check RectangleCLT.Companion.gaussian_one_face_exponential
set_option pp.all true in
#check RectangleCLT.Companion.gaussian_weightCovariance_contraction_of_log_convolution_concave
set_option pp.all true in
#check RectangleCLT.Companion.hasSum_restorationSeriesTerm
set_option pp.all true in
#check RectangleCLT.Companion.integral_massEntropy_le_common_caps
set_option pp.all true in
#check RectangleCLT.Companion.integral_selectorFamilyMeanEnergy_le
set_option pp.all true in
#check RectangleCLT.Companion.integral_selectorFamilyMeanEnergy_le_entropy
set_option pp.all true in
#check RectangleCLT.Companion.integral_selectorFamilyNormalEnergy_le
set_option pp.all true in
#check RectangleCLT.Companion.integral_selectorMeanEnergy_le
set_option pp.all true in
#check RectangleCLT.Companion.lowerConstructionProperties
set_option pp.all true in
#check RectangleCLT.Companion.lowerCoordinateUpperTail_cramer_bound
set_option pp.all true in
#check RectangleCLT.Companion.lowerMaximum_rectangleError_liminf
set_option pp.all true in
#check RectangleCLT.Companion.lowerSkew_cramer_eventually
set_option pp.all true in
#check RectangleCLT.Companion.lowerTwoPointLaw_attains_envelope
set_option pp.all true in
#check RectangleCLT.Companion.lowerTwoPointLaw_third
set_option pp.all true in
#check RectangleCLT.Companion.lowerTwoPointLaw_third_ge
set_option pp.all true in
#check RectangleCLT.Companion.lower_log_relative_tail_to_relative_tail
set_option pp.all true in
#check RectangleCLT.Companion.lower_quantile_cubic_coefficient
set_option pp.all true in
#check RectangleCLT.Companion.lower_skew_linear_scale
set_option pp.all true in
#check RectangleCLT.Companion.lower_skew_quartic_remainder_ratio
set_option pp.all true in
#check RectangleCLT.Companion.normalMaxThreshold
set_option pp.all true in
#check RectangleCLT.Companion.normalizedClippedRows_boundedHypotheses
set_option pp.all true in
#check RectangleCLT.Companion.normalizedResidualRows_sum_covariance_diagonal_le
set_option pp.all true in
#check RectangleCLT.Companion.normalized_variance_le_of_cgf_sub_quadratic_concave
set_option pp.all true in
#check RectangleCLT.Companion.rectangleError_le_of_two_couplings
set_option pp.all true in
#check RectangleCLT.Companion.restorationTranslationCoefficient
set_option pp.all true in
#check RectangleCLT.Companion.selectorWeight_trace_reduction
set_option pp.all true in
#check RectangleCLT.Companion.selector_family_means_le_entropy
set_option pp.all true in
#check RectangleCLT.Companion.subexponentialCLT
set_option pp.all true in
#check RectangleCLT.Companion.subexponential_clipping_reduction
set_option pp.all true in
#check RectangleCLT.Companion.subexponential_transfer_error_weighted_le
set_option pp.all true in
#check RectangleCLT.Companion.sum_selectorWeight_eq
set_option pp.all true in
#check RectangleCLT.Companion.tangentMean_dot_mean
set_option pp.all true in
#check RectangleCLT.Companion.tangentMean_normSq
set_option pp.all true in
#check RectangleCLT.Companion.tangentMean_orthogonal
set_option pp.all true in
#check RectangleCLT.Companion.two_mul_mem_psi1Scales_of_norm_le
set_option pp.all true in
#check RectangleCLT.Companion.unrestrictedCLT
set_option pp.all true in
#check RectangleCLT.Companion.weighted_exp_mean_le
set_option pp.all true in
#check RectangleCLT.Companion.weighted_mean_sq_le_second
set_option pp.all true in
#check RectangleCLT.FaceSmoother.F_eq_exponential_probability
set_option pp.all true in
#check RectangleCLT.FaceSmoother.exponentialEvent_iff_randomRectangle_Inside
set_option pp.all true in
#check RectangleCLT.FaceSmoother.integral_F_eq_randomRectangle_average
set_option pp.all true in
#check RectangleCLT.maskObservationSum_bounded
set_option pp.all true in
#check RectangleCLT.mgf_le_exp_second_moment_of_bounded

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : Array Name := #[
    ``RectangleCLT.BoundedIndependentHypotheses.integral_norm_sum_le,
    ``RectangleCLT.BoundedIndependentHypotheses.integral_norm_sum_le_of_variance,
    ``RectangleCLT.Companion.F_mul_prod_pi_translation,
    ``RectangleCLT.Companion.Psi1IndependentHypotheses.exponentialHypotheses,
    ``RectangleCLT.Companion.SignedSurface.averagedGaussianSelectorTrace_binomial,
    ``RectangleCLT.Companion.SignedSurface.selector_weight_binomial_succ,
    ``RectangleCLT.Companion.SplitV4.C4Test.continuousOn_slepianExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatDerivative_eq_spatial_add_heat,
    ``RectangleCLT.Companion.SplitV4.C4Test.gradient_segment_trapezoidal,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_genericVariableSelectorExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_integral_variableSeededInterpolationLaw,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_array_summand_paired,
    ``RectangleCLT.Companion.SplitV4.C4Test.slepian_gaussian_stein,
    ``RectangleCLT.Companion.SplitV4.ConditionalTranslatedCoefficientBudget.relative_pair,
    ``RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.abs_good_covariance_le_threshold_sq,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_eq_flux,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_upper,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.gradient_energy_eq,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_maximum,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_ramp_composition,
    ``RectangleCLT.Companion.SplitV4.Printed.PolynomialDimensionGrowth,
    ``RectangleCLT.Companion.SplitV4.Printed.TransitionMassBound.oneFace_via_threshold_limit,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_gaussianThresholdTrace_partial_le,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_gaussianThreshold_facet_term_le_mass_from_radial_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_gaussianThreshold_pair_term_le_sector_mass,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_good_covariance_bias_le,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_good_covariance_le_envelope_sq,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_log_normalWeightedTail_deriv_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_mul_standardNormalPDF_le_at_zero,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_original_covariance_le_envelope_sq,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_thresholdSignedSection_le,
    ``RectangleCLT.Companion.SplitV4.Printed.adaptive_sector_fiber_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.adaptive_sector_point,
    ``RectangleCLT.Companion.SplitV4.Printed.affineCubeMaximum_threshold_stability,
    ``RectangleCLT.Companion.SplitV4.Printed.angular_pair_coefficient,
    ``RectangleCLT.Companion.SplitV4.Printed.averagedGaussianThresholdDerivative_sector_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.averagedGaussianThresholdDerivative_sector_bound_of_log_le_two,
    ``RectangleCLT.Companion.SplitV4.Printed.bennettCorrection_le_bernstein,
    ``RectangleCLT.Companion.SplitV4.Printed.bernstein_factorial_lower_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.boundedFamily_printed_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.Printed.boundedRectangleDistanceCLT_of_marginal_lower_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.boundedSymmetricLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_after_standardization_via_current_theorem,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_boundary_layer_le,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_polyhedral_via_current_theorem,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_polynomial_dimension_rate,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_vector_bernstein_exp_moment,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_vector_bernstein_maximum_by_tail_integration,
    ``RectangleCLT.Companion.SplitV4.Printed.canonical_hessian_taylor_triangle,
    ``RectangleCLT.Companion.SplitV4.Printed.centered_gradient_hessian_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.centered_value_hessian_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum,
    ``RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum_tail_le,
    ``RectangleCLT.Companion.SplitV4.Printed.clockLogVector,
    ``RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail_le,
    ``RectangleCLT.Companion.SplitV4.Printed.concaveOn_log_gaussian_convolution_nonnegative,
    ``RectangleCLT.Companion.SplitV4.Printed.concentratedBase_sector_adaptiveLayer_average,
    ``RectangleCLT.Companion.SplitV4.Printed.conditionalGoodKernel_ownGaussian_rectangle_error_le,
    ``RectangleCLT.Companion.SplitV4.Printed.conditionalPolynomial_threshold,
    ``RectangleCLT.Companion.SplitV4.Printed.conditionalRetainedRectangleDistanceCLT,
    ``RectangleCLT.Companion.SplitV4.Printed.conditionalRetained_marginal_half_lower_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.conditional_finite_cauchy_schwarz,
    ``RectangleCLT.Companion.SplitV4.Printed.conditional_finite_pair_contraction,
    ``RectangleCLT.Companion.SplitV4.Printed.contDiff_gaussianMollifiedRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.contDiff_gaussianWeightPotential,
    ``RectangleCLT.Companion.SplitV4.Printed.continuous_integrableOn_planeSector,
    ``RectangleCLT.Companion.SplitV4.Printed.continuous_weighted_gaussianFiniteThreshold,
    ``RectangleCLT.Companion.SplitV4.Printed.convexOn_cubeRampPrimitive_comp_maximum,
    ``RectangleCLT.Companion.SplitV4.Printed.convexOn_realAffineCubeMaximum,
    ``RectangleCLT.Companion.SplitV4.Printed.coordinateRate_tendsto_zero_under_sparse_conditions,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_bound_of_all_positive_radii,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_event_subset_perturbed,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_indicator_le_perturbed,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_unique_case,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_translated_boundary_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_error_le_average_radius,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_indicator_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_probability_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.endpoint_symmDiff_subset_boundary,
    ``RectangleCLT.Companion.SplitV4.Printed.envelope_tendsto_atTop_under_sparse_conditions_above_four,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_lowerMaximum_global_CDF,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_actual_moments,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_distance_le_symmetricWorstDistance,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_moments,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_parameters,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_polynomialIndependent,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_rank_and_gap,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_rademacher_cutoff_conditions,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_capped_logarithmic_gain,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_envelope_asymptotic,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_fourth_asymptotic,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_fourth_correction_ratio,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_rates_tendsto_zero,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_sign_actual_model,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_envelope,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_normalization,
    ``RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_power_sum,
    ``RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_eq_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_printed_interval,
    ``RectangleCLT.Companion.SplitV4.Printed.exists_four_moment_absorption_constant,
    ``RectangleCLT.Companion.SplitV4.Printed.exists_polynomialBennett_rate_four_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.exists_small_threshold_perturbation,
    ``RectangleCLT.Companion.SplitV4.Printed.exists_small_unique_threshold_perturbation,
    ``RectangleCLT.Companion.SplitV4.Printed.expectedClockCutoff_bad_le,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_conditional_covariance_deviation_actual,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_le_exp_moment_by_tail_integration,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_maximum_under_envelope_moment,
    ``RectangleCLT.Companion.SplitV4.Printed.familyGlobal_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.Printed.familyGlobal_discrepancy_div_scale_at,
    ``RectangleCLT.Companion.SplitV4.Printed.familyGlobal_master_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.familyGlobal_remainder_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.familyMaskedSignMaximum_all_active_real_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.familyMaskedSignMaximum_printed_moments,
    ``RectangleCLT.Companion.SplitV4.Printed.familyMasked_printed_failure_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.familyMasked_printed_failure_coverage_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_above_cutoff_error,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_central_error,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_damped_error,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_low_error,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_moderate_far_error,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_outer_error,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacherUpperTail_subgaussian,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacher_log_tail_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf_le,
    ``RectangleCLT.Companion.SplitV4.Printed.familyRademacher_scalar_berryEsseen,
    ``RectangleCLT.Companion.SplitV4.Printed.familyUnmasked_printed_failure_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.fourthMomentLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.fourthMomentOptimal_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianComparisonWithLargeIncrementRemainders,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianEndpointSmoothing_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianLinearRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp_deriv_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp_deriv_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianPDFReal_mul_sq_add_dimension_le,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianPairSectorEvent_mem_adaptiveOutwardTube,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianPairSectorEvent_section,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdDerivative_le_sectorAdaptiveLayer,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdFirst_le_weighted_facet_event_from_radial_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdMixed_le_weighted_sector_event,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdSectorStratumEvent_indicator_sum_le,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdSectorStratumEvent_shared_point,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianThresholdTrace_update_eq_signed_section_integral,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianThreshold_facet_sector_weighted_sum_le,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_cgf_sub_quadratic_eq_nonnegative,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_directional_variance_le_nonnegative,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian_ge_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_integral_potential_density,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_isProbability,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_of_potential_hessian,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_via_printed_potential,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_boundary_layer_le,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_convex_indicator_covariance_contraction,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_endpoint_expected_width,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_integral_shift_pos_of_mass,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_norm_tail_union,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_one_face_exponential_via_independence,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_shifted_probability_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_translation_rectangle_error_le_of_marginal_lower_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_unit_interval_mass_pos,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_weightCovariance_contraction_nonnegative,
    ``RectangleCLT.Companion.SplitV4.Printed.genericRowOperator_eq_signed_hessian,
    ``RectangleCLT.Companion.SplitV4.Printed.genericRowOperator_fourth_from_signed_hessian,
    ``RectangleCLT.Companion.SplitV4.Printed.genericSelectorOperator_eq_signedHessian,
    ``RectangleCLT.Companion.SplitV4.Printed.goodConditional_norm_second_moment_le,
    ``RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_integral_gaussianThresholdTrace_commonShift_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_seededExpectation_signedHessian,
    ``RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_shiftOffsets_theta_pow,
    ``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_coordinate_power_integral,
    ``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_third_moment,
    ``RectangleCLT.Companion.SplitV4.Printed.iid_sign_pi_covariance,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_copy_tilt_integral_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_copy_variance_integral,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_randomThresholdRadius,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_by_union_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_le_four_dimensionLog,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_le_log_add_one_of_exponential_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_normalizedGaussianMaximum_sq_le,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_pow_eq_weighted_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_pow_le_of_gaussian_tail_split,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le_log,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_signedTwoFaceSmoother_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_singleFaceSmoother_standardGaussian,
    ``RectangleCLT.Companion.SplitV4.Printed.integrate_good_event_variable_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsicGaussianBoundary_printed_mollification,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed_avg,
    ``RectangleCLT.Companion.SplitV4.Printed.lemma2_printed_endpoint_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.linear_variance_le_of_potential_hessian,
    ``RectangleCLT.Companion.SplitV4.Printed.log_polynomialSparseParameter,
    ``RectangleCLT.Companion.SplitV4.Printed.logisticPaddedScore_full_entry_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.logisticPaddedScore_full_nuclear_sum_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.logisticPaddedScore_full_nuclear_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.maskedFourthLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.mem_psi1Scales_at_positive_norm_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.mem_psi1Scales_of_norm_le_of_lt,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayCGF_cubic_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayFourth_abs_le_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_quadratic_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_strictMono_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayVariance_exp_bounds_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayVariance_linear_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_taylor_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProductTail_nonneg_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProductWeightedTail_log_error_nonneg,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.no_uniform_closedBox_zero_order_averaged_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.no_uniform_signed_zero_order_averaged_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.no_uniform_zero_order_averaged_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.nonnegative_logConcave_weight_nuclear_reduction,
    ``RectangleCLT.Companion.SplitV4.Printed.norm_second_moment_le_envelope_sq,
    ``RectangleCLT.Companion.SplitV4.Printed.norm_unit_sub_half_angle,
    ``RectangleCLT.Companion.SplitV4.Printed.norm_unit_sum_half_angle,
    ``RectangleCLT.Companion.SplitV4.Printed.normalCDF_power_pred_le_exp_half_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.normalMaximumCDF_second_derivative_global_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_far_positive,
    ``RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_global_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_negative_region,
    ``RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_positive_region,
    ``RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_small_dimension,
    ``RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_tail_envelope,
    ``RectangleCLT.Companion.SplitV4.Printed.normalPair_radius_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.normalWeightedTail_printed_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.normalWeightedTail_printed_upper,
    ``RectangleCLT.Companion.SplitV4.Printed.normal_tail_mass_far_positive,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_L1_error_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_L1,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_in_probability,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_integrability,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.normalized_observations_unequal_variance,
    ``RectangleCLT.Companion.SplitV4.Printed.normalized_observations_via_current_theorem,
    ``RectangleCLT.Companion.SplitV4.Printed.oneFaceReference_integral_le_via_threshold_limit,
    ``RectangleCLT.Companion.SplitV4.Printed.oneFaceThresholds_exp_sum_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.oneFaceThresholds_transition_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.orlicz_polyhedral_via_printed_transfer,
    ``RectangleCLT.Companion.SplitV4.Printed.orlicz_transfer_via_printed_clipping,
    ``RectangleCLT.Companion.SplitV4.Printed.planeSector_maps_into_cone,
    ``RectangleCLT.Companion.SplitV4.Printed.planeSector_mem_adaptiveOutwardTube,
    ``RectangleCLT.Companion.SplitV4.Printed.planeSector_positive_coefficients,
    ``RectangleCLT.Companion.SplitV4.Printed.planeSector_real_area,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransfer,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_exponent_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_isBigO_polylog,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_polylog_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelope_rates_six,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialMomentCLT,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialMomentCLTExists,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialMomentWorstDistanceCLT,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialMoment_four_uniform_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_above_four_eq_ratio,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_four,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_atTop_below_four,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_zero_above_four,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_div_coordinateRate,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_dominates_coordinate_below_four,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_four,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_negligible_to_coordinate_above_four,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomial_decay_exponent_gt_quarter,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomial_dimension_log_factor,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomial_times_gaussian_le,
    ``RectangleCLT.Companion.SplitV4.Printed.positive_standardization_via_current_theorem,
    ``RectangleCLT.Companion.SplitV4.Printed.printedDenseAmplitude_eq,
    ``RectangleCLT.Companion.SplitV4.Printed.printedDenseLower,
    ``RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal,
    ``RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal_constant_first,
    ``RectangleCLT.Companion.SplitV4.Printed.printedDenseParameters,
    ``RectangleCLT.Companion.SplitV4.Printed.printedDenseScale_factor,
    ``RectangleCLT.Companion.SplitV4.Printed.printedDense_uniform_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold_tail_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.printed_dense_fourth_tendsto_one,
    ``RectangleCLT.Companion.SplitV4.Printed.printed_dense_uniform_upper,
    ``RectangleCLT.Companion.SplitV4.Printed.probability_power_difference_with_cap,
    ``RectangleCLT.Companion.SplitV4.Printed.probability_power_difference_with_tail_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.product_power_mean_value,
    ``RectangleCLT.Companion.SplitV4.Printed.psi1_hypotheses_exponential_at_same_scale,
    ``RectangleCLT.Companion.SplitV4.Printed.psi1_projected_at_exact_scale,
    ``RectangleCLT.Companion.SplitV4.Printed.rademacherCutoffAmplitude_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.rademacherRelativeTailError_central,
    ``RectangleCLT.Companion.SplitV4.Printed.rademacherRelativeTailError_gaussian_weighted,
    ``RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius,
    ``RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius_markov,
    ``RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius_tail_le_min,
    ``RectangleCLT.Companion.SplitV4.Printed.randomThresholdShift_norm,
    ``RectangleCLT.Companion.SplitV4.Printed.random_rectangle_sandwich,
    ``RectangleCLT.Companion.SplitV4.Printed.rank_le_two_projection_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.relativeRate_le_of_fourth_cost,
    ``RectangleCLT.Companion.SplitV4.Printed.relativeRate_smoothing_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.ridgeDisplacement_norm,
    ``RectangleCLT.Companion.SplitV4.Printed.sample_dimension_ratio_tendsto_atTop_under_sparse_conditions,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_averaged_upper_power_trace_le,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_exists_logistic_matrix_paper_constant,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_bound_unit_independent,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_estimate_full_first,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_full_padding_estimate,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_signed_upper_selector_trace_le,
    ``RectangleCLT.Companion.SplitV4.Printed.signedTwoFaceSmoother_eq_closedBox,
    ``RectangleCLT.Companion.SplitV4.Printed.signed_hessian_fourth_kernel_expectation,
    ``RectangleCLT.Companion.SplitV4.Printed.signed_hessian_fourth_kernel_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.skewMaintextScale_div_rate,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_detecting_rectangle_liminf_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_exact_product_asymptotic_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_exponentiation_quadratic_error_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_ereal_liminf_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_eventual_lower_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_log_tail_normalized_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_log_tail_remainder_ratio_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_maintext_sharpness_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_mean_value_prefactor_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_rate_tendsto_zero_of_maintext_scale,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_relative_tail_facts_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_signed_product_normalized_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_tail_from_F1_eventually,
    ``RectangleCLT.Companion.SplitV4.Printed.smoothingLemma2_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.sparseMomentLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.sparseMomentOptimal_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.sparseMoment_uniform_comparison_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.sparse_log_dimension_condition_of_log_n,
    ``RectangleCLT.Companion.SplitV4.Printed.sparse_regime_four_iff,
    ``RectangleCLT.Companion.SplitV4.Printed.standardGaussian_map_orthogonal_pair,
    ``RectangleCLT.Companion.SplitV4.Printed.standardGaussian_map_unit_faceDot,
    ``RectangleCLT.Companion.SplitV4.Printed.standardGaussian_orthogonal_faceDots_independent,
    ``RectangleCLT.Companion.SplitV4.Printed.standardNormalCDF_printedNormalMaxThreshold,
    ``RectangleCLT.Companion.SplitV4.Printed.standardNormalPDF_le_at_zero,
    ``RectangleCLT.Companion.SplitV4.Printed.standardNormalPDF_le_uniform_mills,
    ``RectangleCLT.Companion.SplitV4.Printed.standardNormalUpperTail_subgaussian,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.subexponential_polynomial_dimension_rate,
    ``RectangleCLT.Companion.SplitV4.Printed.subexponential_via_printed_clipping,
    ``RectangleCLT.Companion.SplitV4.Printed.subspaceProjectionRadius_tail_union,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_amplifiedFamily_discrepancy_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_gaussianShift_mean_ratio_printed_ui,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_shiftMean_difference_ratio_printed_ui,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_familyRare_gaussian_mean_ratio_printed_ui,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_familyRare_leading_comparison_ratio_printed_ui,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_fourthFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_maskedFourthFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_printedDense_orthantError_div_rate,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_printedDense_rate_div_scale,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_printedNormalMaxThreshold_div_sqrt_two_log,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_rareFamily_discrepancy_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_sparseFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.thresholdPair_planeComponent_norm_le_radius,
    ``RectangleCLT.Companion.SplitV4.Printed.thresholdPair_sector_coefficient_le_radius,
    ``RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_second_third_moments_from_radial_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_tail_beyond_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_tail_union,
    ``RectangleCLT.Companion.SplitV4.Printed.thresholdSector_fiber_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.transition_weight_eq_theta_power_derivative,
    ``RectangleCLT.Companion.SplitV4.Printed.twoPoint_normalized_tail_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.uniformScalarModerateTail_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.weighted_sign_fourth_matrices,
    ``RectangleCLT.Companion.SplitV4.Printed.weighted_triangle_integral_swap,
    ``RectangleCLT.Companion.SplitV4.Printed.zero_order_local_envelope_fails,
    ``RectangleCLT.Companion.SplitV4.RelativeMomentBounds.abs_third_entry_le,
    ``RectangleCLT.Companion.SplitV4.RelativeMomentBounds.sum_integral_abs_coordinate_four_product_le,
    ``RectangleCLT.Companion.SplitV4.RelativeMomentBounds.sum_integral_abs_copy_coordinate_four_product_le,
    ``RectangleCLT.Companion.SplitV4.abs_directSlepianCopyFourthIntegrand_le,
    ``RectangleCLT.Companion.SplitV4.abs_directSlepianCubicTerm_le,
    ``RectangleCLT.Companion.SplitV4.abs_directSlepianFourthRemainder_le,
    ``RectangleCLT.Companion.SplitV4.abs_familyMaskedSignMaximum_le,
    ``RectangleCLT.Companion.SplitV4.abs_iteratedFDeriv_logisticNullWeight_shift_le,
    ``RectangleCLT.Companion.SplitV4.abs_largeIncrementRemainderTerm_le,
    ``RectangleCLT.Companion.SplitV4.abs_relativeCubicContraction_le_envelope,
    ``RectangleCLT.Companion.SplitV4.abs_smoother_gradient_le_envelope,
    ``RectangleCLT.Companion.SplitV4.abs_smoother_hessianTrace_le_envelope,
    ``RectangleCLT.Companion.SplitV4.abs_sub_le_three_time_weights,
    ``RectangleCLT.Companion.SplitV4.additiveGridFactor_ker,
    ``RectangleCLT.Companion.SplitV4.additiveGridFactor_rank,
    ``RectangleCLT.Companion.SplitV4.affineCubeEdgeFlux_nonneg,
    ``RectangleCLT.Companion.SplitV4.affineCube_edge_oscillation,
    ``RectangleCLT.Companion.SplitV4.affineCube_edge_support,
    ``RectangleCLT.Companion.SplitV4.array_gradient_selector_partition,
    ``RectangleCLT.Companion.SplitV4.array_hessian_selector_partitions,
    ``RectangleCLT.Companion.SplitV4.array_restorationFourthDerivative_stein,
    ``RectangleCLT.Companion.SplitV4.array_restorationThirdDerivative_stein,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_rectangle_bound,
    ``RectangleCLT.Companion.SplitV4.averaged_hard_trace_increment_le_of_L1_budget,
    ``RectangleCLT.Companion.SplitV4.averaged_logistic_power_trace_le_of_L1_budget,
    ``RectangleCLT.Companion.SplitV4.averaged_translated_derivative_component,
    ``RectangleCLT.Companion.SplitV4.averaged_translated_derivative_signed_faces,
    ``RectangleCLT.Companion.SplitV4.avg_affineCubeEdgeFlux_sum,
    ``RectangleCLT.Companion.SplitV4.avg_exp_cubeLinear,
    ``RectangleCLT.Companion.SplitV4.avg_exp_cubeLinear_le,
    ``RectangleCLT.Companion.SplitV4.avg_exp_selected_cubeLinear_le,
    ``RectangleCLT.Companion.SplitV4.avg_selected_cubeLinear_le_sqrt,
    ``RectangleCLT.Companion.SplitV4.bandwidthRate_inv_mul_eq_master,
    ``RectangleCLT.Companion.SplitV4.bennettPolynomialCLT,
    ``RectangleCLT.Companion.SplitV4.bennettPolynomialCLT_observations,
    ``RectangleCLT.Companion.SplitV4.bennettPolynomialParameter_eq,
    ``RectangleCLT.Companion.SplitV4.bennett_large_regime_ratio_bounds,
    ``RectangleCLT.Companion.SplitV4.bennett_polynomial_large_regime,
    ``RectangleCLT.Companion.SplitV4.bennett_polynomial_small_regime,
    ``RectangleCLT.Companion.SplitV4.bennett_small_calibration_identities,
    ``RectangleCLT.Companion.SplitV4.boundary_active_slope_square_le_flux,
    ``RectangleCLT.Companion.SplitV4.boundedFamilyParameters,
    ``RectangleCLT.Companion.SplitV4.boundedIndependent_faceProjectedArray,
    ``RectangleCLT.Companion.SplitV4.boundedPolyhedralEnvelopeCLT,
    ``RectangleCLT.Companion.SplitV4.boundedRectangleDistanceCLT_of_marginal_lower_bound,
    ``RectangleCLT.Companion.SplitV4.bounded_face_intrinsic_concentration,
    ``RectangleCLT.Companion.SplitV4.bounded_face_intrinsic_concentration_signed_faces,
    ``RectangleCLT.Companion.SplitV4.bounded_intrinsic_boundary_fixed_shift,
    ``RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_independent_shift_min,
    ``RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_product_shift,
    ``RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_product_shift_log,
    ``RectangleCLT.Companion.SplitV4.bounded_lower_constant_identity,
    ``RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance,
    ``RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance_diagonal,
    ``RectangleCLT.Companion.SplitV4.bounded_vector_bennett_maximum_optimized,
    ``RectangleCLT.Companion.SplitV4.bounded_vector_bernstein_maximum,
    ``RectangleCLT.Companion.SplitV4.calibrated_covariance,
    ``RectangleCLT.Companion.SplitV4.calibrated_cubic_coefficient,
    ``RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel,
    ``RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel_abs_integral_le_one,
    ``RectangleCLT.Companion.SplitV4.calibrated_independent_copy_kernel,
    ``RectangleCLT.Companion.SplitV4.calibrated_third_moment,
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_pair_slot_equivalence,
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_triple_slot_equivalence,
    ``RectangleCLT.Companion.SplitV4.canonical_fourth_reverse,
    ``RectangleCLT.Companion.SplitV4.canonical_hessianTrace_covariance_eq_moments,
    ``RectangleCLT.Companion.SplitV4.canonical_hessian_taylor_two,
    ``RectangleCLT.Companion.SplitV4.canonical_mixed_cubic_integral_zero,
    ``RectangleCLT.Companion.SplitV4.centeredRankOneEntries_variance_budget,
    ``RectangleCLT.Companion.SplitV4.common_point_fourth_contraction,
    ``RectangleCLT.Companion.SplitV4.conditionalGoodKernel_rectangle_error_le,
    ``RectangleCLT.Companion.SplitV4.conditionalKernel_rectangle_error_eq,
    ``RectangleCLT.Companion.SplitV4.conditionalPolynomial_raw_rectangleDistance_le,
    ``RectangleCLT.Companion.SplitV4.conditionalPolynomial_threshold,
    ``RectangleCLT.Companion.SplitV4.conditionalRetained_marginal_lower_bound,
    ``RectangleCLT.Companion.SplitV4.conditionalRetained_normalized_boundedIndependent,
    ``RectangleCLT.Companion.SplitV4.conditionalTranslatedRestorationCoefficient,
    ``RectangleCLT.Companion.SplitV4.conditional_restoration_coefficient_relative_signed_zero_shift,
    ``RectangleCLT.Companion.SplitV4.conditional_restoration_matrix_order_bound,
    ``RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_baseline,
    ``RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_relative_pair,
    ``RectangleCLT.Companion.SplitV4.conditional_translated_score_restoration,
    ``RectangleCLT.Companion.SplitV4.continuous_directSlepianExpectation,
    ``RectangleCLT.Companion.SplitV4.copyArrayLargeMean_ae_eq_condExp,
    ``RectangleCLT.Companion.SplitV4.copyArrayTruncatedCovariance_ae_eq_condExp,
    ``RectangleCLT.Companion.SplitV4.cubeEdgeFlux_controls_squares,
    ``RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_eq_half_copy,
    ``RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_le_norm_sum,
    ``RectangleCLT.Companion.SplitV4.cube_average_contraction,
    ``RectangleCLT.Companion.SplitV4.cube_average_one_column_contraction,
    ``RectangleCLT.Companion.SplitV4.cube_avg_signed_coordinate,
    ``RectangleCLT.Companion.SplitV4.cube_boundary_indicator_energy_le_flux,
    ``RectangleCLT.Companion.SplitV4.cube_pair_bad_variance_probability_le,
    ``RectangleCLT.Companion.SplitV4.cube_square_contraction,
    ``RectangleCLT.Companion.SplitV4.cube_translated_boundary_le_intrinsic,
    ``RectangleCLT.Companion.SplitV4.direct_initialization_bound,
    ``RectangleCLT.Companion.SplitV4.direct_slepian_scalar_kernel_bounds,
    ``RectangleCLT.Companion.SplitV4.direct_time_increment_le,
    ``RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_boundedHypotheses,
    ``RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_second_moment_sum_le,
    ``RectangleCLT.Companion.SplitV4.envelope_cutoff_rate_identities,
    ``RectangleCLT.Companion.SplitV4.envelope_relativeThirdMatrix_abs,
    ``RectangleCLT.Companion.SplitV4.eventually_sparseFamily_parameters,
    ``RectangleCLT.Companion.SplitV4.eventually_sparseFamily_polynomialIndependent,
    ``RectangleCLT.Companion.SplitV4.eventually_sparseLower_probabilities,
    ``RectangleCLT.Companion.SplitV4.existsUnique_moderateArrayMean_eq,
    ``RectangleCLT.Companion.SplitV4.exists_bennett_log_denominator_lower,
    ``RectangleCLT.Companion.SplitV4.exists_logistic_matrix_paper_constant,
    ``RectangleCLT.Companion.SplitV4.exists_moderateArrayMean_eq,
    ``RectangleCLT.Companion.SplitV4.exp_le_chord_of_nonneg_le,
    ``RectangleCLT.Companion.SplitV4.expected_cdf_shift_taylor_error,
    ``RectangleCLT.Companion.SplitV4.expected_centeredRankOneSum_norm_le,
    ``RectangleCLT.Companion.SplitV4.expected_copyArrayLargeMean_norm_le,
    ``RectangleCLT.Companion.SplitV4.expected_copyArrayTruncatedCovariance_fluctuation_le,
    ``RectangleCLT.Companion.SplitV4.expected_maximum_under_envelope_moment,
    ``RectangleCLT.Companion.SplitV4.expected_norm_le_log_signed_mgf,
    ``RectangleCLT.Companion.SplitV4.expected_pairedFourthBudget_le,
    ``RectangleCLT.Companion.SplitV4.facePolyhedron_eq_preimage_standardized,
    ``RectangleCLT.Companion.SplitV4.familyAllSelected_probability,
    ``RectangleCLT.Companion.SplitV4.familyArrayLaw,
    ``RectangleCLT.Companion.SplitV4.familyCovariance_maxOffDiagonal,
    ``RectangleCLT.Companion.SplitV4.familyCovariance_pairGap,
    ``RectangleCLT.Companion.SplitV4.familyCovariance_rank,
    ``RectangleCLT.Companion.SplitV4.familyFinite_minkowski,
    ``RectangleCLT.Companion.SplitV4.familyGaussianPairMap_maximum,
    ``RectangleCLT.Companion.SplitV4.familyGaussianPairMap_scaled_maximum,
    ``RectangleCLT.Companion.SplitV4.familyGaussianShift_independent,
    ``RectangleCLT.Companion.SplitV4.familyMaskedSignMaximum_mean_deficit,
    ``RectangleCLT.Companion.SplitV4.familyNoSelectedColumns_probability,
    ``RectangleCLT.Companion.SplitV4.familyNormalizedObservations_covariance,
    ``RectangleCLT.Companion.SplitV4.familyObservation,
    ``RectangleCLT.Companion.SplitV4.familyObservationShift_independent,
    ``RectangleCLT.Companion.SplitV4.familyRawObservations_Lq_envelope,
    ``RectangleCLT.Companion.SplitV4.familyRawObservations_fourth_scale,
    ``RectangleCLT.Companion.SplitV4.familySeedFlip_preserving,
    ``RectangleCLT.Companion.SplitV4.familySeparatedSum_maximum,
    ``RectangleCLT.Companion.SplitV4.familySeparatedSum_scaled_maximum,
    ``RectangleCLT.Companion.SplitV4.familyUnmasked_failure_bound,
    ``RectangleCLT.Companion.SplitV4.finiteMaximum_pair_contraction,
    ``RectangleCLT.Companion.SplitV4.fourthFamilyParameters,
    ``RectangleCLT.Companion.SplitV4.fourthFamily_polynomialIndependent,
    ``RectangleCLT.Companion.SplitV4.fourth_lower_constant_identity,
    ``RectangleCLT.Companion.SplitV4.gammaMixture_integral_signed_test,
    ``RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound,
    ``RectangleCLT.Companion.SplitV4.gaussianComparisonWithLargeIncrementRemainders,
    ``RectangleCLT.Companion.SplitV4.gaussianFacetEvent_disjoint,
    ``RectangleCLT.Companion.SplitV4.gaussianFacetEvent_mem_outerLayer,
    ``RectangleCLT.Companion.SplitV4.gaussianFacetEvent_pairEvent_disjoint,
    ``RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_fixed_shift,
    ``RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift,
    ``RectangleCLT.Companion.SplitV4.gaussianLaw_map_mulVec_eq_of_gram,
    ``RectangleCLT.Companion.SplitV4.gaussianPairEvent_disjoint_of_active_ne,
    ``RectangleCLT.Companion.SplitV4.gaussianPairEvent_mem_outerLayer,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_identity,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdFirst_le_weighted_facet_event,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_eq_pairBase,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_le_weighted_pair_event,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdTrace_eq_radial_first,
    ``RectangleCLT.Companion.SplitV4.gaussianThreshold_diagonal_identity,
    ``RectangleCLT.Companion.SplitV4.gaussianThreshold_facet_pair_weighted_sum_le,
    ``RectangleCLT.Companion.SplitV4.gaussian_affine_branches_ae_distinct_rows_ne,
    ``RectangleCLT.Companion.SplitV4.gaussian_common_point_fourth_random_data,
    ``RectangleCLT.Companion.SplitV4.gaussian_gradient_contraction,
    ``RectangleCLT.Companion.SplitV4.gaussian_hessian_contraction,
    ``RectangleCLT.Companion.SplitV4.gaussian_restorationFourthDerivative_stein,
    ``RectangleCLT.Companion.SplitV4.gaussian_restorationThirdDerivative_stein,
    ``RectangleCLT.Companion.SplitV4.genericCubicContraction_eq_signedTensor,
    ``RectangleCLT.Companion.SplitV4.genericFixedHeat_eq_half_sum_moments,
    ``RectangleCLT.Companion.SplitV4.genericFourthRowB_eq_correction,
    ``RectangleCLT.Companion.SplitV4.genericFourthRowC_eq_correction,
    ``RectangleCLT.Companion.SplitV4.genericVariableSelectorDerivative_eq_operator,
    ``RectangleCLT.Companion.SplitV4.half_sum_pairedIncrement_product_eq_covariance,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_directSlepianExpectation,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_normalMaximumDensity,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_normalizedSeededExpectation,
    ``RectangleCLT.Companion.SplitV4.hasSum_integral_restorationSeries_ae,
    ``RectangleCLT.Companion.SplitV4.independent_shift_cdf,
    ``RectangleCLT.Companion.SplitV4.independent_shift_comparison,
    ``RectangleCLT.Companion.SplitV4.independent_square_sum_fluctuation_le,
    ``RectangleCLT.Companion.SplitV4.independent_sum_bennett_log_mgf,
    ``RectangleCLT.Companion.SplitV4.independent_sum_bennett_mgf,
    ``RectangleCLT.Companion.SplitV4.independent_sum_norm_symmetrization,
    ``RectangleCLT.Companion.SplitV4.initializationDiscrepancy_le,
    ``RectangleCLT.Companion.SplitV4.integrable_random_repeatedDirectionScore,
    ``RectangleCLT.Companion.SplitV4.integral_bennettTruncate_coordinate_eq_zero,
    ``RectangleCLT.Companion.SplitV4.integral_canonical_hessian_shift_sub,
    ``RectangleCLT.Companion.SplitV4.integral_canonical_third_shift_sub,
    ``RectangleCLT.Companion.SplitV4.integral_cubeConditionalRowSquares_coordinate,
    ``RectangleCLT.Companion.SplitV4.integral_familyActivationCount,
    ``RectangleCLT.Companion.SplitV4.integral_familyActivationCount_sq_le,
    ``RectangleCLT.Companion.SplitV4.integral_familyObservation_fourth,
    ``RectangleCLT.Companion.SplitV4.integral_familyObservation_product,
    ``RectangleCLT.Companion.SplitV4.integral_fourthTimeWeight,
    ``RectangleCLT.Companion.SplitV4.integral_gaussianTimeWeight,
    ``RectangleCLT.Companion.SplitV4.integral_genericCommonCubic_eq_seededLaw,
    ``RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_bounded_component,
    ``RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_component,
    ``RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_gaussian_component,
    ``RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_le_of_layer_bound,
    ``RectangleCLT.Companion.SplitV4.integral_nonnegative_limit_le_uniform_bound,
    ``RectangleCLT.Companion.SplitV4.integral_norm_center_le_copy,
    ``RectangleCLT.Companion.SplitV4.integral_norm_sum_bennettRemainder_le_budget,
    ``RectangleCLT.Companion.SplitV4.integral_norm_sum_le_centeredTruncation_add_tail,
    ``RectangleCLT.Companion.SplitV4.integral_pairedIncrement_fourth_le,
    ``RectangleCLT.Companion.SplitV4.integral_pairedTimeWeight,
    ``RectangleCLT.Companion.SplitV4.integral_positiveGaussianFaceMaximum_le_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.integral_selector_nuclear_sum_le,
    ``RectangleCLT.Companion.SplitV4.integral_smallerEnvelope_directSlepian,
    ``RectangleCLT.Companion.SplitV4.integral_smallerEnvelope_le_of_matching_boundary,
    ``RectangleCLT.Companion.SplitV4.interval_probability_le_of_smooth_tests,
    ``RectangleCLT.Companion.SplitV4.intrinsicCubeMean_le_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary,
    ``RectangleCLT.Companion.SplitV4.iteratedFDeriv_linearExpTotal_apply,
    ``RectangleCLT.Companion.SplitV4.iteratedFDeriv_linearLogistic_partition,
    ``RectangleCLT.Companion.SplitV4.largeIncrementGaussianComparison_bandwidth,
    ``RectangleCLT.Companion.SplitV4.large_relativeBandwidth_rate,
    ``RectangleCLT.Companion.SplitV4.lemma_concentration,
    ``RectangleCLT.Companion.SplitV4.lemma_derivative_envelope,
    ``RectangleCLT.Companion.SplitV4.lemma_paired_restoration,
    ``RectangleCLT.Companion.SplitV4.logisticNullWeight,
    ``RectangleCLT.Companion.SplitV4.logisticPaddedBase_concentrated,
    ``RectangleCLT.Companion.SplitV4.logisticPaddedNormals_linearIndependent,
    ``RectangleCLT.Companion.SplitV4.logisticPaddedNormals_unit,
    ``RectangleCLT.Companion.SplitV4.logisticPaddedScore_upperLeft_entry_tendsto,
    ``RectangleCLT.Companion.SplitV4.logisticPaddedScore_upperLeft_nuclear_tendsto,
    ``RectangleCLT.Companion.SplitV4.logistic_allOrder_local_envelope,
    ``RectangleCLT.Companion.SplitV4.logistic_matrix_bound_unit_independent,
    ``RectangleCLT.Companion.SplitV4.logistic_matrix_estimate,
    ``RectangleCLT.Companion.SplitV4.logistic_smallerEnvelope_shift_le,
    ``RectangleCLT.Companion.SplitV4.maskedFourth_rate_conversion,
    ``RectangleCLT.Companion.SplitV4.masked_fourth_lower_constant_identity,
    ``RectangleCLT.Companion.SplitV4.meanTruncatedCovariance_bias_norm_le,
    ``RectangleCLT.Companion.SplitV4.moderateArrayCGF_cubic,
    ``RectangleCLT.Companion.SplitV4.moderateArrayFourth_abs_le,
    ``RectangleCLT.Companion.SplitV4.moderateArrayGamma_abs_le,
    ``RectangleCLT.Companion.SplitV4.moderateArrayMean_quadratic,
    ``RectangleCLT.Companion.SplitV4.moderateArrayVariance_linear,
    ``RectangleCLT.Companion.SplitV4.moderateProductTail_large_threshold,
    ``RectangleCLT.Companion.SplitV4.moderateProductWeightedTail_abs_error,
    ``RectangleCLT.Companion.SplitV4.moderateProductWeightedTail_log_error,
    ``RectangleCLT.Companion.SplitV4.moderateProduct_log_esscher_error,
    ``RectangleCLT.Companion.SplitV4.moderateProduct_strict_tail_standardized,
    ``RectangleCLT.Companion.SplitV4.moderateProduct_strict_tail_tilt,
    ``RectangleCLT.Companion.SplitV4.moderateTiltFourthCumulant_abs_le,
    ``RectangleCLT.Companion.SplitV4.moderateTiltVariance_exp_bounds,
    ``RectangleCLT.Companion.SplitV4.moderateTilt_density_bounds,
    ``RectangleCLT.Companion.SplitV4.moderate_inverse_expansion,
    ``RectangleCLT.Companion.SplitV4.moderate_legendre_expansion,
    ``RectangleCLT.Companion.SplitV4.moderate_sqrt_variance_expansion,
    ``RectangleCLT.Companion.SplitV4.moderate_tilted_threshold_cancellation,
    ``RectangleCLT.Companion.SplitV4.nonnegative_vector_expected_maximum,
    ``RectangleCLT.Companion.SplitV4.norm_duplicateCoordinates,
    ``RectangleCLT.Companion.SplitV4.normalizedObservationsCLT,
    ``RectangleCLT.Companion.SplitV4.normalizedSeededInterpolationLaw_one,
    ``RectangleCLT.Companion.SplitV4.normalizedSeededInterpolationLaw_zero,
    ``RectangleCLT.Companion.SplitV4.orliczPolyhedralCLT,
    ``RectangleCLT.Companion.SplitV4.pairedIncrement_norm_moment_budget,
    ``RectangleCLT.Companion.SplitV4.pairedTailCoordinateSecond_sq_le,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_bennett_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_direct_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_bound,
    ``RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_rate,
    ``RectangleCLT.Companion.SplitV4.pairedTruncatedArray_fourth_budget_from_original,
    ``RectangleCLT.Companion.SplitV4.paired_derivative_three_weight_bound,
    ``RectangleCLT.Companion.SplitV4.polyhedralDistance_delete_zero_variance_faces,
    ``RectangleCLT.Companion.SplitV4.polyhedralDistance_le_projected_rectangleDistance,
    ``RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransfer,
    ``RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransferRate_ge_one_of_small,
    ``RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists,
    ``RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT,
    ``RectangleCLT.Companion.SplitV4.polynomialTruncation_threshold_rate_le,
    ``RectangleCLT.Companion.SplitV4.probability_bad_rows_le_norm_fluctuation,
    ``RectangleCLT.Companion.SplitV4.projected_exponential_moments,
    ``RectangleCLT.Companion.SplitV4.proposition_relative_derivatives,
    ``RectangleCLT.Companion.SplitV4.rectangleDistance_duplicateCoordinates,
    ``RectangleCLT.Companion.SplitV4.rectangleDistance_le_smoothingDiscrepancy_add_endpoint,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_admissible,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_fourth_cost_le,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_pos,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidth_total_cost_le,
    ``RectangleCLT.Companion.SplitV4.relativeCLT_of_uniform_smooth_comparison,
    ``RectangleCLT.Companion.SplitV4.relativeComparisonLog_le_D_L,
    ``RectangleCLT.Companion.SplitV4.relativeEnvelopeCLT,
    ``RectangleCLT.Companion.SplitV4.relativeFourthAdmissible_of_envelope,
    ``RectangleCLT.Companion.SplitV4.relativeIndependent_standardizedFaces,
    ``RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_fourth_admissible,
    ``RectangleCLT.Companion.SplitV4.relativePolyhedralCLT,
    ``RectangleCLT.Companion.SplitV4.relativePolyhedralDistance_zero_of_all_face_variances_zero,
    ``RectangleCLT.Companion.SplitV4.relativeRate_envelope_le,
    ``RectangleCLT.Companion.SplitV4.relative_rate_of_small_bandwidth_estimate,
    ``RectangleCLT.Companion.SplitV4.relative_smooth_comparison_bound,
    ``RectangleCLT.Companion.SplitV4.restorationFourthExpectation_bound_of_budgets,
    ``RectangleCLT.Companion.SplitV4.restorationFourthExpectation_conditional_transport,
    ``RectangleCLT.Companion.SplitV4.restorationHessianCoefficients_bound,
    ``RectangleCLT.Companion.SplitV4.restorationPairedBandwidth_suffices,
    ``RectangleCLT.Companion.SplitV4.restorationThirdExpectation_bound_of_budget,
    ``RectangleCLT.Companion.SplitV4.restorationThirdExpectation_conditional_transport,
    ``RectangleCLT.Companion.SplitV4.restoration_data_gaussian_identDistrib,
    ``RectangleCLT.Companion.SplitV4.restoration_fourth_relative_product,
    ``RectangleCLT.Companion.SplitV4.restoration_paired_baseline_of_matrixEstimate,
    ``RectangleCLT.Companion.SplitV4.restoration_paired_baseline_product,
    ``RectangleCLT.Companion.SplitV4.restoration_scalar_series_bound,
    ``RectangleCLT.Companion.SplitV4.restoration_third_relative_product,
    ``RectangleCLT.Companion.SplitV4.seededCopyShift_bounded,
    ``RectangleCLT.Companion.SplitV4.seededFourthKernel_eq_integral,
    ``RectangleCLT.Companion.SplitV4.seededInitializationTime_sqrt,
    ``RectangleCLT.Companion.SplitV4.seededInitializationTime_sqrt_complement,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother_F,
    ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother_relativeCubic,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_eq_bounded_shift,
    ``RectangleCLT.Companion.SplitV4.seededSplitBaseDistribution_eq_gaussian_shift,
    ``RectangleCLT.Companion.SplitV4.seededSplitGaussianScale_ge_delta_sqrt,
    ``RectangleCLT.Companion.SplitV4.seededSplitGaussianScale_sq,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_covariance_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fourth_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_fresh_fourth_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_copy_conditional_third_budget,
    ``RectangleCLT.Companion.SplitV4.seeded_derivative_bounds,
    ``RectangleCLT.Companion.SplitV4.seeded_fourth_remainder_bound,
    ``RectangleCLT.Companion.SplitV4.seeded_relative_cubic_product_rate,
    ``RectangleCLT.Companion.SplitV4.seeded_relative_fourth_product_rate,
    ``RectangleCLT.Companion.SplitV4.seeded_time_comparison_bound,
    ``RectangleCLT.Companion.SplitV4.seeded_time_increment_le,
    ``RectangleCLT.Companion.SplitV4.seeded_width_scale_conditions,
    ``RectangleCLT.Companion.SplitV4.selectedSum_eq_midpoint_add_signed_difference,
    ``RectangleCLT.Companion.SplitV4.selectorWeight_nuclear_reduction,
    ``RectangleCLT.Companion.SplitV4.shifted_taylor_bound,
    ``RectangleCLT.Companion.SplitV4.signedCoordinateRows_faceProjectionNorm,
    ``RectangleCLT.Companion.SplitV4.signedCubicTensor_triple,
    ``RectangleCLT.Companion.SplitV4.signedDensity,
    ``RectangleCLT.Companion.SplitV4.signedDensity_can_be_negative,
    ``RectangleCLT.Companion.SplitV4.signedDensity_first_moment,
    ``RectangleCLT.Companion.SplitV4.signedDensity_mass,
    ``RectangleCLT.Companion.SplitV4.signed_logistic_power_eq_gamma_hard_trace,
    ``RectangleCLT.Companion.SplitV4.slepian_fourth_kernel,
    ``RectangleCLT.Companion.SplitV4.smallerEnvelope_scaled_bounded_component,
    ``RectangleCLT.Companion.SplitV4.smallerEnvelope_scaled_gaussian_component,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_tendsto_one,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_test_bound,
    ``RectangleCLT.Companion.SplitV4.smoother_gap_le_actual_two_stage_gaps,
    ``RectangleCLT.Companion.SplitV4.smoothingLemma2,
    ``RectangleCLT.Companion.SplitV4.sparseLower_coverage_lower,
    ``RectangleCLT.Companion.SplitV4.sparseLower_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.sparseMomentOptimal,
    ``RectangleCLT.Companion.SplitV4.sumVector_ae_zero_of_envelope_budget_zero,
    ``RectangleCLT.Companion.SplitV4.sum_mask_genericBernoulliMoment_commonPoint,
    ``RectangleCLT.Companion.SplitV4.symmetricFamilyProperties,
    ``RectangleCLT.Companion.SplitV4.tendsto_amplifiedFamily_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_leading_comparison_ratio,
    ``RectangleCLT.Companion.SplitV4.tendsto_boundedSymmetricLowerRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_denseLowerEnvelopeRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_familyRare_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_familyRare_leading_comparison_ratio,
    ``RectangleCLT.Companion.SplitV4.tendsto_familyUnmasked_maximum_mean_ratio,
    ``RectangleCLT.Companion.SplitV4.tendsto_log_exp_add_rpow_div_rpow,
    ``RectangleCLT.Companion.SplitV4.tendsto_maskedFourthFamily_discrepancy_div_rate,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseFamily_discrepancy_div_nativeScale,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerCoordinateRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerPi_log,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerRate_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLowerTheta,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseLower_coverage,
    ``RectangleCLT.Companion.SplitV4.thresholdFacet_fiber_lower,
    ``RectangleCLT.Companion.SplitV4.thresholdPairSpan_finrank_le,
    ``RectangleCLT.Companion.SplitV4.thresholdPair_coefficient_identity,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_add_le,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments,
    ``RectangleCLT.Companion.SplitV4.thresholdRidge_fiber_lower,
    ``RectangleCLT.Companion.SplitV4.translatedFaceDerivativeSupremum_le,
    ``RectangleCLT.Companion.SplitV4.translated_score_array_series_interchange,
    ``RectangleCLT.Companion.SplitV4.translationD1_eq_selector_partition,
    ``RectangleCLT.Companion.SplitV4.truncated_bennett_maximum_zero_variance,
    ``RectangleCLT.Companion.SplitV4.uniformBoundaryConcentration_seededSplitBase,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_identDistrib,
    ``RectangleCLT.Companion.SplitV4.variableEta_slepianAmplitude,
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw,
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw_isProbability,
    ``RectangleCLT.Companion.SplitV4.variable_covariance_calibration,
    ``RectangleCLT.Companion.SplitV4.variable_cubic_coefficient,
    ``RectangleCLT.Companion.SplitV4.variable_signed_hessian_coefficient,
    ``RectangleCLT.Companion.TransitionMassBound.oneFace,
    ``RectangleCLT.Companion.abs_restorationTranslationCoefficient_le,
    ``RectangleCLT.Companion.bounded_standardization_data,
    ``RectangleCLT.Companion.bounded_unrestrictedCLT_after_standardization,
    ``RectangleCLT.Companion.clipped_standardDeviation_ge_half,
    ``RectangleCLT.Companion.concaveOn_log_gaussian_convolution,
    ``RectangleCLT.Companion.concaveOn_log_selectorWeight_affine,
    ``RectangleCLT.Companion.gaussianTilt_cgf_sub_quadratic_eq,
    ``RectangleCLT.Companion.gaussian_exponential_translation,
    ``RectangleCLT.Companion.gaussian_mean_relative_to_one_face,
    ``RectangleCLT.Companion.gaussian_one_face_exponential,
    ``RectangleCLT.Companion.gaussian_weightCovariance_contraction_of_log_convolution_concave,
    ``RectangleCLT.Companion.hasSum_restorationSeriesTerm,
    ``RectangleCLT.Companion.integral_massEntropy_le_common_caps,
    ``RectangleCLT.Companion.integral_selectorFamilyMeanEnergy_le,
    ``RectangleCLT.Companion.integral_selectorFamilyMeanEnergy_le_entropy,
    ``RectangleCLT.Companion.integral_selectorFamilyNormalEnergy_le,
    ``RectangleCLT.Companion.integral_selectorMeanEnergy_le,
    ``RectangleCLT.Companion.lowerConstructionProperties,
    ``RectangleCLT.Companion.lowerCoordinateUpperTail_cramer_bound,
    ``RectangleCLT.Companion.lowerMaximum_rectangleError_liminf,
    ``RectangleCLT.Companion.lowerSkew_cramer_eventually,
    ``RectangleCLT.Companion.lowerTwoPointLaw_attains_envelope,
    ``RectangleCLT.Companion.lowerTwoPointLaw_third,
    ``RectangleCLT.Companion.lowerTwoPointLaw_third_ge,
    ``RectangleCLT.Companion.lower_log_relative_tail_to_relative_tail,
    ``RectangleCLT.Companion.lower_quantile_cubic_coefficient,
    ``RectangleCLT.Companion.lower_skew_linear_scale,
    ``RectangleCLT.Companion.lower_skew_quartic_remainder_ratio,
    ``RectangleCLT.Companion.normalMaxThreshold,
    ``RectangleCLT.Companion.normalizedClippedRows_boundedHypotheses,
    ``RectangleCLT.Companion.normalizedResidualRows_sum_covariance_diagonal_le,
    ``RectangleCLT.Companion.normalized_variance_le_of_cgf_sub_quadratic_concave,
    ``RectangleCLT.Companion.rectangleError_le_of_two_couplings,
    ``RectangleCLT.Companion.restorationTranslationCoefficient,
    ``RectangleCLT.Companion.selectorWeight_trace_reduction,
    ``RectangleCLT.Companion.selector_family_means_le_entropy,
    ``RectangleCLT.Companion.subexponentialCLT,
    ``RectangleCLT.Companion.subexponential_clipping_reduction,
    ``RectangleCLT.Companion.subexponential_transfer_error_weighted_le,
    ``RectangleCLT.Companion.sum_selectorWeight_eq,
    ``RectangleCLT.Companion.tangentMean_dot_mean,
    ``RectangleCLT.Companion.tangentMean_normSq,
    ``RectangleCLT.Companion.tangentMean_orthogonal,
    ``RectangleCLT.Companion.two_mul_mem_psi1Scales_of_norm_le,
    ``RectangleCLT.Companion.unrestrictedCLT,
    ``RectangleCLT.Companion.weighted_exp_mean_le,
    ``RectangleCLT.Companion.weighted_mean_sq_le_second,
    ``RectangleCLT.FaceSmoother.F_eq_exponential_probability,
    ``RectangleCLT.FaceSmoother.exponentialEvent_iff_randomRectangle_Inside,
    ``RectangleCLT.FaceSmoother.integral_F_eq_randomRectangle_average,
    ``RectangleCLT.maskObservationSum_bounded,
    ``RectangleCLT.mgf_le_exp_second_moment_of_bounded]
  for n in names do
    unless (env.checked.get.find? n).isSome do
      throwError "Mapped correspondence declaration {n} is absent from the checked kernel environment"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected transitive axiom {ax} in mapped printed-proof declaration closure"
  for n in names do
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => ""
    let record := Json.mkObj [("declaration", Json.str n.toString), ("module", Json.str moduleName)]
    liftIO <| IO.println ("PRINTED_CORRESPONDENCE_BINDING " ++ record.compress)
  logInfo m!"PRINTED_CORRESPONDENCE_AUDIT_PASS {names.size} exact mapped declarations/types; official transitive axiom union restricted to propext, Classical.choice, Quot.sound, including mapped definitions and constructors."
