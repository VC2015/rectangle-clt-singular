import RectangleCLTArxivV1.GaussianC1Statement
import RectangleCLTArxivV1.GaussianRectangleIntrinsic
import Lean.Util.CollectAxioms

#check @RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_unit
#check @RectangleCLT.Companion.SplitV4.gaussianFaceRow_normSq
#check @RectangleCLT.Companion.SplitV4.gaussianFaceWeight_nonneg
#check @RectangleCLT.Companion.SplitV4.gaussianFaceWeight_sum
#check @RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_hasDerivAt
#check @RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_hasDerivAt
#check @RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_le_one
#check @RectangleCLT.Companion.SplitV4.smoothGaussianFaceHessian_trace_nonneg
#check @RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein
#check @RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_test_bound
#check @RectangleCLT.Companion.SplitV4.gaussian_affine_branches_ae_distinct_rows_ne
#check @RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_tendsto_one
#check @RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound
#check @RectangleCLT.Companion.SplitV4.Printed.gaussianLinearRamp
#check @RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp
#check @RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp_deriv_tendsto
#check @RectangleCLT.Companion.SplitV4.Printed.intrinsicGaussianBoundary_printed_mollification
#check @RectangleCLT.Companion.SplitV4.integral_exp_positiveGaussianFaceMaximum_le
#check @RectangleCLT.Companion.SplitV4.integral_positiveGaussianFaceMaximum_le_sqrt_log
#check @RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_projection_norm
#check @RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_integral_projection_norm
#check @RectangleCLT.Companion.SplitV4.gaussianPolyhedronLayer_subset_standardized_shell
#check @RectangleCLT.Companion.SplitV4.product_event_probability_le_of_sections
#check @RectangleCLTArxivV1.gaussianModel_covariance
#check @RectangleCLTArxivV1.gaussianModel_supported_on_factor_range
#check @RectangleCLTArxivV1.mergedGaussianThreshold_le
#check @RectangleCLTArxivV1.mergedGaussianThreshold_attains
#check @RectangleCLTArxivV1.gaussianAffineMaximum_merge_thresholds
#check @RectangleCLTArxivV1.positiveGaussianFaceMaximum_eq_projection_norm
#check @RectangleCLTArxivV1.normalizedGaussianFaceRows_opposite
#check @RectangleCLTArxivV1.gaussianFaceNorm_mean_le_sharp
#check @RectangleCLTArxivV1.face_log_le_two_dimensionLog
#check @RectangleCLTArxivV1.gaussianFaceNorm_mean_le_dimension
#check @RectangleCLTArxivV1.gaussianFaceNorm_intrinsic_coefficient_le
#check @RectangleCLTArxivV1.lemma_C1_gaussian_model
#check @RectangleCLTArxivV1.gaussianMaximumMean_le_common_variance
#check @RectangleCLTArxivV1.gaussianMaximumMean_intrinsic_coefficient_le
#check @RectangleCLTArxivV1.gaussianRectangleBoundary_fixed_shift_logarithmic
#check @RectangleCLTArxivV1.gaussianRectangleBoundary_product_logarithmic

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[
    ``RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_unit,
    ``RectangleCLT.Companion.SplitV4.gaussianFaceRow_normSq,
    ``RectangleCLT.Companion.SplitV4.gaussianFaceWeight_nonneg,
    ``RectangleCLT.Companion.SplitV4.gaussianFaceWeight_sum,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_hasDerivAt,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_hasDerivAt,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_le_one,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceHessian_trace_nonneg,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_test_bound,
    ``RectangleCLT.Companion.SplitV4.gaussian_affine_branches_ae_distinct_rows_ne,
    ``RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient_normSq_tendsto_one,
    ``RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianLinearRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianMollifiedRamp_deriv_tendsto,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsicGaussianBoundary_printed_mollification,
    ``RectangleCLT.Companion.SplitV4.integral_exp_positiveGaussianFaceMaximum_le,
    ``RectangleCLT.Companion.SplitV4.integral_positiveGaussianFaceMaximum_le_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_projection_norm,
    ``RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_integral_projection_norm,
    ``RectangleCLT.Companion.SplitV4.gaussianPolyhedronLayer_subset_standardized_shell,
    ``RectangleCLT.Companion.SplitV4.product_event_probability_le_of_sections,
    ``RectangleCLTArxivV1.gaussianModel_covariance,
    ``RectangleCLTArxivV1.gaussianModel_supported_on_factor_range,
    ``RectangleCLTArxivV1.mergedGaussianThreshold_le,
    ``RectangleCLTArxivV1.mergedGaussianThreshold_attains,
    ``RectangleCLTArxivV1.gaussianAffineMaximum_merge_thresholds,
    ``RectangleCLTArxivV1.positiveGaussianFaceMaximum_eq_projection_norm,
    ``RectangleCLTArxivV1.normalizedGaussianFaceRows_opposite,
    ``RectangleCLTArxivV1.gaussianFaceNorm_mean_le_sharp,
    ``RectangleCLTArxivV1.face_log_le_two_dimensionLog,
    ``RectangleCLTArxivV1.gaussianFaceNorm_mean_le_dimension,
    ``RectangleCLTArxivV1.gaussianFaceNorm_intrinsic_coefficient_le,
    ``RectangleCLTArxivV1.lemma_C1_gaussian_model,
    ``RectangleCLTArxivV1.gaussianMaximumMean_le_common_variance,
    ``RectangleCLTArxivV1.gaussianMaximumMean_intrinsic_coefficient_le,
    ``RectangleCLTArxivV1.gaussianRectangleBoundary_fixed_shift_logarithmic,
    ``RectangleCLTArxivV1.gaussianRectangleBoundary_product_logarithmic] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"

-- Re-elaborate the model-Gaussian statement and every printed Gaussian inference endpoint.
example := @RectangleCLTArxivV1.gaussianModel_covariance
example := @RectangleCLT.Companion.SplitV4.smoothGaussianFaceHessian_trace_nonneg
example := @RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein
example := @RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound
example := @RectangleCLT.Companion.SplitV4.Printed.intrinsicGaussianBoundary_printed_mollification
example := @RectangleCLTArxivV1.gaussianFaceNorm_mean_le_dimension
example := @RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift
example := @RectangleCLTArxivV1.gaussianIntrinsicBoundary_independent_shift
example := @RectangleCLTArxivV1.lemma_C1_gaussian_model
