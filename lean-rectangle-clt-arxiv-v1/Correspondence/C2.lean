import RectangleCLTArxivV1
import Lean.Util.CollectAxioms
import Lean.Elab.Command

-- Expanded ordinary data fields: none is a desired comparison or tail estimate.
#print RectangleCLT.BoundedIndependentHypotheses
#check @RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent
#check @RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf

-- C2.1: the original index set and its actual process maxima.
#check @RectangleCLTArxivV1.signedIndex_card
#check @RectangleCLTArxivV1.signedMaximum_eq_norm
#check @RectangleCLTArxivV1.signedAbsMaximum_eq_norm
#check @RectangleCLTArxivV1.signedGaussianLinear
-- C2.2: raw observations, variance, and the proved mixed tail.
#check @RectangleCLTArxivV1.signedContrast_independent
#check @RectangleCLTArxivV1.integral_signedContrast_zero
#check @RectangleCLTArxivV1.signedContrast_discrete_bound
#check @RectangleCLTArxivV1.sum_variance_signedContrast
#check @RectangleCLTArxivV1.signedProcess_hasMixedTail
-- C2.3: exact admissible subsets, dyadic weights, and scales.
#check @RectangleCLTArxivV1.gamma1_eq_admissible_subsets
#check @RectangleCLTArxivV1.gamma2_eq_admissible_subsets
#check @RectangleCLTArxivV1.gaussian_level_weight
#check @RectangleCLTArxivV1.gamma1_metric_homogeneity
#check @RectangleCLTArxivV1.gamma2_metric_homogeneity
-- C2.4: the base-point term follows from the actual unit coordinate moments.
#check @RectangleCLTArxivV1.integral_sum_coordinate_sq
#check @RectangleCLTArxivV1.integral_abs_le_one_of_second_moment
#check @RectangleCLTArxivV1.signed_dirksen_expectation
-- C2.5: the printed least cutoff and singleton-zero/full-set witnesses.
#check @RectangleCLTArxivV1.discreteCutoff_le_iff
#check @RectangleCLTArxivV1.discreteCutoff_weight_le_log
#check @RectangleCLTArxivV1.signedDiscreteNets_initial
#check @RectangleCLTArxivV1.signedDiscreteNets_terminal
#check @RectangleCLTArxivV1.signed_gamma1_discrete_le
-- C2.6: a genuine Gaussian factor, support, canonical metric, and width.
#check @RectangleCLTArxivV1.gaussianLaw_ae_mem_factor_range
#check @RectangleCLTArxivV1.signedVarianceMetric_eq_canonicalDist
#check @RectangleCLTArxivV1.gaussianLaw_integral_signedContrast_sq
#check @RectangleCLTArxivV1.gaussianWidth_signedFactorRows
#check @RectangleCLTArxivV1.gamma2_signedFactorRows_ne_top
#check @RectangleCLTArxivV1.gamma2_signedFactorRows_le
#check @RectangleCLTArxivV1.gaussianMaximumMean_eq_of_covariance
#check @RectangleCLTArxivV1.gaussianLaw_signedCoordinate_ae_eq_of_zero_dist
#check @RectangleCLTArxivV1.gamma2_signedFactorRows_eq_range
#check @RectangleCLTArxivV1.gaussianMaximum_signedFactorRows_ae_eq_range
#check @RectangleCLTArxivV1.gaussianWidth_signedFactorRows_eq_range
#check @RectangleCLTArxivV1.gaussianWidth_signedFactorRows_range
-- C2.7: exact lower calibration and a raw-data universal-constant conclusion.
#check @RectangleCLTArxivV1.standardNormal_integral_abs
#check @RectangleCLTArxivV1.sqrt_two_div_pi_le_gaussianMaximumMean
#check @RectangleCLTArxivV1.bounded_sum_expected_maximum
#check @RectangleCLTArxivV1.bounded_sum_expected_maximum_factor_exists
#check @RectangleCLTArxivV1.lemma_C2_expected_maximum

-- Force elaboration of each mapped endpoint in addition to building its source.
example := @RectangleCLTArxivV1.signedMaximum_eq_norm
example := @RectangleCLTArxivV1.signedProcess_hasMixedTail
example := @RectangleCLTArxivV1.gamma2_eq_admissible_subsets
example := @RectangleCLTArxivV1.signed_dirksen_expectation
example := @RectangleCLTArxivV1.signed_gamma1_discrete_le
example := @RectangleCLTArxivV1.gamma2_signedFactorRows_le
example := @RectangleCLTArxivV1.lemma_C2_expected_maximum
