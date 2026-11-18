import RectangleCLTArxivV1.PairedIntrinsicBennett
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussian_smallerEnvelope_intrinsic,
    ``RectangleCLTArxivV1.gaussianMaximumMean_slepian_scale_div,
    ``RectangleCLTArxivV1.intrinsic_gaussian_gradient_contraction,
    ``RectangleCLTArxivV1.intrinsic_gaussian_hessian_contraction,
    ``RectangleCLTArxivV1.intrinsic_weighted_gaussian_gradient_contraction,
    ``RectangleCLTArxivV1.intrinsic_weighted_gaussian_hessian_contraction,
    ``RectangleCLTArxivV1.intrinsic_slepian_weighted_gradient_contraction,
    ``RectangleCLTArxivV1.intrinsic_slepian_weighted_hessian_contraction,
    ``RectangleCLTArxivV1.gaussian_integral_sum_fourthLocalMajorant_intrinsic,
    ``RectangleCLTArxivV1.intrinsic_gaussian_common_point_fourth_contraction,
    ``RectangleCLTArxivV1.intrinsic_gaussian_common_point_fourth_random_data,
    ``RectangleCLTArxivV1.intrinsic_gaussian_trapezoidal_sum_bound,
    ``RectangleCLTArxivV1.intrinsic_pairedGaussianRemainder_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementHessianTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementGradientTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementRemainderTerm_le,
    ``RectangleCLTArxivV1.intrinsic_largeIncrement_smooth_expectation_comparison_conditional,
    ``RectangleCLTArxivV1.intrinsic_largeIncrement_smooth_expectation_comparison,
    ``RectangleCLTArxivV1.intrinsic_largeIncrementGaussianComparison_bandwidth,
    ``RectangleCLTArxivV1.intrinsic_largeIncrementGaussianComparison,
    ``RectangleCLTArxivV1.intrinsic_gaussianComparisonWithLargeIncrementRemainders,
    ``RectangleCLTArxivV1.lemma_E1_intrinsic_comparison,
    ``RectangleCLTArxivV1.lemma_E3_paired_slepian,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_small_regime,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_large_regime,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT,
    ``RectangleCLTArxivV1.intrinsic_bennett_normalized_width_identity,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT_observations,
    ``RectangleCLTArxivV1.theorem_2_ii_intrinsic,
    ``RectangleCLTArxivV1.lemma_E4_truncated_bennett_maximum,
    ``RectangleCLTArxivV1.lemma_E4_truncated_bennett_maximum_zero_variance]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
