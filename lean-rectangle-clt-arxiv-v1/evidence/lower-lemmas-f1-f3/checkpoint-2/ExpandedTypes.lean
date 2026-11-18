import RectangleCLTArxivV1.LowerLemmaF1Support
import RectangleCLTArxivV1.LowerLemmaF2
import RectangleCLTArxivV1.LowerLemmaF3
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.lemma_F_1_weighted_normal_log_derivative,
    ``RectangleCLTArxivV1.lemma_F_1_weighted_normal_derivative,
    ``RectangleCLT.Companion.SplitV4.moderate_root_displacement,
    ``RectangleCLT.Companion.SplitV4.moderate_inverse_expansion,
    ``RectangleCLT.Companion.SplitV4.moderate_sqrt_variance_expansion,
    ``RectangleCLTArxivV1.scalarModerateTailRadius_pos,
    ``RectangleCLTArxivV1.scalarModerateTailErrorConstant_pos,
    ``RectangleCLTArxivV1.lemma_F_1_bound,
    ``RectangleCLTArxivV1.lemma_F_1_uniform_scalar_moderate_tail,
    ``RectangleCLTArxivV1.lemma_F_2_independent_conditioning,
    ``RectangleCLTArxivV1.lemma_F_2_signed_taylor,
    ``RectangleCLTArxivV1.lemma_F_2_independently_shifted_variables,
    ``RectangleCLTArxivV1.lemma_F_3_raw_covariance,
    ``RectangleCLTArxivV1.lemma_F_3_gaussian_covariance,
    ``RectangleCLTArxivV1.lemma_F_3_properties_of_parameters,
    ``RectangleCLTArxivV1.lemma_F_3_common_symmetric_construction,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_copy_inner,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_independent_copy_inner,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_copy_variance_integral,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_copy_tilt_integral_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayVariance_exp_bounds_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayFourth_abs_le_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayCGF_cubic_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayFourthBound_mono_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayThird_difference_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayVariance_linear_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_quadratic_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_taylor_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_sub_self_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.exists_moderateArrayMean_eq_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_variance_bounds_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_strictMono_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_eq_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_printed_interval,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProduct_log_esscher_error_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProductTail_positive_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProductTail_zero_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProductTail_nonneg_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.strictTailProbability_measurable,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_strict_laplace_weight,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_strict_laplace_tail,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_strict_laplace_correction,
    ``RectangleCLT.Companion.SplitV4.Printed.laplace_decay_primitive,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.strictTailProbability_eq_one_sub_cdf,
    ``RectangleCLT.Companion.SplitV4.Printed.laplace_correction_kernel_mass,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_strict_tail_weight,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_weighted_tail_comparison_nonneg,
    ``RectangleCLT.Companion.SplitV4.Printed.normalWeightedTail_antitone_nonneg,
    ``RectangleCLT.Companion.SplitV4.Printed.normalWeightedTail_printed_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.normalWeightedTail_printed_upper,
    ``RectangleCLT.Companion.SplitV4.Printed.abs_log_normalWeightedTail_deriv_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProductWeightedTail_abs_error_nonneg,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateProductWeightedTail_log_error_nonneg,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_eq_withDensity,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_iIndepFun,
    ``RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_cdf_of_variance_lower,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_inverse_integral,
    ``RectangleCLT.Companion.SplitV4.moderateTiltFourthCumulant_abs_le,
    ``RectangleCLT.Companion.SplitV4.moderateProduct_strict_tail_tilt,
    ``RectangleCLT.Companion.SplitV4.moderateProduct_strict_tail_standardized,
    ``RectangleCLT.Companion.SplitV4.moderateProduct_log_esscher,
    ``RectangleCLT.Companion.SplitV4.moderateIndependent_sum_identDistrib,
    ``RectangleCLT.Companion.SplitV4.moderateArrayGamma_abs_le,
    ``RectangleCLT.Companion.SplitV4.moderate_tilted_threshold_cancellation,
    ``RectangleCLT.Companion.SplitV4.moderate_legendre_expansion,
    ``RectangleCLT.Companion.SplitV4.independent_shift_cdf,
    ``RectangleCLT.Companion.SplitV4.shifted_taylor_bound,
    ``RectangleCLT.Companion.SplitV4.expected_cdf_shift_taylor_error,
    ``RectangleCLT.Companion.SplitV4.shift_convolution_error_bound,
    ``RectangleCLT.Companion.SplitV4.independent_shift_comparison,
    ``RectangleCLT.Companion.SplitV4.secondDerivativeSupNorm_le_iff,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
    ``RectangleCLTArxivV1.lowerFamilyArray_map_seed,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_independent,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_identDistrib,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_iid,
    ``RectangleCLTArxivV1.lowerFamilySeedFlip_preserving,
    ``RectangleCLTArxivV1.lowerFamilyObservation_seedFlip,
    ``RectangleCLTArxivV1.lowerFamilyObservation_centrally_symmetric,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_centrally_symmetric,
    ``RectangleCLTArxivV1.lowerFamilyObservation_norm_le,
    ``RectangleCLTArxivV1.lowerFamilyObservation_envelope,
    ``RectangleCLTArxivV1.integral_lowerFamilyObservation,
    ``RectangleCLTArxivV1.integral_lowerFamilyObservation_product,
    ``RectangleCLTArxivV1.integral_lowerFamilyObservation_fourth,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_centered,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_second,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_fourth,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_boundedIndependent,
    ``RectangleCLTArxivV1.lowerFamilyNormalizedObservations_covariance,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_unit_diagonal,
    ``RectangleCLTArxivV1.lowerFamilyNormalizedObservations_unit_covariance,
    ``RectangleCLTArxivV1.lowerAdditiveGridFactor_mulVec,
    ``RectangleCLTArxivV1.lowerAdditiveGridFactor_gram,
    ``RectangleCLTArxivV1.lowerAdditiveGridFactor_ker,
    ``RectangleCLTArxivV1.lowerAdditiveGridFactor_rank,
    ``RectangleCLTArxivV1.lowerFamilyPairCovariance_gram,
    ``RectangleCLTArxivV1.lowerFamilyPairCovariance_rank,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_eq_pair_submatrix,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_rank,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_abs_offDiagonal_le,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_offDiagonal_attains,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_maxOffDiagonal,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_pairGap,
    ``RectangleCLTArxivV1.lowerFamilyNormalizedObservations_rank,
    ``RectangleCLTArxivV1.lowerFamilyNormalizedObservations_pairGap,
    ``RectangleCLTArxivV1.integral_lowerFamilySeed_indicator_function,
    ``RectangleCLTArxivV1.integral_lowerFamilyActivation_rpow,
    ``RectangleCLTArxivV1.family_rpow_q_root,
    ``RectangleCLTArxivV1.lowerFamilyObservation_Lq_envelope,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_Lq_envelope,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_eq_gaussianGram,
    ``RectangleCLTArxivV1.lowerFamilyCovariance_factor_exists,
    ``RectangleCLTArxivV1.lowerFamilyGaussianFactor_gram,
    ``RectangleCLTArxivV1.lowerFamilyGaussianFactor_matches_covariance,
    ``RectangleCLTArxivV1.lowerFamilyGaussianLaw_eq,
    ``RectangleCLTArxivV1.lowerFamilyGaussianMaximumMean_eq,
    ``RectangleCLTArxivV1.lowerFamilyGaussian_width_bounds,
    ``RectangleCLTArxivV1.lemma_lower_family_properties,
    ``RectangleCLTArxivV1.covariance_lowerGridGaussianLaw,
    ``RectangleCLTArxivV1.lowerGridGaussianMean_lower,
    ``RectangleCLTArxivV1.lowerGridGaussianMean_upper,
    ``RectangleCLTArxivV1.lowerGridGaussianLaw_eq_gaussianLaw]
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
    ("scope", toJson "Named Lemmas F.1/F.2/F.3 actual laws: full types, proof steps and project dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
