import RectangleCLTArxivV1
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``GenericChaining.gaussianWidth_mono_of_increment_le,
    ``RectangleCLT.Companion.D_L_mul_le,
    ``RectangleCLT.Companion.SplitV4.abs_mulVec_le_of_row_l1,
    ``RectangleCLT.Companion.SplitV4.boundedIndependent_projected,
    ``RectangleCLT.Companion.SplitV4.centered_linear_form_ae_zero_of_variance_zero,
    ``RectangleCLT.Companion.SplitV4.facePolyhedron_eq_preimage_standardized,
    ``RectangleCLT.Companion.SplitV4.gaussian_linear_form_ae_zero_of_variance_zero,
    ``RectangleCLT.Companion.SplitV4.mem_facePolyhedron_iff_standardized,
    ``RectangleCLT.Companion.SplitV4.mulVec_fourth_le_weighted_coordinate_fourths,
    ``RectangleCLT.Companion.SplitV4.mulVec_sq_le_weighted_coordinate_squares,
    ``RectangleCLT.Companion.SplitV4.polyhedronError_eq_projected_rectangleError,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_average_fourth,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_envelope_moment,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_fourth_integrable,
    ``RectangleCLT.Companion.SplitV4.standardizedFaceMap_row_l1_le,
    ``RectangleCLT.Companion.SplitV4.zero_variance_faces_negative_threshold,
    ``RectangleCLT.Companion.SplitV4.zero_variance_faces_probability_eq,
    ``RectangleCLT.Companion.absolute_residual_sum_mgf_le,
    ``RectangleCLT.Companion.centeredClippedRows,
    ``RectangleCLT.Companion.centeredResidualRows,
    ``RectangleCLT.Companion.clipped_standardDeviation_ge_half,
    ``RectangleCLT.Companion.clipped_standardDeviation_sub_one_le,
    ``RectangleCLT.Companion.jointRestoration_gaussianCoupling_exists,
    ``RectangleCLT.Companion.normalizedObservationSum_eq_clipped_add_residual,
    ``RectangleCLT.Companion.normalizedResidualRows_sum_covariance_diagonal_le,
    ``RectangleCLT.Companion.normalized_exp_residual_tail,
    ``RectangleCLT.Companion.residual_sum_abs_tail,
    ``RectangleCLT.Companion.standardGaussian_rectangular_norm_tail_log,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_average_second,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_covariance,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_envelope_moment,
    ``RectangleCLTArxivV1.PolynomialFourthHypotheses.projected,
    ``RectangleCLTArxivV1.RelativeFourthBudgets.toRelativeMomentBounds,
    ``RectangleCLTArxivV1.SubexponentialWidthBound,
    ``RectangleCLTArxivV1.abs_clipAt_sub_le,
    ``RectangleCLTArxivV1.boundedPolyhedralCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.boundedPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.boundedPolyhedralEnvelopeCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.clipAt_neg,
    ``RectangleCLTArxivV1.corollary_2_intrinsic,
    ``RectangleCLTArxivV1.corollary_3_bounded_orlicz_intrinsic,
    ``RectangleCLTArxivV1.corollary_3_intrinsic,
    ``RectangleCLTArxivV1.eventually_lowerDenseAmplitude_ge_one,
    ``RectangleCLTArxivV1.eventually_lowerDense_envelope,
    ``RectangleCLTArxivV1.eventually_lowerDense_fourth,
    ``RectangleCLTArxivV1.eventually_lowerFourth_coordinate_fourth,
    ``RectangleCLTArxivV1.eventually_lowerFourth_fourth_factor,
    ``RectangleCLTArxivV1.eventually_lowerFourth_membership,
    ``RectangleCLTArxivV1.eventually_lowerFourth_printed_envelope,
    ``RectangleCLTArxivV1.eventually_lowerFourth_variance_sqrt,
    ``RectangleCLTArxivV1.exists_lowerDense_upper_constant,
    ``RectangleCLTArxivV1.exists_lowerFourth_upper_constant,
    ``RectangleCLTArxivV1.four_n_tail_le_quarter,
    ``RectangleCLTArxivV1.fourthWidthRate_fixed_budget_identity,
    ``RectangleCLTArxivV1.gaussianMaximumMean_clipped_le,
    ``RectangleCLTArxivV1.gaussianMaximumMean_projected,
    ``RectangleCLTArxivV1.gaussianMaximumMean_standardized_le,
    ``RectangleCLTArxivV1.gaussian_probability_le_contractedBox_intrinsic,
    ``RectangleCLTArxivV1.gaussian_probability_shiftedBox_intrinsic,
    ``RectangleCLTArxivV1.intrinsicEnvelopeCLT,
    ``RectangleCLTArxivV1.intrinsicEnvelopeCLT_after_standardization,
    ``RectangleCLTArxivV1.lemma_lower_family_properties,
    ``RectangleCLTArxivV1.lowerDenseAmplitude_moment_identity,
    ``RectangleCLTArxivV1.lowerDenseAmplitude_width_identity,
    ``RectangleCLTArxivV1.lowerDense_actual_rate_le_twelve_raw,
    ``RectangleCLTArxivV1.lowerDense_four_rate,
    ``RectangleCLTArxivV1.mem_psi1Scales_of_norm_le,
    ``RectangleCLTArxivV1.normalized_residual_tail_printed,
    ``RectangleCLTArxivV1.orliczPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.orliczPolyhedralCLT_intrinsic_all_faces,
    ``RectangleCLTArxivV1.polyhedralDistance_eq_positive_faces,
    ``RectangleCLTArxivV1.polyhedralDistance_le_standardizedRectangleDistance,
    ``RectangleCLTArxivV1.polyhedralDistance_zero_of_no_positive_faces,
    ``RectangleCLTArxivV1.polyhedralIntrinsicWidth_le,
    ``RectangleCLTArxivV1.polynomialPolyhedralCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.polynomialPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.polynomialPolyhedralEnvelope_inputs,
    ``RectangleCLTArxivV1.positivePolyhedralFaceCount_le,
    ``RectangleCLTArxivV1.positivePolyhedralFaceScale_pos,
    ``RectangleCLTArxivV1.positivePolyhedralFaceScale_sq,
    ``RectangleCLTArxivV1.printedResidualRadius,
    ``RectangleCLTArxivV1.printedResidualRadius_le_archive,
    ``RectangleCLTArxivV1.projectedGaussian_factor_exists,
    ``RectangleCLTArxivV1.psi1Independent_projected_exact,
    ``RectangleCLTArxivV1.psi1_exponentialHypotheses_exact,
    ``RectangleCLTArxivV1.rectangleError_le_of_two_couplings_intrinsic,
    ``RectangleCLTArxivV1.relativeFourthBudgets_projected,
    ``RectangleCLTArxivV1.residual_power_moment_printed,
    ``RectangleCLTArxivV1.residual_tail_printed,
    ``RectangleCLTArxivV1.signedCoordinate_centeredClipped,
    ``RectangleCLTArxivV1.signedCoordinate_clipAt,
    ``RectangleCLTArxivV1.sqrt_two_div_pi_le_gaussianMaximumMean,
    ``RectangleCLTArxivV1.standardizedProjection_inputs,
    ``RectangleCLTArxivV1.subexponentialCLT_intrinsic,
    ``RectangleCLTArxivV1.subexponentialCLT_psi1_intrinsic,
    ``RectangleCLTArxivV1.subexponentialUnionLog_le_two,
    ``RectangleCLTArxivV1.subexponential_clipping_reduction_intrinsic,
    ``RectangleCLTArxivV1.sum_integral_projection_sq_of_memLp,
    ``RectangleCLTArxivV1.tendsto_lowerDense_fourth_factor,
    ``RectangleCLTArxivV1.tendsto_lowerDense_raw_width_scale,
    ``RectangleCLTArxivV1.tendsto_lowerDense_theta,
    ``RectangleCLTArxivV1.tendsto_lowerFourth_dense_rate,
    ``RectangleCLTArxivV1.theorem4_bounded_symmetric_lower,
    ``RectangleCLTArxivV1.theorem_5_fourth_moment_lower,
    ``RectangleCLTArxivV1.theorem_5_fourth_moment_two_sided,
    ``RectangleCLTArxivV1.theorem_6_growing_fourth_moment_lower,
    ``RectangleCLTArxivV1.theorem_7_fixed_envelope_fourth_lower,
    ``RectangleCLTArxivV1.theorem_7_polynomial_envelope_lower]
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
