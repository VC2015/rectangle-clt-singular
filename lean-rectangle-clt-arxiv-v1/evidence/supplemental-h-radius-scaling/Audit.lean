import RectangleCLTArxivV1.SupplementalHRadius
import RectangleCLTArxivV1.SupplementalHWeightScaling
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.projection_complement_mem_kernel,
    ``RectangleCLTArxivV1.symmetric_projection_dot,
    ``RectangleCLTArxivV1.projection_complement_orthogonal,
    ``RectangleCLTArxivV1.projection_complement_dot,
    ``RectangleCLTArxivV1.projection_normSq_decomposition,
    ``RectangleCLTArxivV1.gaussian_projection_exponential,
    ``RectangleCLTArxivV1.gaussian_projected_mean_sq_le_second,
    ``RectangleCLTArxivV1.gaussian_mean_relative_to_projection,
    ``RectangleCLTArxivV1.gaussian_bounded_logConcave_matrix_reduction,
    ``RectangleCLTArxivV1.gaussian_selector_projected_matrix_bound,
    ``RectangleCLTArxivV1.faceLayer_translate,
    ``RectangleCLTArxivV1.measurableSet_gaussianVariableTube,
    ``RectangleCLTArxivV1.concentrated_base_gaussian_weighted_tube,
    ``RectangleCLTArxivV1.gaussianOutwardVariableTube_eq,
    ``RectangleCLTArxivV1.concentrated_base_gaussian_weighted_outward_tube,
    ``RectangleCLTArxivV1.threeFaceSubspace_finrank_le,
    ``RectangleCLTArxivV1.supplementalHRadius_ge_one,
    ``RectangleCLTArxivV1.supplementalHRadius_pos,
    ``RectangleCLTArxivV1.measurable_supplementalHRadius,
    ``RectangleCLTArxivV1.supplementalHRadius_projection_norm_le,
    ``RectangleCLTArxivV1.supplementalHRadius_small_span_norm_le,
    ``RectangleCLTArxivV1.supplementalHRadius_add_le,
    ``RectangleCLTArxivV1.supplementalHRadius_weighted_moment_le,
    ``RectangleCLTArxivV1.supplementalHRadius_moment_le,
    ``RectangleCLTArxivV1.concentrated_base_threeFace_weighted_outward_tube,
    ``RectangleCLTArxivV1.concentrated_base_threeFace_weighted_outward_tube_large_scale,
    ``RectangleCLTArxivV1.weightMass_const_mul,
    ``RectangleCLTArxivV1.weightMean_const_mul,
    ``RectangleCLTArxivV1.weightedScore_const_mul,
    ``RectangleCLTArxivV1.symmetricNuclearNorm_nonneg_smul,
    ``RectangleCLTArxivV1.NonnegativeLogConcave_const_mul,
    ``RectangleCLTArxivV1.gaussian_logConcave_matrix_reduction_of_bound,
    ``RectangleCLTArxivV1.gaussian_projected_mean_of_bounded_reference]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
