import RectangleCLTArxivV1.SupplementalHProjectedMean
import RectangleCLTArxivV1.SupplementalHLocalizedTube
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.gaussian_mean_relative_to_projection
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussian_selector_projected_matrix_bound
set_option pp.all true in
#check @RectangleCLTArxivV1.concentrated_base_gaussian_weighted_outward_tube

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.projection_complement_mem_kernel,
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
    ``RectangleCLTArxivV1.concentrated_base_gaussian_weighted_outward_tube]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
