import RectangleCLTArxivV1.SupplementalHTrihedralNormals
import RectangleCLTArxivV1.SupplementalHGenericStrata
import RectangleCLTArxivV1.SupplementalHTripleFiber
import RectangleCLTArxivV1.SupplementalHNormalChartIsometry
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.inner_trihedralCoordinateNormal,
    ``RectangleCLTArxivV1.trihedralCoordinateNormal_ne_zero,
    ``RectangleCLTArxivV1.trihedralInwardNormal_norm,
    ``RectangleCLTArxivV1.inner_trihedralInwardNormal,
    ``RectangleCLTArxivV1.trihedralInwardNormal_orthogonal_other,
    ``RectangleCLTArxivV1.trihedralInwardNormal_positive_own,
    ``RectangleCLTArxivV1.trihedralInwardNormal_linearIndependent,
    ``RectangleCLTArxivV1.trihedralInwardNormal_unique,
    ``RectangleCLTArxivV1.mem_trihedralGeneratedCone_iff,
    ``RectangleCLTArxivV1.trihedralGeneratedCone_eq_halfspaces,
    ``RectangleCLTArxivV1.trihedral_facet_eq_generated_other,
    ``RectangleCLTArxivV1.ae_threshold_ne_finite_coordinate_combination,
    ``RectangleCLTArxivV1.threeNormalSpanCoefficients_spec,
    ``RectangleCLTArxivV1.ae_no_extra_active_normal_in_three_span,
    ``RectangleCLTArxivV1.supplementalH_cone_ball_volume,
    ``RectangleCLTArxivV1.adaptive_cone_gaussian_integral_lower_fourth,
    ``RectangleCLTArxivV1.adaptive_cone_spherical_vector_fourth_bound,
    ``RectangleCLTArxivV1.normalSectionChart_zero_add,
    ``RectangleCLTArxivV1.normalSectionChart_coordinates,
    ``RectangleCLTArxivV1.euclideanNormalSectionIsometry_surjective_on_plane]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
