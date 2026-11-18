import RectangleCLTArxivV1.SupplementalHFrameIsometry
import RectangleCLTArxivV1.SupplementalHRidgeTripleGrouping
import RectangleCLTArxivV1.SupplementalHIndependentTriples
import RectangleCLTArxivV1.SupplementalHRidgeAtoms
import RectangleCLTArxivV1.SupplementalHRidgeIndependentGrouping
import RectangleCLTArxivV1.SupplementalHRidgeMeasurable
import RectangleCLTArxivV1.SupplementalHRidgeRegularity
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.orthonormalFrameIsometry_apply,
    ``RectangleCLTArxivV1.orthonormalFrameIsometry_single,
    ``RectangleCLTArxivV1.orthonormalFrameCoordinates_apply,
    ``RectangleCLTArxivV1.orthonormalFrameCoordinates_isometry_apply,
    ``RectangleCLTArxivV1.orthonormalFrameIsometry_coordinates,
    ``RectangleCLTArxivV1.orthonormalFrameIsometry_coordinates_of_mem,
    ``RectangleCLTArxivV1.orthonormalFrameIsometry_range,
    ``RectangleCLTArxivV1.sum_cube_cycle,
    ``RectangleCLTArxivV1.sum_cube_swap_last,
    ``RectangleCLTArxivV1.half_sum_cube_eq_sixth_incidence_groups,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_sum,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdBoundaryIntegral_grouping,
    ``RectangleCLTArxivV1.abs_sum_cube_le,
    ``RectangleCLTArxivV1.abs_hardGaussianRidgeThirdBoundaryIntegral_le_groups,
    ``RectangleCLTArxivV1.sum_cube_eq_sum_triple_functions,
    ``RectangleCLTArxivV1.IndependentNormalTriple.injective,
    ``RectangleCLTArxivV1.sum_eq_sum_subtype_of_zero,
    ``RectangleCLTArxivV1.sum_cube_eq_independent_triples,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_eq_boundaryDensity,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_zero_of_repeated,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_zero_of_zero_residual,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_eq_mass,
    ``RectangleCLTArxivV1.ae_all_tripleIncidenceRegularity,
    ``RectangleCLTArxivV1.ae_hardGaussianRidgeThirdBoundaryIntegral_independent_sum,
    ``RectangleCLTArxivV1.ae_abs_hardGaussianRidgeThirdBoundaryIntegral_le_independent_groups,
    ``RectangleCLTArxivV1.measurable_hardPairSection_integral_threshold,
    ``RectangleCLTArxivV1.measurable_hardGaussianRidgeNormalWeight,
    ``RectangleCLTArxivV1.measurable_hardGaussianSignedRidgeTerm,
    ``RectangleCLTArxivV1.measurable_hardGaussianWeightedRidgeIntegral,
    ``RectangleCLTArxivV1.measurable_hardGaussianRidgeLeadingTerm,
    ``RectangleCLTArxivV1.measurable_hardGaussianRidgeLeadingIntegral,
    ``RectangleCLTArxivV1.allPairResidualThresholdRegularity_isOpen,
    ``RectangleCLTArxivV1.ae_threshold_ae_base_affine_property,
    ``RectangleCLTArxivV1.ae_threshold_ae_base_pairResidualThresholdRegularity,
    ``RectangleCLTArxivV1.AllPairResidualThresholdRegularity.triple]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
