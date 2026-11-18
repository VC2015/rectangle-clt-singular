import RectangleCLTArxivV1.SupplementalHSurfaceFatou
import RectangleCLTArxivV1.SupplementalHActualRidgeEstimates
import RectangleCLTArxivV1.SupplementalHSurfaceEmpty
import RectangleCLTArxivV1.SupplementalHSurfaceMain
import RectangleCLTArxivV1.SupplementalHSurfaceFullDimensional
import RectangleCLTArxivV1.SupplementalHSurfaceFinal
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.integrable_abs_bound_of_ae_parameter_continuity,
    ``RectangleCLTArxivV1.actualFacet_weightedRidgeIntegral_concentrated_base,
    ``RectangleCLTArxivV1.exists_fixed_actualFacet_surface_concentrated_base_bound,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_zero_of_empty,
    ``RectangleCLTArxivV1.hardGaussianSignedRidgeTerm_zero_of_empty,
    ``RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_zero_of_empty,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdEvent_affine_empty,
    ``RectangleCLTArxivV1.hardGaussianSurfaceIntegrals_zero_empty_presentation,
    ``RectangleCLTArxivV1.exists_fixed_surface_bound_of_empty_or_strictInterior,
    ``RectangleCLTArxivV1.hasStrictFacetInterior_of_nonempty_interior,
    ``RectangleCLTArxivV1.HasStrictFacetInterior.nonempty_interior,
    ``RectangleCLTArxivV1.exists_fixed_surface_bound_of_empty_or_fullDimensional]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
