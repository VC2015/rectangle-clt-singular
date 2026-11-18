import RectangleCLTArxivV1.SupplementalHLocalThreshold
import RectangleCLTArxivV1.SupplementalHLocalBoundary
import RectangleCLTArxivV1.SupplementalHSectionTrace
import RectangleCLTArxivV1.SupplementalHGenericThreshold
import RectangleCLTArxivV1.SupplementalHResidualGreen
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_ae_no_boundary_of_slack,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteThresholdCDF_of_slack,
    ``RectangleCLTArxivV1.measurable_gaussianFiniteThresholdCDF,
    ``RectangleCLTArxivV1.continuousAt_gaussianThresholdSectionProbability_of_slack,
    ``RectangleCLTArxivV1.measurable_gaussianThresholdSectionProbability,
    ``RectangleCLTArxivV1.hasDerivAt_integral_Iic_of_continuousAt_integrable,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianThresholdCDF_update_of_slack,
    ``RectangleCLTArxivV1.gaussianThresholdFirst_eq_section_of_slack,
    ``RectangleCLTArxivV1.localThresholdRegularity_isOpen,
    ``RectangleCLTArxivV1.continuousAt_gaussianThresholdFirst_of_slack,
    ``RectangleCLTArxivV1.hasFDerivAt_gaussianThresholdCDF_of_slack,
    ``RectangleCLTArxivV1.gaussianThresholdTrace_eq_radial_first_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianThresholdCDF_translate_of_slack,
    ``RectangleCLTArxivV1.integral_hard_polyhedron_translate,
    ``RectangleCLTArxivV1.gaussian_hard_polyhedron_firstMoment_of_slack,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_normal_score_zero,
    ``RectangleCLTArxivV1.thresholdSignedSection_eq_residual_trace,
    ``RectangleCLTArxivV1.ae_volume_faceDot_ne,
    ``RectangleCLTArxivV1.ae_threshold_ne_two_coordinate_combination,
    ``RectangleCLTArxivV1.ae_threshold_ne_coordinate_multiple,
    ``RectangleCLTArxivV1.ae_localThresholdRegularity,
    ``RectangleCLTArxivV1.ae_threshold_all_two_coordinate_combinations,
    ``RectangleCLTArxivV1.hardGaussianFacet_Green_residual_of_slack,
    ``RectangleCLTArxivV1.ae_residualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_hardGaussianFacet_Green_residual]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
