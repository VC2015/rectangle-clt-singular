import RectangleCLTArxivV1.SupplementalHSurfaceMeasure
import RectangleCLTArxivV1.SupplementalHThresholdRegularity
import RectangleCLTArxivV1.SupplementalHGaussianBoundary
import RectangleCLTArxivV1.SupplementalHHardFacetGreen
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.measurable_normalSectionChart,
    ``RectangleCLTArxivV1.gaussianDensity_normalSectionChart,
    ``RectangleCLTArxivV1.gaussianSection_integral_eq_normalSectionChart,
    ``RectangleCLTArxivV1.gaussianSectionLaw_eq_chart_map,
    ``RectangleCLTArxivV1.map_weighted_density,
    ``RectangleCLTArxivV1.affineSurfaceVolume_gaussian_weight,
    ``RectangleCLTArxivV1.affineSurfaceVolume_chart_independent,
    ``RectangleCLTArxivV1.affineSurfaceVolume_ae_on_hyperplane,
    ``RectangleCLTArxivV1.affineSurfaceVolume_gaussian_integral,
    ``RectangleCLTArxivV1.gaussianSectionLaw_integrable_score_indicator,
    ``RectangleCLTArxivV1.hardFacet_signed_surface_eq_section,
    ``RectangleCLTArxivV1.affineSurfaceVolume_gaussian_integrable_iff,
    ``RectangleCLTArxivV1.hardFacet_signed_surface_integrable,
    ``RectangleCLTArxivV1.gaussianThresholdFirst_eq_section_nonparallel,
    ``RectangleCLTArxivV1.continuous_gaussianThresholdFirst_nonparallel,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianThresholdCDF_update_nonparallel,
    ``RectangleCLTArxivV1.hasFDerivAt_gaussianThresholdCDF_nonparallel,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianThresholdCDF_translate_nonparallel,
    ``RectangleCLTArxivV1.hasDerivAt_gaussian_weight_translate,
    ``RectangleCLTArxivV1.gaussian_hard_polyhedron_firstMoment,
    ``RectangleCLTArxivV1.hardGaussianFacetMass_eq_first,
    ``RectangleCLTArxivV1.gaussian_hard_polyhedron_firstMoment_surface,
    ``RectangleCLTArxivV1.gaussian_hard_polyhedron_firstMoment_kernel,
    ``RectangleCLTArxivV1.hardGaussianFacetIntegral_eq_signedSection,
    ``RectangleCLTArxivV1.hardGaussianFacet_Green_independent]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
