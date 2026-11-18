import RectangleCLTArxivV1.SupplementalHMixedCoareaIntegral
import RectangleCLTArxivV1.SupplementalHMixedCoareaRegularity
import RectangleCLTArxivV1.SupplementalHMixedCoareaDerivative
import RectangleCLTArxivV1.SupplementalHMixedCoareaLipschitz
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFiniteWeightedThreshold,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection,
    ``RectangleCLTArxivV1.measurable_gaussianFiniteWeightedSection,
    ``RectangleCLTArxivV1.integrable_gaussianFiniteWeightedSection,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_update_eq_section_integral,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteWeightedThreshold_update,
    ``RectangleCLTArxivV1.gaussianFacetScore,
    ``RectangleCLTArxivV1.measurable_gaussianFacetScore,
    ``RectangleCLTArxivV1.integrable_gaussianFacetScore,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_score_eq,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteWeightedSection_score_of_slack,
    ``RectangleCLTArxivV1.MixedGaussianSectionSlack,
    ``RectangleCLTArxivV1.hasDerivAt_thresholdSignedSection_update_conditional_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianSignedFacetDensity_update_of_slack,
    ``RectangleCLTArxivV1.ResidualThresholdRegularity.mixedGaussianSectionSlack,
    ``RectangleCLTArxivV1.ae_hasDerivAt_gaussianSignedFacetDensity_update,
    ``RectangleCLTArxivV1.abs_hardGaussianPairSignedSection_le,
    ``RectangleCLTArxivV1.gaussianMixedSectionDensityBudget,
    ``RectangleCLTArxivV1.gaussianMixedSectionDensityBudget_nonneg,
    ``RectangleCLTArxivV1.gaussianPDFReal_pair_sq_add_dimension_le,
    ``RectangleCLTArxivV1.thresholdSignedSection_update_eq_weightedThreshold,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_facetScore_eq_pairSignedSection,
    ``RectangleCLTArxivV1.gaussianSignedFacetDensity_update_eq_section_integral,
    ``RectangleCLTArxivV1.gaussianSignedFacetDensity_update_increment_bound,
    ``RectangleCLTArxivV1.lipschitzWith_gaussianSignedFacetDensity_update]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
