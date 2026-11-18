import RectangleCLTArxivV1.PositiveMixedCoareaDerivative
import RectangleCLTArxivV1.PositiveMixedCoareaBounds
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedPlaneFacetWeight
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstMassDensity
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstPlaneDensity
set_option pp.all true in
#check @RectangleCLTArxivV1.measurable_positiveMixedPlaneFacetWeight
set_option pp.all true in
#check @RectangleCLTArxivV1.integrable_positiveMixedPlaneFacetWeight
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPairConditionalDirection_eq_referenceComplement
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixed_pair_gram_pos
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedPlaneFacetWeight_eq_actual_projection
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_one_eq_cdf
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteWeightedSection_one_eq_sectionProbability
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteWeightedSection_plane_eq_probability
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteWeightedSection_one_eq_pairProbability
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianConditionalPairProbability_eq_native
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPair_conditional_normalLength_eq_native
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstMassDensity_update_eq_weightedThreshold
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_update_eq_weightedThreshold
set_option pp.all true in
#check @RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstMassDensity_conditional
set_option pp.all true in
#check @RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstPlaneDensity_conditional
set_option pp.all true in
#check @RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstMassDensity_native
set_option pp.all true in
#check @RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstPlaneDensity_native
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedPairPlane_projection_normSq
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedGaussianPeak
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedMassBudget
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedPlaneBudget
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedGaussianPeak_nonneg
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedMassBudget_nonneg
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedPlaneBudget_nonneg
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPDFReal_le_positiveMixedGaussianPeak
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPDFReal_sq_le_positiveMixedGaussianPeak
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPDFReal_pair_le_positiveMixedMassBudget
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPDFReal_pair_normSq_le_positiveMixedPlaneBudget
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_one_bounds
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_plane_bounds
set_option pp.all true in
#check @RectangleCLTArxivV1.measurable_gaussianFiniteWeightedThreshold_parameter
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixed_iic_increment_bound
set_option pp.all true in
#check @RectangleCLTArxivV1.measurable_positiveMixedFirstMassDensity
set_option pp.all true in
#check @RectangleCLTArxivV1.measurable_positiveMixedFirstPlaneDensity
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstMassDensity_bounds
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstMassDensity_norm_le
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_bounds
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_norm_le
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairSectionProbability_bounds
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstMassDensity_update_eq_section_integral
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_update_eq_section_integral
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstMassDensity_update_increment_bound
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_update_increment_bound
set_option pp.all true in
#check @RectangleCLTArxivV1.lipschitzWith_positiveMixedFirstMassDensity_update
set_option pp.all true in
#check @RectangleCLTArxivV1.lipschitzWith_positiveMixedFirstPlaneDensity_update

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.positiveMixedPlaneFacetWeight,
    ``RectangleCLTArxivV1.positiveMixedFirstMassDensity,
    ``RectangleCLTArxivV1.positiveMixedFirstPlaneDensity,
    ``RectangleCLTArxivV1.measurable_positiveMixedPlaneFacetWeight,
    ``RectangleCLTArxivV1.integrable_positiveMixedPlaneFacetWeight,
    ``RectangleCLTArxivV1.gaussianPairConditionalDirection_eq_referenceComplement,
    ``RectangleCLTArxivV1.positiveMixed_pair_gram_pos,
    ``RectangleCLTArxivV1.positiveMixedPlaneFacetWeight_eq_actual_projection,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_one_eq_cdf,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_one_eq_sectionProbability,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_plane_eq_probability,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_one_eq_pairProbability,
    ``RectangleCLTArxivV1.hardGaussianConditionalPairProbability_eq_native,
    ``RectangleCLTArxivV1.gaussianPair_conditional_normalLength_eq_native,
    ``RectangleCLTArxivV1.positiveMixedFirstMassDensity_update_eq_weightedThreshold,
    ``RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_update_eq_weightedThreshold,
    ``RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstMassDensity_conditional,
    ``RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstPlaneDensity_conditional,
    ``RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstMassDensity_native,
    ``RectangleCLTArxivV1.hasDerivAt_positiveMixedFirstPlaneDensity_native,
    ``RectangleCLTArxivV1.positiveMixedPairPlane_projection_normSq,
    ``RectangleCLTArxivV1.positiveMixedGaussianPeak,
    ``RectangleCLTArxivV1.positiveMixedMassBudget,
    ``RectangleCLTArxivV1.positiveMixedPlaneBudget,
    ``RectangleCLTArxivV1.positiveMixedGaussianPeak_nonneg,
    ``RectangleCLTArxivV1.positiveMixedMassBudget_nonneg,
    ``RectangleCLTArxivV1.positiveMixedPlaneBudget_nonneg,
    ``RectangleCLTArxivV1.gaussianPDFReal_le_positiveMixedGaussianPeak,
    ``RectangleCLTArxivV1.gaussianPDFReal_sq_le_positiveMixedGaussianPeak,
    ``RectangleCLTArxivV1.gaussianPDFReal_pair_le_positiveMixedMassBudget,
    ``RectangleCLTArxivV1.gaussianPDFReal_pair_normSq_le_positiveMixedPlaneBudget,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_one_bounds,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_plane_bounds,
    ``RectangleCLTArxivV1.measurable_gaussianFiniteWeightedThreshold_parameter,
    ``RectangleCLTArxivV1.positiveMixed_iic_increment_bound,
    ``RectangleCLTArxivV1.measurable_positiveMixedFirstMassDensity,
    ``RectangleCLTArxivV1.measurable_positiveMixedFirstPlaneDensity,
    ``RectangleCLTArxivV1.positiveMixedFirstMassDensity_bounds,
    ``RectangleCLTArxivV1.positiveMixedFirstMassDensity_norm_le,
    ``RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_bounds,
    ``RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_norm_le,
    ``RectangleCLTArxivV1.hardGaussianPairSectionProbability_bounds,
    ``RectangleCLTArxivV1.positiveMixedFirstMassDensity_update_eq_section_integral,
    ``RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_update_eq_section_integral,
    ``RectangleCLTArxivV1.positiveMixedFirstMassDensity_update_increment_bound,
    ``RectangleCLTArxivV1.positiveMixedFirstPlaneDensity_update_increment_bound,
    ``RectangleCLTArxivV1.lipschitzWith_positiveMixedFirstMassDensity_update,
    ``RectangleCLTArxivV1.lipschitzWith_positiveMixedFirstPlaneDensity_update]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
