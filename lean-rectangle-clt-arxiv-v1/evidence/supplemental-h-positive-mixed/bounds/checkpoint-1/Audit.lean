import RectangleCLTArxivV1.PositiveMixedCoareaBounds
import Lean.Util.CollectAxioms
import Lean.Elab.Command

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
