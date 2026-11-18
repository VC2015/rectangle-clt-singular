import RectangleCLTArxivV1.SupplementalHResidualPairMass
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.hardFacetResidualDensity_eq_ridgeDensity
set_option pp.all true in
#check @RectangleCLTArxivV1.hardFacetResidualDensity_symm
set_option pp.all true in
#check @RectangleCLTArxivV1.hardFacetResidualDensity_nonneg
set_option pp.all true in
#check @RectangleCLTArxivV1.hardFacetResidualDensity_zero_of_parallel_slack

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.hardGaussianRidgeDensity_nonneg,
    ``RectangleCLTArxivV1.gaussianResidualSectionProbability_eq_pairBase_le,
    ``RectangleCLTArxivV1.hardFacetResidualDensity_eq_ridgeDensity,
    ``RectangleCLTArxivV1.thresholdPairBisector_swap,
    ``RectangleCLTArxivV1.thresholdPairDifference_swap,
    ``RectangleCLTArxivV1.thresholdPairFirstLevel_swap,
    ``RectangleCLTArxivV1.thresholdPairSecondLevel_swap,
    ``RectangleCLTArxivV1.gaussianSectionPoint_neg_normal,
    ``RectangleCLTArxivV1.gaussianPairBase_swap,
    ``RectangleCLTArxivV1.hardGaussianRidgeDensity_symm,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdFirst_nonneg_of_slack,
    ``RectangleCLTArxivV1.hardFacetResidualDensity_nonneg,
    ``RectangleCLTArxivV1.hardFacetResidualDensity_zero_of_parallel_slack,
    ``RectangleCLTArxivV1.hardFacetResidualDensity_symm_nonparallel,
    ``RectangleCLTArxivV1.gaussianNormalProjection_pair_zero_of_parallel_unit,
    ``RectangleCLTArxivV1.hardFacetResidualDensity_symm]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
