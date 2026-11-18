import RectangleCLTArxivV1.SupplementalHMixedCoareaParallel
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteThresholdEvent_update_zero_of_same_sign
set_option pp.all true in
#check @RectangleCLTArxivV1.eventuallyEq_gaussianFiniteWeightedThreshold_update_zero_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.hasDerivAt_gaussianFiniteWeightedThreshold_update_zero_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.eventuallyEq_thresholdSignedSection_update_parallel_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.hasDerivAt_thresholdSignedSection_update_parallel_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.hasDerivAt_gaussianSignedFacetDensity_update_parallel_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.ResidualThresholdRegularity.parallel_shifted_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.ae_hasDerivAt_gaussianSignedFacetDensity_update_parallel

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFiniteThresholdEvent_update_zero_of_same_sign,
    ``RectangleCLTArxivV1.eventuallyEq_gaussianFiniteWeightedThreshold_update_zero_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteWeightedThreshold_update_zero_of_slack,
    ``RectangleCLTArxivV1.eventuallyEq_thresholdSignedSection_update_parallel_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_thresholdSignedSection_update_parallel_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianSignedFacetDensity_update_parallel_of_slack,
    ``RectangleCLTArxivV1.ResidualThresholdRegularity.parallel_shifted_slack,
    ``RectangleCLTArxivV1.ae_hasDerivAt_gaussianSignedFacetDensity_update_parallel]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
