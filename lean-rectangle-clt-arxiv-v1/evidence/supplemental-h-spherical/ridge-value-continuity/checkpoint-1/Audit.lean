import RectangleCLTArxivV1.SupplementalHRidgeValueContinuity
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairSignedSection_eq_fixed_residual
set_option pp.all true in
#check @RectangleCLTArxivV1.continuousAt_hardGaussianPairSignedSection_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.residualThresholdRegularity_conditional_pair_value_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.continuousAt_hardGaussianConditionalPairSignedSection_of_residual_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.continuousAt_hardGaussianSignedRidgeTerm_of_residual_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.continuousAt_hardGaussianWeightedRidgeIntegral_of_residual_slack

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.hardGaussianPairSignedSection_eq_fixed_residual,
    ``RectangleCLTArxivV1.continuousAt_hardGaussianPairSignedSection_of_slack,
    ``RectangleCLTArxivV1.residualThresholdRegularity_conditional_pair_value_slack,
    ``RectangleCLTArxivV1.continuousAt_hardGaussianConditionalPairSignedSection_of_residual_slack,
    ``RectangleCLTArxivV1.continuousAt_hardGaussianSignedRidgeTerm_of_residual_slack,
    ``RectangleCLTArxivV1.continuousAt_hardGaussianWeightedRidgeIntegral_of_residual_slack]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
