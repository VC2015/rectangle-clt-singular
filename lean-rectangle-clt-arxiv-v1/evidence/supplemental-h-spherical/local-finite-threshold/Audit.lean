import RectangleCLTArxivV1.SupplementalHLocalFiniteThreshold
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.hasFDerivAt_gaussianFiniteThresholdCDF_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_retained_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFiniteThreshold_firstMoment_retained_of_slack

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteThresholdCDF_update_unit_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteThresholdCDF_update_of_slack,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdCDF_update_zero_normal,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteThresholdCDF_zero_of_slack,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdFirst_zero_of_slack,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteThresholdFirst_zero_of_slack,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdFirst_eq_section_of_slack,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteThresholdFirst_of_slack_nonunit,
    ``RectangleCLTArxivV1.localFiniteThresholdRegularity_isOpen,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteThresholdCDF_local_first,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteThresholdFirst_of_slack,
    ``RectangleCLTArxivV1.hasFDerivAt_gaussianFiniteThresholdCDF_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteThresholdCDF_logScale,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_of_slack,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_sum_mul_first_eq_retained,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_retained_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteThresholdCDF_translate_of_slack,
    ``RectangleCLTArxivV1.integral_hard_finite_threshold_translate,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_firstMoment_of_slack,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_firstMoment_retained_of_slack]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
