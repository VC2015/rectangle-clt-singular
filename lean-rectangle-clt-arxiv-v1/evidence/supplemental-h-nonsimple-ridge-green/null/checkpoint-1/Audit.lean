import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNull
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.gaussianFiniteThresholdEvent_has_nonzero_active_of_no_strictInterior,
    ``RectangleCLTArxivV1.ae_not_mem_gaussianFiniteThresholdEvent_of_no_strictInterior,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdEvent_measure_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdCDF_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.integral_gaussianFiniteThreshold_indicator_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdRadialTrace_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.hardGaussianPairSectionProbability_zero_of_no_strictResidualInterior,
    ``RectangleCLTArxivV1.hardGaussianPairSignedSection_zero_of_no_strictResidualInterior]
  let env ← getEnv
  let (_, state) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  for n in state.axioms do
    unless allowed.contains n do
      throwError "Forbidden axiom {n}"
  logInfo m!"PASS: {targets.size} actual-null-section declarations; axioms {state.axioms}"

set_option pp.all true in
#print RectangleCLTArxivV1.gaussianFiniteThresholdEvent_has_nonzero_active_of_no_strictInterior
set_option pp.all true in
#print RectangleCLTArxivV1.ae_not_mem_gaussianFiniteThresholdEvent_of_no_strictInterior
set_option pp.all true in
#print RectangleCLTArxivV1.gaussianFiniteThresholdEvent_measure_zero_of_no_strictInterior
set_option pp.all true in
#print RectangleCLTArxivV1.gaussianFiniteThresholdCDF_zero_of_no_strictInterior
set_option pp.all true in
#print RectangleCLTArxivV1.integral_gaussianFiniteThreshold_indicator_zero_of_no_strictInterior
set_option pp.all true in
#print RectangleCLTArxivV1.gaussianFiniteThresholdRadialTrace_zero_of_no_strictInterior
set_option pp.all true in
#print RectangleCLTArxivV1.hardGaussianPairSectionProbability_zero_of_no_strictResidualInterior
set_option pp.all true in
#print RectangleCLTArxivV1.hardGaussianPairSignedSection_zero_of_no_strictResidualInterior
