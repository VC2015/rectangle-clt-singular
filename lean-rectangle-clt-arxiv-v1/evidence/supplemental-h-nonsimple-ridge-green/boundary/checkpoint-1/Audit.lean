import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenBoundary
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.actualFacetOutwardConormal,
    ``RectangleCLTArxivV1.actualFacetSignedSupportDistance,
    ``RectangleCLTArxivV1.actualFacetGaussianBoundaryMass,
    ``RectangleCLTArxivV1.actualFacet_normal_ne_zero,
    ``RectangleCLTArxivV1.actualFacet_scale_pos,
    ``RectangleCLTArxivV1.actualFacetOutwardConormal_unit,
    ``RectangleCLTArxivV1.actualFacetGaussianBoundaryMass_nonneg,
    ``RectangleCLTArxivV1.actualFacet_finiteThresholdFirst_eq_boundaryMass_div,
    ``RectangleCLTArxivV1.actualFacet_threshold_mul_first_eq_signedDistance_mul_boundaryMass,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_eq_actualBoundary]
  let env ← getEnv
  let (_, state) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  for n in state.axioms do
    unless allowed.contains n do
      throwError "Forbidden axiom {n}"
  logInfo m!"PASS: {targets.size} boundary declarations; axioms {state.axioms}"

set_option pp.all true in
#print RectangleCLTArxivV1.actualFacetOutwardConormal
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacetSignedSupportDistance
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacetGaussianBoundaryMass
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacet_normal_ne_zero
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacet_scale_pos
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacetOutwardConormal_unit
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacetGaussianBoundaryMass_nonneg
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacet_finiteThresholdFirst_eq_boundaryMass_div
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacet_threshold_mul_first_eq_signedDistance_mul_boundaryMass
set_option pp.all true in
#print RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_eq_actualBoundary
