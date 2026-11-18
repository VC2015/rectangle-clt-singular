import RectangleCLTArxivV1.SupplementalHCubicSigns
import RectangleCLTArxivV1.SupplementalHWeightedReference
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_selectorFaceNormal_neg,
    ``RectangleCLTArxivV1.supplementalH_negative_scale_factor,
    ``RectangleCLTArxivV1.supplementalH_negative_cubic_mean_reference_bound_all,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussianWeightedOneFaceMass,
    ``RectangleCLTArxivV1.supplementalH_integrable_positiveDirection,
    ``RectangleCLTArxivV1.supplementalH_integral_positiveDirection_le_one,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_positiveOneFaceMass]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target}: {axioms.toList}"
