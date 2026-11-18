import RectangleCLTArxivV1.SupplementalHAffineResidualRegularity
import RectangleCLTArxivV1.SupplementalHGenericPairGreen
import RectangleCLTArxivV1.SupplementalHEdgeFourthBounds
import RectangleCLTArxivV1.SupplementalHNormalPointUnique
import RectangleCLTArxivV1.SupplementalHRidgeGreen
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.ae_affineResidualThresholdRegularity,
    ``RectangleCLTArxivV1.hardPairResidualLevels_eq_affineResidualThresholds,
    ``RectangleCLTArxivV1.ae_pairResidualThresholdRegularity,
    ``RectangleCLTArxivV1.supplementalH_angle_le_pi_half_chord,
    ``RectangleCLTArxivV1.adaptive_angle_ridge_fourth_bound,
    ``RectangleCLTArxivV1.normalPoint_eq_of_spanning_levels,
    ``RectangleCLTArxivV1.hardGaussianSignedRidgeTerm_Green_of_slack,
    ``RectangleCLTArxivV1.ae_hardGaussianWeightedRidgeIntegral_Green]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
