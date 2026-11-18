import RectangleCLTArxivV1.SupplementalHSurfaceGeometry
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.supplementalHRidgeConormal_norm,
    ``RectangleCLTArxivV1.supplementalHRidgeConormal_pair,
    ``RectangleCLTArxivV1.supplementalH_weighted_ridge_pair_le,
    ``RectangleCLTArxivV1.supplementalH_chord_le_angle,
    ``RectangleCLTArxivV1.supplementalH_weighted_ridge_pair_angle_le,
    ``RectangleCLTArxivV1.supplementalH_weighted_ridge_pair_radius_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
