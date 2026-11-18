import RectangleCLTArxivV1.SupplementalHRidgeTripleTransport
import RectangleCLTArxivV1.SupplementalHRidgeAveraged
import RectangleCLTArxivV1.SupplementalHRidgeMain
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.tripleIncidenceTransportSection_eq_native,
    ``RectangleCLTArxivV1.tripleIncidenceTransportSection_ae_no_boundary,
    ``RectangleCLTArxivV1.tripleIncidenceCommonMass_eq_strict_transport,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_threeFace_bound,
    ``RectangleCLTArxivV1.abs_hardGaussianRidgeThirdBoundaryIntegral_threeFace_tube_bound,
    ``RectangleCLTArxivV1.abs_hardGaussianRidgeThirdBoundaryIntegral_affine_tube_bound,
    ``RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_Green_of_slack,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdBoundaryIntegral_base_tube_bound,
    ``RectangleCLTArxivV1.ae_hardGaussianRidgeThirdBoundaryIntegral_concentrated_base,
    ``RectangleCLTArxivV1.ae_hardGaussianWeightedRidgeIntegral_concentrated_base]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
