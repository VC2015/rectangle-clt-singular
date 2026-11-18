import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeEnumeration
import RectangleCLTArxivV1.SupplementalHNonsimplePrintedQuantities
import RectangleCLTArxivV1.SupplementalHNonsimplePrintedGreen
import RectangleCLTArxivV1.SupplementalHNonsimpleSquareGreen
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.strictRidgeInterior_iff_actual_ridge_face,``RectangleCLTArxivV1.half_native_pair_sum_eq_actual_ridge_sum,``RectangleCLTArxivV1.nonsimpleActualRidgeAngle,``RectangleCLTArxivV1.nonsimpleActualRidgeAngle_eq_pair,``RectangleCLTArxivV1.nonsimpleActualRidgeAngle_nonneg,``RectangleCLTArxivV1.nonsimpleActualRidgeLeading,``RectangleCLTArxivV1.nonsimpleActualIncidenceConormal,``RectangleCLTArxivV1.nonsimpleActualIncidenceConormal_of_incident,``RectangleCLTArxivV1.nonsimpleActualIncidenceConormal_of_not_incident,``RectangleCLTArxivV1.nonsimpleActualConormalSum,``RectangleCLTArxivV1.nonsimpleActualThirdBoundary,``RectangleCLTArxivV1.nonsimpleActualThirdBoundary_eq_ridge_incidence_sum,``RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_Green_actualFaces,``RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_Green_actualFaces_compact,``RectangleCLTArxivV1.exists_actual_facet_ridge_Green,``RectangleCLTArxivV1.nonsimpleSquare_printed_ridge_Green,``RectangleCLTArxivV1.nonsimpleSquare_actualVertex_printed_spherical_balance,``RectangleCLTArxivV1.nonsimpleSquare_actualVertex_printed_spherical_norm_bound]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows),
    ("all_axioms_allowed", toJson true)]).compress
