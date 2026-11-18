import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSpanning
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSelected
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSelectedExistence
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSelectedBijection
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.exists_complete_active_face_rank_three,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.exists_complete_active_face_rank_three_with_selected_strictness,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.incident_face_has_selected_active,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFace,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFaceEquiv,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFace_closedFace,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFace_eq_of_supporting_index,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFace_injective,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFace_mem_iff,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFace_supporting_indices,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedActualFace_triple_span,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedFaceAtPair,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedFaceAtPair_bijective,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedFacePoint,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selectedFacePoint_spec,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.sum_selectedActualFace,
    ``RectangleCLTArxivV1.NonsimpleFacesAtPair,
    ``RectangleCLTArxivV1.nonsimpleClosedFace_eq_spanning_levels,
    ``RectangleCLTArxivV1.nonsimpleFacesAtPairFintype,
    ``RectangleCLTArxivV1.nonsimple_retained_active_has_selected_active]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
