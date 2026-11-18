import RectangleCLTArxivV1.SupplementalHNonsimpleFaceMass
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceFrame
import RectangleCLTArxivV1.SupplementalHNonsimpleActualMass
import RectangleCLTArxivV1.SupplementalHNonsimpleGreenSum
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_inner_of_mem_span,
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_supporting_level,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_union_supporting,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_univ_eq_sdiff_supporting,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass_nonneg,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass_frame_independent,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass_point_independent,
    ``RectangleCLTArxivV1.nonsimpleFaceBasis,
    ``RectangleCLTArxivV1.nonsimpleFaceFrame,
    ``RectangleCLTArxivV1.nonsimpleFaceFrame_orthonormal,
    ``RectangleCLTArxivV1.nonsimpleFaceFrame_span,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_mem,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_levels,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_eq_frameProjection,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_unique,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_eq_of_closedFace,
    ``RectangleCLTArxivV1.nonsimpleNativeNormals,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_nonneg,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_eq_actualFaceMass,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_sdiff_eq_actualFaceMass,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_at_closedFacePoint,
    ``RectangleCLTArxivV1.nonsimpleOrderedFacetPairs,
    ``RectangleCLTArxivV1.nonsimpleOrderedFacetPairs_pair,
    ``RectangleCLTArxivV1.nonsimpleOrderedFacetPairs_card,
    ``RectangleCLTArxivV1.half_ordered_pair_sum_eq_actual_ridge_sum,
    ``RectangleCLTArxivV1.nonsimple_signed_incidence_grouping]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
