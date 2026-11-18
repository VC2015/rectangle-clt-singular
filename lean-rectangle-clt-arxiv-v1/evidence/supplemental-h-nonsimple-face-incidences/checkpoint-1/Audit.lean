import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCofaces
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceConormal
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoverage
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceTubes
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimple_exactStratum_move_to_active_subset, ``RectangleCLTArxivV1.nonsimple_supporting_pair_has_actual_stratum, ``RectangleCLTArxivV1.nonsimple_pair_normalSpace_rank, ``RectangleCLTArxivV1.nonsimple_supporting_pair_has_actual_ridge, ``RectangleCLTArxivV1.NonsimpleRidgeAt, ``RectangleCLTArxivV1.nonsimpleRidgeAtFintype, ``RectangleCLTArxivV1.nonsimpleIncidentDirection, ``RectangleCLTArxivV1.nonsimpleIncidentProjection, ``RectangleCLTArxivV1.nonsimpleIncidentConormal, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_mem, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_inner, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_zero_on_ridge, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_strict_on_other, ``RectangleCLTArxivV1.nonsimpleRidgeAt_exists_other_active, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_ne_zero, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_unit, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_mem, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_zero_on_ridge, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_strict_on_other, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_nonneg, ``RectangleCLTArxivV1.nonsimple_nonzero_polar_covered_by_actual_incidence, ``RectangleCLTArxivV1.NonsimpleCodimThreeFace, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent_disjoint, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent_indicator_sum_le, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent_integral_sum_le]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
