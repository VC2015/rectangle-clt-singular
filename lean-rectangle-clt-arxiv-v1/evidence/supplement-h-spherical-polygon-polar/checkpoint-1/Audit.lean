import RectangleCLTArxivV1.SupplementalHSphericalPolygonPolar
import RectangleCLTArxivV1.SupplementalHSphericalPolygonDual
import RectangleCLTArxivV1.SupplementalHSphericalPolygonConormal
import RectangleCLTArxivV1.SupplementalHSphericalPolygonIncidence
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.sphericalPolygon_exists_orthogonal_pair,
    ``RectangleCLTArxivV1.sphericalPolygon_polar_linear_nonneg_of_one_zero,
    ``RectangleCLTArxivV1.sphericalPolygon_polar_linear_nonneg_of_two_zero,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_eq_nonsimple,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_mem_iff_nonneg_polar,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_mem_iff_supporting_pairs,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_mem_iff_incident_halfspaces,
    ``RectangleCLTArxivV1.sphericalPolygon_vector_eq_coordinate_normal,
    ``RectangleCLTArxivV1.sphericalPolygon_unit_conormal_positive,
    ``RectangleCLTArxivV1.sphericalPolygon_conormal_nonneg_smul,
    ``RectangleCLTArxivV1.sphericalPolygon_unit_conormal_unique,
    ``RectangleCLTArxivV1.sphericalPolygon_conormal_nonneg_smul_of_three,
    ``RectangleCLTArxivV1.sphericalPolygon_incident_ridge_balance,
    ``RectangleCLTArxivV1.sphericalPolygon_incident_ridge_balance_norm_le]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
