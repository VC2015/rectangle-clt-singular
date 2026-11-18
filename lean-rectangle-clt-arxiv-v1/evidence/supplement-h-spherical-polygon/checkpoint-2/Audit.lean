import RectangleCLTArxivV1.SupplementalHSphericalPolygonSupport
import RectangleCLTArxivV1.SupplementalHSphericalPolygonChart
import RectangleCLTArxivV1.SupplementalHSphericalPolygonBalance
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_generator_mem,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_add_mem,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_smul_mem,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_linear_nonneg,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_zero_face_coefficients,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_zero_face_eq_wedge,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_map,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_norm,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_inner,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart_on_plane,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart_eq_positivePlanarWedge,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_nonparallel,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart_angular_area,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_dot,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_unit,
    ``RectangleCLTArxivV1.sphericalPolygon_nonparallel_of_strict_facets,
    ``RectangleCLTArxivV1.sphericalPolygon_distinct_endpoint_pair,
    ``RectangleCLTArxivV1.sphericalPolygon_strict_facets_of_incidence,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_nonparallel,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_facet_angular_area,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_eq_halfspaces,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_facet_angle,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_inward,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_balance,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_balance_norm_le]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
