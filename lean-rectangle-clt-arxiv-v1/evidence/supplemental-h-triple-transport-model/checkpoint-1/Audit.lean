import RectangleCLTArxivV1.SupplementalHTripleTransportModel
import RectangleCLTArxivV1.SupplementalHTripleTransportModelCone
import RectangleCLTArxivV1.SupplementalHTripleTransportModelEvent
import RectangleCLTArxivV1.SupplementalHTripleTransportModelFamily
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.tripleIncidenceTransportIsometry,
    ``RectangleCLTArxivV1.tripleIncidenceTransportPoint,
    ``RectangleCLTArxivV1.tripleIncidenceTransportRay,
    ``RectangleCLTArxivV1.tripleIncidenceTransportIsometry_ray,
    ``RectangleCLTArxivV1.tripleIncidenceTransportRay_linearIndependent,
    ``RectangleCLTArxivV1.tripleIncidenceTransportBasis,
    ``RectangleCLTArxivV1.tripleIncidenceTransportBasis_apply,
    ``RectangleCLTArxivV1.tripleIncidenceTransportIsometry_basis,
    ``RectangleCLTArxivV1.tripleIncidenceTransportBasis_norm,
    ``RectangleCLTArxivV1.tripleIncidenceTransportIsometry_point,
    ``RectangleCLTArxivV1.tripleIncidenceTransportFrame_eq,
    ``RectangleCLTArxivV1.tripleIncidenceTransportFrame_span,
    ``RectangleCLTArxivV1.tripleIncidenceTransport_supporting_levels,
    ``RectangleCLTArxivV1.tripleIncidenceTransportTuple,
    ``RectangleCLTArxivV1.tripleIncidenceTransport_active_span,
    ``RectangleCLTArxivV1.tripleIncidenceTransport_active_levels,
    ``RectangleCLTArxivV1.tripleIncidenceTransport_cone_eq,
    ``RectangleCLTArxivV1.tripleIncidenceTransport_cone_measurableSet,
    ``RectangleCLTArxivV1.tripleIncidenceTransport_cone_smul_iff,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent_eq_outward,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent_measurableSet,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent_exactStratum,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent_mem_adaptiveOutwardTube,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent_mem_outerLayer,
    ``RectangleCLTArxivV1.tripleIncidence_spherical_coefficient_le_threeFace_event,
    ``RectangleCLTArxivV1.independentNormalTripleTransportTuple,
    ``RectangleCLTArxivV1.independentNormalTripleTransportTuple_injective,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent_integral_sum_le,
    ``RectangleCLTArxivV1.tripleIncidenceTransportEvent_threeFace_integral_sum_le]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
