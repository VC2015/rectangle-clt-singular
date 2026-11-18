import RectangleCLTArxivV1.SupplementalHTripleTransportModel
import RectangleCLTArxivV1.SupplementalHTripleTransportModelCone
import RectangleCLTArxivV1.SupplementalHTripleTransportModelEvent
import RectangleCLTArxivV1.SupplementalHTripleTransportModelFamily
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
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
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then
      continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := ci.type.getUsedConstants ++
      (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])
    let deps := deps.toList.eraseDups.toArray
    let projectDeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining"
    graph := graph.push <| Json.mkObj [
      ("name", toJson target.toString),
      ("direct_project_dependencies", toJson (projectDeps.map Name.toString))]
    queue := projectDeps.toList ++ queue
    if targets.contains target then
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "Concrete actual independent-three-normal coordinate model, pulled ray basis, true generated outward cone, actual supporting levels, automatic three-face-radius transport and factor6 over the genuine LI3 family"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
