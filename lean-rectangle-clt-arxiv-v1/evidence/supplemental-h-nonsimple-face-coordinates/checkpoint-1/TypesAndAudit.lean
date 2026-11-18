import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoordinateTransport
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option pp.all true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let requested : Array String := #["RectangleCLTArxivV1.nonsimpleFaceActiveIndex","RectangleCLTArxivV1.nonsimpleFaceActiveIndex_mem","RectangleCLTArxivV1.nonsimpleFaceActiveIndex_injective","RectangleCLTArxivV1.nonsimpleFaceLocalIndex","RectangleCLTArxivV1.nonsimpleFaceActiveIndex_localIndex","RectangleCLTArxivV1.nonsimpleFaceCoordinateMap","RectangleCLTArxivV1.nonsimpleFaceCoordinateMap_of_mem","RectangleCLTArxivV1.nonsimpleFaceCoordinateMap_norm","RectangleCLTArxivV1.nonsimpleFaceCoordinateMap_inner_left","RectangleCLTArxivV1.nonsimpleFaceCoordinateNormals","RectangleCLTArxivV1.nonsimpleFaceCoordinateNormals_inner","RectangleCLTArxivV1.nonsimpleFaceCoordinateNormals_span","RectangleCLTArxivV1.nonsimpleFaceCoordinateNormals_unit","RectangleCLTArxivV1.nonsimpleFaceCoordinateNormals_exists_strictPolar","RectangleCLTArxivV1.nonsimpleFaceRidgeIndex","RectangleCLTArxivV1.nonsimpleRidgeCoordinateConormal","RectangleCLTArxivV1.nonsimpleRidgeCoordinateConormal_unit","RectangleCLTArxivV1.nonsimpleRidgeCoordinateConormal_inner","RectangleCLTArxivV1.nonsimpleRidgeCoordinateConormal_nonneg","RectangleCLTArxivV1.nonsimpleActualRidgePair","RectangleCLTArxivV1.nonsimpleRidgeCoordinateLeft","RectangleCLTArxivV1.nonsimpleRidgeCoordinateRight","RectangleCLTArxivV1.nonsimpleRidgeCoordinateLeft_original","RectangleCLTArxivV1.nonsimpleRidgeCoordinateRight_original","RectangleCLTArxivV1.nonsimpleRidgeCoordinate_pair_distinct","RectangleCLTArxivV1.nonsimpleRidgeCoordinate_pair_image","RectangleCLTArxivV1.nonsimpleRidgeCoordinate_pairs_injective","RectangleCLTArxivV1.nonsimpleOriginal_strictInterior_euclidean","RectangleCLTArxivV1.nonsimpleOriginal_coordinateNormals_unit","RectangleCLTArxivV1.nonsimpleOriginal_coordinateNormals_injective","RectangleCLTArxivV1.nonsimpleOriginal_coordinateConormal_zero","RectangleCLTArxivV1.nonsimpleOriginal_coordinateConormal_strict","RectangleCLTArxivV1.nonsimpleOriginal_coordinateNormals_pair_plus_ne","RectangleCLTArxivV1.nonsimpleOriginal_coordinateNormals_pair_minus_ne","RectangleCLTArxivV1.nonsimpleOriginal_coordinate_nonzero_coverage","RectangleCLTArxivV1.nonsimpleFaceCoordinateCone","RectangleCLTArxivV1.nonsimpleRidgeOriginalAngle","RectangleCLTArxivV1.nonsimpleRidgeCoordinate_angle_original","RectangleCLTArxivV1.nonsimpleFaceCoordinateCone_mem_iff_incident_halfspaces","RectangleCLTArxivV1.nonsimpleFaceCoordinateCone_eq_incident_halfspaces","RectangleCLTArxivV1.nonsimpleFaceCoordinate_incident_nonparallel","RectangleCLTArxivV1.nonsimpleFaceCoordinateCone_facet_angle","RectangleCLTArxivV1.nonsimpleFaceCoordinate_spherical_balance","RectangleCLTArxivV1.nonsimpleFaceCoordinate_spherical_balance_norm_le","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_apply","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_map_of_mem","RectangleCLTArxivV1.nonsimpleFaceCoordinateMap_lift","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_range","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_eq_frameIsometry","RectangleCLTArxivV1.nonsimpleFaceCoordinatePoint","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_point","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_generator","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_conormal","RectangleCLTArxivV1.nonsimpleFaceCoordinateLift_mem_generated_iff","RectangleCLTArxivV1.nonsimpleFaceCoordinateCone_eq_actual_normalCone","RectangleCLTArxivV1.nonsimpleActualNormalCone_eq_incident_halfspaces","RectangleCLTArxivV1.nonsimpleActualNormalCone_isClosed","RectangleCLTArxivV1.nonsimpleActualNormalCone_measurable","RectangleCLTArxivV1.nonsimpleFaceNative_spherical_balance","RectangleCLTArxivV1.nonsimpleFaceNative_spherical_balance_norm_le"]
  let env ← getEnv
  let allNames := env.constants.toList.foldl (fun a (n,_) => a.insert n.toString n) ({} : Std.HashMap String Name)
  let targets ← requested.mapM fun s => do
    match allNames[s]? with
    | some n => pure n
    | none => throwError "Missing exact declaration: {s}"
  let (_, axs) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  let bad := axs.axioms.filter fun n => !(#[``propext,``Classical.choice,``Quot.sound]).contains n
  unless bad.isEmpty do throwError "Unexpected axiom: {bad}"
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let n := queue.head!
    queue := queue.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let ci ← getConstInfo n
    let deps := (ci.type.getUsedConstants ++ (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])).toList.eraseDups.toArray
    let projectDeps := deps.filter fun d =>
      let s := d.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" || s.startsWith "Kane" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining" || s.startsWith "_private.Kane"
    graph := graph.push <| Json.mkObj [("name",toJson n.toString),("direct_project_dependencies",toJson (projectDeps.map Name.toString))]
    queue := projectDeps.toList ++ queue
    if targets.contains n then
      let fmt ← liftTermElabM (Meta.ppExpr ci.type)
      endpoints := endpoints.push <| Json.mkObj [("name",toJson n.toString),("expanded_type",toJson fmt.pretty),("direct_dependencies",toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [("axiom_union",toJson (axs.axioms.map Name.toString)),("endpoints",Json.arr endpoints),("project_dependency_graph",Json.arr graph)]).compress
