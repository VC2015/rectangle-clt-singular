import RectangleCLTArxivV1.SupplementalHNonsimpleFacePrintedSpherical
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option pp.all true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let requested : Array String := #["RectangleCLTArxivV1.nonsimpleRidgeOriginalAngle_eq_actual","RectangleCLTArxivV1.nonsimpleActualConormalSum_eq_coordinate_sum","RectangleCLTArxivV1.nonsimpleActualConormalSum_eq_spherical_vector","RectangleCLTArxivV1.nonsimpleActualConormalSum_norm_le_spherical_area"]
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
