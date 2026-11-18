import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenCanonical
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option pp.all true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryFrame_span_actualFace,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint_eq_actualFaceNormalPoint,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.normalDensity_mul_boundaryMass_eq_actualFaceMass,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.outwardConormal_eq_actualIncidence,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.signedDistance_eq_actualIncidence,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.boundaryCoefficient_eq_actualIncidence]
  let env ← getEnv
  let (_, st) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless (st.axioms.filter fun n => !allowed.contains n).isEmpty do
    throwError "Unexpected axiom: {st.axioms}"
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := (ci.type.getUsedConstants ++ (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])).toList.eraseDups.toArray
    let pdeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" || s.startsWith "Kane" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining" || s.startsWith "_private.Kane"
    graph := graph.push <| Json.mkObj [("name", toJson target.toString), ("direct_project_dependencies", toJson (pdeps.map Name.toString))]
    queue := pdeps.toList ++ queue
    if targets.contains target then
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [("name", toJson target.toString), ("expanded_type", toJson ty), ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [("axiom_union", toJson (st.axioms.map Name.toString)), ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
