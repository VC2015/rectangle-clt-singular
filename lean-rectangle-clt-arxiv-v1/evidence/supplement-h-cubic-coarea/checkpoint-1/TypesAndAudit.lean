import RectangleCLTArxivV1.SupplementalHLogisticCoordinateDerivative
import RectangleCLTArxivV1.SupplementalHGammaAbsoluteFace
import RectangleCLTArxivV1.SupplementalHCubicGammaTrace
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_hasDerivAt_logistic_power_offset,
    ``RectangleCLTArxivV1.supplementalH_hasDerivAt_integral_logistic_power_offset,
    ``RectangleCLTArxivV1.measurable_gaussianThresholdAbsoluteFaceTrace,
    ``RectangleCLTArxivV1.norm_gaussianThresholdAbsoluteFaceTrace_le,
    ``RectangleCLTArxivV1.supplementalH_absoluteFace_soft_power_eq_gamma,
    ``RectangleCLTArxivV1.supplementalH_hasDerivAt_gamma_absoluteFace_offset,
    ``RectangleCLTArxivV1.supplementalH_absoluteFace_soft_coarea,
    ``RectangleCLTArxivV1.supplementalH_logistic_power_face_bounds,
    ``RectangleCLTArxivV1.integrable_gaussianAbsoluteFace_logistic_power,
    ``RectangleCLTArxivV1.integrable_gamma_absoluteFace_facet,
    ``RectangleCLTArxivV1.supplementalH_absoluteFace_soft_sum_coarea]
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
      let axioms ← Lean.collectAxioms target
      let forbidden := axioms.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n
      unless forbidden.isEmpty do
        throwError "Unexpected axioms in {target}: {forbidden}"
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "Actual signed auxiliary Gamma differentiation and soft first-coarea identities"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
