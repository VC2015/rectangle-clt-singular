import RectangleCLTArxivV1.SmoothingGaussianMean
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLT.Companion.weightMass,
    ``RectangleCLT.Companion.weightMean,
    ``RectangleCLT.Companion.tangentMean,
    ``RectangleCLTArxivV1.gaussian_mean_relative_to_single_face,
    ``RectangleCLT.Companion.weighted_exp_mean_le,
    ``RectangleCLT.Companion.weighted_linear_integral_eq_mean,
    ``RectangleCLT.Companion.SplitV4.Printed.standardGaussian_map_unit_faceDot,
    ``RectangleCLT.Companion.SplitV4.Printed.standardGaussian_map_orthogonal_pair,
    ``RectangleCLT.Companion.SplitV4.Printed.standardGaussian_orthogonal_faceDots_independent,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussian_one_face_exponential_via_independence,
    ``RectangleCLT.Companion.tangentMean_orthogonal,
    ``RectangleCLT.Companion.tangentMean_dot_mean,
    ``RectangleCLT.Companion.tangentMean_normSq,
    ``RectangleCLT.Companion.weighted_mean_sq_le_second]
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
    ("scope", toJson "Lemma B.3 printed proof endpoints and project dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
