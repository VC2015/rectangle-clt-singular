import RectangleCLTArxivV1.SupplementalISeededKernel
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.cap_parameter_copy_sum_measurable,
    ``RectangleCLTArxivV1.capSeededPairContribution_measurable_theta,
    ``RectangleCLTArxivV1.capSeededSingleContribution_measurable_theta,
    ``RectangleCLTArxivV1.capSeededExceptionalPattern_measurable_theta,
    ``RectangleCLTArxivV1.capSeededSeparatedPattern_measurable_theta,
    ``RectangleCLTArxivV1.cap_intervalIntegrable_measurable_of_Icc_bound,
    ``RectangleCLTArxivV1.capSeededExceptionalPattern_intervalIntegrable_theta,
    ``RectangleCLTArxivV1.capSeededFourthPattern_measurable_theta,
    ``RectangleCLTArxivV1.capSeededFourthPattern_intervalIntegrable_theta,
    ``RectangleCLTArxivV1.capSeededSeparatedPattern_intervalIntegrable_theta,
    ``RectangleCLTArxivV1.capSeededKernelCombination,
    ``RectangleCLTArxivV1.capSeededKernelCombination_add,
    ``RectangleCLTArxivV1.capSeededExceptionalRemainder,
    ``RectangleCLTArxivV1.capSeededSeparatedRemainder,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_exceptional_split,
    ``RectangleCLTArxivV1.capSeededKernelCombination_abs_le,
    ``RectangleCLTArxivV1.cap_seeded_exceptional_remainder_bound]
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
    ("scope", toJson "Actual seeded theta measurability, scalar-kernel separated/exceptional R4 split and exceptional budget bound"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
