import RectangleCLTCompanion.SplitV4.LogisticSelectorMatrixBound
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLT.Companion.SplitV4.projected_logistic_matrix_bound,
    ``RectangleCLT.Companion.SplitV4.logisticPrivateBase,
    ``RectangleCLT.Companion.SplitV4.logisticPrivateBase_dot,
    ``RectangleCLT.Companion.SplitV4.logisticPrivateBase_projected_law,
    ``RectangleCLT.Companion.SplitV4.logisticPrivateBase_concentrated,
    ``RectangleCLT.Companion.SplitV4.logisticPrivateBase_weight_tendsto,
    ``RectangleCLT.Companion.SplitV4.logisticPrivateBase_nuclear_sum_tendsto,
    ``RectangleCLT.Companion.SplitV4.RectangleBaseConcentration.active_coordinate_concentration,
    ``RectangleCLT.Companion.SplitV4.RectangleBaseConcentration.active_transitionMassBound,
    ``RectangleCLT.Companion.SplitV4.sum_selector_nuclear_eq_active]
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
    ("scope", toJson "Fresh early passage correspondence: C1 bounded/Gaussian, Corollary1 normalization, Lemma2 actual endpoint smoothing; no q0 derivative correspondence claim"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
