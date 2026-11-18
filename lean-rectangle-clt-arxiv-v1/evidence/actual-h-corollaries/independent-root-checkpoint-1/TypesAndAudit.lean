import RectangleCLTArxivV1.ActualMatrixConstant
import RectangleCLTArxivV1.ActualMatrixTransport
import RectangleCLTArxivV1.ActualSeededMatrixBase
import RectangleCLTArxivV1.ActualPairMatrixTransport
import RectangleCLTArxivV1.ActualNormalizedMatrices
import RectangleCLTArxivV1.ActualHFourth
import RectangleCLTArxivV1.ActualCorollaries
import RectangleCLTArxivV1.ActualRemainderIntegral
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.actualMatrixConstant,
    ``RectangleCLTArxivV1.actualMatrixConstant_ge_one,
    ``RectangleCLTArxivV1.actualMatrixConstant_ge_cubic,
    ``RectangleCLTArxivV1.actualMatrixConstant_ge_pair,
    ``RectangleCLTArxivV1.actualMatrix_cubic_power_le,
    ``RectangleCLTArxivV1.actualMatrix_pair_power_le,
    ``RectangleCLTArxivV1.actualMatrix_factorNormal_eq_selectorFaceNormal,
    ``RectangleCLTArxivV1.actualMatrix_physical_pushforward,
    ``RectangleCLTArxivV1.actualMatrix_cubic_supplier_of_physical,
    ``RectangleCLTArxivV1.actual_seededSplitBase_map_eq,
    ``RectangleCLTArxivV1.actual_seeded_physical_concentration,
    ``RectangleCLTArxivV1.actual_normalized_cubic_supplier,
    ``RectangleCLTArxivV1.actualMatrix_pair_supplier_of_physical,
    ``RectangleCLTArxivV1.actual_normalized_matrix_estimates,
    ``RectangleCLTArxivV1.actual_normalized_gap_matrix_estimates,
    ``RectangleCLTArxivV1.theoremH3Constant,
    ``RectangleCLTArxivV1.theoremH3Constant_pos,
    ``RectangleCLTArxivV1.theorem_H3_fourth_derivative,
    ``RectangleCLTArxivV1.corollary4Constant,
    ``RectangleCLTArxivV1.corollary4Constant_ge_one,
    ``RectangleCLTArxivV1.corollary4Constant_pos,
    ``RectangleCLTArxivV1.corollary5Constant,
    ``RectangleCLTArxivV1.corollary5Constant_ge_one,
    ``RectangleCLTArxivV1.corollary5Constant_pos,
    ``RectangleCLTArxivV1.corollary4_positive_correlation_gap,
    ``RectangleCLTArxivV1.corollary5_exceptional_correlation_budget,
    ``RectangleCLTArxivV1.corollary5RemainderConstant,
    ``RectangleCLTArxivV1.corollary5RemainderConstant_pos,
    ``RectangleCLTArxivV1.corollary5_normalized_remainder_abs_intervalIntegrable,
    ``RectangleCLTArxivV1.corollary5_normalized_remainder_integral]
  let env ← getEnv
  let (_, axiomState) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  let forbidden := axiomState.axioms.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n
  unless forbidden.isEmpty do throwError "Unexpected axiom in endpoint union: {forbidden}"
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
    ("scope", toJson "Independent actual fourth derivative, correlation corollaries and source time integral"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
