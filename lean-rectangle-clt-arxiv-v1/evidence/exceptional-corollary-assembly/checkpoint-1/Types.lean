import RectangleCLTArxivV1.ExceptionalFourthBound
import RectangleCLTArxivV1.ExceptionalMatrixSuppliers
import RectangleCLTArxivV1.ExceptionalSeededTensor
import RectangleCLTArxivV1.ExceptionalSeededModel
import RectangleCLTArxivV1.ExceptionalSeededRemainder
import RectangleCLTArxivV1.ExceptionalComparison
import RectangleCLTArxivV1.ExceptionalSeededComparison
import RectangleCLTArxivV1.ExceptionalMain
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.exceptionalFourthCutoffExpectation,
    ``RectangleCLTArxivV1.exceptionalFourth_cutoff_expectation_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates,
    ``RectangleCLTArxivV1.exceptional_seeded_matrix_estimates_of_angle,
    ``RectangleCLTArxivV1.ExceptionalNormalizedMatrixEstimates,
    ``RectangleCLTArxivV1.exceptional_copy_gaussian_outer_sum_eq_product,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_eq_cutoff_product,
    ``RectangleCLTArxivV1.exceptional_seeded_cutoff_product_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_pattern_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_remainder_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_early_late_additive_bound,
    ``RectangleCLTArxivV1.exceptional_integral_majorant_bound,
    ``RectangleCLTArxivV1.exceptionalComparisonConstant,
    ``RectangleCLTArxivV1.exceptionalComparisonConstant_pos,
    ``RectangleCLTArxivV1.exceptional_normalized_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_normalized_remainder_majorant_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_normalized_time_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptionalSmoothComparisonConstant,
    ``RectangleCLTArxivV1.exceptionalSmoothComparisonConstant_pos,
    ``RectangleCLTArxivV1.exceptional_smooth_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptionalBandwidthConstant,
    ``RectangleCLTArxivV1.exceptionalBandwidthConstant_ge_one,
    ``RectangleCLTArxivV1.exceptionalBoundaryConstant,
    ``RectangleCLTArxivV1.exceptionalBoundaryConstant_ge_one,
    ``RectangleCLTArxivV1.exceptional_boundary_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptionalCoreConstant,
    ``RectangleCLTArxivV1.exceptionalCoreConstant_ge_one,
    ``RectangleCLTArxivV1.exceptional_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_CLT_printed_of_matrix_suppliers,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.mk,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.cubic,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.pair]
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
    ("scope", toJson "Actual separated/exceptional Corollary5 assembly with precise cubic and full-angle matrix suppliers"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
