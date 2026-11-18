import RectangleCLTArxivV1.IntrinsicDerivativeProposition
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_logarithmic,
    ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_maximum,
    ``RectangleCLTArxivV1.one_le_intrinsicBoundaryCoefficient,
    ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_gaussian,
    ``RectangleCLTArxivV1.integral_smallerEnvelope_directSlepian_intrinsic,
    ``RectangleCLTArxivV1.abs_directSlepianCubicTerm_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.directSlepian_fourth_copy_data_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.abs_directSlepianFourthRemainder_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.intrinsic_derivative_proposition,
    ``RectangleCLTArxivV1.directSlepian_increment_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.direct_initialization_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.initializationDiscrepancy_intrinsic_le,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_cubic_product_bound,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_fourth_product_bound,
    ``RectangleCLTArxivV1.relativeFourthMatrix_eq_printed,
    ``RectangleCLTArxivV1.relativeFreshFourthMatrix_eq_printed,
    ``RectangleCLTArxivV1.IntrinsicFourthBounds.relativeMomentBounds,
    ``RectangleCLTArxivV1.intrinsic_seeded_matrix_estimate_with_copies,
    ``RectangleCLTArxivV1.intrinsic_seeded_fourth_remainder_bound,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_cubic_product_rate,
    ``RectangleCLTArxivV1.intrinsic_seeded_derivative_bounds,
    ``RectangleCLTArxivV1.intrinsic_seeded_time_comparison_bound,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_fourth_product_rate,
    ``RectangleCLTArxivV1.proposition_1_intrinsic_derivatives,
    ``RectangleCLTArxivV1.intrinsic_smooth_comparison_of_boundary_suppliers,
    ``RectangleCLTArxivV1.intrinsicCLT_of_uniform_boundary_suppliers,
    ``RectangleCLTArxivV1.intrinsicBoundaryCLT,
    ``RectangleCLTArxivV1.intrinsicComparisonLog_le_D_L,
    ``RectangleCLTArxivV1.intrinsicBandwidth_admissible,
    ``RectangleCLTArxivV1.intrinsicBandwidth_total_cost_le,
    ``RectangleCLTArxivV1.intrinsic_rate_of_small_bandwidth_estimate,
    ``RectangleCLTArxivV1.large_intrinsicBandwidth_rate,
    ``RectangleCLTArxivV1.intrinsic_trivial_large_envelope,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT_core,
    ``RectangleCLTArxivV1.theorem_1_intrinsic_clt,
    ``RectangleCLTArxivV1.intrinsicRelativeRate_envelope_le,
    ``RectangleCLTArxivV1.intrinsicEnvelopeCLT]
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
    ("scope", toJson "Intrinsic Theorem 1 and supporting actual interpolation proofs"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
