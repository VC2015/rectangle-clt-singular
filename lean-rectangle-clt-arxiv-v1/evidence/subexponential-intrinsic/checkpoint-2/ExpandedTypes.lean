import RectangleCLTArxivV1.PolyhedralIntrinsicSubexponentialAllFaces
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.mem_psi1Scales_of_norm_le,
    ``RectangleCLTArxivV1.psi1_exponentialHypotheses_exact,
    ``RectangleCLTArxivV1.clipAt_neg,
    ``RectangleCLTArxivV1.signedCoordinate_smul_real,
    ``RectangleCLTArxivV1.abs_clipAt_sub_le,
    ``RectangleCLTArxivV1.signedCoordinate_clipAt,
    ``RectangleCLTArxivV1.signedCoordinate_centeredClipped,
    ``RectangleCLTArxivV1.sum_integral_projection_sq_of_memLp,
    ``RectangleCLTArxivV1.signedCoordinate_memLp_two,
    ``RectangleCLTArxivV1.gaussianMaximumMean_clipped_le,
    ``RectangleCLTArxivV1.residual_tail_printed,
    ``RectangleCLTArxivV1.clipResidual_pow_le_exp,
    ``RectangleCLTArxivV1.residual_power_moment_printed,
    ``RectangleCLTArxivV1.subexponentialTailFactor_le_inv_four_mul,
    ``RectangleCLTArxivV1.four_n_tail_le_quarter,
    ``RectangleCLTArxivV1.subexponentialUnionLog_le_two,
    ``RectangleCLTArxivV1.normalized_residual_tail_printed,
    ``RectangleCLTArxivV1.printedResidualRadius_le_archive,
    ``RectangleCLTArxivV1.rectangleError_le_of_two_couplings_intrinsic,
    ``RectangleCLTArxivV1.subexponential_clipping_reduction_intrinsic,
    ``RectangleCLTArxivV1.one_le_subexponentialWidthConstant,
    ``RectangleCLTArxivV1.subexponentialCLT_intrinsic,
    ``RectangleCLTArxivV1.subexponentialCLT_psi1_intrinsic,
    ``RectangleCLTArxivV1.gaussian_factor_exists_of_psi1,
    ``RectangleCLTArxivV1.corollary_2_intrinsic,
    ``RectangleCLTArxivV1.psi1Independent_projected_exact,
    ``RectangleCLTArxivV1.orliczPolyhedralCLT_intrinsic,
    ``RectangleCLT.Companion.absolute_residual_sum_mgf_le,
    ``RectangleCLT.Companion.residual_sum_abs_tail,
    ``RectangleCLT.Companion.normalized_exp_residual_tail,
    ``RectangleCLT.Companion.normalizedResidualRows_sum_covariance_diagonal_le,
    ``RectangleCLT.Companion.clipped_standardDeviation_sub_one_le,
    ``RectangleCLT.Companion.clipped_standardDeviation_ge_half,
    ``RectangleCLT.Companion.jointRestoration_gaussianCoupling_exists,
    ``RectangleCLT.Companion.standardGaussian_rectangular_norm_tail_log]
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
    ("scope", toJson "Actual Corollary2 D.1 and exact subexponential Corollary3 branch"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
