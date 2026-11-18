import RectangleCLTArxivV1.PolyhedralIntrinsicMain
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_coordinate_memLp_two,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_centered,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_covariance,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_average_second,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_envelope_moment,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected,
    ``RectangleCLTArxivV1.PolynomialFourthHypotheses.toArchived,
    ``RectangleCLTArxivV1.PolynomialFourthHypotheses.projected,
    ``RectangleCLTArxivV1.polyhedralFaceVariance_nonneg,
    ``RectangleCLTArxivV1.positivePolyhedralFaceIndex_injective,
    ``RectangleCLTArxivV1.positivePolyhedralFaceIndex_range,
    ``RectangleCLTArxivV1.positivePolyhedralFaceIndex_variance_pos,
    ``RectangleCLTArxivV1.omittedPolyhedralFace_variance_zero,
    ``RectangleCLTArxivV1.positivePolyhedralFaceScale_pos,
    ``RectangleCLTArxivV1.positivePolyhedralFaceScale_sq,
    ``RectangleCLTArxivV1.polyhedralDistance_eq_positive_faces,
    ``RectangleCLTArxivV1.polyhedralIntrinsicWidth_zero_of_no_positive_faces,
    ``RectangleCLTArxivV1.polyhedralDistance_zero_of_no_positive_faces,
    ``RectangleCLTArxivV1.PolyhedralNormalBound.positive_faces,
    ``RectangleCLTArxivV1.positivePolyhedralFace_variance_identity,
    ``RectangleCLTArxivV1.positivePolyhedralFaceCount_le,
    ``RectangleCLTArxivV1.projectedGaussian_factor_exists,
    ``RectangleCLTArxivV1.polyhedralIntrinsicWidth_le,
    ``RectangleCLTArxivV1.boundedPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.boundedPolyhedralCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.boundedPolyhedralEnvelopeCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.polynomialPolyhedralEnvelope_inputs,
    ``RectangleCLTArxivV1.polynomialPolyhedralWidth_le,
    ``RectangleCLTArxivV1.polynomialPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.normalized_sum_L2_centered,
    ``RectangleCLTArxivV1.polynomialPolyhedralCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.polynomialPolyhedralWidth_all_faces_le,
    ``RectangleCLTArxivV1.psi1Independent_projected_exact,
    ``RectangleCLTArxivV1.orliczPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.orliczPolyhedralCLT_intrinsic_all_faces,
    ``RectangleCLTArxivV1.corollary_3_bounded_orlicz_intrinsic,
    ``RectangleCLTArxivV1.corollary_3_intrinsic]
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
    ("scope", toJson "Corollary3 intrinsic polyhedral transfer, exact moment parameters, actual Gaussian width and canonical zero-face deletion"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
