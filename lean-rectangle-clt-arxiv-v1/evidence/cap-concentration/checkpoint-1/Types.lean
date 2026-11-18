import RectangleCLTArxivV1.CapClosedIntervals
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.frequencyKernel,
    ``RectangleCLTArxivV1.integral_frequencyKernel_sq_le_correlation,
    ``RectangleCLTArxivV1.probability_le_frequencyKernel_sq,
    ``RectangleCLTArxivV1.probability_le_frequency_correlation,
    ``RectangleCLTArxivV1.realPhaseAverage_re_ge_half,
    ``RectangleCLTArxivV1.integral_cond_sub_le,
    ``RectangleCLTArxivV1.probability_le_uniform_frequency_integral,
    ``RectangleCLTArxivV1.capGaussianExponent,
    ``RectangleCLTArxivV1.capSingleMajorant,
    ``RectangleCLTArxivV1.capPairMajorant,
    ``RectangleCLTArxivV1.capGaussianExponent_pos,
    ``RectangleCLTArxivV1.integrable_capSingleMajorant,
    ``RectangleCLTArxivV1.capSingleMajorant_nonneg,
    ``RectangleCLTArxivV1.capSingleMajorant_le_one,
    ``RectangleCLTArxivV1.integral_capSingleMajorant,
    ``RectangleCLTArxivV1.capPairMajorant_factor,
    ``RectangleCLTArxivV1.capPairMajorant_nonneg,
    ``RectangleCLTArxivV1.capPairMajorant_le_one,
    ``RectangleCLTArxivV1.integral_capPairMajorant_inner,
    ``RectangleCLTArxivV1.integrable_capPairMajorant,
    ``RectangleCLTArxivV1.integral_capPairMajorant,
    ``RectangleCLTArxivV1.integral_capPairMajorant_pi,
    ``RectangleCLTArxivV1.capMixedValue,
    ``RectangleCLTArxivV1.capMixedCovariance,
    ``RectangleCLTArxivV1.cap_matrixQuadratic_add,
    ``RectangleCLTArxivV1.cap_dotProduct_sum,
    ``RectangleCLTArxivV1.cap_integral_projection_zero,
    ``RectangleCLTArxivV1.norm_integral_unitPhase_sub_const,
    ``RectangleCLTArxivV1.norm_integral_unitPhase_mixed_le,
    ``RectangleCLTArxivV1.capFrequencyRadius,
    ``RectangleCLTArxivV1.capFrequencyInterval,
    ``RectangleCLTArxivV1.capFrequencySquare,
    ``RectangleCLTArxivV1.capPairWeight,
    ``RectangleCLTArxivV1.capPairPhase,
    ``RectangleCLTArxivV1.measurableSet_capFrequencySquare,
    ``RectangleCLTArxivV1.capFrequencyRadius_pos,
    ``RectangleCLTArxivV1.volume_capFrequencyInterval,
    ``RectangleCLTArxivV1.capFrequencyInterval_volume_ne_zero,
    ``RectangleCLTArxivV1.capFrequencyInterval_volume_ne_top,
    ``RectangleCLTArxivV1.volume_capFrequencySquare,
    ``RectangleCLTArxivV1.capFrequencySquare_volume_ne_zero,
    ``RectangleCLTArxivV1.capFrequencySquare_volume_ne_top,
    ``RectangleCLTArxivV1.capFrequency_square_member_abs,
    ``RectangleCLTArxivV1.capFrequency_square_sub_abs,
    ``RectangleCLTArxivV1.abs_capPairPhase_le_one,
    ``RectangleCLTArxivV1.abs_capPairWeight_projection_le_half,
    ``RectangleCLTArxivV1.cap_pair_matrixQuadratic,
    ``RectangleCLTArxivV1.cap_pair_quadratic_nonneg,
    ``RectangleCLTArxivV1.cap_two_projection_small_box,
    ``RectangleCLTArxivV1.cap_one_projection_small_interval,
    ``RectangleCLTArxivV1.integral_weight_le_of_local_probability,
    ``RectangleCLTArxivV1.capLaplace,
    ``RectangleCLTArxivV1.integrable_capLaplace,
    ``RectangleCLTArxivV1.integral_capLaplace,
    ``RectangleCLTArxivV1.capLaplace_local,
    ``RectangleCLTArxivV1.cap_logistic_single_le,
    ``RectangleCLTArxivV1.cap_logistic_pair_le,
    ``RectangleCLTArxivV1.logisticTupleWeight_single_le_capLaplace,
    ``RectangleCLTArxivV1.logisticTupleWeight_pair_le_capLaplace,
    ``RectangleCLTArxivV1.capPairLaplace,
    ``RectangleCLTArxivV1.integrable_capPairLaplace,
    ``RectangleCLTArxivV1.integral_capPairLaplace,
    ``RectangleCLTArxivV1.capLaplace_nonneg,
    ``RectangleCLTArxivV1.capLaplace_le_one,
    ``RectangleCLTArxivV1.capPairLaplace_local,
    ``RectangleCLTArxivV1.abs_normalized_sub_le_one,
    ``RectangleCLTArxivV1.integral_capLaplace_le_of_intervals,
    ``RectangleCLTArxivV1.integral_capPairLaplace_le_of_boxes,
    ``RectangleCLTArxivV1.integral_logistic_single_le_of_intervals,
    ``RectangleCLTArxivV1.integral_logistic_pair_le_of_boxes,
    ``RectangleCLTArxivV1.cap_one_face_tuple_mass,
    ``RectangleCLTArxivV1.cap_two_face_tuple_mass,
    ``RectangleCLTArxivV1.integral_logisticTupleWeight_product_le,
    ``RectangleCLTArxivV1.cap_one_face_tuple_mass_product,
    ``RectangleCLTArxivV1.cap_two_face_tuple_mass_product,
    ``RectangleCLTArxivV1.capVarianceScale,
    ``RectangleCLTArxivV1.capVarianceScale_pos,
    ``RectangleCLTArxivV1.capVarianceScale_sq_mul,
    ``RectangleCLTArxivV1.capMixedValue_smul,
    ``RectangleCLTArxivV1.capMixedCovariance_smul,
    ``RectangleCLTArxivV1.cap_scaled_interval_iff,
    ``RectangleCLTArxivV1.cap_one_projection_small_interval_of_lower_variance,
    ``RectangleCLTArxivV1.cap_two_projection_small_box_of_lower_variance,
    ``RectangleCLTArxivV1.cap_one_face_tuple_mass_of_lower_variance,
    ``RectangleCLTArxivV1.cap_two_face_tuple_mass_of_lower_variance,
    ``RectangleCLTArxivV1.cap_one_projection_zero_width,
    ``RectangleCLTArxivV1.cap_one_projection_small_interval_nonneg,
    ``RectangleCLTArxivV1.cap_two_projection_small_box_nonneg]
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
    ("scope", toJson "Actual compact-frequency small-box concentration and logistic weight masses"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
