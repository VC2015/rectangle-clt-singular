import RectangleCLTArxivV1.RademacherBoundary
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.lemma_C1_rademacher_boundary,
    ``RectangleCLTArxivV1.lemma_C1_rademacher_maximum,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax,
    ``RectangleCLT.Companion.SplitV4.Printed.exists_small_threshold_perturbation,
    ``RectangleCLT.Companion.SplitV4.Printed.exists_small_unique_threshold_perturbation,
    ``RectangleCLT.Companion.SplitV4.Printed.affineCubeMaximum_threshold_stability,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_event_subset_perturbed,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_indicator_le_perturbed,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_bound_of_all_positive_radii,
    ``RectangleCLT.Companion.SplitV4.Printed.cubeVertex,
    ``RectangleCLT.Companion.SplitV4.Printed.cubeLinearCLM,
    ``RectangleCLT.Companion.SplitV4.Printed.cubeLinearCLM_apply,
    ``RectangleCLT.Companion.SplitV4.Printed.realAffineCubeMaximum,
    ``RectangleCLT.Companion.SplitV4.Printed.realAffineCubeMaximum_vertex,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.strict_active,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.eventually_eq_active,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_maximum,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedCubeRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.continuous_normalizedCubeRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedCubeRamp_nonneg,
    ``RectangleCLT.Companion.SplitV4.Printed.normalizedCubeRamp_le_one,
    ``RectangleCLT.Companion.SplitV4.Printed.monotone_normalizedCubeRamp,
    ``RectangleCLT.Companion.SplitV4.Printed.cubeRampPrimitive,
    ``RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_cubeRampPrimitive,
    ``RectangleCLT.Companion.SplitV4.Printed.monotone_cubeRampPrimitive,
    ``RectangleCLT.Companion.SplitV4.Printed.convexOn_cubeRampPrimitive,
    ``RectangleCLT.Companion.SplitV4.Printed.convexOn_realAffineCubeMaximum,
    ``RectangleCLT.Companion.SplitV4.Printed.convexOn_cubeRampPrimitive_comp_maximum,
    ``RectangleCLT.Companion.SplitV4.Printed.cubeLinearCLM_single,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_ramp_composition,
    ``RectangleCLT.Companion.SplitV4.Printed.cubeGradientRadial,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.gradient_radial_eq,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.gradient_energy_eq,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_eq_flux,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_coefficient_bound_pos,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.gradient_radial_upper,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_lower,
    ``RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_upper,
    ``RectangleCLT.Companion.SplitV4.Printed.cube_boundary_unique_case,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed_avg,
    ``RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed,
    ``RectangleCLT.Companion.SplitV4.avg_exp_cubeLinear,
    ``RectangleCLT.Companion.SplitV4.avg_exp_cubeLinear_le,
    ``RectangleCLT.Companion.SplitV4.avg_exp_selected_cubeLinear_le,
    ``RectangleCLT.Companion.SplitV4.avg_selected_cubeLinear_le_sqrt,
    ``RectangleCLT.Companion.SplitV4.positiveLinearMaximum_selected,
    ``RectangleCLT.Companion.SplitV4.intrinsicCubeMean_le_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.cubeSign,
    ``RectangleCLT.Companion.SplitV4.cubeLinear,
    ``RectangleCLT.Companion.SplitV4.positiveLinearMaximum,
    ``RectangleCLT.Companion.SplitV4.intrinsicCubeMean,
    ``RectangleCLT.Companion.SplitV4.positiveLinearMaximum_nonneg,
    ``RectangleCLT.Companion.SplitV4.cubeLinear_le_positiveMaximum,
    ``RectangleCLT.Companion.SplitV4.intrinsicCubeMean_nonneg,
    ``RectangleCLT.Companion.SplitV4.cubeRamp,
    ``RectangleCLT.Companion.SplitV4.cubeRamp_nonneg,
    ``RectangleCLT.Companion.SplitV4.cubeRamp_le_width,
    ``RectangleCLT.Companion.SplitV4.cubeRamp_monotone,
    ``RectangleCLT.Companion.SplitV4.cubeRamp_eq_linear,
    ``RectangleCLT.Companion.SplitV4.cubeEdgeFlux,
    ``RectangleCLT.Companion.SplitV4.cubeEdgeFlux_nonneg,
    ``RectangleCLT.Companion.SplitV4.cubeEdgeFlux_controls_squares,
    ``RectangleCLT.Companion.SplitV4.cube_avg_signed_coordinate,
    ``RectangleCLT.Companion.SplitV4.affineCubeMaximum,
    ``RectangleCLT.Companion.SplitV4.activeCubeBranch,
    ``RectangleCLT.Companion.SplitV4.activeCubeBranch_attains,
    ``RectangleCLT.Companion.SplitV4.affineCubeMaximum_supports,
    ``RectangleCLT.Companion.SplitV4.cubeLinear_edge_difference,
    ``RectangleCLT.Companion.SplitV4.activeCubeSlope,
    ``RectangleCLT.Companion.SplitV4.affineCubeEdgeFlux,
    ``RectangleCLT.Companion.SplitV4.cubeBoundaryIndicator,
    ``RectangleCLT.Companion.SplitV4.affineCube_edge_support,
    ``RectangleCLT.Companion.SplitV4.affineCubeEdgeFlux_nonneg,
    ``RectangleCLT.Companion.SplitV4.affineCube_edge_oscillation,
    ``RectangleCLT.Companion.SplitV4.boundary_active_slope_square_le_flux,
    ``RectangleCLT.Companion.SplitV4.cube_boundary_indicator_energy_le_flux,
    ``RectangleCLT.Companion.SplitV4.avg_affineCubeEdgeFlux_sum,
    ``RectangleCLT.Companion.SplitV4.cubeUniformLaw,
    ``RectangleCLT.Companion.SplitV4.integral_cubeUniformLaw_eq_avg,
    ``RectangleCLT.Companion.SplitV4.cubeUniformLaw_boundary_eq_avg,
    ``Kane.exp_avg_le_avg_exp,
    ``Kane.avg_le_sqrt_of_exp_moment]
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
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" || s.startsWith "Kane" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining" || s.startsWith "_private.Kane"
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
    ("scope", toJson "Printed Rademacher unique-max genuine derivatives, ramp/edge/discrete-IBP proof, actual generic perturbation and numerical limit, genuine uniform-cube MGF/Jensen maximum bound"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
