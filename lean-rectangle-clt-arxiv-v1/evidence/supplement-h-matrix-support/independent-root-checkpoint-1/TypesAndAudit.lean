import RectangleCLTArxivV1.SupplementalHOuterEntropy
import RectangleCLTArxivV1.SupplementalHSelectorTuples
import RectangleCLTArxivV1.SupplementalHSelectorReductions
import RectangleCLTArxivV1.SupplementalHCubicWeights
import RectangleCLTArxivV1.SupplementalHCubicMoments
import RectangleCLTArxivV1.SupplementalHQuantitativeEntropy
import RectangleCLTArxivV1.SupplementalHCubicMatrix
import RectangleCLTArxivV1.SupplementalHIntrinsicMass
import RectangleCLTArxivV1.SupplementalHWeightedMass
import RectangleCLTArxivV1.SupplementalHLineReference
import RectangleCLTArxivV1.SupplementalHCubicSigns
import RectangleCLTArxivV1.SupplementalHWeightedReference
import RectangleCLTArxivV1.SupplementalHKernelMass
import RectangleCLTArxivV1.SupplementalHProjectionMoments
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.entropy_term_le_reference,
    ``RectangleCLTArxivV1.entropy_term_nonneg,
    ``RectangleCLTArxivV1.integrable_entropy_term,
    ``RectangleCLTArxivV1.entropy_term_common_factor,
    ``RectangleCLTArxivV1.integral_sum_entropy_le_fixed_scale,
    ``RectangleCLTArxivV1.integral_sum_entropy_le_log_ratio,
    ``RectangleCLTArxivV1.sum_face_tuples_cons,
    ``RectangleCLTArxivV1.sum_face_probability_products,
    ``RectangleCLTArxivV1.sum_selector_first_weight,
    ``RectangleCLTArxivV1.sum_selector_first_pair_weight,
    ``RectangleCLTArxivV1.sum_selector_first_weight_le,
    ``RectangleCLTArxivV1.sum_selector_first_pair_weight_le,
    ``RectangleCLTArxivV1.selector_extra_factors_binomial,
    ``RectangleCLTArxivV1.supplementalHSelectorMass,
    ``RectangleCLTArxivV1.supplementalHSelectorProjection,
    ``RectangleCLTArxivV1.supplementalHSelectorEntropy,
    ``RectangleCLTArxivV1.supplementalHSelectorRadialTrace,
    ``RectangleCLTArxivV1.supplementalH_selector_projected_reduction,
    ``RectangleCLTArxivV1.supplementalH_sum_weighted_selector_reduction,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_nonneg,
    ``RectangleCLTArxivV1.supplementalH_nonnegative_logConcave_mul,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_logConcave,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_logConcave,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_sub,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_add,
    ``RectangleCLTArxivV1.supplementalH_integrable_abs_linear_normSq,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_moments,
    ``RectangleCLTArxivV1.supplementalH_standardNormal_positive_halfline,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_mass_pos,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_matrix_reduction,
    ``RectangleCLTArxivV1.supplementalH_entropy_cardinality_budget,
    ``RectangleCLTArxivV1.supplementalH_integral_entropy_cardinality_bound,
    ``RectangleCLTArxivV1.supplementalHCubicSelectorScore,
    ``RectangleCLTArxivV1.supplementalH_cross_nuclear_le,
    ``RectangleCLTArxivV1.supplementalH_cubic_selector_decomposition,
    ``RectangleCLTArxivV1.supplementalHCubicMeanEnergy,
    ``RectangleCLTArxivV1.supplementalH_cubic_selector_nuclear_reduction,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_transitionMassBound,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_oneFaceMass,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_selectorMass,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussianWeightedSelectorMass,
    ``RectangleCLTArxivV1.supplementalH_rankOne_mulVec,
    ``RectangleCLTArxivV1.supplementalH_rankOne_transpose,
    ``RectangleCLTArxivV1.supplementalH_rankOne_idempotent,
    ``RectangleCLTArxivV1.supplementalH_rankOne_coordinate,
    ``RectangleCLTArxivV1.supplementalH_rankOne_normSq,
    ``RectangleCLTArxivV1.supplementalH_cubic_mean_reference_bound,
    ``RectangleCLTArxivV1.supplementalH_cubic_mean_reference_bound_all,
    ``RectangleCLTArxivV1.supplementalH_selectorFaceNormal_neg,
    ``RectangleCLTArxivV1.supplementalH_negative_scale_factor,
    ``RectangleCLTArxivV1.supplementalH_negative_cubic_mean_reference_bound_all,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussianWeightedOneFaceMass,
    ``RectangleCLTArxivV1.supplementalH_integrable_positiveDirection,
    ``RectangleCLTArxivV1.supplementalH_integral_positiveDirection_le_one,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_positiveOneFaceMass,
    ``RectangleCLTArxivV1.supplementalH_dominated_kernel_mass_properties,
    ``RectangleCLTArxivV1.supplementalHProjectionRadius,
    ``RectangleCLTArxivV1.supplementalHProjectionRadius_ge_one,
    ``RectangleCLTArxivV1.measurable_supplementalHProjectionRadius,
    ``RectangleCLTArxivV1.abs_faceDot_le_supplementalHProjectionRadius,
    ``RectangleCLTArxivV1.supplementalHProjectionRadius_moment_le]
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
    ("scope", toJson "Independent H matrix support kernels; no final matrix headline or coarea bridge"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
