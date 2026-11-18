import RectangleCLTArxivV1.SupplementalHTripleTransportThreeFace
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.gaussianTripleSectionPoint,
    ``RectangleCLTArxivV1.gaussianTripleSectionMap,
    ``RectangleCLTArxivV1.measurable_gaussianTripleSectionMap,
    ``RectangleCLTArxivV1.gaussianTripleSectionMap_measurePreserving,
    ``RectangleCLTArxivV1.integrable_gaussianTripleSectionMap_iff,
    ``RectangleCLTArxivV1.integral_gaussianTripleSectionMap,
    ``RectangleCLTArxivV1.faceDot_gaussianSectionPoint_of_orthogonal,
    ``RectangleCLTArxivV1.gaussianTripleSectionPoint_eq_affine,
    ``RectangleCLTArxivV1.gaussianTripleSectionPoint_levels,
    ``RectangleCLTArxivV1.tripleScalarEquiv,
    ``RectangleCLTArxivV1.tripleScalarEquiv_apply,
    ``RectangleCLTArxivV1.tripleScalarEquiv_symm_apply,
    ``RectangleCLTArxivV1.tripleScalarEquiv_measurePreserving,
    ``RectangleCLTArxivV1.tripleScalarEquiv_volumePreserving,
    ``RectangleCLTArxivV1.tripleEuclideanScalarEquiv,
    ``RectangleCLTArxivV1.tripleEuclideanScalarEquiv_apply,
    ``RectangleCLTArxivV1.tripleEuclideanScalarEquiv_symm_apply,
    ``RectangleCLTArxivV1.tripleEuclideanScalarEquiv_volumePreserving,
    ``RectangleCLTArxivV1.tripleScalarGaussian,
    ``RectangleCLTArxivV1.tripleEuclideanGaussian,
    ``RectangleCLTArxivV1.tripleScalarGaussian_isProbability,
    ``RectangleCLTArxivV1.tripleEuclideanGaussian_isProbability,
    ``RectangleCLTArxivV1.tripleEuclideanScalarEquiv_gaussianPreserving,
    ``RectangleCLTArxivV1.tripleEuclideanGaussian_eq_map_standardGaussian,
    ``RectangleCLTArxivV1.gaussianTripleEuclideanSectionMap_measurePreserving,
    ``RectangleCLTArxivV1.tripleEuclideanDensity,
    ``RectangleCLTArxivV1.continuous_tripleEuclideanDensity,
    ``RectangleCLTArxivV1.tripleEuclideanDensity_nonneg,
    ``RectangleCLTArxivV1.tripleEuclideanDensity_pullback,
    ``RectangleCLTArxivV1.tripleEuclideanGaussian_integral_density,
    ``RectangleCLTArxivV1.tripleEuclideanGaussian_integrable_density_iff,
    ``RectangleCLTArxivV1.tripleEuclideanGaussian_integral_dominates_translated_fiber,
    ``RectangleCLTArxivV1.tripleEuclideanDensity_eq_scalarProduct,
    ``RectangleCLTArxivV1.tripleTransportFrame,
    ``RectangleCLTArxivV1.tripleTransportNormal,
    ``RectangleCLTArxivV1.tripleTransportFrame_orthonormal,
    ``RectangleCLTArxivV1.tripleTransportNormal_unit,
    ``RectangleCLTArxivV1.tripleTransportNormal_orthogonal,
    ``RectangleCLTArxivV1.tripleTransportFrame_sum,
    ``RectangleCLTArxivV1.tripleTransportSection,
    ``RectangleCLTArxivV1.tripleTransportSection_measurePreserving,
    ``RectangleCLTArxivV1.tripleTransportSection_eq_frame,
    ``RectangleCLTArxivV1.tripleTransportSection_eq_affine_projection,
    ``RectangleCLTArxivV1.tripleTransportCoordinate,
    ``RectangleCLTArxivV1.measurable_tripleTransportCoordinate,
    ``RectangleCLTArxivV1.tripleTransportCoordinate_section,
    ``RectangleCLTArxivV1.tripleTransportSection_comp,
    ``RectangleCLTArxivV1.tripleTransportSection_add_normal,
    ``RectangleCLTArxivV1.measurable_tripleTransportSection,
    ``RectangleCLTArxivV1.integral_tripleTransportSection,
    ``RectangleCLTArxivV1.tripleConeEvent,
    ``RectangleCLTArxivV1.measurableSet_tripleConeEvent,
    ``RectangleCLTArxivV1.tripleConeEvent_section,
    ``RectangleCLTArxivV1.tripleCone_fiber_coefficient_bound,
    ``RectangleCLTArxivV1.tripleCone_spherical_coefficient_le_fourth_event,
    ``RectangleCLTArxivV1.tripleOutwardNormalCone,
    ``RectangleCLTArxivV1.tripleOutwardNormalCone_smul_iff,
    ``RectangleCLTArxivV1.tripleTransportSection_reconstruct,
    ``RectangleCLTArxivV1.tripleTransportSection_active_levels,
    ``RectangleCLTArxivV1.tripleConeEvent_exactStratum,
    ``RectangleCLTArxivV1.tripleConeEvent_mem_adaptiveOutwardTube,
    ``RectangleCLTArxivV1.tripleConeEvent_mem_outerLayer,
    ``RectangleCLTArxivV1.TripleFaceTuple,
    ``RectangleCLTArxivV1.tripleFaceTupleFintype,
    ``RectangleCLTArxivV1.tripleFaceActive,
    ``RectangleCLTArxivV1.tripleFaceTuple_eq_perm_of_active_eq,
    ``RectangleCLTArxivV1.tripleOrderedEvent,
    ``RectangleCLTArxivV1.tripleOrderedEvent_shared_active,
    ``RectangleCLTArxivV1.tripleOrderedEvent_indicator_sum_le,
    ``RectangleCLTArxivV1.tripleOrderedEvent_integral_sum_le,
    ``RectangleCLTArxivV1.tripleTransport_normalPoint_norm_le_threeFaceRadius,
    ``RectangleCLTArxivV1.tripleCone_spherical_coefficient_le_threeFace_event]
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
    ("scope", toJson "Independent actual rank-three cone/Gaussian transport review; not raw J_e grouping or full all-threshold H1"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
