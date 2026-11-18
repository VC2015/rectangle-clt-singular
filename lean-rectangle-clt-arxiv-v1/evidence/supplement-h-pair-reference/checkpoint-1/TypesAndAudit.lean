import RectangleCLTArxivV1.SupplementalHPairReference
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.hReferenceSingle,
    ``RectangleCLTArxivV1.hReferencePair,
    ``RectangleCLTArxivV1.measurable_hReferenceSingle,
    ``RectangleCLTArxivV1.measurable_hReferencePair,
    ``RectangleCLTArxivV1.hReferenceSingle_nonneg,
    ``RectangleCLTArxivV1.hReferencePair_nonneg,
    ``RectangleCLTArxivV1.hReferenceSingle_le_capLaplace,
    ``RectangleCLTArxivV1.hReferencePair_le_capLaplace,
    ``RectangleCLTArxivV1.hReferenceSingle_le_one,
    ``RectangleCLTArxivV1.hReferencePair_le_one,
    ``RectangleCLTArxivV1.hReferenceSingle_integrable_probability,
    ``RectangleCLTArxivV1.hReferencePair_integrable_probability,
    ``RectangleCLTArxivV1.integrable_hReferenceSingle,
    ``RectangleCLTArxivV1.integrable_hReferencePair,
    ``RectangleCLTArxivV1.hReferenceSingle_integral,
    ``RectangleCLTArxivV1.hReferencePair_inner_integral,
    ``RectangleCLTArxivV1.hReferencePair_integral,
    ``RectangleCLTArxivV1.hReferenceSingle_lower,
    ``RectangleCLTArxivV1.hReference_gaussianPDF_le,
    ``RectangleCLTArxivV1.hReference_gaussianPDF_le_one,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussian_marginal_density,
    ``RectangleCLTArxivV1.hReferenceConditionalPairDensity,
    ``RectangleCLTArxivV1.hReferenceConditionalPairDensity_nonneg,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussian_pair_density,
    ``RectangleCLTArxivV1.hReference_normal_integral_le_volume,
    ``RectangleCLTArxivV1.hReferencePair_normal_fiber_bound,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_oneFace_normal_average,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pair_normal_reference_mass,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pair_angular_reference_mass]
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
    ("scope", toJson "Actual scalar reference integrals, densities and product-Gaussian pair mass"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
