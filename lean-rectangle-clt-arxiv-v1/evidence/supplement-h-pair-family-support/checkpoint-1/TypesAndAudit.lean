import RectangleCLTArxivV1.SupplementalHPairFamilyReference
import RectangleCLTArxivV1.SupplementalHPairFamilyEntropy
import RectangleCLTArxivV1.SupplementalHPairAveragingKernels
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalHPairTupleAngle,
    ``RectangleCLTArxivV1.supplementalHPairTupleMass,
    ``RectangleCLTArxivV1.supplementalHPairTupleReferenceMass,
    ``RectangleCLTArxivV1.supplementalHPairTupleReferenceMass_properties,
    ``RectangleCLTArxivV1.supplementalHPairTupleMass_properties,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairTupleReference,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairReferenceFamily,
    ``RectangleCLTArxivV1.supplementalH_weighted_pair_mass_le_reference,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairFamilyEntropy_of_mass,
    ``RectangleCLTArxivV1.supplementalH_dominated_signed_kernel_properties,
    ``RectangleCLTArxivV1.supplementalHPairTupleProjection,
    ``RectangleCLTArxivV1.supplementalHPairTupleRadialTrace,
    ``RectangleCLTArxivV1.supplementalHPairTupleEntropy,
    ``RectangleCLTArxivV1.supplementalHPairTupleProjection_properties,
    ``RectangleCLTArxivV1.supplementalHPairTupleRadialTrace_properties,
    ``RectangleCLTArxivV1.supplementalH_angle_weighted_pair_selector_reduction]
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
    ("scope", toJson "Actual angle-weighted pair reference counts, outer entropy step and weighted H2 kernel reduction"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
