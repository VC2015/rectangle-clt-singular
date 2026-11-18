import RectangleCLTArxivV1.SupplementalHPairProjectionLaw
import RectangleCLTArxivV1.SupplementalHPairReferenceTransport
import RectangleCLTArxivV1.SupplementalHPhysicalConcentration
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.hReferencePairComplement,
    ``RectangleCLTArxivV1.hReferencePairComplement_orthogonal,
    ``RectangleCLTArxivV1.hReferencePairComplement_unit,
    ``RectangleCLTArxivV1.hReferencePairComplement_reconstruct,
    ``RectangleCLTArxivV1.hReferencePair_unit_coordinates_map,
    ``RectangleCLTArxivV1.hReferencePair_projected_integral,
    ``RectangleCLTArxivV1.hReferencePair_projected_product_integral,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pair_projected_reference_mass,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pair_projected_angular_reference_mass,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_physical_layer,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_remove_ae_shift,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_physical_layer_of_ae_shift]
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
    ("scope", toJson "Independent actual projected Gaussian pair-reference transport and physical layer concentration"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
