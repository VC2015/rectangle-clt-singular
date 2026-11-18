import RectangleCLTArxivV1.SupplementalHPairPositiveCoordinates
import RectangleCLTArxivV1.SupplementalHPairPhysicalMoments
import RectangleCLTArxivV1.SupplementalHPairMatrixEstimate
import RectangleCLTArxivV1.SupplementalHPairRectangular
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalHPairMass_baseline_eq_native,
    ``RectangleCLTArxivV1.integrable_gaussian_pair_projection_selector,
    ``RectangleCLTArxivV1.supplementalHPairProjection_baseline_eq_native,
    ``RectangleCLTArxivV1.supplementalHPairMassConstant,
    ``RectangleCLTArxivV1.supplementalHPairProjectionConstant,
    ``RectangleCLTArxivV1.supplementalHPairMassConstant_nonneg,
    ``RectangleCLTArxivV1.supplementalHPairProjectionConstant_nonneg,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairPhysicalMass,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairPhysicalProjection,
    ``RectangleCLTArxivV1.supplementalHPairPhysicalMatrixConstant,
    ``RectangleCLTArxivV1.supplementalHPairPhysicalMatrixConstant_ge_four,
    ``RectangleCLTArxivV1.proposition_H2_pair_matrix,
    ``RectangleCLTArxivV1.supplementalHInputShift_pairScore,
    ``RectangleCLTArxivV1.proposition_H2_pair_matrix_rectangular,
    ``RectangleCLTArxivV1.proposition_H2_pair_matrix_shifted]
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
    ("scope", toJson "Actual physical pair moments and full arbitrary rectangular shifted pair matrix proposition"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
