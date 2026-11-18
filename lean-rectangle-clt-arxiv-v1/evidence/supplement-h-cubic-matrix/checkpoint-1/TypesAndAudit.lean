import RectangleCLTArxivV1.SupplementalHCubicPowerTrace
import RectangleCLTArxivV1.SupplementalHCubicTraceRestoration
import RectangleCLTArxivV1.SupplementalHCubicPhysicalTrace
import RectangleCLTArxivV1.SupplementalHCubicMatrixMain
import RectangleCLTArxivV1.SupplementalHCubicMatrixEstimate
import RectangleCLTArxivV1.SupplementalHInputShift
import RectangleCLTArxivV1.SupplementalHCubicRectangular
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalHSoftCubicPowerTrace,
    ``RectangleCLTArxivV1.supplementalH_softCubicPowerTrace_concentrated_base,
    ``RectangleCLTArxivV1.supplementalHSoftCubicTrace,
    ``RectangleCLTArxivV1.supplementalHSoftCubicTrace_eq_binomial,
    ``RectangleCLTArxivV1.supplementalH_softCubicTrace_concentrated_base,
    ``RectangleCLTArxivV1.supplementalHCubicPhysicalTrace,
    ``RectangleCLTArxivV1.integrable_gaussianAbsoluteFace_selector_physical,
    ``RectangleCLTArxivV1.supplementalHCubicPhysicalTrace_eq_softTrace,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_cubicPhysicalTrace,
    ``RectangleCLTArxivV1.supplementalH_cubic_selector_nuclear_reduction_all,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_cubicMatrix_raw,
    ``RectangleCLTArxivV1.proposition_H1_cubic_matrix,
    ``RectangleCLTArxivV1.supplementalHInputShift,
    ``RectangleCLTArxivV1.supplementalHInputShift_faceScore,
    ``RectangleCLTArxivV1.supplementalHInputShift_weights,
    ``RectangleCLTArxivV1.supplementalHInputShift_selectorWeight,
    ``RectangleCLTArxivV1.supplementalHInputShift_cubicScore,
    ``RectangleCLTArxivV1.proposition_H1_cubic_matrix_rectangular,
    ``RectangleCLTArxivV1.proposition_H1_cubic_matrix_shifted]
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
    ("scope", toJson "Actual full intrinsic cubic matrix proposition including signed trace restoration and arbitrary rectangular shifted model"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
