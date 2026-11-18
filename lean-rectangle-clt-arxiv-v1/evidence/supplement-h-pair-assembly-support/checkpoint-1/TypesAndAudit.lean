import RectangleCLTArxivV1.SupplementalHPairExtraFactors
import RectangleCLTArxivV1.SupplementalHPairMatrixAssembly
import RectangleCLTArxivV1.SupplementalHPairConstant
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_pair_kernel_extra_factors,
    ``RectangleCLTArxivV1.supplementalH_gaussian_projection_normSq_integrable,
    ``RectangleCLTArxivV1.supplementalHPairTupleMass_extra_factors,
    ``RectangleCLTArxivV1.supplementalHPairTupleProjection_extra_factors,
    ``RectangleCLTArxivV1.supplementalH_integrable_angle_weighted_pair_nuclear_sum,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairMatrix_of_mass_projection_trace,
    ``RectangleCLTArxivV1.supplementalHPairMatrixConstant,
    ``RectangleCLTArxivV1.supplementalHPairMatrixConstant_ge_four,
    ``RectangleCLTArxivV1.supplementalH_pair_matrix_bracket_le_power]
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
    ("scope", toJson "Actual extra-factor collapse, pair matrix assembly from ordinary kernels and universal scalar absorption"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
