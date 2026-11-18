import RectangleCLTArxivV1.PositiveGammaPairSum
import RectangleCLTArxivV1.PositiveGammaMeans
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection,
    ``RectangleCLTArxivV1.positiveGammaMixedMassKernel_eq_ridgeDensity,
    ``RectangleCLTArxivV1.positiveGamma_angle_mul_massKernel,
    ``RectangleCLTArxivV1.positiveGamma_angle_mul_planeKernel,
    ``RectangleCLTArxivV1.positiveGammaMixedMassKernel_norm_le,
    ``RectangleCLTArxivV1.positiveGammaMixedPlaneKernel_norm_le,
    ``RectangleCLTArxivV1.integrable_gamma_positiveEdge_mass,
    ``RectangleCLTArxivV1.integrable_gamma_positiveEdge_projection,
    ``RectangleCLTArxivV1.integrable_gaussian_positive_soft_pair_mass,
    ``RectangleCLTArxivV1.integrable_gaussian_positive_soft_pair_projection,
    ``RectangleCLTArxivV1.positiveGamma_mass_angle_soft_coarea,
    ``RectangleCLTArxivV1.positiveGamma_projection_angle_soft_coarea,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_coarea_scaled,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_coarea_scaled,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_eq_gamma,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_eq_gamma,
    ``RectangleCLTArxivV1.positiveSoftPairMassConstant,
    ``RectangleCLTArxivV1.positiveSoftPairProjectionConstant,
    ``RectangleCLTArxivV1.positiveSoftPairMassConstant_pos,
    ``RectangleCLTArxivV1.positiveSoftPairProjectionConstant_pos,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_concentrated_base,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_concentrated_base]
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
    ("scope", toJson "Independent actual positive ordered Gamma sums and concentrated-base mean verification"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
