import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeEnumeration
import RectangleCLTArxivV1.SupplementalHNonsimplePrintedQuantities
import RectangleCLTArxivV1.SupplementalHNonsimplePrintedGreen
import RectangleCLTArxivV1.SupplementalHNonsimpleSquareGreen
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.all true
open Lean Elab Command in
run_cmd do
  let requested : Array String := #[
    "RectangleCLTArxivV1.strictRidgeInterior_iff_actual_ridge_face",
    "RectangleCLTArxivV1.half_native_pair_sum_eq_actual_ridge_sum",
    "RectangleCLTArxivV1.nonsimpleActualRidgeAngle",
    "RectangleCLTArxivV1.nonsimpleActualRidgeAngle_eq_pair",
    "RectangleCLTArxivV1.nonsimpleActualRidgeAngle_nonneg",
    "RectangleCLTArxivV1.nonsimpleActualRidgeLeading",
    "RectangleCLTArxivV1.nonsimpleActualIncidenceConormal",
    "RectangleCLTArxivV1.nonsimpleActualIncidenceConormal_of_incident",
    "RectangleCLTArxivV1.nonsimpleActualIncidenceConormal_of_not_incident",
    "RectangleCLTArxivV1.nonsimpleActualConormalSum",
    "RectangleCLTArxivV1.nonsimpleActualThirdBoundary",
    "RectangleCLTArxivV1.nonsimpleActualThirdBoundary_eq_ridge_incidence_sum",
    "RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_Green_actualFaces",
    "RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_Green_actualFaces_compact",
    "RectangleCLTArxivV1.exists_actual_facet_ridge_Green",
    "RectangleCLTArxivV1.nonsimpleSquare_printed_ridge_Green",
    "RectangleCLTArxivV1.nonsimpleSquare_actualVertex_printed_spherical_balance",
    "RectangleCLTArxivV1.nonsimpleSquare_actualVertex_printed_spherical_norm_bound"]
  let env ← getEnv
  let allNames := env.constants.toList.foldl (fun acc (n, _) => acc.insert n.toString n)
    ({} : Std.HashMap String Name)
  let targets ← requested.mapM fun s => do
    match allNames[s]? with
    | some n => pure n
    | none => throwError "Missing exact mapped declaration: {s}"
  -- Checking the complete union implies that every individual target closure
  -- contains only allowed axioms; the shared visited state avoids replay.
  let (_, axiomState) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  let forbidden := axiomState.axioms.filter fun n =>
    !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n
  unless forbidden.isEmpty do throwError "Unexpected kernel axiom in mapped union: {forbidden}"
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := (ci.type.getUsedConstants ++
      (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])).toList.eraseDups.toArray
    let projectDeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" || s.startsWith "Kane" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining" ||
        s.startsWith "_private.Kane"
    graph := graph.push <| Json.mkObj [("name", toJson target.toString),
      ("direct_project_dependencies", toJson (projectDeps.map Name.toString))]
    queue := projectDeps.toList ++ queue
    if targets.contains target then
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      let mod := (env.getModuleIdxFor? target).bind fun i => env.header.moduleNames[i.toNat]?
      endpoints := endpoints.push <| Json.mkObj [("name", toJson target.toString),
        ("expanded_type", toJson ty), ("direct_dependencies", toJson (deps.map Name.toString)),
        ("kernel_import_module", toJson (mod.map Name.toString))]
  IO.println <| (Json.mkObj [("scope", toJson "Exact fresh mapped types and kernel project graph; no blanket legacy-CLT exclusion"),
    ("axiom_strategy", toJson "One complete shared kernel axiom-union over every requested declaration; allowed union implies each closure is allowed"),
    ("axiom_union", toJson (axiomState.axioms.map Name.toString)),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
