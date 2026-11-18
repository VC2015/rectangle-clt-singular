import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceIndependence
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceNormalCone
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.all true
open Lean Elab Command in
run_cmd do
  let requested : Array String := #[
    "RectangleCLTArxivV1.nonsimpleActiveSet",
    "RectangleCLTArxivV1.mem_nonsimpleActiveSet",
    "RectangleCLTArxivV1.mem_exactStratum_iff_activeSet",
    "RectangleCLTArxivV1.nonsimpleActiveSet_exactStratum",
    "RectangleCLTArxivV1.nonsimpleClosedFace",
    "RectangleCLTArxivV1.exactStratum_subset_nonsimpleClosedFace",
    "RectangleCLTArxivV1.nonsimpleClosedFace_antitone",
    "RectangleCLTArxivV1.nonsimpleClosedFace_subset_iff",
    "RectangleCLTArxivV1.nonsimpleClosedFace_eq_iff",
    "RectangleCLTArxivV1.nonsimpleFaceNormalSpace",
    "RectangleCLTArxivV1.nonsimpleFaceNormalSpace_mono",
    "RectangleCLTArxivV1.nonsimple_normal_mem",
    "RectangleCLTArxivV1.NonsimpleFaceIndex",
    "RectangleCLTArxivV1.nonsimpleFaceIndexFintype",
    "RectangleCLTArxivV1.nonsimpleFaceRepresentative",
    "RectangleCLTArxivV1.nonsimpleFaceRepresentative_mem",
    "RectangleCLTArxivV1.nonsimpleFaceRepresentative_levels",
    "RectangleCLTArxivV1.nonsimpleFaceRepresentative_strict",
    "RectangleCLTArxivV1.nonsimpleFaceRepresentative_activeSet",
    "RectangleCLTArxivV1.nonsimpleFaceIndex_closedFace_injective",
    "RectangleCLTArxivV1.nonsimpleFaceIncidences",
    "RectangleCLTArxivV1.nonsimpleFaceIncidencesFintype",
    "RectangleCLTArxivV1.nonsimpleFaceIncidence_closedFace_subset",
    "RectangleCLTArxivV1.nonsimpleFace_exists_strictPolar",
    "RectangleCLTArxivV1.nonsimpleFace_generated_isOutward",
    "RectangleCLTArxivV1.nonsimple_active_pair_linearIndependent",
    "RectangleCLTArxivV1.nonsimple_active_triple_linearIndependent",
    "RectangleCLTArxivV1.nonsimple_active_triple_euclidean_linearIndependent",
    "RectangleCLTArxivV1.nonsimple_active_rank_le_two_card_le_two",
    "RectangleCLTArxivV1.nonsimpleFaceNormalSpace_finrank_le_card",
    "RectangleCLTArxivV1.nonsimple_ridge_card_eq_two",
    "RectangleCLTArxivV1.nonsimple_ridge_exists_actual_pair_witness",
    "RectangleCLTArxivV1.nonsimple_codimThree_triple_spans",
    "RectangleCLTArxivV1.nonsimple_codimThree_exists_spanning_triple",
    "RectangleCLTArxivV1.nonsimple_codimThree_supporting_pair_strict",
    "RectangleCLTArxivV1.nonsimple_exactStratum_local_feasible_ray",
    "RectangleCLTArxivV1.nonsimple_isOutwardNormal_iff_activeGeneratedCone",
    "RectangleCLTArxivV1.nonsimpleFace_genuine_normalCone",
    "RectangleCLTArxivV1.nonsimple_generator_mem_activeCone",
    "RectangleCLTArxivV1.nonsimple_generated_mem_normalSpace",
    "RectangleCLTArxivV1.nonsimple_activeCone_eq_of_presentation",
    "RectangleCLTArxivV1.nonsimple_activeNormalSpace_eq_of_presentation",
    "RectangleCLTArxivV1.nonsimple_active_normal_ne_zero",
    "RectangleCLTArxivV1.nonsimple_singleton_presentation_active_multiple"]
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
