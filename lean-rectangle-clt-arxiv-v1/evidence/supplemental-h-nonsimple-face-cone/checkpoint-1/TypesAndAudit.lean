import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCone
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option pp.all true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let requested : Array String := #["RectangleCLTArxivV1.nonsimpleGeneratedCone","RectangleCLTArxivV1.zero_mem_nonsimpleGeneratedCone","RectangleCLTArxivV1.generator_mem_nonsimpleGeneratedCone","RectangleCLTArxivV1.nonsimpleGeneratedCone_innerDual","RectangleCLTArxivV1.nonsimpleGeneratedCone_coefficient_bound","RectangleCLTArxivV1.nonsimpleGeneratedCone_isClosed","RectangleCLTArxivV1.nonsimpleGeneratedCone_bipolar","RectangleCLTArxivV1.nonsimpleGeneratedCone_mem_iff_polar","RectangleCLTArxivV1.nonsimpleGeneratedCone_no_cancellation","RectangleCLTArxivV1.nonsimpleActiveGeneratedCone","RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_mem_iff","RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_isClosed","RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_mem_iff_polar"]
  let env ← getEnv
  let allNames := env.constants.toList.foldl (fun a (n,_) => a.insert n.toString n)
    ({} : Std.HashMap String Name)
  let targets ← requested.mapM fun s => do
    match allNames[s]? with
    | some n => pure n
    | none => throwError "Missing exact declaration: {s}"
  let (_, axs) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  let bad := axs.axioms.filter fun n => !(#[``propext,``Classical.choice,``Quot.sound]).contains n
  unless bad.isEmpty do throwError "Unexpected axiom: {bad}"
  let mut endpoints : Array Json := #[]
  for n in targets do
    let ci ← getConstInfo n
    let fmt ← liftTermElabM (Meta.ppExpr ci.type)
    let deps := (ci.type.getUsedConstants ++ (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])).toList.eraseDups.toArray
    endpoints := endpoints.push <| Json.mkObj [("name",toJson n.toString),("expanded_type",toJson fmt.pretty),("direct_dependencies",toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [("axiom_union",toJson (axs.axioms.map Name.toString)),("endpoints",Json.arr endpoints)]).compress
