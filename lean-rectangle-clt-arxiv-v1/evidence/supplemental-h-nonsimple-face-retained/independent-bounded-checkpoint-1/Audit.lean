import RectangleCLTArxivV1.SupplementalHNonsimpleFaceRetained
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.nonsimple_retained_presentation_active_multiple_of_exactStratum,
    ``RectangleCLTArxivV1.nonsimple_retained_presentation_active_multiple]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
