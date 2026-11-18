import RectangleCLTArxivV1.ActualHFourthPrinted
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.theoremH3BandwidthConstant,
    ``RectangleCLTArxivV1.theoremH3BandwidthConstant_ge_one,
    ``RectangleCLTArxivV1.theoremH3BandwidthConstant_pos,
    ``RectangleCLTArxivV1.theoremH3BandwidthConstant_controls_width,
    ``RectangleCLTArxivV1.lemma_H3_fourth_derivative]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
