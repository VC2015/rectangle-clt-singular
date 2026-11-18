import RectangleCLTArxivV1.SupplementalGSecondTransfer
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.cap_softFaceDirectional_coordinate_sum,
    ``RectangleCLTArxivV1.cap_softFaceMixedSecond_jet,
    ``RectangleCLTArxivV1.cap_softFaceMixedSecond_row,
    ``RectangleCLTArxivV1.cap_hasDerivAt_softFaceDirectional_coordinate_line,
    ``RectangleCLTArxivV1.cap_softFaceMixedSecond_quadratic,
    ``RectangleCLTArxivV1.cap_secondHermite_softFace_transfer,
    ``RectangleCLTArxivV1.capSoftFaceSecond_smul,
    ``RectangleCLTArxivV1.cap_secondHermite_pair_transfer_scaled]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
