import RectangleCLTArxivV1.SupplementalGSmallAngle
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.measurable_capSoftFaceSecond_comp,
    ``RectangleCLTArxivV1.cap_pair_coefficient_integrable,
    ``RectangleCLTArxivV1.cap_small_angle_copy_bound,
    ``RectangleCLTArxivV1.cap_softFaceWeight_pair_eq,
    ``RectangleCLTArxivV1.cap_small_angle_actual_expectation,
    ``RectangleCLTArxivV1.cap_small_angle_complementary_remainder]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
