import RectangleCLTArxivV1.SupplementalHSubsystemConcentration
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.subsystemExtendedThresholds,
    ``RectangleCLTArxivV1.subsystemExtendedThresholds_selected,
    ``RectangleCLTArxivV1.subsystemExtendedThresholds_unused,
    ``RectangleCLTArxivV1.eventually_mem_facePolyhedron_subsystem,
    ``RectangleCLTArxivV1.eventually_mem_faceLayer_subsystem,
    ``RectangleCLTArxivV1.tendsto_real_faceLayer_subsystem,
    ``RectangleCLTArxivV1.faceLayer_concentration_subsystem]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
