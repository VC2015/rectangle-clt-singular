import RectangleCLTArxivV1.SupplementalGCapOptimization
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.dimensionCapGain,
    ``RectangleCLTArxivV1.dimensionCapBandwidth,
    ``RectangleCLTArxivV1.dimensionCapRate,
    ``RectangleCLTArxivV1.one_le_dimensionCapGain,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_admissible,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_pos,
    ``RectangleCLTArxivV1.dimensionCap_time_log_le,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_total_cost,
    ``RectangleCLTArxivV1.dimensionCap_large_bandwidth_rate,
    ``RectangleCLTArxivV1.dimensionCap_rate_of_small_bandwidth_estimate,
    ``RectangleCLTArxivV1.dimensionCapRate_le_coefficient,
    ``RectangleCLTArxivV1.dimensionCap_trivial_large_envelope]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
