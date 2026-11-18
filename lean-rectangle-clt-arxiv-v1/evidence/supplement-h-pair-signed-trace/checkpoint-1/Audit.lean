import RectangleCLTArxivV1.SupplementalHPairPowerTrace
import RectangleCLTArxivV1.SupplementalHPairTraceRestoration
import RectangleCLTArxivV1.SupplementalHPairPhysicalTrace
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalHPairTraceConstant,
    ``RectangleCLTArxivV1.supplementalHPairTraceConstant_nonneg,
    ``RectangleCLTArxivV1.supplementalHSoftPairPowerTrace,
    ``RectangleCLTArxivV1.supplementalH_softPairPowerTrace_concentrated_base,
    ``RectangleCLTArxivV1.supplementalHSoftPairTrace,
    ``RectangleCLTArxivV1.supplementalHSoftPairTrace_eq_binomial,
    ``RectangleCLTArxivV1.supplementalH_softPairTrace_concentrated_base,
    ``RectangleCLTArxivV1.sum_activeFace_pair_weight_physical,
    ``RectangleCLTArxivV1.supplementalHPairPhysicalTrace,
    ``RectangleCLTArxivV1.integrable_gaussian_pair_radial_selector_physical,
    ``RectangleCLTArxivV1.supplementalHPairPhysicalTrace_eq_softTrace,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairPhysicalTrace]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
