import RectangleCLTArxivV1.SupplementalGCapIntegration
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.cap_inv_sqrt_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_inv_mul_sqrt_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_integral_inv_sqrt,
    ``RectangleCLTArxivV1.cap_integral_inv_mul_sqrt,
    ``RectangleCLTArxivV1.cap_const_inv_continuousOn,
    ``RectangleCLTArxivV1.cap_const_inv_sqrt_continuousOn,
    ``RectangleCLTArxivV1.cap_const_inv_mul_sqrt_continuousOn,
    ``RectangleCLTArxivV1.cap_integral_const_inv,
    ``RectangleCLTArxivV1.cap_integral_const_inv_sqrt,
    ``RectangleCLTArxivV1.cap_integral_const_inv_mul_sqrt,
    ``RectangleCLTArxivV1.cap_integral_single_minimum,
    ``RectangleCLTArxivV1.cap_integral_pair_minimum_crossing,
    ``RectangleCLTArxivV1.cap_integral_pair_minimum,
    ``RectangleCLTArxivV1.cap_seed_single_ratio,
    ``RectangleCLTArxivV1.cap_seed_pair_ratio,
    ``RectangleCLTArxivV1.cap_single_ratio_log_le,
    ``RectangleCLTArxivV1.cap_pair_ratio_log_le,
    ``RectangleCLTArxivV1.cap_integrated_remainder_dimension_bound,
    ``RectangleCLTArxivV1.cap_integrated_remainder_direct_bound,
    ``RectangleCLTArxivV1.cap_integrated_remainder_min_bound]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
