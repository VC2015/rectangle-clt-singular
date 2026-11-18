import RectangleCLTArxivV1.SupplementalGArrayDecomposition
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.cap_sum_integral_prod_swap,
    ``RectangleCLTArxivV1.cap_integrable_bounded_coefficient_score,
    ``RectangleCLTArxivV1.cap_original_pair_coefficient_abs_le,
    ``RectangleCLTArxivV1.cap_array_fourth_expectation_single_pair,
    ``RectangleCLTArxivV1.cap_product_array_marginal,
    ``RectangleCLTArxivV1.cap_array_fourth_expectation_product_single_pair]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
