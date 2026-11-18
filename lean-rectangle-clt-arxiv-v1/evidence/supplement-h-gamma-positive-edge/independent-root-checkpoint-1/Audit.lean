import RectangleCLTArxivV1.SupplementalHGammaPositiveEdgeBudget
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_gamma_positive_edge_mass_budget,
    ``RectangleCLTArxivV1.supplementalH_gamma_positive_edge_normSq_budget,
    ``RectangleCLTArxivV1.supplementalH_gamma_ridge_leading_budget,
    ``RectangleCLTArxivV1.supplementalH_gamma_weighted_ridge_budget,
    ``RectangleCLTArxivV1.supplementalH_gamma_positive_edge_mass_budget_small_delta,
    ``RectangleCLTArxivV1.supplementalH_gamma_positive_edge_normSq_budget_small_delta,
    ``RectangleCLTArxivV1.supplementalH_gamma_ridge_leading_budget_small_delta,
    ``RectangleCLTArxivV1.supplementalH_gamma_weighted_ridge_budget_small_delta]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
