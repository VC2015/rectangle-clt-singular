import RectangleCLTArxivV1.SupplementalGSeededPairTransfer
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.cap_secondHermite_pair_halves_transfer,
    ``RectangleCLTArxivV1.cap_random_pair_halves_transfer,
    ``RectangleCLTArxivV1.cap_array_middle_swap,
    ``RectangleCLTArxivV1.cap_fixed_gaussian_score_copy_integrable,
    ``RectangleCLTArxivV1.cap_seeded_pair_contribution_eq_second]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
