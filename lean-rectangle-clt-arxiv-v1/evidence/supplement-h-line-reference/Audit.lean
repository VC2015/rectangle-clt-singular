import RectangleCLTArxivV1.SupplementalHLineReference
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_rankOne_mulVec,
    ``RectangleCLTArxivV1.supplementalH_rankOne_transpose,
    ``RectangleCLTArxivV1.supplementalH_rankOne_idempotent,
    ``RectangleCLTArxivV1.supplementalH_rankOne_coordinate,
    ``RectangleCLTArxivV1.supplementalH_rankOne_normSq,
    ``RectangleCLTArxivV1.supplementalH_cubic_mean_reference_bound,
    ``RectangleCLTArxivV1.supplementalH_cubic_mean_reference_bound_all]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target}: {axioms.toList}"
