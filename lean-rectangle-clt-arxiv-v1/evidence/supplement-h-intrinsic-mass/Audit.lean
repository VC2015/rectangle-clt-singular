import RectangleCLTArxivV1.SupplementalHIntrinsicMass
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_transitionMassBound,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_oneFaceMass,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_selectorMass]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target}: {axioms.toList}"
