import RectangleCLTArxivV1.PositiveGammaMeans
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.positiveSoftPairMassConstant,
    ``RectangleCLTArxivV1.positiveSoftPairProjectionConstant,
    ``RectangleCLTArxivV1.positiveSoftPairMassConstant_pos,
    ``RectangleCLTArxivV1.positiveSoftPairProjectionConstant_pos,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_concentrated_base,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_concentrated_base]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
