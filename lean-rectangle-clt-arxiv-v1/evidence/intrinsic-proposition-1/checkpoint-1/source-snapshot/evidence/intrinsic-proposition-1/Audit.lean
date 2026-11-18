import RectangleCLTArxivV1.IntrinsicDerivativeProposition
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.intrinsicDerivativeConstant_pos,
    ``RectangleCLTArxivV1.intrinsicDerivativeConstant_ge_direct,
    ``RectangleCLTArxivV1.intrinsicDerivativeConstant_ge_seeded,
    ``RectangleCLTArxivV1.initializationDiscrepancy_intrinsic_le,
    ``RectangleCLTArxivV1.intrinsic_derivative_proposition,
    ``RectangleCLTArxivV1.proposition_1_intrinsic_derivatives]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
