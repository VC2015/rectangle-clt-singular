import RectangleCLTArxivV1.LowerWidthBudget
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.lowerWidthBudget_linear,
    ``RectangleCLTArxivV1.lowerWidthBudget_shift_square,
    ``RectangleCLTArxivV1.lowerWidthBudget_coordinate_square,
    ``RectangleCLTArxivV1.lowerWidthBudget_range,
    ``RectangleCLTArxivV1.lowerWidthBudget_combined]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
