import RectangleCLTArxivV1.LowerFourthPrintedMoments
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.lower_fourth_power_add_le,
    ``RectangleCLTArxivV1.lowerFamilyRawObservations_fourth_envelope_le,
    ``RectangleCLTArxivV1.eventually_lowerFourth_printed_envelope,
    ``RectangleCLTArxivV1.eventually_lowerFourth_variance_sqrt]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
