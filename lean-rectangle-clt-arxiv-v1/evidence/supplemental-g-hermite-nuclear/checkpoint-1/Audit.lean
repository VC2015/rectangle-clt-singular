import RectangleCLTArxivV1.SupplementalGHermiteNuclearMoments
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.cap_standardRealGaussian_integral_fourth,
    ``RectangleCLTArxivV1.cap_standardGaussian_integral_coordinate_fourth,
    ``RectangleCLTArxivV1.capSecondHermite_nuclear_le,
    ``RectangleCLTArxivV1.capThirdHermite_nuclear_le,
    ``RectangleCLTArxivV1.capThirdHermiteMatrix_nuclear_integrable,
    ``RectangleCLTArxivV1.capSecondHermite_nuclear_integrable,
    ``RectangleCLTArxivV1.capSecondHermite_integral_nuclear_le,
    ``RectangleCLTArxivV1.capThirdHermite_integral_nuclear_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
