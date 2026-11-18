import RectangleCLTArxivV1.SupplementalHSurfaceEstimates
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.localizedGaussianSurfaceConstant,
    ``RectangleCLTArxivV1.localizedGaussianSurfaceConstant_pos,
    ``RectangleCLTArxivV1.ae_localizedGaussianSurfaceEstimates]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
