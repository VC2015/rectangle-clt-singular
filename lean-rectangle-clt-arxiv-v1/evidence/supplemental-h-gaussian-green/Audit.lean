import RectangleCLTArxivV1.SupplementalHGaussianGreen
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.sum_smul_gaussianSectionTangent,
    ``RectangleCLTArxivV1.sum_self_smul_gaussianSectionTangent,
    ``RectangleCLTArxivV1.gaussianSectionPoint_update,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianSection_test,
    ``RectangleCLTArxivV1.gaussianSection_Green_pullback,
    ``RectangleCLTArxivV1.gaussianSection_Green]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
