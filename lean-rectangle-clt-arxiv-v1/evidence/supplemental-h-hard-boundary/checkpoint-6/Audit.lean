import RectangleCLTArxivV1.SupplementalHFrameSections
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFrameProjection_eq_orthogonalProjection,
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_eq_affine_projection,
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_frame_independent,
    ``RectangleCLTArxivV1.gaussianFrame_normalPoint_normSq,
    ``RectangleCLTArxivV1.gaussianFrame_density_eq_normalKernel,
    ``RectangleCLTArxivV1.gaussianFrame_density_frame_independent]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
