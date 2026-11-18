import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenFrame
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryFrame,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryLevels,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryFrame_orthonormal,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryFrame_span,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint_native,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint_supporting_levels,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint_mem_span]
  let env ← getEnv
  let (_, state) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  for n in state.axioms do
    unless allowed.contains n do
      throwError "Forbidden axiom {n}"
  logInfo m!"PASS: {targets.size} actual boundary-frame declarations; axioms {state.axioms}"

set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryFrame
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryLevels
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryFrame_orthonormal
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryFrame_span
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint_native
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint_supporting_levels
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.nativeBoundaryPoint_mem_span
