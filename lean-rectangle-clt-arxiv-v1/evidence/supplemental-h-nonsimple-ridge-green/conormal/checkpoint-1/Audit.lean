import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenConormal
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.ActualRidgeFacetPresentation.originalNormal_inner_outwardConormal_eq_scale,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.originalNormal_inner_outwardConormal_pos,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.outwardConormal_unique]
  let env ← getEnv
  let (_, state) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  for n in state.axioms do
    unless allowed.contains n do
      throwError "Forbidden axiom {n}"
  logInfo m!"PASS: {targets.size} actual conormal targets; axioms {state.axioms}"

set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.originalNormal_inner_outwardConormal_eq_scale
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.originalNormal_inner_outwardConormal_pos
set_option pp.all true in
#print RectangleCLTArxivV1.ActualRidgeFacetPresentation.outwardConormal_unique
