import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenNativeGeometry
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.thresholdPair_frame_levels_of_support,
    ``RectangleCLTArxivV1.actualFacet_pairResidual_nonzero_or_level,
    ``RectangleCLTArxivV1.actualFacet_pair_support_nonparallel]
  let env ← getEnv
  let (_, state) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  for n in state.axioms do
    unless allowed.contains n do
      throwError "Forbidden axiom {n}"
  logInfo m!"PASS: {targets.size} native geometry targets; axioms {state.axioms}"

set_option pp.all true in
#print RectangleCLTArxivV1.thresholdPair_frame_levels_of_support
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacet_pairResidual_nonzero_or_level
set_option pp.all true in
#print RectangleCLTArxivV1.actualFacet_pair_support_nonparallel
