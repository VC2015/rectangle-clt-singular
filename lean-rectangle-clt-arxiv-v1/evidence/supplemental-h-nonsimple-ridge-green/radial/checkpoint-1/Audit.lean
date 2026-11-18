import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenRadial
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.actualFacet_localFiniteThresholdRegularity,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_of_actualFacets,
    ``RectangleCLTArxivV1.exists_actual_facet_radial_green]
  let env ← getEnv
  let (_, axiomState) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  for n in axiomState.axioms do
    unless allowed.contains n do
      throwError "Nonsimple radial supplier depends on forbidden axiom {n}"
  logInfo m!"PASS: {targets.size} radial Green targets; shared axioms {axiomState.axioms}"

set_option pp.all true in
#print RectangleCLTArxivV1.actualFacet_localFiniteThresholdRegularity
set_option pp.all true in
#print RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_of_actualFacets
set_option pp.all true in
#print RectangleCLTArxivV1.exists_actual_facet_radial_green
