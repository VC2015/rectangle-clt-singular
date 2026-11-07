import RectangleCLTCompanion.SplitV4.ObservationNormalization
import Lean.Util.CollectAxioms

/-! Fresh execution of this file prints the full Corollary 1 endpoint and
rejects every transitive axiom except the three permitted logical axioms.
Checking in this file alone is not evidence that the audit has run. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsRectangleDistanceCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsCLTExists
#print RectangleCLT.Companion.rectangleDistance

#print axioms RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance
#print axioms RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance_diagonal
#print axioms RectangleCLT.Companion.SplitV4.normalizedObservationsCLT
#print axioms RectangleCLT.Companion.SplitV4.normalizedObservationsRectangleDistanceCLT
#print axioms RectangleCLT.Companion.SplitV4.normalizedObservationsCLTExists

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance,
    ``RectangleCLT.Companion.SplitV4.bounded_normalizedObservationSum_covariance_diagonal,
    ``RectangleCLT.Companion.SplitV4.normalizedObservationsCLT,
    ``RectangleCLT.Companion.SplitV4.normalizedObservationsRectangleDistanceCLT,
    ``RectangleCLT.Companion.SplitV4.normalizedObservationsCLTExists]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in normalized-observation dependency closure"
  logInfo "Audited split-V4 Corollary 1 endpoint and normalization helpers."
