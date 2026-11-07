import RectangleCLTCompanion.SplitV4.GaussianFaceTransfer
import Lean.Util.CollectAxioms

/-! Exact Gaussian pushforward, polyhedral supremum, and bounded-envelope
transfer audit. This does not certify the other parts of Corollary 3. -/

#print RectangleCLT.Companion.SplitV4.polyhedronError
#print RectangleCLT.Companion.SplitV4.polyhedralDistance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianLaw_map_mulVec_eq_of_gram

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polyhedralDistance_le_projected_rectangleDistance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedPolyhedralEnvelopeCLT

#print axioms RectangleCLT.Companion.SplitV4.gaussianLaw_map_mulVec_eq_of_gram
#print axioms RectangleCLT.Companion.SplitV4.polyhedralDistance_le_projected_rectangleDistance
#print axioms RectangleCLT.Companion.SplitV4.boundedPolyhedralEnvelopeCLT

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.gaussianLaw_map_mulVec,
    ``RectangleCLT.Companion.SplitV4.gaussianLaw_map_mulVec_eq_of_gram,
    ``RectangleCLT.Companion.SplitV4.facePolyhedron_eq_preimage_lowerOrthant,
    ``RectangleCLT.Companion.SplitV4.measurableSet_facePolyhedron,
    ``RectangleCLT.Companion.SplitV4.polyhedronError_le_one,
    ``RectangleCLT.Companion.SplitV4.polyhedralErrors_bddAbove,
    ``RectangleCLT.Companion.SplitV4.polyhedronError_eq_projected_rectangleError,
    ``RectangleCLT.Companion.SplitV4.polyhedralDistance_le_projected_rectangleDistance,
    ``RectangleCLT.Companion.SplitV4.sumVector_mulVec,
    ``RectangleCLT.Companion.SplitV4.boundedPolyhedralEnvelopeCLT]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Gaussian face-transfer closure"
  logInfo "Audited 10 Gaussian face-transfer declarations, including the actual bounded-envelope polyhedral endpoint."
  logInfo "The relative-moment, polynomial and sub-exponential parts of Corollary 3 remain separate obligations."
