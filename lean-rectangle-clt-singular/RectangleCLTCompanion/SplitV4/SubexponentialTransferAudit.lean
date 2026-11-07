import RectangleCLTCompanion.SplitV4.SubexponentialTransfer
import Lean.Util.CollectAxioms

/-! Run to inspect the exact supremum endpoint and reject nonstandard
axioms in its transitive proof dependencies. Source presence alone is not
evidence that the audit has executed. -/

#print RectangleCLT.Companion.psi1Scales
#print RectangleCLT.Companion.psi1Norm
#print RectangleCLT.Companion.Psi1IndependentHypotheses
#print RectangleCLT.Companion.rectangleDistance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLT_psi1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLTExists

#print axioms RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLT_psi1
#print axioms RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLTExists

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLT_psi1,
    ``RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLTExists]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in split-V4 sub-exponential dependency closure"
  logInfo "Audited split-V4 Corollary 2 rectangle-distance endpoints."
