import RectangleCLTCompanion.SplitV4.RelativeMoments
import Lean.Util.CollectAxioms

/-! Source presence does not establish execution. Running this file prints
the actual moment contracts and rejects extra transitive axioms. -/

#print RectangleCLT.Companion.SplitV4.QuadraticLE
#print RectangleCLT.Companion.SplitV4.relativeThirdMatrix
#print RectangleCLT.Companion.SplitV4.relativeFourthMatrix
#print RectangleCLT.Companion.SplitV4.relativeFreshFourthMatrix
#print RectangleCLT.Companion.SplitV4.RelativeMomentBounds

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope

#print axioms RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope
#print axioms RectangleCLT.Companion.SplitV4.relativeFreshFourthMatrix_eq_independent_copy
#print axioms RectangleCLT.Companion.SplitV4.integrable_relativeFreshFourth_entry

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.RelativeMoments then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative-moment dependency closure"
  logInfo m!"Audited {names.size} relative-moment helper declarations; main relative CLT remains open."
