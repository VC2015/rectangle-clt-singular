import RectangleCLTCompanion.SplitV4.BoundedFaceIntrinsicConcentration
import Lean.Util.CollectAxioms

/-! Actual arbitrary-face wrapper of the bounded half of Lemma 1. -/
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_face_intrinsic_concentration
#print axioms RectangleCLT.Companion.SplitV4.bounded_face_intrinsic_concentration

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.BoundedFaceIntrinsicConcentration" then
          names := names.push n
  unless names.size > 0 do
    throwError "No arbitrary-face bounded concentration declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in arbitrary-face bounded concentration closure"
  logInfo m!"Audited all {names.size} arbitrary-face bounded concentration theorem declarations."
