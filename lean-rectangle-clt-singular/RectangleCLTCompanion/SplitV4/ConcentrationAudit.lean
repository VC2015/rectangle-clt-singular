import RectangleCLTCompanion.SplitV4.Concentration
import Lean.Util.CollectAxioms

/-! Whole-statement audit for Lemma 1 (`lem:concentration`). Both complete
model classes are printed, with the constant quantified before all model
data. The Gaussian coefficient `2` and original `L=log(e p)` are explicit.
-/

#print RectangleCLT.Companion.SplitV4.faceProjectionNorm
#print RectangleCLT.Companion.SplitV4.gaussianPolyhedronLayer
set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.BoundedConcentrationContract
set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.GaussianConcentrationContract
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.lemma_concentration

#print axioms RectangleCLT.Companion.SplitV4.dimensionLog_double_le
#print axioms RectangleCLT.Companion.SplitV4.bounded_face_intrinsic_concentration_signed_faces
#print axioms RectangleCLT.Companion.SplitV4.gaussian_intrinsic_concentration_signed_faces
#print axioms RectangleCLT.Companion.SplitV4.lemma_concentration

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.Concentration" then
          names := names.push n
  unless names.size > 0 do
    throwError "No whole Lemma 1 theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in whole Lemma 1 dependency closure"
  logInfo m!"Audited all {names.size} whole Lemma 1 theorem declarations; only the three permitted axioms."
