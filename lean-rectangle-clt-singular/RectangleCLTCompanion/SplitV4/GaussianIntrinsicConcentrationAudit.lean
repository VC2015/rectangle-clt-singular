import RectangleCLTCompanion.SplitV4.GaussianIntrinsicConcentration
import Lean.Util.CollectAxioms

/-! Strict audit for whole Gaussian intrinsic concentration with arbitrary
independent shifts and positive common face variance. -/

#print RectangleCLT.Companion.SplitV4.faceProjectionNorm
#print RectangleCLT.Companion.SplitV4.gaussianPolyhedronLayer
#print RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_unit
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift_logarithmic

#print axioms RectangleCLT.Companion.SplitV4.normalizedGaussianFaceRows_unit
#print axioms RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_fixed_shift
#print axioms RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_product
#print axioms RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift
#print axioms RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift_logarithmic
#print axioms RectangleCLT.Companion.SplitV4.integrable_faceProjectionNorm_of_gaussian_law

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.GaussianIntrinsicConcentration" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in whole Gaussian intrinsic concentration closure"
  logInfo m!"Audited {names.size} whole Gaussian intrinsic concentration theorem declarations; only the permitted three axioms."
  logInfo "The actual polyhedral layer under arbitrary measurable independent shift is bounded by min 1 ((2*s/v)*E faceProjectionNorm), and by 4*min 1 (s*sqrt(log(em)/v)). No shift moments, rank condition, or distinct-row premise is present."
