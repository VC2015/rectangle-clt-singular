import RectangleCLTCompanion.SplitV4.ModerateTailGeneral
import Lean.Util.CollectAxioms

/-! Complete iid-free Lemma F.1 contract and strict transitive axiom audit. -/
#print RectangleCLT.Companion.SplitV4.moderateScalarTilt
#print RectangleCLT.Companion.SplitV4.moderateTiltMoment
#print RectangleCLT.Companion.SplitV4.moderateTiltFourthCumulant
#print RectangleCLT.Companion.SplitV4.moderateArrayCGF
#print RectangleCLT.Companion.SplitV4.moderateArrayGamma
#print RectangleCLT.Companion.SplitV4.moderateScalarSum
#print RectangleCLT.Companion.SplitV4.moderateProductWeightedTail
#print RectangleCLT.Companion.SplitV4.moderateTaylorConstant
#print RectangleCLT.Companion.SplitV4.moderateTailSmallConstant
#print RectangleCLT.Companion.SplitV4.moderateTailRemainderConstant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformScalarModerateTail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateScalarTail_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateArrayCGF_cubic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exists_moderateArrayMean_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.existsUnique_moderateArrayMean_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateTiltFourthCumulant_abs_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderateProduct_strict_tail_standardized

#print axioms RectangleCLT.Companion.SplitV4.uniformScalarModerateTail
#print axioms RectangleCLT.Companion.SplitV4.moderateScalarTail_bound
#print axioms RectangleCLT.Companion.SplitV4.moderateProductTail_large_threshold

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.ModerateCumulants",
    "RectangleCLTCompanion.SplitV4.ModerateTiltBounds", "RectangleCLTCompanion.SplitV4.ModerateFourthCumulant",
    "RectangleCLTCompanion.SplitV4.ModerateArrayCumulants", "RectangleCLTCompanion.SplitV4.ModerateInverseTilt",
    "RectangleCLTCompanion.SplitV4.ModerateProductCumulants", "RectangleCLTCompanion.SplitV4.ModerateSmallThreshold",
    "RectangleCLTCompanion.SplitV4.ModerateProductTail", "RectangleCLTCompanion.SplitV4.ModerateTail",
    "RectangleCLTCompanion.SplitV4.ModerateTailGeneral"]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in iid-free moderate-tail closure"
  logInfo m!"Audited {names.size} iid-free moderate-tail theorem declarations; only the permitted three axioms."
  logInfo "Lemma F.1 is proved for arbitrary independent centered bounded scalar variables. Absolute constants precede all dimensions and laws; the tail is strict and its positivity is proved, including atoms at zero."
