import RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea
import Lean.Util.CollectAxioms

/-! Exact two-normal Gaussian measure-preserving and coarea contracts.
The mixed derivative is the actual derivative from the hard-CDF chain. -/

#print RectangleCLT.Companion.SplitV4.gaussianPairSectionMap
#print RectangleCLT.Companion.SplitV4.gaussianPairSectionPoint
#print RectangleCLT.Companion.SplitV4.gaussianPairBase
#print RectangleCLT.Companion.SplitV4.gaussianPairConditionalDirection
#print RectangleCLT.Companion.SplitV4.gaussianPairConditionalLevel

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairSectionMap_measurePreserving
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_gaussianPairSectionMap_iff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.standardGaussian_integral_pair_sections
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairConditionalBase_eq_pairBase
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPair_conditional_density_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_eq_pairBase

#print axioms RectangleCLT.Companion.SplitV4.gaussianPairSectionMap_measurePreserving
#print axioms RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_eq_pairBase

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `RectangleCLTCompanion.SplitV4.GaussianPairSections,
    `RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.contains env.header.moduleNames[idx.toNat]! then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in genuine two-normal Gaussian coarea closure"
  logInfo m!"Audited {names.size} genuine two-normal Gaussian coarea declarations."
