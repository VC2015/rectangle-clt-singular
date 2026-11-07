import RectangleCLTCompanion.SplitV4.GaussianThresholdTubeGeometry
import Lean.Util.CollectAxioms

/-! Strict audit for actual hard Gaussian pair frames and adaptive tube
membership/disjointness, including the ordered-incidence constant two. -/

#print RectangleCLT.Companion.SplitV4.thresholdPairBisector
#print RectangleCLT.Companion.SplitV4.thresholdPairDifference
#print RectangleCLT.Companion.SplitV4.gaussianPairBase
#print RectangleCLT.Companion.SplitV4.gaussianThresholdStratumEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPair_residualNormal_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairBase_frame_levels
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairEvent_mem_adaptiveOutwardTube
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdStratumEvent_indicator_sum_le

#print axioms RectangleCLT.Companion.SplitV4.thresholdPair_residualNormal_eq
#print axioms RectangleCLT.Companion.SplitV4.gaussianPairBase_frame_levels
#print axioms RectangleCLT.Companion.SplitV4.gaussianPairBase_reconstruct
#print axioms RectangleCLT.Companion.SplitV4.gaussianFacetEvent_mem_adaptiveOutwardTube
#print axioms RectangleCLT.Companion.SplitV4.gaussianPairEvent_mem_adaptiveOutwardTube
#print axioms RectangleCLT.Companion.SplitV4.gaussianThresholdStratumEvent_indicator_sum_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.GaussianThresholdTubeGeometry" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Gaussian threshold tube geometry closure"
  logInfo m!"Audited {names.size} Gaussian threshold tube geometry theorem declarations; only the permitted three axioms."
  logInfo "The actual facet and pair events enter disjoint adaptive outward tubes. Ordered pair multiplicity contributes only the universal incidence factor two. No desired threshold estimate, covariance gap, or coarea premise is assumed."
