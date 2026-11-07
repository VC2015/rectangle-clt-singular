import RectangleCLTCompanion.SplitV4.SymmetricFamilyCertification
import Lean.Util.CollectAxioms

/-! Exact-law contract and strict transitive kernel-axiom audit for Lemma F.3. -/

#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters
#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters.variance
#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters.scale
#print RectangleCLT.Companion.SplitV4.familyBernoulli
#print RectangleCLT.Companion.SplitV4.familySignLaw
#print RectangleCLT.Companion.SplitV4.familyMaskLaw
#print RectangleCLT.Companion.SplitV4.familyRestLaw
#print RectangleCLT.Companion.SplitV4.familySeedLaw
#print RectangleCLT.Companion.SplitV4.familyArrayLaw
#print RectangleCLT.Companion.SplitV4.familyActivated
#print RectangleCLT.Companion.SplitV4.familyObservation
#print RectangleCLT.Companion.SplitV4.familyRawObservations
#print RectangleCLT.Companion.SplitV4.familyNormalizedObservations
#print RectangleCLT.Companion.SplitV4.familyCovariance
#print RectangleCLT.Companion.SplitV4.CommonSymmetricFamilyProperties

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.symmetricFamilyProperties
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyRawObservations_fourth
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyRawObservations_Lq_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyNormalizedObservations_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyNormalizedObservations_rank
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyNormalizedObservations_pairGap

#print axioms RectangleCLT.Companion.SplitV4.symmetricFamilyProperties
#print axioms RectangleCLT.Companion.SplitV4.integral_familyObservation_fourth
#print axioms RectangleCLT.Companion.SplitV4.familyObservation_Lq_envelope

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.SymmetricFamilyFinite",
    "RectangleCLTCompanion.SplitV4.SymmetricFamily", "RectangleCLTCompanion.SplitV4.SymmetricFamilyMoments",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyProperties", "RectangleCLTCompanion.SplitV4.SymmetricFamilyEnvelope",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyCertification"]
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
      throwError "Unexpected axiom {ax} in actual symmetric-family closure"
  logInfo m!"Audited {names.size} symmetric-family theorem declarations; only the permitted three axioms."
  logInfo "Lemma F.3 uses the actual finite product law with independent signs, common activation and coordinate masks; exact covariance, fourth moments, Lq envelope and covariance rank are conclusions."
