import RectangleCLTCompanion.SplitV4.SymmetricBoundedLower
import Lean.Util.CollectAxioms

/-! Strict transitive audit for the actual-law bounded symmetric lower construction
and all new owned maximum, local-comparison, and calibration support. -/

#print RectangleCLT.Companion.SplitV4.boundedFamilyParameters
#print RectangleCLT.Companion.SplitV4.familyArrayLaw
#print RectangleCLT.Companion.SplitV4.familyRawObservations
#print RectangleCLT.Companion.SplitV4.familyNormalizedObservations
#print RectangleCLT.Companion.SplitV4.familyComparisonDistance
#print RectangleCLT.Companion.SplitV4.familyGaussianSquareFactor
#print RectangleCLT.Companion.SplitV4.familyOrthant
#print RectangleCLT.Companion.SplitV4.boundedSymmetricLowerRate
#print RectangleCLT.Companion.rectangleDistance
#print RectangleCLT.Companion.SplitV4.BoundedSymmetricLowerConstruction

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedSymmetricLower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_orthantError_div_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedFamily_distance_ereal_liminf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_boundedFamily_distance_div_rate_ge
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_discrepancy_div_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyLocal_master_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyRademacherMaximum_local_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyMaskedSignMaximum_all_active_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyGaussianSquareFactor_gram

#print axioms RectangleCLT.Companion.SplitV4.boundedSymmetricLower

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyMaximum",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyCount",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyCountBounds",
    "RectangleCLTCompanion.SplitV4.RectangularGaussianLaw",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyGaussian",
    "RectangleCLTCompanion.SplitV4.FiniteProductColumns",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyActivation",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyAllActive",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyUnmasked",
    "RectangleCLTCompanion.SplitV4.RademacherCalibration",
    "RectangleCLTCompanion.SplitV4.RademacherLocalComparison",
    "RectangleCLTCompanion.SplitV4.LocalizedShiftComparison",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyShifts",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyMaster",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyOrthant",
    "RectangleCLTCompanion.SplitV4.SymmetricBoundedParameters",
    "RectangleCLTCompanion.SplitV4.SymmetricBoundedShiftLimits",
    "RectangleCLTCompanion.SplitV4.SymmetricBoundedMoments",
    "RectangleCLTCompanion.SplitV4.SymmetricBoundedRademacher",
    "RectangleCLTCompanion.SplitV4.SymmetricBoundedLower" ]
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
      throwError "Unexpected axiom {ax} in bounded symmetric lower declarations"
  logInfo m!"Audited {names.size} bounded symmetric lower theorem declarations, each transitively; only the permitted three axioms."
  logInfo "Theorem 4 is proved for the genuine independent finite sign/activation model: centered symmetric raw observations bounded by two, unit marginal variances, matching singular Gaussian, actual detecting orthant limit 1/(8e), and full rectangle-distance extended-real lower limit. No probability-comparison or asymptotic-calibration conclusion is a premise."
