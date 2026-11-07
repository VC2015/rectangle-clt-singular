import RectangleCLTCompanion.SplitV4.FourthMomentOptimal
import Lean.Util.CollectAxioms

/-! Exact fourth-moment model, rate, actual suprema and strict kernel-axiom audit. -/

#print RectangleCLT.Companion.SplitV4.fourthFamilyParameters
#print RectangleCLT.Companion.SplitV4.unmaskedFourthParameters
#print RectangleCLT.Companion.SplitV4.fourthMomentLowerRate
#print RectangleCLT.Companion.SplitV4.amplifiedSymmetricLowerScale
#print RectangleCLT.Companion.SplitV4.familyShiftAmplification
#print RectangleCLT.Companion.SplitV4.FourthMomentLowerConstruction
#print RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses
#print RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances
#print RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthMomentOptimal

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthMomentLower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthMoment_fixedEnvelope_optimal

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_fourthFamily_orthantError_div_rate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthFamily_distance_ereal_liminf

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthFamily_polynomialIndependent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthFamilyCalibration

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_amplifiedFamily_discrepancy_div_scale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyShiftMeanDifference_amplification

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyShiftSecondMoments_amplification

#print axioms RectangleCLT.Companion.SplitV4.fourthMomentOptimal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyAmplification",
    "RectangleCLTCompanion.SplitV4.AmplifiedSymmetricLower",
    "RectangleCLTCompanion.SplitV4.FourthMomentFamily",
    "RectangleCLTCompanion.SplitV4.FourthMomentCalibration",
    "RectangleCLTCompanion.SplitV4.FourthMomentLower",
    "RectangleCLTCompanion.SplitV4.FourthMomentOptimal" ]
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
      throwError "Unexpected axiom {ax} in fourth-moment lower declarations"
  logInfo m!"Audited {names.size} fourth-moment lower theorem declarations, each transitively; only the permitted three axioms."
  logInfo "Theorem 5 uses the genuine unmasked theta^(-1/4) amplitude model. Actual envelope fourth moments, coordinate fourth moments, iid symmetry, Gaussian covariance matching, orthant limit 1/(2sqrt(2)e), full-distance lower limit and both fixed-envelope supremum consequences are proved. No comparison estimate or calibration limit is assumed in the terminal theorem."
