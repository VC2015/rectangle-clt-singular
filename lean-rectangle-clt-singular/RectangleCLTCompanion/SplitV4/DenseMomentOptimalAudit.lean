import RectangleCLTCompanion.SplitV4.DenseMomentOptimal
import Lean.Util.CollectAxioms

/-! Strict exact-statement and transitive axiom audit of the full fixed-B q>4 lower result. -/

#print RectangleCLT.Companion.SplitV4.denseFamilyParameters
#print RectangleCLT.Companion.SplitV4.unmaskedAmplitudeParameters
#print RectangleCLT.Companion.SplitV4.denseMomentLowerRate
#print RectangleCLT.Companion.SplitV4.denseLowerRateConversion
#print RectangleCLT.Companion.SplitV4.denseLowerConstant
#print RectangleCLT.Companion.SplitV4.DenseMomentLowerConstruction
#print RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses
#print RectangleCLT.Companion.SplitV4.polynomialClassDistances
#print RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseMomentOptimal

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseMomentLower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseMoment_uniform_comparison

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_denseFamily_orthantError_div_rate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseFamily_distance_ereal_liminf

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_denseFamily_polynomialIndependent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseFamilyCalibration

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialWorstDistance_envelope_le

#print axioms RectangleCLT.Companion.SplitV4.denseMomentOptimal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    "RectangleCLTCompanion.SplitV4.DenseMomentFamily",
    "RectangleCLTCompanion.SplitV4.DenseMomentCalibration",
    "RectangleCLTCompanion.SplitV4.DenseMomentLower",
    "RectangleCLTCompanion.SplitV4.DenseMomentOptimal" ]
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
      throwError "Unexpected axiom {ax} in dense lower declarations"
  logInfo m!"Audited {names.size} fixed-envelope q>4 lower theorem declarations, each transitively; only the permitted three axioms."
  logInfo "Theorem 7 is proved for actual iid centrally symmetric observations in the literal polynomial class. Its terminal hypotheses are only q>4, B>=2, m tending to infinity and V tending to zero. The full rectangle-distance lower limit is strictly positive; both actual suprema satisfy the stated lower rate and the upper logarithmic comparison, with upper coefficient depending only on q."
