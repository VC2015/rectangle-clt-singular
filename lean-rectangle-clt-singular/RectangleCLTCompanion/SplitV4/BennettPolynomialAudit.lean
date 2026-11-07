import RectangleCLTCompanion.SplitV4.BennettPolynomial
import Lean.Util.CollectAxioms

/-! Actual paired-copy polynomial moments, variance tails, both Bennett
optimization regimes, and the complete original-observation Proposition 3. -/

#check RectangleCLT.Companion.SplitV4.identDistrib_pairedIncrement_neg
#check RectangleCLT.Companion.SplitV4.identDistrib_copyLargeIncrement_neg
#check RectangleCLT.Companion.SplitV4.iIndepFun_copyLargeIncrementIntegrand
#check RectangleCLT.Companion.SplitV4.pairedIncrement_norm_moment_budget
#check RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_direct_bound
#check RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_bennett_bound
#check RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_bound
#check RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_rate
#print RectangleCLT.Companion.SplitV4.bennettSmallRegimeConstant
#print RectangleCLT.Companion.SplitV4.bennettPolynomialConstant
#check RectangleCLT.Companion.SplitV4.bennett_small_calibration_identities

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_polynomial_small_regime

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennettPolynomialCLT

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennettPolynomialCLT_observations

#print axioms RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum_bennett_bound
#print axioms RectangleCLT.Companion.SplitV4.pairedTailVariance_polynomial_rate
#print axioms RectangleCLT.Companion.SplitV4.bennett_polynomial_small_regime
#print axioms RectangleCLT.Companion.SplitV4.bennett_polynomial_large_regime
#print axioms RectangleCLT.Companion.SplitV4.bennettPolynomialCLT
#print axioms RectangleCLT.Companion.SplitV4.bennettPolynomialCLT_observations

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.BennettPolynomial then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Bennett polynomial dependency closure"
  logInfo m!"Audited {names.size} Bennett polynomial theorem declarations; only propext, Classical.choice and Quot.sound."
