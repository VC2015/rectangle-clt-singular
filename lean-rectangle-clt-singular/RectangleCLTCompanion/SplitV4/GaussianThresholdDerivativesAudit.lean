import RectangleCLTCompanion.SplitV4.GaussianThresholdAPI
import Lean.Util.CollectAxioms

/-! Genuine hard Gaussian CDF differentiation. The public statements use
actual coordinate derivatives and actual Gaussian section probabilities;
unit linear independence is explicit and no positive gap lower bound is
added. All owned support declarations and their transitive axioms are checked. -/

#print RectangleCLT.Companion.SplitV4.gaussianThresholdCDF
#print RectangleCLT.Companion.SplitV4.gaussianThresholdFirst
#print RectangleCLT.Companion.SplitV4.gaussianThresholdMixed
#print RectangleCLT.Companion.SplitV4.gaussianThresholdSectionProbability
#print RectangleCLT.Companion.SplitV4.gaussianNormalProjection
#print RectangleCLT.Companion.SplitV4.gaussianThresholdMixedSection
#print RectangleCLT.Companion.SplitV4.gaussianThresholdResidualScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_gaussianThresholdCDF
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.standardGaussian_integral_section_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasFDerivAt_gaussianThresholdCDF
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdFirst_eq_normal_section
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_eq_two_normal_section
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThreshold_diagonal_formula
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThreshold_mixed_symmetry
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianThresholdFirst_coordinate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_gaussianThresholdMixed_of_unit_independent

#print axioms RectangleCLT.Companion.SplitV4.gaussianThresholdFirst_eq_normal_section
#print axioms RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_eq_two_normal_section
#print axioms RectangleCLT.Companion.SplitV4.gaussianThreshold_diagonal_formula
#print axioms RectangleCLT.Companion.SplitV4.gaussianThreshold_mixed_symmetry

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `RectangleCLTCompanion.SplitV4.GaussianThresholdSections,
    `RectangleCLTCompanion.SplitV4.GaussianThresholdDerivatives,
    `RectangleCLTCompanion.SplitV4.GaussianFiniteThresholdDerivatives,
    `RectangleCLTCompanion.SplitV4.GaussianThresholdMixedDerivatives,
    `RectangleCLTCompanion.SplitV4.GaussianThresholdDiagonal,
    `RectangleCLTCompanion.SplitV4.GaussianThresholdAPI,
    `RectangleCLTCompanion.SplitV4.ContinuousSecondPartials]
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
      throwError "Unexpected axiom {ax} in genuine hard Gaussian threshold closure"
  logInfo m!"Audited {names.size} genuine hard Gaussian threshold declarations."
