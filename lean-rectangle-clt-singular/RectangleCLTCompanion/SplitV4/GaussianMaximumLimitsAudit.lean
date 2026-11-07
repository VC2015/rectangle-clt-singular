import RectangleCLTCompanion.SplitV4.GaussianMaximumLimits
import Lean.Util.CollectAxioms

/-! Exact maximum law and genuine C1 ramp certificates. The interval
implication explicitly records its smooth-test premise; it is a helper
until the intrinsic Gaussian argument supplies that premise. -/

#print RectangleCLT.Companion.SplitV4.gaussianAffineMaximum
#print RectangleCLT.Companion.SplitV4.gaussianIntervalRampDensity
#print RectangleCLT.Companion.SplitV4.gaussianIntervalRamp
#print RectangleCLT.Companion.SplitV4.gaussianIntervalRampDerivative

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.standardGaussian_affine_hyperplane_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_noAtoms
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_affine_branches_ae_distinct_rows_ne
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntervalRamp_hasDerivAt
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.interval_probability_le_of_smooth_tests
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.centered_interval_probability_le_of_smooth_tests
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.centered_cdf_increment_le_of_smooth_tests

#print axioms RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_noAtoms
#print axioms RectangleCLT.Companion.SplitV4.centered_interval_probability_le_of_smooth_tests

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.GaussianMaximumLimits then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Gaussian maximum limits closure"
  logInfo m!"Audited {names.size} Gaussian maximum law and ramp declarations."
