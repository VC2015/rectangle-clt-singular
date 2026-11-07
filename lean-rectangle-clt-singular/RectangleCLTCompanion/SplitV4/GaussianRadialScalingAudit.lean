import RectangleCLTCompanion.SplitV4.GaussianRadialScaling
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity_eq

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity_zero

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianLogScaleDensity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_gaussianLogScaleDensity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity_derivative_bound

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_gaussianLogScaleMajorant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianLogScaleIntegral

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianLogScaleIntegral_eq

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_standardGaussian_logScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianThresholdCDF_logScale

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdTrace_eq_radial_first

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[``RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity,
    ``RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity_eq,
    ``RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity_zero,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianLogScaleDensity,
    ``RectangleCLT.Companion.SplitV4.measurable_gaussianLogScaleDensity,
    ``RectangleCLT.Companion.SplitV4.gaussianLogScaleDensity_derivative_bound,
    ``RectangleCLT.Companion.SplitV4.integrable_gaussianLogScaleMajorant,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianLogScaleIntegral,
    ``RectangleCLT.Companion.SplitV4.gaussianLogScaleIntegral_eq,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_standardGaussian_logScale,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_gaussianThresholdCDF_logScale,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdTrace_eq_radial_first]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual hard-test Gaussian radial differentiation"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual Gaussian log-scaling densities, normalization, polynomial-Gaussian domination, integrability, bounded-hard-test differentiation and genuine radial CDF derivative."
