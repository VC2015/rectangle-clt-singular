import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

#check RectangleCLT.Companion.SplitV4.Printed.gaussian_norm_tail_union
#check RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_by_union_tail
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_in_probability
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_integrability
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_L1
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability
#check RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold_tail_identity
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_printedNormalMaxThreshold_div_sqrt_two_log
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMoments,
    `RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumQuantile,
    `RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.contains env.header.moduleNames[idx.toNat]! then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in the printed Gaussian maximum moment route"
  let mut seen : NameSet := {}
  let mut todo := #[``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability]
  let mut i := 0
  while i < todo.size do
    let n := todo[i]!
    i := i + 1
    unless seen.contains n do
      seen := seen.insert n
      if n == ``RectangleCLT.Companion.SplitV4.tendsto_gaussianMaximumMean_div_sqrt_log ||
          n == ``RectangleCLT.Companion.SplitV4.integral_gaussian_norm_sq_le ||
          n == ``RectangleCLT.Companion.SplitV4.integral_finiteGaussianMaximum_sq_le then
        throwError "The new printed UI proof still uses the preserved alternative moment endpoint {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? then todo := todo ++ v.getUsedConstants
  logInfo m!"Audited {names.size} printed Gaussian maximum moment/quantile theorems transitively; only the three permitted axioms. Checked {seen.size} constants in the new UI/mean closure; no old mean limit or old quantitative maximum second-moment bound."
