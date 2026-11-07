import RectangleCLTCompanion.SplitV4.UnrestrictedGaussianComparison
import Lean.Util.CollectAxioms

/-! Actual unrestricted Gaussian comparison types and strict transitive
axiom audit. This is the Gaussian-to-Gaussian input to Appendix E, distinct
from the large-increment non-Gaussian comparison required in Appendix G. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparison_smooth_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparison_of_marginal_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparisonExists

#print RectangleCLT.proxyCovarianceDiscrepancy
#print RectangleCLT.Companion.rectangleDistance

#print axioms RectangleCLT.Companion.SplitV4.gaussianComparison_expected_variance_le
#print axioms RectangleCLT.Companion.SplitV4.gaussianComparison_second_sum_le
#print axioms RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparison_smooth_le
#print axioms RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparison
#print axioms RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparison_of_marginal_lower_bound
#print axioms RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparisonExists

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.UnrestrictedGaussianComparison then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in unrestricted Gaussian comparison closure"
  logInfo m!"Audited {names.size} unrestricted Gaussian comparison declarations."
