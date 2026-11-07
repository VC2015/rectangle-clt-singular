import RectangleCLTCompanion.SplitV4.ProductConditional
import Lean.Util.CollectAxioms

/-! Actual independent-copy conditional coefficients and expected-norm
contraction, with a strict transitive axiom audit. These are prerequisites
to the paired Slepian identity; they do not assert its time derivative. -/

#print RectangleCLT.Companion.SplitV4.originalSigma
#print RectangleCLT.Companion.SplitV4.copyAverage
#print RectangleCLT.Companion.SplitV4.copyLargeIncrementMean
#print RectangleCLT.Companion.SplitV4.copyTruncatedCovariance
#print RectangleCLT.Companion.SplitV4.productArrayCopyLaw

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.copyAverage_ae_eq_condExp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_norm_copyAverage_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.productArrayLargeMean_ae_eq_condExp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.productArrayTruncatedCovariance_ae_eq_condExp

#print axioms RectangleCLT.Companion.SplitV4.copyAverage_ae_eq_condExp
#print axioms RectangleCLT.Companion.SplitV4.integral_norm_copyAverage_le
#print axioms RectangleCLT.Companion.SplitV4.productArrayLargeMean_ae_eq_condExp
#print axioms RectangleCLT.Companion.SplitV4.productArrayTruncatedCovariance_ae_eq_condExp

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.ProductConditional then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in product conditional-expectation closure"
  logInfo m!"Audited {names.size} actual product conditional-expectation helpers."
