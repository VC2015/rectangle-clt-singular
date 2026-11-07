import RectangleCLTCompanion.SplitV4.ArraySlepian
import Lean.Util.CollectAxioms

/-! Fresh full G.3 audit. The conditional coefficients are concrete copy
integrals; their separately proved conditional-expectation contracts are
included in the transitive-axiom checks below. -/

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.C4Test.arrayCopyPoint

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.C4Test.arrayCopyIncrement

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.C4Test.trapezoidalRemainder

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.productArrayLargeMean_ae_eq_condExp

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.productArrayTruncatedCovariance_ae_eq_condExp

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_paired_stein_of_independent_base,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_array_summand_paired,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_array_paired_sum,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian_paired,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths,
    ``RectangleCLT.Companion.SplitV4.copyArrayLargeMean_ae_eq_condExp,
    ``RectangleCLT.Companion.SplitV4.copyArrayTruncatedCovariance_ae_eq_condExp,
    ``RectangleCLT.Companion.SplitV4.originalSigma_eq_original_coordinate_sigma,
    ``RectangleCLT.Companion.SplitV4.productArrayLargeMean_ae_eq_condExp,
    ``RectangleCLT.Companion.SplitV4.productArrayTruncatedCovariance_ae_eq_condExp]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in paired finite-array Slepian theorem {name}"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited full paired finite-array Slepian derivative, large increments, matrix fluctuation, and signed fourth-order remainder."
