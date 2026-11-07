import RectangleCLTCompanion.SplitV4.SlepianDerivative
import Lean.Util.CollectAxioms

/-! Audit of the actual Slepian derivative and its singular-Gaussian
integration-by-parts step. The expectation, path, and Hessian contraction
are printed explicitly; a supplied analytic identity is not an input. -/

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.C4Test.slepianPoint

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.C4Test.slepianExpectation

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.C4Test.hessianTrace

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.C4Test.integrable_value_of_norm,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation_raw,
    ``RectangleCLT.Companion.SplitV4.C4Test.gaussian_gradient_coordinate_stein,
    ``RectangleCLT.Companion.SplitV4.C4Test.gaussian_gradient_stein,
    ``RectangleCLT.Companion.SplitV4.C4Test.slepian_gaussian_stein,
    ``RectangleCLT.Companion.SplitV4.C4Test.continuousOn_slepianExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.slepianExpectation_zero,
    ``RectangleCLT.Companion.SplitV4.C4Test.slepianExpectation_one,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in Slepian derivative {name}"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited the actual Slepian expectation derivative, finite-moment domination, and Gaussian IBP."
