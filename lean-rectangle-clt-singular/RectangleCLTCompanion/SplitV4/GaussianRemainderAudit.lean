import RectangleCLTCompanion.SplitV4.GaussianRemainder
import Lean.Util.CollectAxioms

/-! Audit of the actual fourth remainder after common-point contraction,
singular Gaussian scaling, and justified segment/product integration. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_trapezoidal_sum_bound

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedGaussianRemainder_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_pairedFourthBudget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.gaussian_trapezoidal_sum_bound,
    ``RectangleCLT.Companion.SplitV4.pairedGaussianRemainder_le,
    ``RectangleCLT.Companion.SplitV4.smootherC4Test_fourthDiagonal_eq_diagonalFourth,
    ``RectangleCLT.Companion.SplitV4.integrable_pairedFourthBudget]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in Gaussian fourth remainder {name}"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited the genuine paired Gaussian fourth remainder, segment Fubini, scaling, and fourth budget integrability."
