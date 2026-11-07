import RectangleCLTCompanion.SplitV4.Printed.InterpolationSignedHessian
import RectangleCLTCompanion.SplitV4.Printed.EnvelopeConditionalPair
import RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrder
import Lean.Util.CollectAxioms

#print axioms RectangleCLT.Companion.SplitV4.Printed.centered_value_hessian_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.centered_gradient_hessian_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_seededExpectation_signedHessian
#print axioms RectangleCLT.Companion.SplitV4.Printed.conditional_finite_cauchy_schwarz
#print axioms RectangleCLT.Companion.SplitV4.Printed.conditional_finite_pair_contraction
#print axioms RectangleCLT.Companion.SplitV4.Printed.no_uniform_zero_order_averaged_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array String := #[
    "RectangleCLTCompanion.SplitV4.Printed.InterpolationTaylorTwo",
    "RectangleCLTCompanion.SplitV4.Printed.InterpolationSignedHessian",
    "RectangleCLTCompanion.SplitV4.Printed.EnvelopeConditionalPair",
    "RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrder"]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed interpolation closure"
  logInfo m!"Audited {names.size} printed interpolation/envelope theorem declarations; only the permitted three axioms."
