import RectangleCLTCompanion.SplitV4.Printed.PolynomialAssembly
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Strict audit of the added G.1/E.1/Propositions 2–3/Theorem 2 printed
routes. Every theorem in the seven owned extension modules is audited
transitively. The new Proposition 2 endpoint is also checked not to use the
historical bounded CLT that the earlier certificate retained. -/

#check RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf
#check RectangleCLT.Companion.SplitV4.Printed.expected_le_exp_moment_by_tail_integration
#check RectangleCLT.Companion.SplitV4.Printed.bounded_vector_bernstein_maximum_by_tail_integration
#check RectangleCLT.Companion.SplitV4.Printed.gaussianComparisonWithLargeIncrementRemainders
#check RectangleCLT.Companion.SplitV4.Printed.expected_maximum_under_envelope_moment
#check RectangleCLT.Companion.SplitV4.Printed.abs_good_covariance_le_envelope_sq
#check RectangleCLT.Companion.SplitV4.Printed.conditionalRetained_marginal_half_lower_bound
#check RectangleCLT.Companion.SplitV4.Printed.conditionalGoodKernel_ownGaussian_rectangle_error_le
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransfer
#check RectangleCLT.Companion.SplitV4.Printed.bennettPolynomialCLT_observations
#check RectangleCLT.Companion.SplitV4.Printed.polynomialMomentCLTExists

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `RectangleCLTCompanion.SplitV4.Printed.Bernstein,
    `RectangleCLTCompanion.SplitV4.Printed.EnvelopeMaximum,
    `RectangleCLTCompanion.SplitV4.Printed.LargeIncrement,
    `RectangleCLTCompanion.SplitV4.Printed.PolynomialMoments,
    `RectangleCLTCompanion.SplitV4.Printed.Polynomial,
    `RectangleCLTCompanion.SplitV4.Printed.Bennett,
    `RectangleCLTCompanion.SplitV4.Printed.PolynomialAssembly]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.contains env.header.moduleNames[idx.toNat]! then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in the printed large-increment/polynomial dependency closure"
  let mut visited : NameSet := {}
  let mut pending := #[``RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransfer]
  let mut i := 0
  while i < pending.size do
    let n := pending[i]!
    i := i + 1
    unless visited.contains n do
      visited := visited.insert n
      if n == ``RectangleCLT.Companion.bounded_unrestrictedCLT_after_standardization ||
          n == ``RectangleCLT.Companion.unrestrictedCLT then
        throwError "The new printed conditional route still depends on historical bounded endpoint {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          pending := pending ++ v.getUsedConstants
  logInfo m!"Audited {names.size} added printed G.1/E.1/polynomial theorem declarations transitively; only propext, Classical.choice and Quot.sound. Checked {visited.size} constants in the new Proposition 2 closure: current relative theorem route, no historical unrestricted bounded endpoint."
