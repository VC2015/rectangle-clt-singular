import RectangleCLTCompanion.SplitV4.ConditionalPolynomialOptimization
import Lean.Util.CollectAxioms

/-! Proposition 2: exact polynomial envelope rate, actual normalized
observations, no coordinate fourth-moment premise, and universal constant. -/

#print RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransferConstant
#print RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransferRate
#print RectangleCLT.Companion.SplitV4.polynomialEnvelopeV
#print RectangleCLT.Companion.SplitV4.polynomialTruncationThreshold

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransferRate_eq_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialTruncation_first_term
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialTruncation_covariance_term_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialTruncation_threshold_rate_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransfer

#print axioms RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransfer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.ConditionalPolynomialOptimization then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in polynomial envelope transfer closure"
  logInfo m!"Audited {names.size} polynomial envelope transfer declarations."
