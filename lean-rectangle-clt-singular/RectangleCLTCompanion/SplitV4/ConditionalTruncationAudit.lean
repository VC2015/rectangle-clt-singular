import RectangleCLTCompanion.SplitV4.ConditionalTruncation
import Lean.Util.CollectAxioms

/-! Strict audit of actual conditional laws and fixed-mask models.
The full sigma-field disintegration and polynomial CLT remain pending. -/

#print RectangleCLT.Companion.SplitV4.conditionalVectorLaw
#print RectangleCLT.Companion.SplitV4.goodConditionalLaw
#print RectangleCLT.Companion.SplitV4.conditionalGoodMean
#print RectangleCLT.Companion.SplitV4.conditionalGoodProductLaw
#print RectangleCLT.Companion.SplitV4.conditionalRetainedSummand

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_good_bad_mixture
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exceptional_probability_lt_quarter
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.goodConditional_covariance_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalRetained_normalized_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.originalGoodPart_boundedIndependent

#print axioms RectangleCLT.Companion.SplitV4.conditional_good_bad_mixture
#print axioms RectangleCLT.Companion.SplitV4.goodConditional_covariance_tail
#print axioms RectangleCLT.Companion.SplitV4.conditionalRetained_normalized_covariance
#print axioms RectangleCLT.Companion.SplitV4.originalGoodPart_boundedIndependent

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[
    ``RectangleCLT.Companion.SplitV4.conditionalVectorLaw_isProbability,
    ``RectangleCLT.Companion.SplitV4.goodConditionalLaw_isProbability,
    ``RectangleCLT.Companion.SplitV4.conditionalGoodProductLaw_isProbability]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.ConditionalTruncation" then
          unless names.contains name do names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional-truncation dependency closure"
  logInfo m!"Audited {names.size} conditional-truncation theorem and probability-instance declarations; only the permitted three axioms."
  logInfo "Full conditioning on the mask/exceptional-value sigma-field and the polynomial CLT endpoint are not asserted."
