import RectangleCLTCompanion.SplitV4.ConditionalTruncationKernel
import Lean.Util.CollectAxioms

/-! Strict audit for the constructed exceptional-data Markov kernel and
its exact reconstruction identity against all bounded measurable tests. -/

#print RectangleCLT.Companion.SplitV4.truncationMaskWeight
#print RectangleCLT.Companion.SplitV4.selectedConditionalProduct
#print RectangleCLT.Companion.SplitV4.conditionalTruncationKernel
#print RectangleCLT.Companion.SplitV4.conditionalExceptionalShift

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.productLaw_eq_truncationMaskMixture
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_product_conditionalTruncationKernel
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.selectConditionalArrays_eq_retained_add_shift

#print axioms RectangleCLT.Companion.SplitV4.productLaw_eq_truncationMaskMixture
#print axioms RectangleCLT.Companion.SplitV4.conditionalArrays_select_law
#print axioms RectangleCLT.Companion.SplitV4.observed_selected_tag_ae
#print axioms RectangleCLT.Companion.SplitV4.integral_product_conditionalTruncationKernel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[
    ``RectangleCLT.Companion.SplitV4.selectedConditionalLaw_isProbability,
    ``RectangleCLT.Companion.SplitV4.selectedConditionalProduct_isProbability,
    ``RectangleCLT.Companion.SplitV4.badConditionalProduct_isProbability,
    ``RectangleCLT.Companion.SplitV4.conditionalTruncationKernel_isMarkov]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.ConditionalTruncationKernel" then
          unless names.contains name do names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional-truncation kernel closure"
  logInfo m!"Audited {names.size} conditional-truncation kernel theorem and probability-instance declarations; only the permitted three axioms."
  logInfo "The actual exceptional-data disintegration is reconstructed explicitly. Numeric covariance estimates and the polynomial CLT endpoint remain separate."
