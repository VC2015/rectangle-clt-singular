import RectangleCLTCompanion.SplitV4.ShiftComparison
import Lean.Util.CollectAxioms

/-! Whole-statement audit for Lemma F.2 (`lower:shift-comparison`). The
distribution function, supremum distance, and second-derivative supremum
norm are actual definitions, printed alongside both exact endpoints. -/

#print RectangleCLT.Companion.SplitV4.realCDF
#print RectangleCLT.Companion.SplitV4.realCDFDistance
#print RectangleCLT.Companion.SplitV4.secondDerivativeSupNorm
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.realCDFDistance_le_iff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.secondDerivativeSupNorm_le_iff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_shift_comparison_of_second_derivative_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_shift_comparison

#print axioms RectangleCLT.Companion.SplitV4.independent_shift_cdf
#print axioms RectangleCLT.Companion.SplitV4.shifted_taylor_bound
#print axioms RectangleCLT.Companion.SplitV4.expected_cdf_shift_taylor_error
#print axioms RectangleCLT.Companion.SplitV4.independent_shift_comparison_of_second_derivative_bound
#print axioms RectangleCLT.Companion.SplitV4.independent_shift_comparison

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.ShiftComparison" then
          names := names.push n
  unless names.size > 0 do
    throwError "No shift-comparison theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Lemma F.2 dependency closure"
  logInfo m!"Audited all {names.size} Lemma F.2 theorem declarations; only the three permitted axioms."
