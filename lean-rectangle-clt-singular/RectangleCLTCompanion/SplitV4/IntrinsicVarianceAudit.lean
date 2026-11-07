import RectangleCLTCompanion.SplitV4.IntrinsicVariance
import Lean.Util.CollectAxioms

/-! Strict audit of the actual copy/sign symmetrization and conditional
variance chain in Appendix C. -/

#print RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget
#print RectangleCLT.Companion.SplitV4.cubeConditionalRowSquares
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_square_sum_fluctuation_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_pair_bad_variance_probability_le
#print axioms RectangleCLT.Companion.SplitV4.independent_sum_norm_symmetrization
#print axioms RectangleCLT.Companion.SplitV4.independent_square_sum_fluctuation_le
#print axioms RectangleCLT.Companion.SplitV4.integral_cubeConditionalRowSquares_coordinate
#print axioms RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_eq_half_copy
#print axioms RectangleCLT.Companion.SplitV4.cubePairIntrinsicBudget_le_norm_sum
#print axioms RectangleCLT.Companion.SplitV4.cube_pair_bad_variance_probability_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.IntrinsicVariance" then
          names := names.push n
  unless names.size > 0 do
    throwError "No intrinsic-variance theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in intrinsic-variance dependency closure"
  logInfo m!"Audited all {names.size} intrinsic-variance theorem declarations; only the three permitted axioms."
