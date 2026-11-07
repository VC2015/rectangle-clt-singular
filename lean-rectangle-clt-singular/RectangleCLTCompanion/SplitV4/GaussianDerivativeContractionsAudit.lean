import RectangleCLTCompanion.SplitV4.GaussianDerivativeContractions
import Lean.Util.CollectAxioms

/-! The printed endpoints retain actual Gaussian factors, arbitrary original
coefficient dependence, and genuine first-moment weight budgets. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.weighted_gaussian_gradient_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.weighted_gaussian_hessian_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.slepian_weighted_gradient_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.slepian_weighted_hessian_contraction

#print axioms RectangleCLT.Companion.SplitV4.gaussian_gradient_contraction
#print axioms RectangleCLT.Companion.SplitV4.gaussian_hessian_contraction
#print axioms RectangleCLT.Companion.SplitV4.weighted_gaussian_gradient_contraction
#print axioms RectangleCLT.Companion.SplitV4.weighted_gaussian_hessian_contraction
#print axioms RectangleCLT.Companion.SplitV4.gaussianLaw_map_scalar
#print axioms RectangleCLT.Companion.SplitV4.slepian_weighted_gradient_contraction
#print axioms RectangleCLT.Companion.SplitV4.slepian_weighted_hessian_contraction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.GaussianDerivativeContractions" then
          names := names.push n
  unless names.size > 0 do
    throwError "No Gaussian derivative contraction declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Gaussian derivative contraction closure"
  logInfo m!"Audited all {names.size} Gaussian derivative contraction theorem declarations."
