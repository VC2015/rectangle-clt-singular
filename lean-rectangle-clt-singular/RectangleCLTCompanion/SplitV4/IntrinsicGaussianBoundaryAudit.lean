import RectangleCLTCompanion.SplitV4.IntrinsicGaussianBoundary
import Lean.Util.CollectAxioms

/-! Strict audit for the exact intrinsic Gaussian boundary estimate. -/

#print RectangleCLT.Companion.SplitV4.gaussianFaceWeight
#print RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum
#print RectangleCLT.Companion.SplitV4.smoothGaussianFaceGradient
#print RectangleCLT.Companion.SplitV4.smoothGaussianFaceHessian
#print RectangleCLT.Companion.SplitV4.positiveGaussianFaceMaximum

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoothGaussianFaceHessian_trace
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary_logarithmic

#print axioms RectangleCLT.Companion.SplitV4.smoothGaussianFaceMaximum_stein
#print axioms RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound
#print axioms RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary
#print axioms RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary_absoluteMaximum
#print axioms RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary_logarithmic
#print axioms RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary_Ioc
#print axioms RectangleCLT.Companion.SplitV4.intrinsicGaussianBoundary_min_one

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.IntrinsicGaussianBoundary" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in intrinsic Gaussian boundary closure"
  logInfo m!"Audited {names.size} intrinsic Gaussian boundary theorem declarations; only the permitted three axioms."
  logInfo "The exact coefficient-two boundary inequality is discharged from actual Gaussian Stein, softmax convergence, and genuine C1 ramps. No covariance gap, invertibility, distinct-row, or desired-concentration premise is assumed."
