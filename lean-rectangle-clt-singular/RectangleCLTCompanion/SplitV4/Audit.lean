import RectangleCLTCompanion.SplitV4.Main
import Lean.Util.CollectAxioms

/-!
Exact public contracts and strict transitive axiom audit for the split-V4
checkpoint.  Printing an older theorem here establishes neither fresh
execution nor correspondence with a stronger manuscript statement.  The
execution record stores those facts separately.
-/

set_option pp.proofs false
set_option pp.universes true

-- The probability classes, full measurable rectangle class, actual covariance,
-- and rates are printed alongside the endpoint types so that their assumptions
-- are not hidden behind proposition or structure names.
#print RectangleCLT.BoundedIndependentHypotheses
#print RectangleCLT.Rect
#print RectangleCLT.Rect.carrier
#print RectangleCLT.sumVector
#print RectangleCLT.covariance
#print RectangleCLT.gaussianLaw
#print RectangleCLT.rectangleError
#print RectangleCLT.dimensionLog
#print RectangleCLT.Companion.logPlus
#print RectangleCLT.Companion.D_L
#print RectangleCLT.Companion.unrestrictedRate
#print RectangleCLT.Companion.UnrestrictedCLT
#print RectangleCLT.Companion.UnrestrictedCLTExists
#print RectangleCLT.Companion.normalizedObservationSum
#print RectangleCLT.Companion.subexponentialScale
#print RectangleCLT.Companion.psi1Scales
#print RectangleCLT.Companion.psi1Norm
#print RectangleCLT.Companion.Psi1IndependentHypotheses
#print RectangleCLT.Companion.SubexponentialIndependentHypotheses
#print RectangleCLT.Companion.rectangleDistance
#print RectangleCLT.Companion.lowerConstructionDistance
#print RectangleCLT.Companion.lowerSkewRate
#print RectangleCLT.Companion.skewLowerScaleConstant
#print RectangleCLT.Companion.LowerConstructionProperties
#print RectangleCLT.Companion.SkewedTwoPointLowerScale
#print RectangleCLT.Companion.SplitV4.QuadraticLE
#print RectangleCLT.Companion.SplitV4.relativeThirdMatrix
#print RectangleCLT.Companion.SplitV4.relativeFourthMatrix
#print RectangleCLT.Companion.SplitV4.relativeFreshFourthMatrix
#print RectangleCLT.Companion.SplitV4.RelativeMomentBounds
#print RectangleCLT.Companion.SplitV4.closedBoxSmoothingGap
#print RectangleCLT.Companion.SplitV4.smoothingDiscrepancy
#print RectangleCLT.Companion.weightMass
#print RectangleCLT.Companion.weightMean
#print RectangleCLT.faceDot
#print RectangleCLT.vectorNormSq

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsRectangleDistanceCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsCLTExists
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLT_psi1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.subexponentialRectangleDistanceCLTExists
set_option pp.all true in
#check RectangleCLT.Companion.subexponentialCLT_psi1
set_option pp.all true in
#check RectangleCLT.Companion.skewedTwoPointLowerScale
set_option pp.all true in
#check RectangleCLT.Companion.unrestrictedCLT
set_option pp.all true in
#check RectangleCLT.Companion.gaussian_mean_relative_to_one_face
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleDistance_le_smoothingDiscrepancy_add_endpoint

#check RectangleCLT.Companion.unrestrictedCLTExists
#check RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent
#check RectangleCLT.Companion.gaussian_factor_exists_of_subexponential

#print axioms RectangleCLT.Companion.SplitV4.normalizedObservationsCLT
#print axioms RectangleCLT.Companion.subexponentialCLT_psi1
#print axioms RectangleCLT.Companion.skewedTwoPointLowerScale
#print axioms RectangleCLT.Companion.unrestrictedCLT
#print axioms RectangleCLT.Companion.unrestrictedCLTExists
#print axioms RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent
#print axioms RectangleCLT.Companion.gaussian_factor_exists_of_subexponential
#print axioms RectangleCLT.Companion.gaussian_mean_relative_to_one_face

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[
    ``RectangleCLT.Companion.subexponentialCLT_psi1,
    ``RectangleCLT.Companion.skewedTwoPointLowerScale,
    ``RectangleCLT.Companion.unrestrictedCLT,
    ``RectangleCLT.Companion.unrestrictedCLTExists,
    ``RectangleCLT.Companion.gaussian_mean_relative_to_one_face,
    ``RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent,
    ``RectangleCLT.Companion.gaussian_factor_exists_of_subexponential]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString.startsWith "RectangleCLTCompanion.SplitV4." then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in split-V4 checkpoint dependency closure"
  logInfo m!"Audited {names.size} split-V4 checkpoint theorem declarations and reused endpoints; only propext, Classical.choice and Quot.sound."
  logInfo "This checkpoint does not certify all split-V4 statements or revised analytic proof routes."
