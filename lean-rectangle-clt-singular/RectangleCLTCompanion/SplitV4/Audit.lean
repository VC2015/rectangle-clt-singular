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
#print RectangleCLT.Companion.SplitV4.gaussianSmoothingConstant
#print RectangleCLT.Companion.SplitV4.bennettTruncate
#print RectangleCLT.Companion.SplitV4.envelopeMaximumConstant
#print RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparisonConstant
#print RectangleCLT.Companion.SplitV4.polyhedronError
#print RectangleCLT.Companion.SplitV4.polyhedralDistance
#print RectangleCLT.Companion.SplitV4.coordinateFourthBudget
#print RectangleCLT.Companion.SplitV4.diagonalFourth
#print RectangleCLT.Companion.SplitV4.C4Test
#print RectangleCLT.Companion.SplitV4.C4Test.ofContDiff
#print RectangleCLT.Companion.SplitV4.smootherC4Test
#print RectangleCLT.Companion.SplitV4.originalSigma
#print RectangleCLT.Companion.SplitV4.copyAverage
#print RectangleCLT.Companion.SplitV4.productArrayLargeMean
#print RectangleCLT.Companion.SplitV4.productArrayTruncatedCovariance
#print RectangleCLT.Companion.SplitV4.copyArrayLargeMean
#print RectangleCLT.Companion.SplitV4.copyArrayTruncatedCovariance
#print RectangleCLT.Companion.SplitV4.pairedIncrement
#print RectangleCLT.Companion.SplitV4.matrixMaxEntryNorm
#print RectangleCLT.Companion.SplitV4.conditionalVectorLaw
#print RectangleCLT.Companion.SplitV4.conditionalGoodProductLaw
#print RectangleCLT.Companion.SplitV4.conditionalRetainedSummand
#print RectangleCLT.Companion.SplitV4.conditionalTruncationKernel
#print RectangleCLT.Companion.SplitV4.normalizedSummands
#print RectangleCLT.Companion.SplitV4.coordinateFourthMomentSums
#print RectangleCLT.Companion.SplitV4.arrayFourthMomentBudget
#print RectangleCLT.Companion.SplitV4.deltaOne
#print RectangleCLT.Companion.SplitV4.largeIncrementMasterConstant
#print RectangleCLT.Companion.SplitV4.largeIncrementMasterRate
#print RectangleCLT.Companion.SplitV4.pairedTailVariance
#print RectangleCLT.Companion.SplitV4.pairedTailExpectedMaximum
#print RectangleCLT.Companion.SplitV4.realCDF
#print RectangleCLT.Companion.SplitV4.realCDFDistance
#print RectangleCLT.Companion.SplitV4.secondDerivativeSupNorm
#print RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses
#print RectangleCLT.Companion.SplitV4.polynomialClassDistances
#print RectangleCLT.Companion.SplitV4.polynomialWorstDistance
#print RectangleCLT.Companion.SplitV4.PolynomialModelBound
#print RectangleCLT.Companion.SplitV4.polynomialBennettObservationRate
#print RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransferRate
#print RectangleCLT.Companion.SplitV4.polynomialCombinedRate
#print RectangleCLT.Companion.SplitV4.polynomialUniversalConstant
#print RectangleCLT.Companion.SplitV4.cubeUniformLaw
#print RectangleCLT.Companion.SplitV4.affineCubeMaximum
#print RectangleCLT.Companion.SplitV4.positiveLinearMaximum
#print RectangleCLT.Companion.SplitV4.intrinsicCubeMean
#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters
#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters.variance
#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters.scale
#print RectangleCLT.Companion.SplitV4.familySeedLaw
#print RectangleCLT.Companion.SplitV4.familyArrayLaw
#print RectangleCLT.Companion.SplitV4.familyObservation
#print RectangleCLT.Companion.SplitV4.familyRawObservations
#print RectangleCLT.Companion.SplitV4.CommonSymmetricFamilyProperties

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalizedObservationsCLT
#print RectangleCLT.Companion.SplitV4.BoundedConcentrationContract
#print RectangleCLT.Companion.SplitV4.GaussianConcentrationContract
#print RectangleCLT.Companion.SplitV4.moderateArrayCGF
#print RectangleCLT.Companion.SplitV4.moderateArrayGamma
#print RectangleCLT.Companion.SplitV4.moderateScalarSum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.lemma_concentration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformScalarModerateTail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_fourth_admissibility
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
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianEndpointSmoothing
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.truncated_bennett_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.truncated_bennett_maximum_zero_variance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_maximum_under_envelope_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.unrestrictedGaussianComparisonExists
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedPolyhedralEnvelopeCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.orliczPolyhedralCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_slepianExpectation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smootherC4Test_fourthDiagonal_eq_diagonalFourth
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_common_point_fourth_random_data
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_coordinateFourthBudget_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.copyAverage_ae_eq_condExp
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalRetained_normalized_covariance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianComparisonWithLargeIncrementRemainders
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_shift_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransfer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennettPolynomialCLT_observations
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialWorstDistance_le_iff_modelBound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsic_cube_boundary
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsic_cube_mean_le_sqrt_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.symmetricFamilyProperties
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT

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
