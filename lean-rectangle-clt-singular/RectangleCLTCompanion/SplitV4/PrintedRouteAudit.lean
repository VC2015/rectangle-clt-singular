import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import RectangleCLTCompanion.SplitV4.Printed.BoundedConcentration
import RectangleCLTCompanion.SplitV4.Printed.ClockMarkov
import RectangleCLTCompanion.SplitV4.Printed.CovariancePotential
import RectangleCLTCompanion.SplitV4.Printed.DenseOptimal
import RectangleCLTCompanion.SplitV4.Printed.EndpointGaussian
import RectangleCLTCompanion.SplitV4.Printed.EnvelopeConditionalPair
import RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrder
import RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrderSigned
import RectangleCLTCompanion.SplitV4.Printed.GammaDifferentiation
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness
import RectangleCLTCompanion.SplitV4.Printed.GaussianMollification
import RectangleCLTCompanion.SplitV4.Printed.GaussianOrthogonalIndependence
import RectangleCLTCompanion.SplitV4.Printed.InterpolationSignedHessian
import RectangleCLTCompanion.SplitV4.Printed.InterpolationTriangle
import RectangleCLTCompanion.SplitV4.Printed.LowerActivation
import RectangleCLTCompanion.SplitV4.Printed.LowerLaplace
import RectangleCLTCompanion.SplitV4.Printed.LowerModerateGeneral
import RectangleCLTCompanion.SplitV4.Printed.LowerOptimal
import RectangleCLTCompanion.SplitV4.Printed.MatrixNonnegativeContraction
import RectangleCLTCompanion.SplitV4.Printed.MatrixNuclearReduction
import RectangleCLTCompanion.SplitV4.Printed.MatrixPaddingRoute
import RectangleCLTCompanion.SplitV4.Printed.MatrixReferenceLimit
import RectangleCLTCompanion.SplitV4.Printed.MatrixSectorPaper
import RectangleCLTCompanion.SplitV4.Printed.MatrixShiftIdentity
import RectangleCLTCompanion.SplitV4.Printed.ObservationRates
import RectangleCLTCompanion.SplitV4.Printed.PolyhedralTransfer
import RectangleCLTCompanion.SplitV4.Printed.PolynomialAssembly
import RectangleCLTCompanion.SplitV4.Printed.PolynomialRegimes
import RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusMoments
import RectangleCLTCompanion.SplitV4.Printed.ProjectionTail
import RectangleCLTCompanion.SplitV4.Printed.RademacherMaximumGlobal
import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorApplication
import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorAveraging
import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorFiber
import RectangleCLTCompanion.SplitV4.Printed.SkewLowerMaintext
import RectangleCLTCompanion.SplitV4.Printed.SkewLowerModerate
import RectangleCLTCompanion.SplitV4.Printed.WeightedSignProduct
import RectangleCLTCompanion.SplitV4.PrintedProofs

/-! Fresh strict execution of every nested printed-route audit.
The bodies are verbatim apart from import consolidation. Regenerate with
split-v4-certification/printed-proof-extension/generate_route_audit.py after
changing a nested audit. The existing checkpoint runner executes this file
directly, rerunning every route and transitive-axiom assertion. -/

-- Source SHA-256: 983ce7a316be6bb9980ec74afa63979b56ad9e71d6a6db970d9e2262db049ef4
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/ClockAudit.lean

#print RectangleCLT.Companion.SplitV4.Printed.clockLogVector
#print RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum
#print RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius
#print RectangleCLT.Companion.SplitV4.Printed.expectedClockCutoff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_le_log_add_one_of_exponential_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.expectedClockCutoff_bad_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if #["RectangleCLTCompanion.SplitV4.Printed.ClockTails", "RectangleCLTCompanion.SplitV4.Printed.ClockMean", "RectangleCLTCompanion.SplitV4.Printed.ClockMarkov"].contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed clock expectation route"
  logInfo m!"Audited {names.size} printed exponential-clock tail, expected-width and Markov declarations; only permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/ClockAudit.lean

-- Source SHA-256: f3ab9a8e52c3f971109aed6a163709f185734c542d724dfe4bc21eed68b78bfd
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/CovariancePotentialAudit.lean

#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian_ge_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_isProbability
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_integral_potential_density
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_of_potential_hessian
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_via_printed_potential

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.CovariancePotential" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed CovariancePotential closure"
  logInfo m!"Audited {names.size} printed CovariancePotential theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/CovariancePotentialAudit.lean

-- Source SHA-256: bdd2ff5edc72f089a193a2d49edb60aa4bbab15270c98d34345dcabc74074166
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/CubeAudit.lean

/-! Strict transitive audit for the printed C.1 proof and the bounded
intrinsic Lemma 1 chain that now uses it. -/

#print RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax
#print RectangleCLT.Companion.SplitV4.Printed.realAffineCubeMaximum
#print RectangleCLT.Companion.SplitV4.Printed.normalizedCubeRamp
#print RectangleCLT.Companion.SplitV4.Printed.cubeRampPrimitive
#print RectangleCLT.Companion.SplitV4.Printed.cubeGradientRadial
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exists_small_unique_threshold_perturbation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.cube_boundary_event_subset_perturbed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.convexOn_cubeRampPrimitive_comp_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_upper
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed

#print axioms RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed
#print axioms RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString.startsWith "RectangleCLTCompanion.SplitV4.Printed.Cube" ||
            mod.toString == "RectangleCLTCompanion.SplitV4.Printed.BoundedConcentration" then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed-cube theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed C.1 / bounded Lemma 1 dependency closure"
  logInfo m!"Audited all {names.size} printed-cube / bounded-concentration theorem declarations; only the three permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/CubeAudit.lean

-- Source SHA-256: 1d6d784d7c14e46ae2f9b1cd3b30be1541c9347864203b3a5ad4d6f8056567ba
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/DenseAudit.lean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseAmplitude
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseScale_factor
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_actual_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_printedDense_rank_and_gap
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_printedDense_rate_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseLower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal_constant_first

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let owned := #["DenseCalibration", "DenseLower", "DenseOptimal"]
  for (n,ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if owned.any (fun suffix => mod == "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_,state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed dense construction"
  for n in state.visited.toList do
    let s := n.toString
    if s == "RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransfer" ||
        s == "RectangleCLT.Companion.SplitV4.polynomialMomentWorstDistanceCLT" ||
        s == "RectangleCLT.Companion.SplitV4.denseMomentOptimal" ||
        s == "RectangleCLT.Companion.SplitV4.tendsto_amplifiedFamily_discrepancy_div_scale" ||
        s == "RectangleCLT.Companion.SplitV4.denseMomentLower" ||
        s == "RectangleCLT.Companion.SplitV4.denseMomentLower_of_two_le" ||
        s == "RectangleCLT.Companion.SplitV4.tendsto_denseFamily_discrepancy_div_rate" ||
        s == "RectangleCLT.Companion.SplitV4.denseFamily_distance_ereal_liminf" then
      throwError "Forbidden old dense final-bound bypass {n}"
  let checkRoute : Name → Array Name → CommandElabM Unit := fun target required => do
    let (_,deps) := ((CollectAxioms.collect target).run env).run {}
    for n in required do
      unless deps.visited.contains n do
        throwError "Printed dense terminal {target} omits required route declaration {n}"
  let required := #[``RectangleCLT.Companion.SplitV4.Printed.printedDenseLower,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_amplifiedFamily_discrepancy_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold,
    ``RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransfer,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability]
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal required
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.printedDenseOptimal_constant_first required
  logInfo m!"Audited {names.size} exact B/2 amplitude, actual moment, covariance rank/gap, rate and dense lower declarations; no old dense final-bound bypass and only the three permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/DenseAudit.lean

-- Source SHA-256: 88ca720f5e23ff1281effa8bead9e1554a339f01c922034d8e33baa2db211a08
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/EndpointAudit.lean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.endpoint_error_le_average_radius
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_boundary_layer_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_boundary_layer_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.lemma2_printed_endpoint_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.smoothingLemma2_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussian_endpoint_expected_width
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.gaussianEndpointSmoothing_printed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if #["RectangleCLTCompanion.SplitV4.Printed.ClockTails",
          "RectangleCLTCompanion.SplitV4.Printed.ClockMean",
          "RectangleCLTCompanion.SplitV4.Printed.ClockMarkov",
          "RectangleCLTCompanion.SplitV4.Printed.EndpointMixture",
          "RectangleCLTCompanion.SplitV4.Printed.EndpointConcentration",
          "RectangleCLTCompanion.SplitV4.Printed.EndpointLemma2",
          "RectangleCLTCompanion.SplitV4.Printed.EndpointGaussian"].contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed endpoint proof route"
  logInfo m!"Audited {names.size} printed clock/Lemma 2/G.2 declarations; only permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/EndpointAudit.lean

-- Source SHA-256: 871580c3686b7c7d0b21278f9930aaa7db7f1f18846e282d357c16c53e9fb3e0
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/EnvelopeZeroOrderSignedAudit.lean

#print axioms RectangleCLT.Companion.SplitV4.Printed.signedTwoFaceSmoother_eq_closedBox
#print axioms RectangleCLT.Companion.SplitV4.Printed.no_uniform_signed_zero_order_averaged_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrderSigned" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed signed-face order-zero counterexample"
  logInfo m!"Audited {names.size} signed-face order-zero scope theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/EnvelopeZeroOrderSignedAudit.lean

-- Source SHA-256: 6c4e062d01d66b64ae9d04dcbee12c621df89d43bd28801e4caa1872b132a323
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GammaDifferentiationAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.GammaDifferentiation" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed GammaDifferentiation closure"
  logInfo m!"Audited {names.size} printed GammaDifferentiation theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GammaDifferentiationAudit.lean

-- Source SHA-256: bb5a31eccd7808984a95710abd07627ba4afa79339c1f9ffb4fcb64b95a74bad
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianMaximumMomentsAudit.lean

#check RectangleCLT.Companion.SplitV4.Printed.gaussian_norm_tail_union
#check RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_by_union_tail
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_in_probability
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_integrability
#check RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_L1
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability
#check RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold_tail_identity
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_printedNormalMaxThreshold_div_sqrt_two_log
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMoments,
    `RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumQuantile,
    `RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.contains env.header.moduleNames[idx.toNat]! then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in the printed Gaussian maximum moment route"
  let mut seen : NameSet := {}
  let mut todo := #[``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability]
  let mut i := 0
  while i < todo.size do
    let n := todo[i]!
    i := i + 1
    unless seen.contains n do
      seen := seen.insert n
      if n == ``RectangleCLT.Companion.SplitV4.tendsto_gaussianMaximumMean_div_sqrt_log ||
          n == ``RectangleCLT.Companion.SplitV4.integral_gaussian_norm_sq_le ||
          n == ``RectangleCLT.Companion.SplitV4.integral_finiteGaussianMaximum_sq_le then
        throwError "The new printed UI proof still uses the preserved alternative moment endpoint {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? then todo := todo ++ v.getUsedConstants
  logInfo m!"Audited {names.size} printed Gaussian maximum moment/quantile theorems transitively; only the three permitted axioms. Checked {seen.size} constants in the new UI/mean closure; no old mean limit or old quantitative maximum second-moment bound."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianMaximumMomentsAudit.lean

-- Source SHA-256: d8ef5382b6a5f0e94bc82a9580ae8d4917f91c273aeb0ec22d982ea777e3302c
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianMaximumSmoothnessAudit.lean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_tail_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_negative_region
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_positive_region
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_far_positive
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_small_dimension
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumCDF_second_derivative_global_bound
#print axioms RectangleCLT.Companion.SplitV4.Printed.normalMaximumCDF_second_derivative_global_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness" then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed global Gaussian maximum smoothness declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed Gaussian maximum smoothness closure"
  logInfo m!"Audited all {names.size} printed Gaussian maximum smoothness theorem declarations; only the three permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianMaximumSmoothnessAudit.lean

-- Source SHA-256: dd40aef476fee87b032799223d56234917d327fd63be29d7f9ea82bafe9767c2
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianMollificationAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.GaussianMollification" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed GaussianMollification closure"
  logInfo m!"Audited {names.size} printed GaussianMollification theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianMollificationAudit.lean

-- Source SHA-256: 9b37df7268ac7e85d2b4b0f22a3b201d9726a796aee0802836c10ee9208dd57e
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianOrthogonalIndependenceAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.GaussianOrthogonalIndependence" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed GaussianOrthogonalIndependence closure"
  logInfo m!"Audited {names.size} printed GaussianOrthogonalIndependence theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GaussianOrthogonalIndependenceAudit.lean

-- Source SHA-256: 2bc908f8ac19aa47f98a2d7e15a96283e18fe6310c10a077f4ed94a8532f545c
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GeometryAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["PolarPlane", "ProjectionTail", "RidgeSector", "RidgeAngular",
    "RidgeSectorGeometry", "RidgeSectorFiber"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.any (fun m => env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed." ++ m) then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed polar/sector declarations selected"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed polar/sector argument"
  logInfo m!"Audited {names.size} printed polar, Gaussian radial-tail and sector declarations; only permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/GeometryAudit.lean

-- Source SHA-256: 6a5c6a205de7b3a22a2f7333d58847630df5853568460ac2cc3d0c0c5083170e
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/InterpolationAudit.lean

#print axioms RectangleCLT.Companion.SplitV4.Printed.centered_value_hessian_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.centered_gradient_hessian_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.hasDerivAt_seededExpectation_signedHessian
#print axioms RectangleCLT.Companion.SplitV4.Printed.conditional_finite_cauchy_schwarz
#print axioms RectangleCLT.Companion.SplitV4.Printed.conditional_finite_pair_contraction
#print axioms RectangleCLT.Companion.SplitV4.Printed.no_uniform_zero_order_averaged_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array String := #[
    "RectangleCLTCompanion.SplitV4.Printed.InterpolationTaylorTwo",
    "RectangleCLTCompanion.SplitV4.Printed.InterpolationSignedHessian",
    "RectangleCLTCompanion.SplitV4.Printed.EnvelopeConditionalPair",
    "RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrder"]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed interpolation closure"
  logInfo m!"Audited {names.size} printed interpolation/envelope theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/InterpolationAudit.lean

-- Source SHA-256: 3ada88ea232530c2d900063b598bc36c9a6fd3ef66a3f1ef05c8a2d65f27ade3
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/InterpolationTriangleAudit.lean

#print axioms RectangleCLT.Companion.SplitV4.Printed.weighted_triangle_integral_swap
#print axioms RectangleCLT.Companion.SplitV4.Printed.signed_hessian_fourth_kernel_expectation
#print axioms RectangleCLT.Companion.SplitV4.Printed.genericRowOperator_fourth_from_signed_hessian

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.InterpolationTriangle" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed triangular interpolation transition"
  logInfo m!"Audited {names.size} triangular interpolation theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/InterpolationTriangleAudit.lean

-- Source SHA-256: 3e41e0521eb8446dacda8c3387341907792509e111140a54484d89da64a3e114
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/LargeIncrementAudit.lean

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
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/LargeIncrementAudit.lean

-- Source SHA-256: 660c4f89b5f73540d7bc93538ac49e1fd7d3f7267f6323d6b92788e069a80d25
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/LowerAudit.lean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.uniformScalarModerateTail_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.independent_copy_variance_integral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyMaskedSignMaximum_all_active_real_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyGlobal_master_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.tendsto_sparseFamily_orthantError_div_rate_printed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["LowerActivation", "LowerMaster", "LowerGlobalRates", "LowerGlobalComparison",
    "LowerPrintedThreshold", "LowerTheorems", "LowerConstruction", "LowerOptimal", "LowerGaussianShifts",
    "LowerModerateArray", "LowerModerateCumulants",
    "LowerStrictTail", "LowerModerateTail", "LowerModerateGeneral", "LowerLaplace"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.any (fun m => env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed." ++ m) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed lower/F.1 proof route"
  logInfo m!"Audited {names.size} printed common-lower/F.1 declarations; only permitted axioms."

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[``RectangleCLT.Companion.SplitV4.Printed.uniformScalarModerateTail_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.smoothingLemma2_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.gaussianEndpointSmoothing_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_boundedFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_fourthFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_maskedFourthFamily_orthantError_div_rate_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_sparseFamily_orthantError_div_rate_printed]
  let forbidden := #[``RectangleCLT.Companion.SplitV4.smoothingLemma2,
    ``RectangleCLT.Companion.SplitV4.gaussianEndpointSmoothing,
    ``RectangleCLT.Companion.SplitV4.familyLocal_master_comparison,
    ``RectangleCLT.Companion.SplitV4.independent_local_shift_comparison,
    ``RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_amplifiedFamily_discrepancy_div_scale,
    ``RectangleCLT.Companion.SplitV4.tendsto_familyRare_discrepancy_div_scale]
  for target in targets do
    let (_, state) := ((CollectAxioms.collect target).run env).run {}
    for bad in forbidden do
      if state.visited.contains bad then
        throwError "Old alternative final route {bad} occurs in dependency closure of {target}"
  let (_, f1) := ((CollectAxioms.collect targets[0]!).run env).run {}
  for bad in #[``RectangleCLT.Companion.SplitV4.moderateTiltVariance_exp_bounds,
    ``RectangleCLT.Companion.SplitV4.moderateArray_local_taylor,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_small_threshold,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_bound] do
    if f1.visited.contains bad then
      throwError "Old alternative F.1 step {bad} occurs in literal all-threshold F.1 closure"
  for required in #[``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_taylor_printed] do
    unless f1.visited.contains required do
      throwError "Literal printed F.1 step {required} is absent from final dependency closure"
  logInfo m!"Checked {targets.size} actual printed terminal dependency closures: old alternative endpoint/local-lower finals absent; literal F.1 omits old variance-minimization and small-threshold branches."

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[``RectangleCLT.Companion.SplitV4.Printed.boundedSymmetricLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.fourthMomentLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.maskedFourthLower_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.sparseMomentLower_printed]
  let required := #[``RectangleCLT.Companion.SplitV4.Printed.familyGlobal_master_comparison,
    ``RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error,
    ``RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability,
    ``RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_by_union_tail]
  let forbidden := #[``RectangleCLT.Companion.SplitV4.familyLocal_master_comparison,
    ``RectangleCLT.Companion.SplitV4.independent_local_shift_comparison,
    ``RectangleCLT.Companion.normalMaxThreshold,
    ``RectangleCLT.Companion.SplitV4.tendsto_gaussianMaximumMean_div_sqrt_log,
    ``RectangleCLT.Companion.SplitV4.boundedSymmetricLower,
    ``RectangleCLT.Companion.SplitV4.fourthMomentLower,
    ``RectangleCLT.Companion.SplitV4.maskedFourthLower,
    ``RectangleCLT.Companion.SplitV4.sparseMomentLower]
  for target in targets do
    let (_, state) := ((CollectAxioms.collect target).run env).run {}
    for needed in required do
      unless state.visited.contains needed do
        throwError "Printed lower step {needed} is absent from actual terminal {target}"
    for bad in forbidden do
      if state.visited.contains bad then
        throwError "Old alternative lower step {bad} occurs in actual printed terminal {target}"
  logInfo m!"Checked {targets.size} full T4/T5/T6/T8 construction closures: global master/CDF, exact printed quantile/density, Gaussian UI mean and union-tail moments present; old local and old quantile routes absent."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/LowerAudit.lean

-- Source SHA-256: 4fe5628685f13c690a28c01235a4c073682aa690f9629d48e927695bd478da51
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/LowerLaplaceAudit.lean

#print axioms RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison
#print axioms RectangleCLT.Companion.SplitV4.Printed.integrable_strict_laplace_correction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.LowerLaplace" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed strict Laplace closure"
  logInfo m!"Audited {names.size} printed strict Laplace theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/LowerLaplaceAudit.lean

-- Source SHA-256: 88e8fa2517ecaf3eafed50ad6692c07fa45a8022fd22fe7a874832e7357e124d
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixNonnegativeContractionAudit.lean

#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussian_integral_shift_pos_of_mass
#print axioms RectangleCLT.Companion.SplitV4.Printed.concaveOn_log_gaussian_convolution_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_cgf_sub_quadratic_eq_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_directional_variance_le_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussian_weightCovariance_contraction_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.nonnegativeLogConcave_indicator
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussian_convex_indicator_covariance_contraction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.MatrixNonnegativeContraction" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed nonnegative covariance closure"
  logInfo m!"Audited {names.size} printed nonnegative covariance theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixNonnegativeContractionAudit.lean

-- Source SHA-256: 4b875d18db78e74d1a9020d2ac3778fbfabbcce81000dbe787110532c8774975
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixNuclearReductionAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.MatrixNuclearReduction" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed MatrixNuclearReduction closure"
  logInfo m!"Audited {names.size} printed MatrixNuclearReduction theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixNuclearReductionAudit.lean

-- Source SHA-256: 306c98c5cd35796a9c2b6e8a9278117674b8666f99a54d93227d273df0c60475
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixPaddingRouteAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.MatrixPaddingRoute" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed MatrixPaddingRoute closure"
  logInfo m!"Audited {names.size} printed MatrixPaddingRoute theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixPaddingRouteAudit.lean

-- Source SHA-256: d216ada773c80f32d5d1f69b8e0236b81bae7fde2e85fa7cfb498f783d32aef2
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixReferenceLimitAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.MatrixReferenceLimit" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed MatrixReferenceLimit closure"
  logInfo m!"Audited {names.size} printed MatrixReferenceLimit theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixReferenceLimitAudit.lean

-- Source SHA-256: 57ada32e72ad68264cb2393578a1d6138929864eb45a52770bcfa8c561bc12f9
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixSectorAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if #["MatrixSectorBound", "MatrixSectorRegularized", "MatrixSectorPaper"].any
            (fun suffix => env.header.moduleNames[idx.toNat]!.toString ==
              "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in sector-derived printed B4 route"
  let forbidden := #[
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_succ,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_of_log_le_two,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer,
    ``RectangleCLT.Companion.SplitV4.logistic_matrix_estimate,
    ``RectangleCLT.Companion.SplitV4.logistic_matrix_bound_unit_independent,
    ``RectangleCLT.Companion.SplitV4.exists_logistic_matrix_paper_constant,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_estimate]
  let mut visited : NameSet := {}
  let mut pending := #[``RectangleCLT.Companion.SplitV4.Printed.sector_exists_logistic_matrix_paper_constant]
  let mut offset := 0
  while offset < pending.size do
    let n := pending[offset]!
    offset := offset + 1
    unless visited.contains n do
      visited := visited.insert n
      if forbidden.contains n then
        throwError "Printed matrix endpoint bypassed sector/full-Fatou route through {n}"
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          pending := pending ++ v.getUsedConstants
  logInfo m!"Audited {names.size} sector-derived printed B4 theorem declarations; only permitted axioms. Final full-padding/Fatou-before-compression endpoint closure checked across {visited.size} constants without old B4/B5 bounds, old MGF radius moments or block-first sector endpoint."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixSectorAudit.lean

-- Source SHA-256: 2d368c1ff87bd87b22ab680114311caff1618a46cbbf8a60c24cac7bae127bb5
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixShiftIdentityAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.MatrixShiftIdentity" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed MatrixShiftIdentity closure"
  logInfo m!"Audited {names.size} printed MatrixShiftIdentity theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/MatrixShiftIdentityAudit.lean

-- Source SHA-256: 9f40310880da58c2a1a75aa0d62b8c8dc73d6a60d01763f8cd49f8a3700aa04a
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/ObservationTransferAudit.lean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalized_observations_via_current_theorem
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.mem_psi1Scales_at_positive_norm_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.orlicz_transfer_via_printed_clipping
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.psi1_projected_at_exact_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.orlicz_polyhedral_via_printed_transfer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalized_observations_unequal_variance
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_polynomial_dimension_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.subexponential_polynomial_dimension_rate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.polynomial_dimension_log_factor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let owned := #["ObservationTransfer", "OrliczClosure", "OrliczTransfer", "PolyhedralTransfer", "SkewLowerModerate", "ObservationRates"]
  for (n,ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if owned.any (fun suffix => mod == "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_,state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed transfer/F1 law application"
  logInfo m!"Audited {names.size} printed normalization, exact Orlicz closure, projection and generic F1 application declarations; only the three permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/ObservationTransferAudit.lean

-- Source SHA-256: 6f35923bd55c6c247c683b539124d9e138da4cb36156221d6fe70907b2d16f76
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/PolynomialRegimesAudit.lean

#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_atTop_below_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_dominates_coordinate_below_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialMoment_four_uniform_bound
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_zero_above_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_negligible_to_coordinate_above_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_isBigO_polylog
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelope_rates_six
#check RectangleCLT.Companion.SplitV4.Printed.sparse_log_dimension_condition_of_log_n
#check RectangleCLT.Companion.SplitV4.Printed.sparse_regime_four_iff
#check RectangleCLT.Companion.SplitV4.Printed.envelope_tendsto_atTop_under_sparse_conditions_above_four

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.Printed.PolynomialRegimes then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in the printed polynomial regime arithmetic"
  logInfo m!"Audited {names.size} printed polynomial regime theorem declarations transitively; only propext, Classical.choice and Quot.sound."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/PolynomialRegimesAudit.lean

-- Source SHA-256: 92499fa40bde5019138a430a45f8de3519d52dedace03a6c91fc81d84bf6ae04
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/ProjectionRadiusAudit.lean

#print axioms RectangleCLT.Companion.SplitV4.Printed.rank_le_two_projection_tail
#print axioms RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_tail_union
#print axioms RectangleCLT.Companion.SplitV4.Printed.integral_pow_le_of_gaussian_tail_split
#print axioms RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_second_third_moments_from_radial_tail

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array String := #[
    "RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusLaw",
    "RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusUnion",
    "RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusMoments"]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed projection-radius closure"
  logInfo m!"Audited {names.size} printed projection-radius theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/ProjectionRadiusAudit.lean

-- Source SHA-256: 4bbc5a393697a2f570cf916467a4631f9581afdbfaca73a0d46544e1eab234bc
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/RademacherMaximumAudit.lean

#print RectangleCLT.Companion.SplitV4.Printed.rademacherGlobalError
#print RectangleCLT.Companion.SplitV4.Printed.rademacherGlobalSmallConstant
#print RectangleCLT.Companion.SplitV4.Printed.rademacherGlobalConstant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_scalar_berryEsseen
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_damped_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_low_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherUpperTail_subgaussian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_rademacher_cutoff_conditions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error
#print axioms RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString.startsWith
            "RectangleCLTCompanion.SplitV4.Printed.RademacherMaximum" then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed global Rademacher maximum declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed global Rademacher maximum closure"
  logInfo m!"Audited all {names.size} printed global Rademacher maximum theorem declarations; only the three permitted axioms."
  let forbidden := #[
    ``RectangleCLT.Companion.SplitV4.familyRademacher_log_tail,
    ``RectangleCLT.Companion.SplitV4.familyRademacherMaximum_pointwise_error,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_bound,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_small_threshold]
  let required := #[
    ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_copy_variance_integral]
  let mut visited : NameSet := {}
  let mut pending := #[``RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error]
  let mut offset := 0
  while offset < pending.size do
    let n := pending[offset]!
    offset := offset + 1
    unless visited.contains n do
      visited := visited.insert n
      if forbidden.contains n then
        throwError "Global printed Rademacher comparison bypassed the printed F.1 route through {n}"
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          pending := pending ++ v.getUsedConstants
  for n in required do
    unless visited.contains n do
      throwError "Global printed Rademacher comparison does not reach required printed F.1 input {n}"
  logInfo m!"Global Rademacher endpoint closure checked across {visited.size} constants: literal all-x F.1, Laplace IBP and copy variance reached; old F.1/small-x/log-tail endpoints absent."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/RademacherMaximumAudit.lean

-- Source SHA-256: 33dfaf8681765ca2a45bb82a688af2abd5aa76671279d60503abd193205aa16b
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/RidgeSectorApplicationAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.RidgeSectorApplication" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed RidgeSectorApplication closure"
  logInfo m!"Audited {names.size} printed RidgeSectorApplication theorem declarations; only the permitted three axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/RidgeSectorApplicationAudit.lean

-- Source SHA-256: 073fa894a75a091364b974f8356799f563dff4b2b0fc39b510f9713910e0040a
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/SectorAssemblyAudit.lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["FacetRadius", "RidgeSectorThreshold", "RidgeSectorBound", "RidgeSectorAveraging"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.any (fun m => env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed." ++ m) then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed sector assembly"
  let mut visited : NameSet := {}
  let mut pending := #[``RectangleCLT.Companion.SplitV4.Printed.averagedGaussianThresholdDerivative_sector_bound_of_log_le_two]
  let mut index := 0
  while index < pending.size do
    let n := pending[index]!
    index := index + 1
    unless visited.contains n do
      visited := visited.insert n
      if #[``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment,
          ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments,
          ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer,
          ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound].contains n then
        throwError "Printed sector route unexpectedly uses bypass {n}"
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          pending := pending ++ v.getUsedConstants
  logInfo m!"Audited {names.size} printed facet/sector assembly declarations; only permitted axioms."
  logInfo m!"Checked {visited.size} constants in the sector endpoint closure; old coordinate-MGF radius and rectangular-layer endpoints are absent."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/SectorAssemblyAudit.lean

-- Source SHA-256: 65fe0630f1b033fdf9b7b367cf39c26734fdb1145bff5daca845850a310c8a80
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/SkewLowerAudit.lean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.twoPoint_normalized_tail_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_log_tail_normalized_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_exact_product_asymptotic_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_mean_value_prefactor_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_detecting_rectangle_liminf_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_ereal_liminf_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_maintext_sharpness_from_F1

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let owned := #["SkewLowerModerate", "SkewLowerTail", "SkewLowerProduct", "SkewLowerMeanValue", "SkewLowerMaintext"]
  for (n,ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if owned.any (fun suffix => mod == "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_,state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed Theorem 3"
  for n in state.visited.toList do
    let s := n.toString
    if s == "RectangleCLT.Companion.SplitV4.moderateScalarTail_bound" ||
        s == "RectangleCLT.Companion.lowerSkew_cramer_eventually" ||
        s == "RectangleCLT.Companion.lowerScaleRectangle_liminf" ||
        s == "RectangleCLT.Companion.lowerScaleRectangleDistance_liminf" ||
        s == "RectangleCLT.Companion.skewedTwoPointLowerScale" ||
        s == "RectangleCLT.Companion.lowerConstructionDistance_le" ||
        s == "RectangleCLT.Companion.lowerConstructionDistance_ratio_eventually_le" then
      throwError "Forbidden old tail/final-bound bypass {n} in printed Theorem 3"
  let checkRoute : Name → Array Name → CommandElabM Unit := fun target required => do
    let (_,deps) := ((CollectAxioms.collect target).run env).run {}
    for n in required do
      unless deps.visited.contains n do
        throwError "Printed Theorem 3 terminal {target} omits required route declaration {n}"
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_ereal_liminf_from_F1
    #[``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail,
      ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
      ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison,
      ``RectangleCLT.Companion.SplitV4.Printed.skew_signed_product_normalized_from_F1]
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.skew_exact_product_asymptotic_from_F1
    #[``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail,
      ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
      ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison]
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.skew_mean_value_prefactor_from_F1
    #[``RectangleCLT.Companion.SplitV4.Printed.product_power_mean_value,
      ``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail,
      ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
      ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison]
  logInfo m!"Audited {names.size} printed F1 law application, skew-tail, exact signed product and lower-distance declarations; no old Cramer/final-bound bypass and only the three permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/SkewLowerAudit.lean

-- Source SHA-256: 017cb85a6b45021c7cad089efd01f9ba5ea6d0831b2da3ec0db6d1408c15670f
-- BEGIN PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/WeightedSignAudit.lean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.relativeRate_le_of_fourth_cost
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.weighted_sign_fourth_matrices
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_normalization
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_sign_actual_model
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_envelope_asymptotic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_fourth_asymptotic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_capped_logarithmic_gain

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let owned := #["WeightedSignExample", "WeightedSignRates", "WeightedSignProduct"]
  for (n,ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if owned.any (fun suffix => mod == "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_,state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed weighted-sign example"
  logInfo m!"Audited {names.size} actual weighted-sign product-law, exact fourth matrices, exceptional weights and capped logarithmic gain declarations; only the three permitted axioms."
-- END PRINTED_ROUTE RectangleCLTCompanion/SplitV4/Printed/WeightedSignAudit.lean
