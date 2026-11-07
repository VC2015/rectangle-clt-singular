import RectangleCLTCompanion.SplitV4.Printed.DenseOptimal
import Lean.Util.CollectAxioms

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
