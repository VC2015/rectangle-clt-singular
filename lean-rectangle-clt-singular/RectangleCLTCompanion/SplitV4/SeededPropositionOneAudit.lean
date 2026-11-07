import RectangleCLTCompanion.SplitV4.SeededPropositionOne
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.seededRestorationBandwidth
#print RectangleCLT.Companion.SplitV4.seededDerivativeConstant
#print RectangleCLT.Companion.SplitV4.normalizedSeededCubicTerm
#print RectangleCLT.Companion.SplitV4.normalizedSeededFourthRemainder
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_derivative_bounds
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seeded_time_comparison_bound
#print axioms RectangleCLT.Companion.SplitV4.seeded_derivative_bounds
#print axioms RectangleCLT.Companion.SplitV4.seeded_time_comparison_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.SeededPathBase",
    "RectangleCLTCompanion.SplitV4.SeededGaussianSplit",
    "RectangleCLTCompanion.SplitV4.SeededRestorationBounds",
    "RectangleCLTCompanion.SplitV4.SeededRestorationRates",
    "RectangleCLTCompanion.SplitV4.NormalizedSeededPath",
    "RectangleCLTCompanion.SplitV4.NormalizedSeededEndpoints",
    "RectangleCLTCompanion.SplitV4.SeededTimeIntegration",
    "RectangleCLTCompanion.SplitV4.CalibratedSeededExpectation",
    "RectangleCLTCompanion.SplitV4.SeededPathIdentity",
    "RectangleCLTCompanion.SplitV4.SeededRemainderBound",
    "RectangleCLTCompanion.SplitV4.SeededPropositionOne"]
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
      throwError "Unexpected axiom {ax} in seeded Proposition One closure"
  logInfo m!"Audited {names.size} actual seeded-base, normalization, derivative-bound and time-integration theorem declarations; only the permitted three axioms."
  logInfo "The terminal seeded derivative and comparison bounds assume only the genuine bounded independent data, actual signed relative third and both fourth matrices, unit marginal variances and bandwidth condition. The signed cubic aggregate and copy-dependent fourth shifts retain their actual laws; no analytic oracle is supplied."
