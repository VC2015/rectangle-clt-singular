import RectangleCLTCompanion.SplitV4.Printed.EndpointGaussian
import Lean.Util.CollectAxioms

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
