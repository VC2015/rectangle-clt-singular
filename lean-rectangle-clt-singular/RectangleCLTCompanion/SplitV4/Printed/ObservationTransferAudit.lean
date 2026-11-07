import RectangleCLTCompanion.SplitV4.Printed.PolyhedralTransfer
import RectangleCLTCompanion.SplitV4.Printed.SkewLowerModerate
import RectangleCLTCompanion.SplitV4.Printed.ObservationRates
import Lean.Util.CollectAxioms

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
