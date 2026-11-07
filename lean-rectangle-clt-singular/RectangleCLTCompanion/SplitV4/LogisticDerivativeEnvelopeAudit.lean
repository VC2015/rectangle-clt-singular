import RectangleCLTCompanion.SplitV4.LogisticDerivativeFaceEnvelope
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_iteratedFDeriv_logisticNullWeight_shift_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.iteratedFDeriv_linearLogistic_partition

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if #["RectangleCLTCompanion.SplitV4.LogisticScalarJets", "RectangleCLTCompanion.SplitV4.LogisticDerivativeEnvelope", "RectangleCLTCompanion.SplitV4.LogisticDerivativeFaceEnvelope"].contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in all-order logistic derivative envelope"
  logInfo m!"Audited {names.size} all-order logistic derivative envelope declarations; only the three permitted axioms."
