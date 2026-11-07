import RectangleCLTCompanion.SplitV4.BennettNormalization
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.rawPolynomialEnvelopeScale
#print RectangleCLT.Companion.SplitV4.rawPolynomialFourthScale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalized_q_envelope_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalized_coordinate_fourth_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rawPolynomialParameter_eq

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.BennettNormalization" then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in polynomial moment normalization"
  logInfo m!"Audited {names.size} polynomial moment normalization theorem declarations."
