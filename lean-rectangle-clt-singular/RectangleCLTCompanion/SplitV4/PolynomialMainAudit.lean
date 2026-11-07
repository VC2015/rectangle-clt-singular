import RectangleCLTCompanion.SplitV4.PolynomialMain
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.polynomialBennettObservationRate
#print RectangleCLT.Companion.SplitV4.polynomialEnvelopeTransferRate
#print RectangleCLT.Companion.SplitV4.polynomialCombinedRate
#print RectangleCLT.Companion.SplitV4.polynomialUniversalConstant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialMomentCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialMomentWorstDistanceCLT
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialBennettObservationRate_four
#print axioms RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.PolynomialMain" then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in whole Theorem 2 dependency closure"
  logInfo m!"Audited {names.size} whole polynomial CLT theorem declarations."
