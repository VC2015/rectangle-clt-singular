import RectangleCLTCompanion.SubexponentialMain
import Lean.Util.CollectAxioms

/-! Inspect the actual end-to-end statements, then reject every nonstandard
axiom anywhere in the transitive closure of the new proof modules. -/

#print RectangleCLT.Companion.SubexponentialIndependentHypotheses
#print RectangleCLT.Companion.Psi1IndependentHypotheses
#print RectangleCLT.Companion.SubexponentialCLT
#print RectangleCLT.Companion.FixedGapSubexponentialCLT
#check RectangleCLT.Companion.subexponentialCLT
#check RectangleCLT.Companion.fixedGapSubexponentialCLT
#check RectangleCLT.Companion.subexponentialCLT_psi1
#check RectangleCLT.Companion.fixedGapSubexponentialCLT_psi1
#check RectangleCLT.Companion.gaussian_factor_exists_of_subexponential
#check RectangleCLT.Companion.subexponentialCLTExists
#check RectangleCLT.Companion.fixedGapSubexponentialCLTExists

#print axioms RectangleCLT.Companion.subexponentialCLT
#print axioms RectangleCLT.Companion.fixedGapSubexponentialCLT
#print axioms RectangleCLT.Companion.subexponentialCLT_psi1
#print axioms RectangleCLT.Companion.fixedGapSubexponentialCLT_psi1
#print axioms RectangleCLT.Companion.gaussian_factor_exists_of_subexponential

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString.startsWith "RectangleCLTCompanion.Subexponential" then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in sub-exponential dependency closure"
  logInfo m!"Audited {names.size} sub-exponential theorem declarations; only propext, Classical.choice and Quot.sound."
