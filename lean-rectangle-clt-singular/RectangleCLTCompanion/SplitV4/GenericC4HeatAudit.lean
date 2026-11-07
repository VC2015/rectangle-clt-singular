import RectangleCLTCompanion.SplitV4.GenericC4Heat
import Lean.Util.CollectAxioms

/-! Strict audit of the actual general-C4-test heat decomposition and its
dominated differentiation prerequisites. -/

#print RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatExpectation
#print RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatDerivative
#print RectangleCLT.Companion.SplitV4.C4Test.hessianCoordinate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.generic_shifted_gaussian_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatDerivative_eq_spatial_add_heat_of_integrable
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatDerivative_eq_spatial_add_heat
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_genericVariableHeatExpectation_spatial_add_heat
#print axioms RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatDerivative_eq_spatial_add_heat
#print axioms RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_genericVariableHeatExpectation_spatial_add_heat

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let modName := env.header.moduleNames[idx.toNat]!
        if modName == `RectangleCLTCompanion.SplitV4.GenericC4Heat ||
            modName == `RectangleCLTCompanion.SplitV4.GenericC4Interpolation then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 heat differentiation closure"
  logInfo m!"Audited {names.size} generic C4 heat and interpolation theorems."
