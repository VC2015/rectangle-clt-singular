import RectangleCLTCompanion.SplitV4.SymmetricFamilyRareCalibration
import RectangleCLTCompanion.SplitV4.SymmetricFamilyPolynomial
import Lean.Util.CollectAxioms

/-! Strict actual-law audit for masked rare maximum calibration and polynomial moments. -/
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.familyMasked_failure_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_familyMasked_maximum_mean_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.symmetricFamily_polynomialIndependent

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.SymmetricFamilyRareCalibration",
    "RectangleCLTCompanion.SplitV4.SymmetricFamilyPolynomial"]
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
      throwError "Unexpected axiom {ax} in actual masked maximum/moment declarations"
  logInfo m!"Audited {names.size} actual masked maximum/moment theorem declarations; only the permitted three axioms."
