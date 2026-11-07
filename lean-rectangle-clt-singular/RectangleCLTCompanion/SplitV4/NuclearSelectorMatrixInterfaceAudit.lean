import RectangleCLTCompanion.SplitV4.NuclearSelectorMatrixInterface
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.logisticPrivateBase
#print RectangleCLT.Companion.SplitV4.activeFaceProjection
#print RectangleCLT.Companion.SplitV4.RectangleBaseConcentration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedSelectorMatrixEstimate_of_rectangle_concentration
#print axioms RectangleCLT.Companion.SplitV4.averagedSelectorMatrixEstimate_of_rectangle_concentration

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.LogisticProjectedPadding",
    "RectangleCLTCompanion.SplitV4.LogisticProjectedBound",
    "RectangleCLTCompanion.SplitV4.LogisticActiveFaces",
    "RectangleCLTCompanion.SplitV4.LogisticActiveConcentration",
    "RectangleCLTCompanion.SplitV4.LogisticSelectorMatrixBound",
    "RectangleCLTCompanion.SplitV4.NuclearSelectorMatrixInterface"]
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
      throwError "Unexpected axiom {ax} in arbitrary-base selector matrix adapter"
  logInfo m!"Audited {names.size} private-padding, active-face and actual selector matrix interface theorem declarations; only the permitted three axioms."
  logInfo "The final historical matrix interface consumes only genuine original rectangle base concentration, unit factor rows and the displayed scale conditions. Arbitrary projected bases, rectangular singular factors, omitted faces, zero Gaussian scale and measurable nonsymmetric coefficients are included."
