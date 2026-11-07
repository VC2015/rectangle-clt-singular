import RectangleCLTCompanion.SplitV4.MaskedFourthLower
import Lean.Util.CollectAxioms

/-! Exact actual-law audit for the growing fourth-moment lower result. -/

#print RectangleCLT.Companion.SplitV4.maskedFourthFamilyParameters
#print RectangleCLT.Companion.SplitV4.maskedFourthMomentLowerRate
#print RectangleCLT.Companion.SplitV4.maskedFourthLog
#print RectangleCLT.Companion.SplitV4.maskedFourthCount
#print RectangleCLT.Companion.SplitV4.maskedFourthTheta
#print RectangleCLT.Companion.SplitV4.maskedFourthPi
#print RectangleCLT.Companion.SplitV4.maskedFourthAmplitude
#print RectangleCLT.Companion.SplitV4.maskedFourthVariance
#print RectangleCLT.Companion.SplitV4.maskedFourthScale
#print RectangleCLT.Companion.SplitV4.maskedFourthRate
#print RectangleCLT.Companion.SplitV4.MaskedFourthLowerConstruction

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthLower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_maskedFourthFamily_orthantError_div_rate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthFamily_distance_ereal_liminf

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthFamilyCalibration

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_maskedFourthFamily_polynomialIndependent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.maskedFourthFamily_identities

#print axioms RectangleCLT.Companion.SplitV4.maskedFourthLower

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    "RectangleCLTCompanion.SplitV4.MaskedFourthFamily",
    "RectangleCLTCompanion.SplitV4.MaskedFourthCalibration",
    "RectangleCLTCompanion.SplitV4.MaskedFourthLower" ]
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
      throwError "Unexpected axiom {ax} in growing fourth-moment lower declarations"
  logInfo m!"Audited {names.size} growing fourth-moment lower theorem declarations, each transitively; only the permitted three axioms."
  logInfo "Theorem 6 is proved with the actual masked finite family and exact paper rate. Both moments of C4(B_n), iid central symmetry, matching Gaussian, actual orthant limit 1/(4e), and full rectangle-distance extended-real lower limit are conclusions. The terminal assumes only dimensions and envelope tending to infinity, Lambda/logm tending to zero and the paper rate tending to zero."
