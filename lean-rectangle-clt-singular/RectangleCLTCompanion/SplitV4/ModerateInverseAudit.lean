import RectangleCLTCompanion.SplitV4.ModerateInverse
import Lean.Util.CollectAxioms

/-! Quantitative scalar consequences of the checked local cumulant
remainders. These are helpers for F.1, with the Taylor and inverse-root
inputs visible in their exact public types. -/

#print RectangleCLT.Companion.SplitV4.moderateInverseDisplacementConstant
#print RectangleCLT.Companion.SplitV4.moderateInverseExpansionConstant
#print RectangleCLT.Companion.SplitV4.moderateLegendreConstant
#print RectangleCLT.Companion.SplitV4.moderateCancellationConstant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_root_displacement
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_inverse_expansion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_legendre_expansion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_sqrt_variance_expansion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_tilted_threshold_cancellation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.moderate_tilted_threshold_scale

#print axioms RectangleCLT.Companion.SplitV4.moderate_legendre_expansion
#print axioms RectangleCLT.Companion.SplitV4.moderate_tilted_threshold_cancellation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.ModerateInverse then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in moderate inverse/cancellation closure"
  logInfo m!"Audited {names.size} moderate inverse and cubic-cancellation helpers."
