import RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusMoments
import Lean.Util.CollectAxioms

#print axioms RectangleCLT.Companion.SplitV4.Printed.rank_le_two_projection_tail
#print axioms RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_tail_union
#print axioms RectangleCLT.Companion.SplitV4.Printed.integral_pow_le_of_gaussian_tail_split
#print axioms RectangleCLT.Companion.SplitV4.Printed.thresholdProjectionRadius_second_third_moments_from_radial_tail

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array String := #[
    "RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusLaw",
    "RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusUnion",
    "RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusMoments"]
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
      throwError "Unexpected axiom {ax} in printed projection-radius closure"
  logInfo m!"Audited {names.size} printed projection-radius theorem declarations; only the permitted three axioms."
