import RectangleCLTCompanion.SplitV4.RelativeMain
import Lean.Util.CollectAxioms

/-! Strict audit of the actual relative CLT and face transfer closure. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeFourthMomentCLT

#print axioms RectangleCLT.Companion.SplitV4.relativeFourthMomentCLT

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.relativeBandwidthConstant,
    ``RectangleCLT.Companion.SplitV4.relativeSmoothComparisonConstant,
    ``RectangleCLT.Companion.SplitV4.relativeCoreConstant,
    ``RectangleCLT.Companion.SplitV4.relativeUniversalConstant,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidthConstant_ge_four,
    ``RectangleCLT.Companion.SplitV4.relativeBandwidthConstant_ge_seeded,
    ``RectangleCLT.Companion.SplitV4.relativeSmoothComparisonConstant_pos,
    ``RectangleCLT.Companion.SplitV4.one_le_relativeCoreConstant,
    ``RectangleCLT.Companion.SplitV4.one_le_relativeUniversalConstant,
    ``RectangleCLT.Companion.SplitV4.relativeMomentCLT_core,
    ``RectangleCLT.Companion.SplitV4.relativeMomentCLT,
    ``RectangleCLT.Companion.SplitV4.relativeFourthMomentCLT,
    ``RectangleCLT.Companion.SplitV4.relativeEnvelopeCLT]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative CLT/face closure"
  logInfo "Audited 13 RelativeMain declarations; only the three standard axioms are permitted."
