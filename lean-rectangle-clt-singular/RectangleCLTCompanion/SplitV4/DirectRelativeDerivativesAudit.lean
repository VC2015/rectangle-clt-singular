import RectangleCLTCompanion.SplitV4.DirectCubicMoments
import RectangleCLTCompanion.SplitV4.DirectFourthRestoration
import RectangleCLTCompanion.SplitV4.DirectFourthAveraging
import RectangleCLTCompanion.SplitV4.SignedCoordinateMoments
import RectangleCLTCompanion.SplitV4.DirectInitialization
import Lean.Util.CollectAxioms

/-! Strict audit of direct relative derivative inputs for Proposition 1.
These are genuine signed cubic and restored fourth-copy estimates; the
path construction and initialization integration are separate joins. -/

#print RectangleCLT.Companion.SplitV4.relativeCubicContraction
#print RectangleCLT.Companion.SplitV4.directCopyCoordinate
#print RectangleCLT.Companion.SplitV4.directCopyVector
#print RectangleCLT.Companion.SplitV4.signedCoordinateFaceEquiv
#print RectangleCLT.Companion.SplitV4.signedCoordinateRows
#print RectangleCLT.Companion.SplitV4.directSlepianFourthRemainder
#print RectangleCLT.Companion.SplitV4.directInitializationGap
#print RectangleCLT.Companion.SplitV4.initializationDiscrepancy
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.RelativeMomentBounds.abs_third_entry_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeCubicContraction_eq_sum_integral_canonical_third
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_relativeCubicContraction_and_integral_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.RelativeMomentBounds.sum_integral_abs_copy_coordinate_four_product_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sum_integral_norm_fourth_shift_copies_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sum_integral_norm_fourth_shift_copies_common_base_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_relativeCubicContraction_full_smoother_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_directSlepianCubicTerm_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.directSlepian_fourth_copy_data
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_directSlepianFourthRemainder_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.direct_initialization_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.initializationDiscrepancy_le
#print axioms RectangleCLT.Companion.SplitV4.relativeCubicContraction_eq_sum_integral_canonical_third
#print axioms RectangleCLT.Companion.SplitV4.sum_integral_norm_fourth_shift_copies_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mods : Array Name := #[
    `RectangleCLTCompanion.SplitV4.DirectRelativeDerivatives,
    `RectangleCLTCompanion.SplitV4.DirectCubicMoments,
    `RectangleCLTCompanion.SplitV4.DirectFourthProducts,
    `RectangleCLTCompanion.SplitV4.DirectFourthRestoration,
    `RectangleCLTCompanion.SplitV4.DirectFourthAveraging,
    `RectangleCLTCompanion.SplitV4.SignedCoordinateSmoother,
    `RectangleCLTCompanion.SplitV4.SignedCoordinateMoments,
    `RectangleCLTCompanion.SplitV4.SlepianEnvelope,
    `RectangleCLTCompanion.SplitV4.DirectSlepianCubic,
    `RectangleCLTCompanion.SplitV4.DirectSlepianFourth,
    `RectangleCLTCompanion.SplitV4.DirectSlepianRemainder,
    `RectangleCLTCompanion.SplitV4.DirectInitialization]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if mods.contains env.header.moduleNames[idx.toNat]! then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in direct relative derivative closure"
  logInfo m!"Audited {names.size} direct signed-cubic and restored-fourth derivative theorems."
