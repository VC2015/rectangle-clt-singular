import RectangleCLTCompanion.SplitV4.Printed.BoundedConcentration
import Lean.Util.CollectAxioms

/-! Strict transitive audit for the printed C.1 proof and the bounded
intrinsic Lemma 1 chain that now uses it. -/

#print RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax
#print RectangleCLT.Companion.SplitV4.Printed.realAffineCubeMaximum
#print RectangleCLT.Companion.SplitV4.Printed.normalizedCubeRamp
#print RectangleCLT.Companion.SplitV4.Printed.cubeRampPrimitive
#print RectangleCLT.Companion.SplitV4.Printed.cubeGradientRadial
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exists_small_unique_threshold_perturbation
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.cube_boundary_event_subset_perturbed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.convexOn_cubeRampPrimitive_comp_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_lower
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_upper
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed

#print axioms RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed
#print axioms RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString.startsWith "RectangleCLTCompanion.SplitV4.Printed.Cube" ||
            mod.toString == "RectangleCLTCompanion.SplitV4.Printed.BoundedConcentration" then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed-cube theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed C.1 / bounded Lemma 1 dependency closure"
  logInfo m!"Audited all {names.size} printed-cube / bounded-concentration theorem declarations; only the three permitted axioms."
