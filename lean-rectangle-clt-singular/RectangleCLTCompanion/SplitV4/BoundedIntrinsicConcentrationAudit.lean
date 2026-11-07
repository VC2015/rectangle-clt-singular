import RectangleCLTCompanion.SplitV4.BoundedIntrinsicConcentration
import Lean.Util.CollectAxioms

/-! Audit of the bounded half of Lemma 1 (`lem:concentration`). The actual
polyhedron layer, intrinsic expected maximum, arbitrary positive common
variance, and same-space independent shift are visible in the endpoint. -/

#print RectangleCLT.Companion.SplitV4.projectedFacePolyhedron
#print RectangleCLT.Companion.SplitV4.projectedFaceLayer
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_product_shift_min
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_independent_shift_min
#print axioms RectangleCLT.Companion.SplitV4.bounded_intrinsic_boundary_fixed_shift
#print axioms RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_product_shift
#print axioms RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_product_shift_log
#print axioms RectangleCLT.Companion.SplitV4.bounded_intrinsic_layer_independent_shift_min

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.BoundedIntrinsicConcentration" then
          names := names.push n
  unless names.size > 0 do
    throwError "No bounded intrinsic-concentration theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in bounded intrinsic-concentration dependency closure"
  logInfo m!"Audited all {names.size} bounded intrinsic-concentration theorem declarations; only the three permitted axioms."
