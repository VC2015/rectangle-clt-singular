import RectangleCLTCompanion.SplitV4.PairedSlepian
import Lean.Util.CollectAxioms

/-! These exact identities certify the vector trapezoidal and centered-copy
steps of Lemma G.3. The full Slepian time derivative and conditional-array
coefficient assembly are not asserted by this audit. -/

#print RectangleCLT.Companion.SplitV4.C4Test
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.ofContDiff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.gradient_segment_trapezoidal
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.integral_paired_gradient_increment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.integral_paired_stein_with_large_increment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.integral_paired_stein_with_independent_base

#print axioms RectangleCLT.Companion.SplitV4.C4Test.gradient_segment_trapezoidal
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_gradient_segment_trapezoidal
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_paired_gradient_increment
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_paired_truncated_gradient
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_centered_copy_gradient
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_paired_stein_with_large_increment
#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_paired_stein_with_independent_base
#print axioms RectangleCLT.Companion.SplitV4.C4Test.ofContDiff

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[``RectangleCLT.Companion.SplitV4.C4Test.ofContDiff]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.PairedSlepian" then
          names := names.push n
  unless names.size > 1 do
    throwError "No paired-Slepian theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in paired-Slepian ingredient closure"
  logInfo m!"Audited {names.size - 1} paired-Slepian theorem declarations, including private helpers, and the canonical C4 constructor."
