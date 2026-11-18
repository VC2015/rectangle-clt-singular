import RectangleCLTCompanion.SplitV4.GaussianIntrinsicConcentration
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_fixed_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_independent_shift,
    ``RectangleCLT.Companion.SplitV4.gaussianIntrinsicConcentration_fixed_shift,
    ``RectangleCLT.Companion.SplitV4.gaussianAffineMaximum_test_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
