import RectangleCLTArxivV1.SupplementalHLocalPartials
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.hasFDerivAt_of_local_continuous_coordinate_derivatives

open Lean Elab Command in
run_cmd do
  let target := ``RectangleCLTArxivV1.hasFDerivAt_of_local_continuous_coordinate_derivatives
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms target
  for ax in axioms do
    unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
  logInfo m!"{target} uses {axioms.toList}"
