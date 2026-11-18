import RectangleCLTArxivV1.SupplementalHKernelMass
import RectangleCLTArxivV1.SupplementalHProjectionMoments
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_dominated_kernel_mass_properties,
    ``RectangleCLTArxivV1.supplementalHProjectionRadius,
    ``RectangleCLTArxivV1.supplementalHProjectionRadius_ge_one,
    ``RectangleCLTArxivV1.measurable_supplementalHProjectionRadius,
    ``RectangleCLTArxivV1.abs_faceDot_le_supplementalHProjectionRadius,
    ``RectangleCLTArxivV1.supplementalHProjectionRadius_moment_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target}: {axioms.toList}"
